/**
 * Virtual DOM patching algorithm based on Snabbdom by
 * Simon Friis Vindum (@paldepind)
 * Licensed under the MIT License
 * https://github.com/paldepind/snabbdom/blob/master/LICENSE
 *
 * modified by Evan You (@yyx990803)
 *
 * Not type-checking this because this file is perf-critical and the cost
 * of making flow understand it is not worth it.
 */

import VNode, { cloneVNode } from './vnode'
import config from '../config'
import { SSR_ATTR } from 'shared/constants'
import { registerRef } from './modules/template-ref'
import { traverse } from '../observer/traverse'
import { activeInstance } from '../instance/lifecycle'
import { isTextInputType } from 'web/util/element'

import {
  warn,
  isDef,
  isUndef,
  isTrue,
  isArray,
  makeMap,
  isRegExp,
  isPrimitive
} from '../util/index'

export const emptyNode = new VNode('', {}, [])

const hooks = ['create', 'activate', 'update', 'remove', 'destroy']

//判断是不是相同节点的方式，没有进行子节点的比较
//key相同，asyncFactory相同，
//两个条件组任意满足同一个 普通组件的相同条件【tag相同，isComment相同，data全都定义了，input类型相同】
//或者 异步组件的相同条件【isAsyncPlaceholder相同并且没有asyncFactory.error报错】
//不知道其中的某些属性对应着什么
function sameVnode (a, b) {
  return (
    a.key === b.key &&
    a.asyncFactory === b.asyncFactory &&
    ((a.tag === b.tag &&
      a.isComment === b.isComment &&
      isDef(a.data) === isDef(b.data) &&
      sameInputType(a, b))
      ||
      (isTrue(a.isAsyncPlaceholder) && isUndef(b.asyncFactory.error)))
  )
}

function sameInputType (a, b) {
  if (a.tag !== 'input') return true
  let i
  const typeA = isDef((i = a.data)) && isDef((i = i.attrs)) && i.type
  const typeB = isDef((i = b.data)) && isDef((i = i.attrs)) && i.type
  return typeA === typeB || (isTextInputType(typeA) && isTextInputType(typeB))
}

function createKeyToOldIdx (children, beginIdx, endIdx) {
  let i, key
  const map = {}

  //从指定的开始序号遍历到指定的结束序号
  //为map中的每个key赋值它对应的index
  for (i = beginIdx; i <= endIdx; ++i) {
    key = children[i].key
    if (isDef(key)) map[key] = i
  }
  //返回key与index的映射
  return map
}

export function createPatchFunction (backend) {
  //看起来有非常多操作，但不论如何最后返回的是一个函数
  let i, j
  const cbs: any = {} //在这里创建了cbs，后续会在createElm中使用

  const { modules, nodeOps } = backend
  //modules只在这里使用了，nodeOps在后续过程中使用了很多
  for (i = 0; i < hooks.length; ++i) {
    cbs[hooks[i]] = []
    for (j = 0; j < modules.length; ++j) {
      if (isDef(modules[j][hooks[i]])) {
        //把已经定义好了的函数推进去，这里只做了这个操作，对不起我看错了，后续有非常多的函数
        cbs[hooks[i]].push(modules[j][hooks[i]])
      }
    }
  }

  function emptyNodeAt (elm) {
    return new VNode(nodeOps.tagName(elm).toLowerCase(), {}, [], undefined, elm)
  }

  function createRmCb (childElm, listeners) {
    function remove () {
      if (--remove.listeners === 0) {
        removeNode(childElm)
      }
    }
    remove.listeners = listeners
    return remove
  }

  function removeNode (el) {
    const parent = nodeOps.parentNode(el)
    // element may have already been removed due to v-html / v-text
    if (isDef(parent)) {
      nodeOps.removeChild(parent, el)
    }
  }

  function isUnknownElement (vnode, inVPre) {
    return (
      !inVPre &&
      !vnode.ns &&
      !(
        config.ignoredElements.length &&
        config.ignoredElements.some(ignore => {
          return isRegExp(ignore)
            ? ignore.test(vnode.tag)
            : ignore === vnode.tag
        })
      ) &&
      config.isUnknownElement(vnode.tag)
    )
  }

  let creatingElmInVPre = 0

  /**
   * 
   * @param vnode 要新增的节点
   * @param insertedVnodeQueue 新增节点要插入的vnode队列
   * @param parentElm 父节点的dom实例引用
   * @param refElm 兄弟节点的dom实例应用，用来定位插入位置（可为空
   * @param nested QA:only used in createChildren? 被createChildren递归调用时才会为true
   * @param ownerArray QA:和新增节点要插入的vnode队列什么区别？孩子节点所属的孩子节点队列
   * @param index QA：要插入的位置吗？for循环中的序号
   * @returns 没有返回值，是纯操作的函数
   */
  function createElm (
    vnode,
    insertedVnodeQueue,
    parentElm?: any,
    refElm?: any,
    nested?: any,
    ownerArray?: any,
    index?: any
  ) {
    //0.拷贝节点的情况
    if (isDef(vnode.elm) && isDef(ownerArray)) {
      // 同一个列表里的节点有相似节点的情况下，直接拷贝？
      // This vnode was used in a previous render!
      // now it's used as a new node, overwriting its elm would cause
      // potential patch errors down the road when it's used as an insertion
      // reference node. Instead, we clone the node on-demand before creating
      // associated DOM element for it.
      // 按需克隆节点，并为其创建关联dom元素
      vnode = ownerArray[index] = cloneVNode(vnode)
    }

    //1.创建组件的情况
    //通常来说isRootInsert是true，构造函数Vnode创建的新节点默认是true
    vnode.isRootInsert = !nested // for transition enter check
    //如果是组件，去创建组件，和后续的创建节点情况不同。
    if (createComponent(vnode, insertedVnodeQueue, parentElm, refElm)) {
      //创建组件成功就return 0？
      return
    }

    //2.创建普通节点的情况
    //2.1元素节点，2.2备注节点，2.3文本节点
    const data = vnode.data
    const children = vnode.children
    const tag = vnode.tag


    if (isDef(tag)) {
      //2.1 创建元素节点
      if (__DEV__) {
        //测试环境下自定义组件tag或者元素节点的警告识别
        if (data && data.pre) {
          //TODO：元素节点标志为，data里为啥会有pre？pre是干嘛的？
          //而且测试环境下才会有这个比阿智
          creatingElmInVPre++
        }
        if (isUnknownElement(vnode, creatingElmInVPre)) {
          //查询是否有这个元素，没有就警告
          warn(
            'Unknown custom element: <' +
            tag +
            '> - did you ' +
            'register the component correctly? For recursive components, ' +
            'make sure to provide the "name" option.',
            vnode.context
          )
        }
      }

      //在这里开始区分不同的节点类型，对节点做不同的操作
      //vnode.ns里存了什么？存了namespaceMap，根据节点类型调用了不同的创建节点函数
      vnode.elm = vnode.ns
        ? nodeOps.createElementNS(vnode.ns, tag)
        : nodeOps.createElement(tag, vnode)

      //为css scoped添加字段
      setScope(vnode)

      //父组件字段准备完毕，开始创建子节点
      createChildren(vnode, children, insertedVnodeQueue)

      //如果有数据，开始调用create钩子函数
      if (isDef(data)) {
        invokeCreateHooks(vnode, insertedVnodeQueue)
      }

      //插入节点
      insert(parentElm, vnode.elm, refElm)

      if (__DEV__ && data && data.pre) {
        //任务完成，标识为归零
        creatingElmInVPre--
      }
    } else if (isTrue(vnode.isComment)) {
      //2.2创建备注节点
      //如果是注释节点，创建注释节点并插入
      vnode.elm = nodeOps.createComment(vnode.text)
      insert(parentElm, vnode.elm, refElm)
    } else {
      //2.3创建文本节点
      //只剩文本节点啦，创建文本节点并插入
      vnode.elm = nodeOps.createTextNode(vnode.text)
      insert(parentElm, vnode.elm, refElm)
    }

  }

  function createComponent (vnode, insertedVnodeQueue, parentElm, refElm) {
    let i = vnode.data
    if (isDef(i)) {
      const isReactivated = isDef(vnode.componentInstance) && i.keepAlive
      if (isDef((i = i.hook)) && isDef((i = i.init))) {
        i(vnode, false /* hydrating */)
      }
      // after calling the init hook, if the vnode is a child component
      // it should've created a child instance and mounted it. the child
      // component also has set the placeholder vnode's elm.
      // in that case we can just return the element and be done.
      if (isDef(vnode.componentInstance)) {
        initComponent(vnode, insertedVnodeQueue)
        insert(parentElm, vnode.elm, refElm)
        if (isTrue(isReactivated)) {
          reactivateComponent(vnode, insertedVnodeQueue, parentElm, refElm)
        }
        return true
      }
    }
  }

  function initComponent (vnode, insertedVnodeQueue) {
    if (isDef(vnode.data.pendingInsert)) {
      insertedVnodeQueue.push.apply(
        insertedVnodeQueue,
        vnode.data.pendingInsert
      )
      vnode.data.pendingInsert = null
    }
    vnode.elm = vnode.componentInstance.$el
    if (isPatchable(vnode)) {
      invokeCreateHooks(vnode, insertedVnodeQueue)
      setScope(vnode)
    } else {
      // empty component root.
      // skip all element-related modules except for ref (#3455)
      registerRef(vnode)
      // make sure to invoke the insert hook
      insertedVnodeQueue.push(vnode)
    }
  }

  function reactivateComponent (vnode, insertedVnodeQueue, parentElm, refElm) {
    let i
    // hack for #4339: a reactivated component with inner transition
    // does not trigger because the inner node's created hooks are not called
    // again. It's not ideal to involve module-specific logic in here but
    // there doesn't seem to be a better way to do it.
    let innerNode = vnode
    while (innerNode.componentInstance) {
      innerNode = innerNode.componentInstance._vnode
      if (isDef((i = innerNode.data)) && isDef((i = i.transition))) {
        for (i = 0; i < cbs.activate.length; ++i) {
          cbs.activate[i](emptyNode, innerNode)
        }
        insertedVnodeQueue.push(innerNode)
        break
      }
    }
    // unlike a newly created component,
    // a reactivated keep-alive component doesn't insert itself
    insert(parentElm, vnode.elm, refElm)
  }

  //就是朴素的插入dom节点操作
  function insert (parent, elm, ref) {
    if (isDef(parent)) {
      if (isDef(ref)) {
        //指定了同级，并且验证同级和父级是同级
        if (nodeOps.parentNode(ref) === parent) {
          nodeOps.insertBefore(parent, elm, ref)
        }
      } else {
        //如果没有指定同级位置就直接添加子元素
        nodeOps.appendChild(parent, elm)
      }
    }
  }

  function createChildren (vnode, children, insertedVnodeQueue) {
    //chilren不是数组并且该节点也不含文本更新时，直接跳过这个步骤
    if (isArray(children)) {
      //子节点是数组，就直接递归创建子节点
      if (__DEV__) {
        //测试环境才会测试有无重复的key
        checkDuplicateKeys(children)
      }
      for (let i = 0; i < children.length; ++i) {
        createElm(
          children[i],
          insertedVnodeQueue,
          vnode.elm,
          null,
          true,
          children,
          i
        )
      }
    } else if (isPrimitive(vnode.text)) {
      //children不是数据，并且当前节点包含文本更新时，就直接更新文本
      //Q：如果不是数组，并且是文本节点或者注释节点，就直接创建文本节点？？？注释节点呢？？？
      nodeOps.appendChild(vnode.elm, nodeOps.createTextNode(String(vnode.text)))
    }
  }

  function isPatchable (vnode) {
    while (vnode.componentInstance) {
      vnode = vnode.componentInstance._vnode
    }
    return isDef(vnode.tag)
  }

  function invokeCreateHooks (vnode, insertedVnodeQueue) {
    for (let i = 0; i < cbs.create.length; ++i) {
      cbs.create[i](emptyNode, vnode)
    }
    i = vnode.data.hook // Reuse variable
    if (isDef(i)) {
      if (isDef(i.create)) i.create(emptyNode, vnode)
      if (isDef(i.insert)) insertedVnodeQueue.push(vnode)
    }
  }

  // set scope id attribute for scoped CSS.
  // this is implemented as a special case to avoid the overhead
  // of going through the normal attribute patching process.
  function setScope (vnode) {
    let i
    if (isDef((i = vnode.fnScopeId))) {
      nodeOps.setStyleScope(vnode.elm, i)
    } else {
      let ancestor = vnode
      while (ancestor) {
        if (isDef((i = ancestor.context)) && isDef((i = i.$options._scopeId))) {
          nodeOps.setStyleScope(vnode.elm, i)
        }
        ancestor = ancestor.parent
      }
    }
    // for slot content they should also get the scopeId from the host instance.
    if (
      isDef((i = activeInstance)) &&
      i !== vnode.context &&
      i !== vnode.fnContext &&
      isDef((i = i.$options._scopeId))
    ) {
      nodeOps.setStyleScope(vnode.elm, i)
    }
  }

  /**
   * 
   * @param parentElm 
   * @param refElm 
   * @param vnodes 
   * @param startIdx 
   * @param endIdx 
   * @param insertedVnodeQueue 
   * @returns 纯操作函数，没有返回值
   */
  function addVnodes (
    parentElm,
    refElm,
    vnodes,
    startIdx,
    endIdx,
    insertedVnodeQueue
  ) {
    for (; startIdx <= endIdx; ++startIdx) {
      createElm(
        vnodes[startIdx],
        insertedVnodeQueue,
        parentElm,
        refElm,
        false,
        vnodes,
        startIdx
      )
    }
  }

  function invokeDestroyHook (vnode) {
    let i, j
    const data = vnode.data
    //OQ：什么情况下vnode会有data？
    if (isDef(data)) {
      //如果data定义了，就调用vnode.data.hook.destroy(vnode)
      if (isDef((i = data.hook)) && isDef((i = i.destroy))) i(vnode)
      //把根据平台保存的cbs.destroy里的函数全部调用一遍
      for (i = 0; i < cbs.destroy.length; ++i) cbs.destroy[i](vnode)
    }
    if (isDef((i = vnode.children))) {
      //看看有没有孩子节点，有的话就遍历递归调用invokeDestroyHook
      for (j = 0; j < vnode.children.length; ++j) {
        invokeDestroyHook(vnode.children[j])
      }
    }
  }

  function removeVnodes (vnodes, startIdx, endIdx) {
    for (; startIdx <= endIdx; ++startIdx) {
      const ch = vnodes[startIdx]
      if (isDef(ch)) {
        if (isDef(ch.tag)) {
          //有钩子的情况下先做前置处理，再移除
          removeAndInvokeRemoveHook(ch)
          invokeDestroyHook(ch)
        } else {
          // Text node
          removeNode(ch.elm)
        }
      }
    }
  }

  function removeAndInvokeRemoveHook (vnode, rm?: any) {
    if (isDef(rm) || isDef(vnode.data)) {
      //如果有自定义的remove函数就使用自定义的rm
      //Q：什么节点会有自定义的rm？
      let i
      const listeners = cbs.remove.length + 1
      if (isDef(rm)) {
        // we have a recursively passed down rm callback
        // increase the listeners count
        rm.listeners += listeners
      } else {
        // directly removing
        // 创建了rmove的函数，这个函数会在vnode.elm上调用removeNode
        rm = createRmCb(vnode.elm, listeners)
      }
      //先移除子节点，最后再移除自己
      // recursively invoke hooks on child component root node
      if (
        isDef((i = vnode.componentInstance)) &&
        isDef((i = i._vnode)) &&
        isDef(i.data)
      ) {
        removeAndInvokeRemoveHook(i, rm)
      }
      for (i = 0; i < cbs.remove.length; ++i) {
        cbs.remove[i](vnode, rm)
      }
      if (isDef((i = vnode.data.hook)) && isDef((i = i.remove))) {
        i(vnode, rm)
      } else {
        rm()
      }
    } else {
      //单纯的Node就直接移除
      removeNode(vnode.elm)
    }
  }

  //只有一个调用用例
  //updateChildren(elm, oldCh, ch, insertedVnodeQueue, removeOnly)
  function updateChildren (
    parentElm,
    oldCh,
    newCh,
    insertedVnodeQueue,
    removeOnly,//用于动效处理的标志
  ) {
    //嚯，好多遍历标志，让我猜猜这是什么遍历？
    //从0开始，到length-1结束
    //startVnode也从0开始
    //endVnode是最后一个
    let oldStartIdx = 0
    let newStartIdx = 0
    let oldEndIdx = oldCh.length - 1
    let oldStartVnode = oldCh[0]
    let oldEndVnode = oldCh[oldEndIdx]
    let newEndIdx = newCh.length - 1
    let newStartVnode = newCh[0]
    let newEndVnode = newCh[newEndIdx]

    //这四个标识位是用来干嘛的？
    let oldKeyToIdx, idxInOld, vnodeToMove, refElm

    // removeOnly is a special flag used only by <transition-group>
    // to ensure removed elements stay in correct relative positions
    // during leaving transitions
    const canMove = !removeOnly

    if (__DEV__) {
      //在开发环境下检测重复的key
      checkDuplicateKeys(newCh)
    }

    //当两个遍历的头尾标志都没有碰上就继续遍历，那意味着如果有一个遍历较短，就会提前结束遍历。
    //不会有漏掉的情况吗？
    while (oldStartIdx <= oldEndIdx && newStartIdx <= newEndIdx) {
      //前两个当前节点为空的情况都是被“新旧节点相似，且指定新节点位置不在头尾处”造成的。
      if (isUndef(oldStartVnode)) {
        //如果第一个旧节点是空的，那就切换到下一个节点
        //Q：为什么这里的备注说Vnode 已左移？
        oldStartVnode = oldCh[++oldStartIdx] // Vnode has been moved left
      } else if (isUndef(oldEndVnode)) {
        //如果最后一个旧节点是空的，那就前移到上一个节点
        //总之进行到这一步的时候，oldStartVnode和oldEndVnode都不能为空
        oldEndVnode = oldCh[--oldEndIdx]
      } else if (sameVnode(oldStartVnode, newStartVnode)) {
        //如果新旧开头节点相似，则深入迭代调用
        patchVnode(
          oldStartVnode,
          newStartVnode,
          insertedVnodeQueue,
          newCh,
          newStartIdx
        )
        //直到他这里的孩子全都调用结束，就继续后移两个遍历的开头节点
        //直到某一次，新旧开头节点不相似，进入下一个分支
        oldStartVnode = oldCh[++oldStartIdx]
        newStartVnode = newCh[++newStartIdx]
      } else if (sameVnode(oldEndVnode, newEndVnode)) {
        //如果新旧结尾节点相似，则深入迭代调用
        patchVnode(
          oldEndVnode,
          newEndVnode,
          insertedVnodeQueue,
          newCh,
          newEndIdx
        )
        //直到他这里的孩子全都调用结束，就继续后移两个遍历的开头节点
        //直到某一次，新旧结尾节点不相似，进入下一个分支
        oldEndVnode = oldCh[--oldEndIdx]
        newEndVnode = newCh[--newEndIdx]
      } else if (sameVnode(oldStartVnode, newEndVnode)) {
        // 如果旧开头节点和新结束节点相似，说明旧开头节点右移到了最后
        // 深入迭代调用
        // Vnode moved right
        // 是在patchVnode的时候移动的吗？好像不是
        patchVnode(
          oldStartVnode,
          newEndVnode,
          insertedVnodeQueue,
          newCh,
          newEndIdx
        )

        //搞搞动画，但是这里似乎和动画没关系
        //那开了动画怎么移动呢？
        //意思是不开动画的时候就直接移动了？
        //可是不开动画的时候都不会执行插入代码啊，那怎么移动呢？
        canMove &&
          nodeOps.insertBefore(
            parentElm,
            oldStartVnode.elm,
            nodeOps.nextSibling(oldEndVnode.elm)
          )

        //将对比标识位移动
        oldStartVnode = oldCh[++oldStartIdx]
        newEndVnode = newCh[--newEndIdx]
      } else if (sameVnode(oldEndVnode, newStartVnode)) {
        // 如果旧结束节点和新开头节点相似，说明旧结束节点左移到了开头
        // 深入迭代调用
        // Vnode moved left
        patchVnode(
          oldEndVnode,
          newStartVnode,
          insertedVnodeQueue,
          newCh,
          newStartIdx
        )
        //搞搞动画
        canMove &&
          nodeOps.insertBefore(parentElm, oldEndVnode.elm, oldStartVnode.elm)
        //将对比过后的标识位移动
        oldEndVnode = oldCh[--oldEndIdx]
        newStartVnode = newCh[++newStartIdx]
      } else {
        //如果新旧节点当前位置对比不相似，交叉对比位置不相似，进入该分支
        //如何排除节点是被移到了中间的情况？？？未处理节点始终位于中间，处理过后的节点始终不在这个范围，所以可以排除问题所述的情况。

        //如果oldKeyToIdx未定义，则为其赋值
        //只有一个地方调用了createKeyToOldIdx
        //在这里保存了oldChildren里key和index 的映射
        if (isUndef(oldKeyToIdx))
          oldKeyToIdx = createKeyToOldIdx(oldCh, oldStartIdx, oldEndIdx)

        //如果新开头节点有key，就直接看看旧节点中有没有对应的映射
        //如果没有，就直接把新开头节点丢入findIdxInOld中寻找旧孩子中是否有相似节点，如果有
        //如果可以找到新旧相似的节点，那么idxInOld是有值的
        idxInOld = isDef(newStartVnode.key)
          ? oldKeyToIdx[newStartVnode.key]
          : findIdxInOld(newStartVnode, oldCh, oldStartIdx, oldEndIdx)
        if (isUndef(idxInOld)) {
          //没有找到相似的节点，就新建节点
          // New element
          createElm(
            newStartVnode,
            insertedVnodeQueue,
            parentElm,
            oldStartVnode.elm,
            false,
            newCh,
            newStartIdx
          )
        } else {
          //找到了相似的节点，就直接让新旧节点开始更新，然后把对比后的旧节点删除防止重复对比
          vnodeToMove = oldCh[idxInOld]
          if (sameVnode(vnodeToMove, newStartVnode)) {
            patchVnode(
              vnodeToMove,
              newStartVnode,
              insertedVnodeQueue,
              newCh,
              newStartIdx
            )
            oldCh[idxInOld] = undefined
            canMove &&
              nodeOps.insertBefore(
                parentElm,
                vnodeToMove.elm,
                oldStartVnode.elm
              )
          } else {
            // same key but different element. treat as new element
            createElm(
              newStartVnode,
              insertedVnodeQueue,
              parentElm,
              oldStartVnode.elm,
              false,
              newCh,
              newStartIdx
            )
          }
        }
        //也更新一下新孩子节点的引用
        newStartVnode = newCh[++newStartIdx]
        //所以会出现旧孩子列表中间插着undefined的情况，在开头补足跳过
      }
    }


    //Q：不懂这里会在什么情况下触发
    //A 莫非是旧孩子节点遍历完了，提前结束了循环，此时新孩子节点里剩余的都是新增节点，所以全部添加
    if (oldStartIdx > oldEndIdx) {
      //如果出现了旧孩子节点开头超过结尾的情况，需要补充一些新节点
      refElm = isUndef(newCh[newEndIdx + 1]) ? null : newCh[newEndIdx + 1].elm
      //Q：怎么就直接新增了呢！
      addVnodes(
        parentElm,
        refElm,
        newCh,
        newStartIdx,
        newEndIdx,
        insertedVnodeQueue
      )
    } else if (newStartIdx > newEndIdx) {
      //A：那这里就是新孩子节点都遍历完了，那么多余的旧孩子节点就都可以删除了
      removeVnodes(oldCh, oldStartIdx, oldEndIdx)
    }
  }

  function checkDuplicateKeys (children) {
    const seenKeys = {}
    for (let i = 0; i < children.length; i++) {
      const vnode = children[i]
      const key = vnode.key
      if (isDef(key)) {
        if (seenKeys[key]) {
          warn(
            `Duplicate keys detected: '${ key }'. This may cause an update error.`,
            vnode.context
          )
        } else {
          seenKeys[key] = true
        }
      }
    }
  }

  function findIdxInOld (node, oldCh, start, end) {
    for (let i = start; i < end; i++) {
      const c = oldCh[i]
      if (isDef(c) && sameVnode(node, c)) return i
    }
  }

  //1.当新旧父节点相似时会调用该函数
  //patchVnode(oldVnode, vnode, insertedVnodeQueue, null, null, removeOnly：顶层传入的值)
  function patchVnode (
    oldVnode,//旧节点
    vnode,//新节点
    insertedVnodeQueue,//要插入的vnode队列引用
    ownerArray,//空的
    index,//空的
    removeOnly?: any//顶层调用传入的值，在该函数中也没有自己使用，而是传给了updateChildren
  ) {
    if (oldVnode === vnode) {
      // 7.4.1 静态节点
      //新旧节点完全是同一个引用时，直接返回，不用更新
      return
    }

    if (isDef(vnode.elm) && isDef(ownerArray)) {
      // 为父节点插入一个旧元素的拷贝，但是这个拷贝位于ownerArray的第index个位置
      // clone reused vnode
      vnode = ownerArray[index] = cloneVNode(vnode)
    }

    //将旧节点的elm引用复制给新节点，并且保存到elm常量中
    const elm = (vnode.elm = oldVnode.elm)

    if (isTrue(oldVnode.isAsyncPlaceholder)) {
      //异步组件的分支
      if (isDef(vnode.asyncFactory.resolved)) {
        hydrate(oldVnode.elm, vnode, insertedVnodeQueue)
      } else {
        vnode.isAsyncPlaceholder = true
      }
      return
    }

    // reuse element for static trees.
    // note we only do this if the vnode is cloned -
    // if the new node is not cloned it means the render functions have been
    // reset by the hot-reload-api and we need to do a proper re-render.
    // 静态树复用的情况

    //新旧节点都是isStatic，且新旧节点的key相同，且满足以下条件之一：
    //1.新节点是克隆节点
    //2.新节点是被克隆的原本节点
    if (
      isTrue(vnode.isStatic) &&
      isTrue(oldVnode.isStatic) &&
      vnode.key === oldVnode.key &&
      (isTrue(vnode.isCloned) || isTrue(vnode.isOnce))
    ) {
      vnode.componentInstance = oldVnode.componentInstance
      return
    }

    let i
    const data = vnode.data
    if (isDef(data) && isDef((i = data.hook)) && isDef((i = i.prepatch))) {
      //进行了一些patch子元素之前的预处理
      //vnode.data.hook.prepatch(oldVnode,vnode)
      i(oldVnode, vnode)
    }

    //新旧子元素
    const oldCh = oldVnode.children
    const ch = vnode.children
    //一个分支，副逻辑处理
    if (isDef(data) && isPatchable(vnode)) {
      //如果vnode有自己的tab，和data，就做下列操作
      //TODO：哪来的cbs啊？
      //把所有的cbs中的update调用一遍
      for (i = 0; i < cbs.update.length; ++i) cbs.update[i](oldVnode, vnode)

      //如果存在，就调用vnode.data.hook.update(oldVnode,vnode)
      if (isDef((i = data.hook)) && isDef((i = i.update))) i(oldVnode, vnode)
    }

    //主逻辑处理，两个分支：
    if (isUndef(vnode.text)) {
      // 7.4.3 新节点没有文本属性

      // 7.4.3.1 新旧节点都有孩子元素
      if (isDef(oldCh) && isDef(ch)) {
        //新旧节点都有子元素，并且新旧节点的孩子不是同一个数组
        if (oldCh !== ch)
          //更新孩子节点
          updateChildren(elm, oldCh, ch, insertedVnodeQueue, removeOnly)
      } else if (isDef(ch)) {
        // 旧节点没有子元素，只有新节点有子元素
        // Q：为什么这里没有移除旧节点的操作？
        if (__DEV__) {
          //在开发环境下检查是否有重复的key
          checkDuplicateKeys(ch)
        }
        //如果旧节点是文本节点将文字置空
        if (isDef(oldVnode.text)) nodeOps.setTextContent(elm, '')
        //再新增所有的孩子节点
        addVnodes(elm, null, ch, 0, ch.length - 1, insertedVnodeQueue)
      } else if (isDef(oldCh)) {
        //只有旧节点有子元素，移除所有旧元素的孩子节点
        removeVnodes(oldCh, 0, oldCh.length - 1)
      } else if (isDef(oldVnode.text)) {
        //旧节点是备注或文本节点，将文字置空
        nodeOps.setTextContent(elm, '')
      }
    } else if (oldVnode.text !== vnode.text) {
      //7.4.2 新节点是有文本属性的节点
      //新组件是备注节点或者文字节点，直接更新文字
      nodeOps.setTextContent(elm, vnode.text)
    }


    //vnode.data.hook.postpatch(oldVnode,vnode)
    if (isDef(data)) {
      if (isDef((i = data.hook)) && isDef((i = i.postpatch))) i(oldVnode, vnode)
    }
  }

  function invokeInsertHook (vnode, queue, initial) {
    // 调用queue中所有元素的insert钩子
    // delay insert hooks for component root nodes, invoke them after the
    // element is really inserted
    if (isTrue(initial) && isDef(vnode.parent)) {
      vnode.parent.data.pendingInsert = queue
    } else {
      for (let i = 0; i < queue.length; ++i) {
        queue[i].data.hook.insert(queue[i])
      }
    }
  }

  let hydrationBailed = false
  // list of modules that can skip create hook during hydration because they
  // are already rendered on the client or has no need for initialization
  // Note: style is excluded because it relies on initial clone for future
  // deep updates (#7063).
  const isRenderedModule = makeMap('attrs,class,staticClass,staticStyle,key')

  // Note: this is a browser-only function so we can assume elms are DOM nodes.
  function hydrate (elm, vnode, insertedVnodeQueue, inVPre?: boolean) {
    let i
    const { tag, data, children } = vnode
    inVPre = inVPre || (data && data.pre)
    vnode.elm = elm

    if (isTrue(vnode.isComment) && isDef(vnode.asyncFactory)) {
      vnode.isAsyncPlaceholder = true
      return true
    }
    // assert node match
    if (__DEV__) {
      if (!assertNodeMatch(elm, vnode, inVPre)) {
        return false
      }
    }
    if (isDef(data)) {
      if (isDef((i = data.hook)) && isDef((i = i.init)))
        i(vnode, true /* hydrating */)
      if (isDef((i = vnode.componentInstance))) {
        // child component. it should have hydrated its own tree.
        initComponent(vnode, insertedVnodeQueue)
        return true
      }
    }
    if (isDef(tag)) {
      if (isDef(children)) {
        // empty element, allow client to pick up and populate children
        if (!elm.hasChildNodes()) {
          createChildren(vnode, children, insertedVnodeQueue)
        } else {
          // v-html and domProps: innerHTML
          if (
            isDef((i = data)) &&
            isDef((i = i.domProps)) &&
            isDef((i = i.innerHTML))
          ) {
            if (i !== elm.innerHTML) {
              /* istanbul ignore if */
              if (
                __DEV__ &&
                typeof console !== 'undefined' &&
                !hydrationBailed
              ) {
                hydrationBailed = true
                console.warn('Parent: ', elm)
                console.warn('server innerHTML: ', i)
                console.warn('client innerHTML: ', elm.innerHTML)
              }
              return false
            }
          } else {
            // iterate and compare children lists
            let childrenMatch = true
            let childNode = elm.firstChild
            for (let i = 0; i < children.length; i++) {
              if (
                !childNode ||
                !hydrate(childNode, children[i], insertedVnodeQueue, inVPre)
              ) {
                childrenMatch = false
                break
              }
              childNode = childNode.nextSibling
            }
            // if childNode is not null, it means the actual childNodes list is
            // longer than the virtual children list.
            if (!childrenMatch || childNode) {
              /* istanbul ignore if */
              if (
                __DEV__ &&
                typeof console !== 'undefined' &&
                !hydrationBailed
              ) {
                hydrationBailed = true
                console.warn('Parent: ', elm)
                console.warn(
                  'Mismatching childNodes vs. VNodes: ',
                  elm.childNodes,
                  children
                )
              }
              return false
            }
          }
        }
      }
      if (isDef(data)) {
        let fullInvoke = false
        for (const key in data) {
          if (!isRenderedModule(key)) {
            fullInvoke = true
            invokeCreateHooks(vnode, insertedVnodeQueue)
            break
          }
        }
        if (!fullInvoke && data['class']) {
          // ensure collecting deps for deep class bindings for future updates
          traverse(data['class'])
        }
      }
    } else if (elm.data !== vnode.text) {
      elm.data = vnode.text
    }
    return true
  }

  function assertNodeMatch (node, vnode, inVPre) {
    if (isDef(vnode.tag)) {
      return (
        vnode.tag.indexOf('vue-component') === 0 ||
        (!isUnknownElement(vnode, inVPre) &&
          vnode.tag.toLowerCase() ===
          (node.tagName && node.tagName.toLowerCase()))
      )
    } else {
      return node.nodeType === (vnode.isComment ? 8 : 3)
    }
  }

  return function patch (oldVnode, vnode, hydrating, removeOnly) {
    // OQ:hydrating和removeOnly什么时候会使用？
    //三种情况，1.删除节点，2.新增节点（2.1完全新节点，2.2替换旧节点）3.更新节点
    //1.vnode为空但oldVnode不为空，直接删除旧节点
    if (isUndef(vnode)) {
      // OQ:为什么这里看起来没有直接删除oldVnode对应的dom节点呢？它怎么知道oldVnode没有dom节点？
      if (isDef(oldVnode)) invokeDestroyHook(oldVnode)
      return
    }

    let isInitialPatch = false
    const insertedVnodeQueue: any[] = []//全局唯一的队列，用来存储所有插入的节点
    //OQ:在最后调用钩子函数时使用吗？是的，最后会调用insert钩子函数，还有其他作用，例如keep-alive组件的缓存

    //2.vnode不为空，但oldVnode为空，直接新建节点
    if (isUndef(oldVnode)) {
      // 新增节点的情况2.1:没有旧节点直接新增节点
      // empty mount (likely as component), create new root element
      //Q:这里为什么要设置isInitialPatch为true呢？
      //A：因为这里是第一次patch，所以是初始化patch，所以设置为true
      isInitialPatch = true
      //Q：完全的新增节点没有插入位置的限制吗？
      createElm(vnode, insertedVnodeQueue)
    } else {
      const isRealElement = isDef(oldVnode.nodeType)
      if (!isRealElement && sameVnode(oldVnode, vnode)) {
        // 3.更新节点
        // 旧节点不是真实节点，并且新旧节点相似时，进行进一步的对比。
        // 但是这里如果新旧节点引用完全相同就会被返回。
        // Q：可能会有潜在的3.2码？为什么新旧节点的引用完全相等时就可以返回了呢？
        // 它如何保证一个节点更新后的引用值和之前不同呢？
        // patch existing root node
        patchVnode(oldVnode, vnode, insertedVnodeQueue, null, null, removeOnly)
      } else {
        //2.2 替换旧节点：新旧节点不同，或者不是真实节点，都会进入这个分支
        if (isRealElement) {
          // 旧节点存在，并且旧节点已经渲染，那删除旧节点
          // 此时情况：isRealElement===true&&sameVnode===false
          // 把旧节点直接替换成空节点，进行下一步的更新操作
          // 旧节点是真实节点时，那新旧节点确实不一样，这时候要干嘛？？？？
          // mounting to a real element
          // check if this is server-rendered content and if we can perform
          // a successful hydration.
          if (oldVnode.nodeType === 1 && oldVnode.hasAttribute(SSR_ATTR)) {
            //当旧Vnode是以一个元素节点时，并且旧节点包含ssr服务的字段
            //删除服务端渲染字段
            oldVnode.removeAttribute(SSR_ATTR)
            //开启补水字段
            hydrating = true
          }
          if (isTrue(hydrating)) {
            //也不知道补水是个什么东西
            //如果补水字段为真，就开始补水并观察返回
            if (hydrate(oldVnode, vnode, insertedVnodeQueue)) {
              //补水成功，就开始触发insert钩子
              //Q：因为是服务端渲染？所以不需要自己调用插入钩子？
              invokeInsertHook(vnode, insertedVnodeQueue, true)
              //返回旧节点？？？，竟然还有返回？
              return oldVnode
            } else if (__DEV__) {
              //补水失败，并且是开发环境，就报错
              warn(
                'The client-side rendered virtual DOM tree is not matching ' +
                'server-rendered content. This is likely caused by incorrect ' +
                'HTML markup, for example nesting block-level elements inside ' +
                '<p>, or missing <tbody>. Bailing hydration and performing ' +
                'full client-side render.'
              )
            }
          }


          // either not server-rendered, or hydration failed.
          // create an empty node and replace it
          // 将旧节点替换为空节点，但其实oldNode存在在返回值的.elm里面
          oldVnode = emptyNodeAt(oldVnode)
        }
        // Q：旧节点不是真实节点时，就不需要置为空了，直接在旧节点的基础上更新新节点？啊？？？A：删除操作还是要有的。
        // 获取传入的旧节点本身
        // replacing existing element
        const oldElm = oldVnode.elm
        // 通过封装方法获取旧节点的父节点
        const parentElm = nodeOps.parentNode(oldElm)

        // 建立新节点
        // 在这里调用的入参会干什么呢？
        // create new node，这里的createElm比上面的多了两个参数
        // 这一步做完新节点的dom变更了
        createElm(
          vnode,
          insertedVnodeQueue,
          // extremely rare edge case: do not insert if old element is in a
          // leaving transition. Only happens when combining transition +
          // keep-alive + HOCs. (#4590)
          oldElm._leaveCb ? null : parentElm,//判断有没有父元素
          nodeOps.nextSibling(oldElm)//获取兄弟节点，用来定位插入位置，这里是替换旧节点所以要指定插入位置
        )


        // update parent placeholder node element, recursively
        if (isDef(vnode.parent)) {
          let ancestor = vnode.parent
          const patchable = isPatchable(vnode)
          while (ancestor) {
            for (let i = 0; i < cbs.destroy.length; ++i) {
              cbs.destroy[i](ancestor)
            }
            ancestor.elm = vnode.elm
            if (patchable) {
              for (let i = 0; i < cbs.create.length; ++i) {
                cbs.create[i](emptyNode, ancestor)
              }
              // #6513
              // invoke insert hooks that may have been merged by create hooks.
              // e.g. for directives that uses the "inserted" hook.
              const insert = ancestor.data.hook.insert
              if (insert.merged) {
                // start at index 1 to avoid re-invoking component mounted hook
                for (let i = 1; i < insert.fns.length; i++) {
                  insert.fns[i]()
                }
              }
            } else {
              registerRef(ancestor)
            }
            ancestor = ancestor.parent
          }
        }

        // 彻底删除旧节点门
        // destroy old node
        if (isDef(parentElm)) {
          removeVnodes([oldVnode], 0, 0)
        } else if (isDef(oldVnode.tag)) {
          invokeDestroyHook(oldVnode)
        }
      }
    }

    //调用新增节点的钩子函数
    invokeInsertHook(vnode, insertedVnodeQueue, isInitialPatch)
    return vnode.elm
  }
}
