/**
 * Not type-checking this file because it's mostly vendor code.
 */

/*!
 * HTML Parser By John Resig (ejohn.org)
 * Modified by Juriy "kangax" Zaytsev
 * Original code by Erik Arvidsson (MPL-1.1 OR Apache-2.0 OR GPL-2.0-or-later)
 * http://erik.eae.net/simplehtmlparser/simplehtmlparser.js
 */

import { makeMap, no } from 'shared/util'
import { isNonPhrasingTag } from 'web/compiler/util'
import { unicodeRegExp } from 'core/util/lang'
import { ASTAttr, CompilerOptions } from 'types/compiler'

// Regular Expressions for parsing tags and attributes
const attribute =
  /^\s*([^\s"'<>\/=]+)(?:\s*(=)\s*(?:"([^"]*)"+|'([^']*)'+|([^\s"'=<>`]+)))?/
const dynamicArgAttribute =
  /^\s*((?:v-[\w-]+:|@|:|#)\[[^=]+?\][^\s"'<>\/=]*)(?:\s*(=)\s*(?:"([^"]*)"+|'([^']*)'+|([^\s"'=<>`]+)))?/
const ncname = `[a-zA-Z_][\\-\\.0-9_a-zA-Z${ unicodeRegExp.source }]*`
//qname是一个标签名，可以是一个普通的标签名，也可以是一个命名空间标签名，属性名也可以用这个正则
const qnameCapture = `((?:${ ncname }\\:)?${ ncname })`
//开始标签头
const startTagOpen = new RegExp(`^<${ qnameCapture }`)
//开始标签尾
const startTagClose = /^\s*(\/?)>/
const endTag = new RegExp(`^<\\/${ qnameCapture }[^>]*>`)
const doctype = /^<!DOCTYPE [^>]+>/i
// #7298: escape - to avoid being passed as HTML comment when inlined in page
const comment = /^<!\--/
//条件注释
const conditionalComment = /^<!\[/

// Special Elements (can contain anything)
export const isPlainTextElement = makeMap('script,style,textarea', true)
const reCache = {}

const decodingMap = {
  '&lt;': '<',
  '&gt;': '>',
  '&quot;': '"',
  '&amp;': '&',
  '&#10;': '\n',
  '&#9;': '\t',
  '&#39;': "'"
}
const encodedAttr = /&(?:lt|gt|quot|amp|#39);/g
const encodedAttrWithNewLines = /&(?:lt|gt|quot|amp|#39|#10|#9);/g

// #5992
const isIgnoreNewlineTag = makeMap('pre,textarea', true)
const shouldIgnoreFirstNewline = (tag, html) =>
  tag && isIgnoreNewlineTag(tag) && html[0] === '\n'

function decodeAttr (value, shouldDecodeNewlines) {
  const re = shouldDecodeNewlines ? encodedAttrWithNewLines : encodedAttr
  return value.replace(re, match => decodingMap[match])
}

export interface HTMLParserOptions extends CompilerOptions {
  start?: (
    tag: string,
    attrs: ASTAttr[],
    unary: boolean,
    start: number,
    end: number
  ) => void
  end?: (tag: string, start: number, end: number) => void
  chars?: (text: string, start?: number, end?: number) => void
  comment?: (content: string, start: number, end: number) => void
}

export function parseHTML (html, options: HTMLParserOptions) {
  const stack: any[] = []
  //expectHTML这个字段用来标记当前是否在处理html？他在baseOptions中被设置为true 
  const expectHTML = options.expectHTML
  //用来判断是否一元标签的func
  const isUnaryTag = options.isUnaryTag || no
  //用来判断是否可以省略闭合标签的func
  const canBeLeftOpenTag = options.canBeLeftOpenTag || no
  //当前处理进度index（相对于原始html模版字符串
  let index = 0
  //last：剩余的html字符串，lastTag：最近一个处理的tag
  let last, lastTag
  while (html) {
    last = html
    // Make sure we're not in a plaintext content element like script/style
    // 判断最近处理的tag是不是在script、style、textarea标签中
    // 为什么会有textarea？(can contain anything)
    if (!lastTag || !isPlainTextElement(lastTag)) {
      // 如果lastTag为空，或者lastTab不是万物tag
      // 获取字符串中第一个<的位置
      let textEnd = html.indexOf('<')

      //如果<就在第一个位置，说明是一个标签
      if (textEnd === 0) {
        // Comment:
        // 正则验证是不是备注开头
        if (comment.test(html)) {
          //获取备注结尾的位置
          const commentEnd = html.indexOf('-->')
          //意见有了备注node开头和结尾的所有信息，开始处理
          if (commentEnd >= 0) {
            if (options.shouldKeepComment && options.comment) {
              //如果配置里说保存备注，并且有处理备注的方法，就调用
              options.comment(
                html.substring(4, commentEnd),
                index,
                index + commentEnd + 3
              )
            }
            //讲处理进度推进到下一个位置
            advance(commentEnd + 3)
            //结束本次循环，开始下次循环
            continue
          }
        }

        // 是不是条件备注
        // https://en.wikipedia.org/wiki/Conditional_comment#Downlevel-revealed_conditional_comment
        if (conditionalComment.test(html)) {
          const conditionalEnd = html.indexOf(']>')
          if (conditionalEnd >= 0) {
            advance(conditionalEnd + 2)
            continue
          }
        }

        // 进行到这一步，说明这个节点肯定不是备注了
        // 检验是不是Doctype节点，步骤同上
        // Doctype:
        const doctypeMatch = html.match(doctype)
        if (doctypeMatch) {
          advance(doctypeMatch[0].length)
          continue
        }

        // 检验这个标签是不是结束标签，如果是结束标签就获取到标签字符串数组
        // End tag:
        const endTagMatch = html.match(endTag)
        if (endTagMatch) {
          //如果是结束标签，就将进度跳到最近的一个结束标签后面
          const curIndex = index//index是循环外部的变量，记录了处理进度
          advance(endTagMatch[0].length)
          //并且调用parseEndTag方法处理下一个结束标签
          //Q：为什么是下一个结束标签？
          //Q：curIndex和index的值看起来像等，为什么要传递两遍？
          parseEndTag(endTagMatch[1], curIndex, index)
          continue
        }

        // 不是结束标签再开始检测是不是开始标签
        // OQ：为什么处理结束标签的优先级比开始标签高？
        // Start tag:
        // 将startTag的信息从html解析出来
        const startTagMatch = parseStartTag()
        if (startTagMatch) {
          //如果确实获取成功，就
          handleStartTag(startTagMatch)
          if (shouldIgnoreFirstNewline(startTagMatch.tagName, html)) {
            advance(1)
          }
          continue
        }
      }

      // 如果<的位置大于等于第一个，说明中间夹着文本或者空白
      let text, rest, next
      if (textEnd >= 0) {
        //将这段文本截掉，留着剩余html
        rest = html.slice(textEnd)
        //如果剩余html中同时符合以下四个条件，则执行循环
        while (
          !endTag.test(rest) &&
          !startTagOpen.test(rest) &&
          !comment.test(rest) &&
          !conditionalComment.test(rest)
        ) {
          // 即没有endTag，也没有开启着的startTag，也不是备注，也没有条件备注
          // < in plain text, be forgiving and treat it as text
          // 跳过这一段文本
          // 获取下一个<符号的位置
          next = rest.indexOf('<', 1)
          //如果没有更多<符号就停止循环
          //如果有<符号就把textEnd推进到下一个<符号的位置，并且更新剩余html
          if (next < 0) break
          textEnd += next
          rest = html.slice(textEnd)
        }
        //获取这段包含<符号的文本
        text = html.substring(0, textEnd)
      }

      // 如果字符串中不包括<，那剩余的字符串按照文本处理
      if (textEnd < 0) {
        text = html
      }
      // 

      // 如果有纯文本，则将纯文本的长度从html中截取掉，前进！
      if (text) {
        advance(text.length)
      }

      // Q：这是在干什么？
      if (options.chars && text) {
        options.chars(text, index - text.length, index)
      }
    } else {
      // lastTag不为空，或者是script，style，textarea标签之一
      // 为什么lastTag不为空也要来这个分支？因为这个分支处理的是script，style，textarea标签之一，而这三个标签是可以嵌套的，所以lastTag不为空也要来这个分支
      //如果包含最近要处理的tag，或者是script，style，textarea标签之一
      let endTagLength = 0
      const stackedTag = lastTag.toLowerCase()

      //重新入栈的标签，reStackedTag里似乎保存一个根据当前tag建立的正则表达式
      //OP：这一步是为了处理script，style，textarea标签中的特殊字符？
      //为什么叫reStackedTag？因为这个正则表达式是根据当前tag建立的
      const reStackedTag =
        reCache[stackedTag] ||
        (reCache[stackedTag] = new RegExp(
          '([\\s\\S]*?)(</' + stackedTag + '[^>]*>)',
          'i'
        ))

      //截取掉整段纯文本标签
      const rest = html.replace(reStackedTag, function (all, text, endTag) {
        endTagLength = endTag.length
        if (!isPlainTextElement(stackedTag) && stackedTag !== 'noscript') {
          //如果不是script，style，textarea标签之一，就把text中的特殊字符转义
          text = text
            .replace(/<!\--([\s\S]*?)-->/g, '$1') // #7298
            .replace(/<!\[CDATA\[([\s\S]*?)]]>/g, '$1')
        }
        if (shouldIgnoreFirstNewline(stackedTag, text)) {
          //如果是script，style，textarea标签之一，就把text中的第一个换行符去掉
          //Q: 为什么要去掉第一个换行符？
          text = text.slice(1)
        }
        if (options.chars) {
          //调用options.chars方法，处理text
          options.chars(text)
        }
        return ''
      })

      //更新处理进度
      index += html.length - rest.length
      html = rest

      //闭合标签
      parseEndTag(stackedTag, index - endTagLength, index)
    }

    //如果html没有变化，说明已经处理大部分逻辑，只剩标签尾收尾了，所以提前跳出循环
    if (html === last) {
      options.chars && options.chars(html)
      if (__DEV__ && !stack.length && options.warn) {
        options.warn(`Mal-formatted tag at end of template: "${ html }"`, {
          start: index + html.length
        })
      }
      break
    }
  }

  // Clean up any remaining tags
  parseEndTag()

  //把处理位置向前推进n个字符
  function advance (n) {
    index += n
    html = html.substring(n)
  }

  function parseStartTag () {
    // 在本函数调用前，外部判断过其他情况，所以这里需要自己再进行校验
    // 解析标签头
    const start = html.match(startTagOpen)
    if (start) {
      //Q:哪来的start：index啊？似乎是当前html被处理的index？
      const match: any = {
        tagName: start[1],
        attrs: [],
        start: index
      }
      //将处理进度推进到标签头后面
      advance(start[0].length)
      //解析开始标签中的属性
      let end, attr
      while (
        !(end = html.match(startTagClose)) &&
        (attr = html.match(dynamicArgAttribute) || html.match(attribute))
      ) {
        //当没有碰到结束标签，并且还有动态属性or静态属性时，就继续解析
        attr.start = index
        advance(attr[0].length)
        attr.end = index
        
        match.attrs.push(attr)
      }
      //解析标签尾
      if (end) {
        //unarySlash是自闭合标签的结束符 
        //将标签尾的符号保存下来（如果有斜杠就是斜杠，没有就是空字符串
        match.unarySlash = end[1]
        advance(end[0].length)
        match.end = index
        //把标签的end index也保存在match中
        return match
      }
    }
  }

  function handleStartTag (match) {
    const tagName = match.tagName
    const unarySlash = match.unarySlash

    if (expectHTML) {
      //expectHTML是全局默认为true
      //父节点是p标签，并且当前节点不是语义化标签，就闭合p标签
      if (lastTag === 'p' && isNonPhrasingTag(tagName)) {
        //如果上一个标签是p，而当前标签是非语义标签，就闭合p标签
        //OQ：为什么要闭合p标签？
        parseEndTag(lastTag)
      }
      //如果当前节点是可以省略闭合标签的标签，并且上一个标签和当前标签是同一个标签，就闭合当前标签
      if (canBeLeftOpenTag(tagName) && lastTag === tagName) {
        //如果当前标签是可以省略闭合标签的标签，而且上一个标签和当前标签是同一个标签
        parseEndTag(tagName)
      }
    }

    //如果当前标签是自闭合标签，或者unarySlash不为空
    const unary = isUnaryTag(tagName) || !!unarySlash

    //attrs是一个数组，保存了当前标签的所有属性
    const l = match.attrs.length
    const attrs: ASTAttr[] = new Array(l)
    for (let i = 0; i < l; i++) {
      const args = match.attrs[i]
      const value = args[3] || args[4] || args[5] || ''
      const shouldDecodeNewlines =
        tagName === 'a' && args[1] === 'href'
          ? options.shouldDecodeNewlinesForHref
          : options.shouldDecodeNewlines
      attrs[i] = {
        name: args[1],
        value: decodeAttr(value, shouldDecodeNewlines)
      }
      if (__DEV__ && options.outputSourceRange) {
        attrs[i].start = args.start + args[0].match(/^\s*/).length
        attrs[i].end = args.end
      }
    }

    if (!unary) {
      stack.push({
        tag: tagName,
        lowerCasedTag: tagName.toLowerCase(),
        attrs: attrs,
        start: match.start,
        end: match.end
      })
      lastTag = tagName
    }

    if (options.start) {
      options.start(tagName, attrs, unary, match.start, match.end)
    }
  }

  function parseEndTag (tagName?: any, start?: any, end?: any) {
    let pos, lowerCasedTagName
    if (start == null) start = index //外部闭包index
    if (end == null) end = index

    // Find the closest opened tag of the same type
    if (tagName) {
      lowerCasedTagName = tagName.toLowerCase()
      for (pos = stack.length - 1; pos >= 0; pos--) {
        //遍历stack获取最近的一个同类型的tag
        //Q：但不做任何处理？？？直接跳过？
        //A：看错了，其实pos这里就保存了相同tag的位置
        if (stack[pos].lowerCasedTag === lowerCasedTagName) {
          break
        }
      }
    } else {
      // If no tag name is provided, clean shop
      pos = 0
    }

    //如果获取到了pos，开始闭合标签
    if (pos >= 0) {
      // Close all the open elements, up the stack
      // 把 pos 以内的所有标签都闭合
      for (let i = stack.length - 1; i >= pos; i--) {
        if (__DEV__ && (i > pos || !tagName) && options.warn) {
          //dev环境做一些警告，比如说有一个标签没有闭合
          options.warn(`tag <${ stack[i].tag }> has no matching end tag.`, {
            start: stack[i].start,
            end: stack[i].end
          })
        }
        //调用options.end方法，闭合标签
        //Q：这里的start和end是什么？
        if (options.end) {
          options.end(stack[i].tag, start, end)
        }
      }

      // Remove the open elements from the stack
      // 更新最近一个未闭合的标签
      stack.length = pos
      lastTag = pos && stack[pos - 1].tag
    } else if (lowerCasedTagName === 'br') {
      //  处理br标签的单独闭合
      if (options.start) {
        options.start(tagName, [], true, start, end)
      }
    } else if (lowerCasedTagName === 'p') {
      // Q：为什么p标签要单独处理？
      if (options.start) {
        options.start(tagName, [], false, start, end)
      }
      if (options.end) {
        options.end(tagName, start, end)
      }
    }
  }
}
