/**
 * @name Host-like inbound → outbound HTTP (broad)
 * @description Track external inputs to outbound HTTP requests (ClientRequest).
 * @id js/hhi/host-to-outbound
 * @kind path-problem
 * @problem.severity warning
 * @tags security; external/cwe/cwe-918; correctness; experimental
 */

import javascript
import semmle.javascript.frameworks.ClientRequests
import semmle.javascript.security.dataflow.HostHeaderPoisoningInEmailGenerationQuery

module S1_AllFuncs_Config implements DataFlow::ConfigSig {

  /** Sources：Host / Forwarded 系列请求头（名称小写匹配） */
  predicate isSource(DataFlow::Node n) {
    // A) 官方内置的 Host 污染来源（覆盖 Express/Koa/Hapi 等常见派生）
    HostHeaderPoisoningConfig::isSource(n)
    or
    // B1) *.headers["host" | "x-forwarded-host" | "forwarded" | ":authority"]
    exists(PropAccess p, PropAccess base |
      n.asExpr() = p and
      p.getPropertyName().regexpMatch("(?i)^(host|x-forwarded-host|forwarded|:authority)$") and
      base = p.getBase() and
      base.getPropertyName().regexpMatch("(?i)^(headers|rawheaders)$")
    )
    or
    // B2) *.headers.host（点号形式）
    exists(PropAccess p2, PropAccess base2 |
      n.asExpr() = p2 and
      p2.getPropertyName() = "host" and
      base2 = p2.getBase() and
      base2.getPropertyName().regexpMatch("(?i)^(headers|rawheaders)$")
    )
    or
    // B3) req.get("host") / req.header("host") / ctx.get("host")
    exists(MethodCallExpr m, StringLiteral arg0 |
      n.asExpr() = m and
      m.getMethodName().regexpMatch("(?i)^(get|header)$") and
      arg0 = m.getArgument(0) and
      arg0.getValue().regexpMatch("(?i)^(host|x-forwarded-host|forwarded|:authority)$")
    )
    or
    // B4) Express 派生：req.hostname
    exists(PropAccess e1 |
      n.asExpr() = e1 and
      e1.getPropertyName() = "hostname"
    )
    or
    // B5) Koa 派生：ctx.host / ctx.origin / ctx.href
    exists(PropAccess e2 |
      n.asExpr() = e2 and
      e2.getPropertyName().regexpMatch("(?i)^(host|origin|href)$")
    )
    or
    // B6) Hapi 派生：request.info.host / request.info.uri
    exists(PropAccess leaf, PropAccess info |
      n.asExpr() = leaf and
      leaf.getPropertyName().regexpMatch("(?i)^(host|uri)$") and
      info = leaf.getBase() and
      info.getPropertyName() = "info"
    )
    /* 如在实际例子中则可以使用以下代码：
    or
    exists (Http::RequestHeaderAccess h |
      n = h and
      (
        h.getAHeaderName() = "host" or
        h.getAHeaderName() = "x-forwarded-host" or
        h.getAHeaderName() = "forwarded" or
        h.getAHeaderName() = ":authority"
      )
    )
    */
  }

  /** 让属性写入/赋值产生的别名有流动（可留可删） */
  predicate isAdditionalFlowStep(DataFlow::Node pred, DataFlow::Node succ) {
    exists(AssignExpr a |
      a.getRhs() = pred.asExpr() and succ.asExpr() = a.getLhs()
    )
    or
    exists(DataFlow::PropWrite w |
      w.getRhs() = pred and succ = w.getBase()
    )
  }

  /** Sinks：所有调用点的所有实参（函数/方法/构造/反射） */
  predicate isSink(DataFlow::Node n) {


  /*
   // 辅助：判断“像响应对象”的接收者（res/response/ctx/context/h/reply 或 *.response/*.res）
  // —— 为避免你不想要辅助谓词，这里直接内联在每个 exists 分支里。

  // (0) 超宽：任何“响应对象”上的任何方法的所有实参
  exists (DataFlow::InvokeNode call, MethodCallExpr m |
    m = call.getInvokeExpr() and
    (
      exists(Identifier id0 |
        id0 = m.getReceiver() and id0.getName().regexpMatch("(?i)^(res|response|ctx|context|h|reply)$")
      )
      or
      exists(PropAccess pa0 |
        pa0 = m.getReceiver() and pa0.getPropertyName().regexpMatch("(?i)^(response|res)$")
      )
    ) and
    n = call.getAnArgument()
  )
  or
  // (1) res.redirect(url) / res.redirect(status, url)
  exists (DataFlow::InvokeNode c1, MethodCallExpr m1 |
    m1 = c1.getInvokeExpr() and m1.getMethodName() = "redirect" and
    (
      exists(Identifier id1 |
        id1 = m1.getReceiver() and id1.getName().regexpMatch("(?i)^(res|response|ctx|context|h|reply)$")
      )
      or
      exists(PropAccess pa1 |
        pa1 = m1.getReceiver() and pa1.getPropertyName().regexpMatch("(?i)^(response|res)$")
      )
    ) and
    (
      (c1.getNumArgument() = 1 and n = c1.getArgument(0)) or
      (c1.getNumArgument() = 2 and n = c1.getArgument(1))
    )
  )
  or
  // (2) res.location(url)
  exists (DataFlow::InvokeNode c2, MethodCallExpr m2 |
    m2 = c2.getInvokeExpr() and m2.getMethodName() = "location" and
    (
      exists(Identifier id2 |
        id2 = m2.getReceiver() and id2.getName().regexpMatch("(?i)^(res|response|ctx|context|h|reply)$")
      )
      or
      exists(PropAccess pa2 |
        pa2 = m2.getReceiver() and pa2.getPropertyName().regexpMatch("(?i)^(response|res)$")
      )
    ) and
    c2.getNumArgument() >= 1 and n = c2.getArgument(0)
  )
  or
  // (3) res.set/header/setHeader('Location', url) —— 第二个参数是 URL
  exists (DataFlow::InvokeNode c3, MethodCallExpr m3, StringLiteral hname |
    m3 = c3.getInvokeExpr() and
    m3.getMethodName().regexpMatch("(?i)^(set|setHeader|header)$") and
    (
      exists(Identifier id3 |
        id3 = m3.getReceiver() and id3.getName().regexpMatch("(?i)^(res|response|ctx|context|h|reply)$")
      )
      or
      exists(PropAccess pa3 |
        pa3 = m3.getReceiver() and pa3.getPropertyName().regexpMatch("(?i)^(response|res)$")
      )
    ) and
    hname = m3.getArgument(0) and hname.getValue().regexpMatch("(?i)^location$") and
    c3.getNumArgument() >= 2 and n = c3.getArgument(1)
  )
  or
  // (4) res.set({ Location: url }) / res.writeHead(status, { Location: url })
  exists (DataFlow::InvokeNode c4, MethodCallExpr m4, ObjectExpr obj, Property p |
    m4 = c4.getInvokeExpr() and
    m4.getMethodName().regexpMatch("(?i)^(set|setHeader|header|writeHead)$") and
    (
      exists(Identifier id4 |
        id4 = m4.getReceiver() and id4.getName().regexpMatch("(?i)^(res|response|ctx|context|h|reply)$")
      )
      or
      exists(PropAccess pa4 |
        pa4 = m4.getReceiver() and pa4.getPropertyName().regexpMatch("(?i)^(response|res)$")
      )
    ) and
    (
      obj = m4.getArgument(0) and obj instanceof ObjectExpr or
      obj = m4.getArgument(1) and obj instanceof ObjectExpr
    ) and
    p = obj.getAProperty() and
    p.getName().regexpMatch("(?i)^location$") and
    n.asExpr() = p.getInit()
  )
    
    // 如需所有函数/方法/构造的所有参数，用这段替换上面的 InvokeNode 版本：
    or

        */
    exists(DataFlow::InvokeNode call | n = call.getAnArgument() or n = call.getASpreadArgument() )


    /* 如需只看“外接 API（出站 HTTP）”，用这段替换上面的 InvokeNode 版本：
    or
    exists(ClientRequest r |
      n = r.getUrl() or
      n = r.getHost() or
      n = r.getADataNode() or
      n = r.getAnArgument() or
      n = r.getASavePath()
    )
    */
  }
}

/** 运行全局污点跟踪（保持官方风格） */
module S1_AllFuncs_Flow = TaintTracking::Global<S1_AllFuncs_Config>;
import S1_AllFuncs_Flow::PathGraph

from S1_AllFuncs_Flow::PathNode src, S1_AllFuncs_Flow::PathNode snk
where S1_AllFuncs_Flow::flowPath(src, snk)
select snk.getNode(), src, snk,
  "Untrusted $@ reaches a function argument (broad API coverage).",
  src.getNode(), "Host-related header"
