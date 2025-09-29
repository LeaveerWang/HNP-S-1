/**
 * pyhnp.ql — S1: Host/URL poisoning
 * Sources: request.host / get_host() / headers|META|environ|scope 里的 Host 读取
 * Additional flow: str.format / sep.join / URL 构造（url_for/build_absolute_uri/reverse/...）的“返回值”传播
 * Sinks: ① 任意函数/方法/构造 *的参数*；② 任意 *调用表达式本身*（返回值）；③ 关键响应头赋值
 */

import python
import semmle.python.dataflow.new.DataFlow
import semmle.python.dataflow.new.TaintTracking

// ---------------------------------------------------------------------------
// Helpers
// ---------------------------------------------------------------------------

/** 文本兜底：headers["Host"] / META["HTTP_HOST"] / environ["HTTP_HOST"] / scope["headers"]["host"] */
predicate looksLikeHeaderIndexText(Expr e) {
  e.toString().regexpMatch(
    "(?i)(headers|META|environ|scope)\\s*\\[\\s*['\\\"](host|http_host|x-forwarded-host)['\\\"]\\s*\\]"
  )
}

/** URL 构造/反解调用（Flask/Django/Starlette/Tornado/Pyramid 常见名） */
predicate isUrlBuilderCall(Call c) {
  exists(Name n | n = c.getFunc() and
    n.getId().regexpMatch("(?i)^(url_for|build_absolute_uri|reverse|reverse_lazy|full_url|reverse_url|route_url)$")
  )
  or
  exists(Attribute f | f = c.getFunc() and
    f.getAttr().regexpMatch("(?i)^(url_for|build_absolute_uri|reverse|reverse_lazy|full_url|reverse_url|route_url|url)$")
  )
}

/** Host-ish 表达式：属性读取 / get_host() / 头部下标（只做表达式形态识别） */
predicate isHostExpr(Expr e) {
  exists(Attribute a | a = e and (
    a.getAttr() = "host" or a.getAttr() = "hostname" or a.getAttr() = "netloc" or
    a.getAttr() = "url_root" or a.getAttr() = "base_url" or a.getAttr() = "scheme"
  ))
  or exists(Call c, Attribute f | c = e and f = c.getFunc() and f.getAttr() = "get_host")
  or looksLikeHeaderIndexText(e)
}

/** 关键响应头赋值（headers["Location"]=... 等）文本兜底 */
predicate isHeaderAssignmentExpr(Expr e) {
  e.toString().regexpMatch(
    "(?i)(headers\\s*\\[\\s*['\\\"](Location|Content-Location|Refresh|Link|Access-Control-Allow-Origin)['\\\"]\\s*\\]\\s*=)"
  )
}

// ---------------------------------------------------------------------------
// Config
// ---------------------------------------------------------------------------

module HNPConfig implements DataFlow::ConfigSig {

  // ---------- Sources ----------
  predicate isSource(DataFlow::Node source) {
    exists(Expr e |
      DataFlow::exprNode(e) = source and (

        // *.host / *.hostname / *.netloc / *.url_root / *.base_url / *.scheme
        exists(Attribute a | a = e and (
          a.getAttr() = "host" or a.getAttr() = "hostname" or a.getAttr() = "netloc" or
          a.getAttr() = "url_root" or a.getAttr() = "base_url" or a.getAttr() = "scheme"
        ))

        // Django: request.get_host()
        or exists(Call c, Attribute f |
          c = e and f = c.getFunc() and f.getAttr() = "get_host"
        )

        // headers|META|environ|scope 读取 Host（兜底）
        or looksLikeHeaderIndexText(e)
      )
    )
  }

  // ---------- Additional taint steps ----------
  predicate isAdditionalFlowStep(DataFlow::Node pred, DataFlow::Node succ) {
    exists(Expr pe, Expr se |
      DataFlow::exprNode(pe) = pred and
      DataFlow::exprNode(se) = succ and (

        // 1) "str".format(...) 传播
        exists(Call c, Attribute f |
          se = c and f = c.getFunc() and f.getAttr() = "format" and
          (pe = f.getObject() or pe = c.getAnArg())
        )

        // 2) sep.join(parts) 传播
        or exists(Call c2, Attribute f2 |
          se = c2 and f2 = c2.getFunc() and f2.getAttr() = "join" and
          (pe = f2.getObject() or pe = c2.getAnArg())
        )

        // 3) URL 构造：参数/接收者 → 调用结果
        or exists(Call uc |
          se = uc and isUrlBuilderCall(uc) and
          (pe = uc.getAnArg() or exists(Attribute ufo | ufo = uc.getFunc() and pe = ufo.getObject()))
        )

        // 4) URL 构造：Host 表达式（隐式来源） → 调用结果
        //    覆盖 Flask url_for(..., _external=True) 这类“返回值依赖 request.host/url_root”的情况
        or exists(Call uc2 |
          se = uc2 and isUrlBuilderCall(uc2) and
          exists(Expr hostE | isHostExpr(hostE) and pe = hostE)
        )
      )
    )
  }

  // ---------- Sinks ----------
  predicate isSink(DataFlow::Node sink) {
    // A) 任意函数/方法/构造的「参数位」作为 sink（接口/出站函数的共同落点）
    exists(Call call, Expr arg |
      arg = call.getAnArg() and
      DataFlow::exprNode(arg) = sink
    )
    // B) 任意「调用表达式本身（返回值）」作为 sink
    or exists(Call call2 |
      DataFlow::exprNode(call2) = sink
    )
    // C) 关键响应头赋值
    or exists(Expr e | DataFlow::exprNode(e) = sink and isHeaderAssignmentExpr(e))
  }
}

// Apply global taint tracking
module HNPFlow = TaintTracking::Global<HNPConfig>;

// ---------------------------------------------------------------------------
// Pretty labels (optional): 在结果里显示“落点函数名”
// ---------------------------------------------------------------------------
predicate sinkIsCallArg(DataFlow::Node sink, Call call, Expr arg) {
  arg = call.getAnArg() and DataFlow::exprNode(arg) = sink
}
predicate sinkIsCallResult(DataFlow::Node sink, Call call) {
  DataFlow::exprNode(call) = sink
}
predicate getCalleeName(Call call, string name) {
  exists(Name n | n = call.getFunc() and name = n.getId())
  or exists(Attribute f | f = call.getFunc() and name = f.getAttr())
  or name = call.getFunc().toString()
}
predicate sinkLabel(DataFlow::Node sink, string label) {
  exists(Call c, Expr a | sinkIsCallArg(sink, c, a) and getCalleeName(c, label))
  or exists(Call c2 | sinkIsCallResult(sink, c2) and getCalleeName(c2, label))
  or (exists(Expr e | DataFlow::exprNode(e) = sink and isHeaderAssignmentExpr(e)) and label = "response-header-assignment")
}

// ---------------------------------------------------------------------------
// Main query
// ---------------------------------------------------------------------------
from DataFlow::Node source, DataFlow::Node sink, string callee
where HNPFlow::flow(source, sink) and sinkLabel(sink, callee)
select source, sink,
  "Host-derived data flows into " + callee + " (possible host/url poisoning)."
