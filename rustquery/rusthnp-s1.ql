import rust
import codeql.rust.dataflow.DataFlow
import codeql.rust.dataflow.TaintTracking

module S1_Config implements DataFlow::ConfigSig {

  /** ========= isSource =========
   *  A) req.headers().get(...)
   *  B) req.connection_info().(host|scheme|uri)(...)
   *  C) （新增建模）URL 生成 API 的调用“本身”作为 Host-派生的 Source：
   *     req.full_url() / req.url_for() / req.url_for_static()
   */
  predicate isSource(DataFlow::Node n) {
    // A) headers().get(...)
    exists (Call hs, Call get |
      hs.getMethodName() = "headers" and
      get.getMethodName() = "get" and
      get.getReceiver() = hs and
      n.asExpr().getExpr() = get
    )
    or
    // B) connection_info().(host|scheme|uri)(...)
    exists (Call ci, Call m |
      ci.getMethodName() = "connection_info" and
      m.getReceiver() = ci and
      m.getMethodName().regexpMatch("^(host|scheme|uri)$") and
      n.asExpr().getExpr() = m
    )
    or
    // C) 把 URL 生成 API 调用的“返回值”当作 Host-派生 Source（建模函数体内部的 Host 读取）
    exists (Call u |
      u.getMethodName().regexpMatch("^(full_url|url_for|url_for_static)$") and
      n.asExpr().getExpr() = u
    )
  }

  /** ========= isSink =========
   *  1) 任意调用实参（超宽，保证不漏掉“外接 API”）
   *  2) URL 生成/重定向/客户端请求调用点“本身”作为落点（即使只被赋值）
   */
  predicate isSink(DataFlow::Node n) {
    // 1) 任何调用（函数或方法）的任意实参
    exists (CallExpr c | n.asExpr().getExpr() = c.getArg(_))
    or
    exists (MethodCallExpr m | n.asExpr().getExpr() = m.getArg(_))

    // 2a) URL 生成 API 调用本身
    or exists (Call u |
      u.getMethodName().regexpMatch("^(url_for|url_for_static|full_url)$") and
      n.asExpr().getExpr() = u
    )

    // 2b) 设置 Location 的响应头（insert_header/append_header，出现 header::LOCATION）
    or exists (Call u |
      u.getMethodName().regexpMatch("^(insert_header|append_header)$") and
      u.toString().regexpMatch("\\bheader::LOCATION\\b") and
      n.asExpr().getExpr() = u
    )

    // 2c) URL/URI 解析点
    or exists (Call u |
      u.toString().regexpMatch("\\b(Url::parse|Uri::try_from)\\b") and
      n.asExpr().getExpr() = u
    )

    // 2d) awc 客户端出站请求
    or exists (Call u |
      u.toString().regexpMatch("\\bClient::(get|post|put|patch|delete|request)\\b") and
      n.asExpr().getExpr() = u
    )
  }

  /** ========= isAdditionalFlowStep =========
   *  将 “参数/接收者 → 调用结果” 视为一步，覆盖 format!/to_string/链式 builder/中转函数 等
   */
  predicate isAdditionalFlowStep(DataFlow::Node a, DataFlow::Node b) {
    // 函数调用：arg -> result
    exists (CallExpr c |
      b.asExpr().getExpr() = c and
      a.asExpr().getExpr() = c.getArg(_)
    )
    or
    // 方法调用：receiver/arg -> result
    exists (MethodCallExpr m |
      b.asExpr().getExpr() = m and
      (
        a.asExpr().getExpr() = m.getReceiver()
        or
        a.asExpr().getExpr() = m.getArg(_)
      )
    )
  }
}

module S1 = TaintTracking::Global<S1_Config>;
import S1::PathGraph

from S1::PathNode src, S1::PathNode snk
where S1::flowPath(src, snk)
select snk, src, "Host-like source → URL/Location/Client sink (broad, with URL-API-as-source modeling)."
