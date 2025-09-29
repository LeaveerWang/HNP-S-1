/**
 * @name Host-like inbound → outbound (Java, broad)
 * @description Track host-derived input (Host/server name/request URL, Spring builders) to ANY call argument.
 * @id java/hhi/host-to-any-arg
 * @kind path-problem
 * @problem.severity warning
 * @tags security; external/cwe/cwe-918; correctness; experimental
 */

import java
import semmle.code.java.dataflow.DataFlow
import semmle.code.java.dataflow.TaintTracking

/**
 * 统一判断：方法 m 是否属于 ServletRequest（javax 或 jakarta）
 */
predicate isServletRequestMethod(Method m) {
  m.getDeclaringType().hasQualifiedName("javax.servlet.http", "HttpServletRequest") or
  m.getDeclaringType().hasQualifiedName("jakarta.servlet.http", "HttpServletRequest")
}

/**
 * Host / Host-like 的“来源”
 *  - request.getHeader("Host" | "X-Forwarded-Host" | "Forwarded" | ":authority")
 *  - request.getServerName(), getRequestURL(), getScheme(), getServerPort()
 *  - Spring: ServletUriComponentsBuilder.fromCurrentRequestUri()/fromCurrentContextPath()
 *  - Spring HATEOAS linkTo(...)（常见地会基于 ServletUriComponentsBuilder）
 */
module HostToAnyArg_Config implements DataFlow::ConfigSig {

  predicate isSource(DataFlow::Node src) {
    // 1) HttpServletRequest.getHeader("<host-like>")
    exists(MethodCall mc, Method m, StringLiteral lit |
    src.asExpr() = mc and
    m = mc.getMethod() and
    isServletRequestMethod(m) and
    m.hasName("getHeader") and
    lit = mc.getArgument(0) and
    lit.getValue().regexpMatch("(?i)^(host|x-forwarded-host|forwarded|:authority)$")
    )
    or
    // 2) HttpServletRequest.getServerName()
    exists(MethodCall mc2, Method m2 |
      src.asExpr() = mc2 and
      m2 = mc2.getMethod() and
      isServletRequestMethod(m2) and
      m2.hasName("getServerName")
    )
    or
    // 3) HttpServletRequest.getRequestURL()
    exists(MethodCall mc3, Method m3 |
      src.asExpr() = mc3 and
      m3 = mc3.getMethod() and
      isServletRequestMethod(m3) and
      m3.hasName("getRequestURL")
    )
    or
    // 4) HttpServletRequest.getScheme() / getServerPort()
    exists(MethodCall mc4, Method m4 |
      src.asExpr() = mc4 and
      m4 = mc4.getMethod() and
      isServletRequestMethod(m4) and
      (m4.hasName("getScheme") or m4.hasName("getServerPort"))
    )
    or
    // 5) Spring: ServletUriComponentsBuilder.fromCurrentRequestUri()/fromCurrentContextPath()
    exists(MethodCall scb, Method sm |
      src.asExpr() = scb and
      sm = scb.getMethod() and
      sm.getDeclaringType().hasQualifiedName(
        "org.springframework.web.servlet.support",
        "ServletUriComponentsBuilder"
      ) and
      (sm.hasName("fromCurrentRequestUri") or sm.hasName("fromCurrentContextPath"))
    )
    or
    // 6) Spring HATEOAS: WebMvcLinkBuilder.linkTo(...)
    exists(MethodCall linkTo, Method lm |
      src.asExpr() = linkTo and
      lm = linkTo.getMethod() and
      lm.getDeclaringType().hasQualifiedName(
        "org.springframework.hateoas.server.mvc",
        "WebMvcLinkBuilder"
      ) and
      lm.hasName("linkTo")
    )
  }

  /** Sink：任何调用/构造的任何实参（超宽覆盖，不会再用 getNumberOfArguments） */
  predicate isSink(DataFlow::Node sink) {
    exists(Call c |
      exists(Expr a | a = c.getAnArgument() and sink.asExpr() = a)
    )
  }

  // 不额外指定 barrier / 额外步；Java 数据流库已涵盖常规赋值/返回等
}

module HostToAnyArg_Flow = TaintTracking::Global<HostToAnyArg_Config>;
import HostToAnyArg_Flow::PathGraph

from HostToAnyArg_Flow::PathNode src, HostToAnyArg_Flow::PathNode snk
where HostToAnyArg_Flow::flowPath(src, snk)
select snk.getNode(), src, snk,
  "Untrusted host-related value flows into a call argument.",
  src.getNode(), "Host-derived source"
