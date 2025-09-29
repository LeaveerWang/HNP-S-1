/**
 * @name Host header → ANY call site (max coverage, fixed)
 * @description Track taint from Host-like inputs to ANY function/method call:
 *              - every call argument (over-taint by design)
 *              - every call result (the call expression itself)
 * @kind path-problem
 * @problem.severity warning
 * @id go/hhi/host-to-any-call
 * @tags security hhi broad sink url redirect external
 */

import go
import TaintTracking

/* 1) Sources: Host-like inputs */
predicate isHostSource(DataFlow::Node n) {
  exists(CallExpr call, Method m |
    call.getTarget() = m and
    (m.hasQualifiedName("net/http", "Header", "Get") or m.getName() = "Get") and
    call.getArgument(0).getStringValue().regexpMatch("(?i)^(host|x-forwarded-host|x-original-host)$") and
    n = DataFlow::exprNode(call)
  )
  or
  exists(SelectorExpr sel |
    sel.getSelector().getName() = "Host" and
    n = DataFlow::exprNode(sel)
  )
}

/* 2) Broad sinks: ANY call arg + ANY call result */
predicate isAnyCallArgSink(DataFlow::Node n) {
  exists(CallExpr c | n = DataFlow::exprNode(c.getAnArgument()))
}

predicate isAnyCallResultSink(DataFlow::Node n) {
  exists(CallExpr c | n = DataFlow::exprNode(c))   // the call expression result itself
}

/* >>> rename to avoid shadowing the Config.isSink <<< */
predicate isBroadSink(DataFlow::Node n) { isAnyCallArgSink(n) or isAnyCallResultSink(n) }

/* 3) Taint config */
module Cfg implements DataFlow::ConfigSig {
  predicate isSource(DataFlow::Node s) { isHostSource(s) }
  predicate isSink  (DataFlow::Node t) { isBroadSink(t) }
  // 可选降噪：
  // predicate isBarrier(DataFlow::Node n) { /* e.g., validateHost(...) */ }
  // predicate isAdditionalFlowStep(DataFlow::Node a, DataFlow::Node b) { /* custom */ }
}

module Flow = TaintTracking::Global<Cfg>;

/* 4) 单一 SELECT：标注是“参数”还是“返回值” */
predicate sinkLabel(DataFlow::Node n, string label) {
  exists(CallExpr c, Function f |
    n = DataFlow::exprNode(c.getAnArgument()) and c.getTarget() = f |
    label = "arg of " + f.getQualifiedName()
  )
  or
  exists(CallExpr c2, Function f2 |
    n = DataFlow::exprNode(c2) and c2.getTarget() = f2 |
    label = "result of " + f2.getQualifiedName()
  )
}

from DataFlow::Node src, DataFlow::Node sink, string what
where Flow::flow(src, sink) and sinkLabel(sink, what)
select sink,
  "Host-controlled data flows into " + what + " from $@.",
  src, src.toString()
