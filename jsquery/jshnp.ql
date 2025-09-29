/**
 * Provides a taint tracking configuration for reasoning about host header
 * poisoning in email generation.
 */

import javascript
import semmle.javascript.security.dataflow.HostHeaderPoisoningInEmailGenerationQuery
import HostHeaderPoisoningFlow::PathGraph

/**
 * A taint tracking configuration for host header poisoning.
 */
module HostHeaderPoisoningConfig implements DataFlow::ConfigSig {
  predicate isSource(DataFlow::Node node) {
    exists(Http::RequestHeaderAccess input | node = input |
      input.getKind() = "header" and
      input.getAHeaderName() = "host"
    )
  }
  predicate isAdditionalFlowStep(DataFlow::Node pred, DataFlow::Node succ) {
    exists(AssignExpr assign |
      assign.getRhs() = pred.asExpr() and
      succ.asExpr() = assign.getLhs()
    )
    or exists(DataFlow::PropWrite write |
      write.getRhs() = pred and
      succ = write.getBase()
    )
    or exists(CallExpr call |
      call.getAnArgument() = pred.asExpr() and
      call.getCalleeName().matches("%template%") and
      succ.asExpr() = call
    )
  }

  predicate isSink(DataFlow::Node node) { 
    exists(EmailSender email | node = email.getABody()) 
    //any()
  }
  predicate observeDiffInformedIncrementalMode() { any() }
}

module HostHeaderPoisoningFlow = TaintTracking::Global<HostHeaderPoisoningConfig>;

from HostHeaderPoisoningFlow::PathNode source, HostHeaderPoisoningFlow::PathNode sink
where HostHeaderPoisoningFlow::flowPath(source, sink)
select sink.getNode(), source, sink, "Links in this email can be hijacked by poisoning the $@.",
   source.getNode(), "HTTP host header"

// /**
//  * @kind path-problem
//  */
// import javascript

// module MyConfig implements DataFlow::ConfigSig {
//   predicate isSource(DataFlow::Node node) { ... }
//   predicate isSink(DataFlow::Node node) { ... }
//   predicate isAdditionalFlowStep(DataFlow::Node pred, DataFlow::Node succ) { ... }
// }

// module MyFlow = TaintTracking::Global<MyConfig>;

// from MyFlow::PathNode source, MyFlow::PathNode sink
// where MyFlow::flowPath(source, sink)
// select sink.getNode(), source, sink, "taint from $@.", source.getNode(), "here"

// module SensitiveLoggerConfig implements DataFlow::ConfigSig {  // 1: module always implements DataFlow::ConfigSig or DataFlow::StateConfigSig
//   predicate isSource(DataFlow::Node source) { source.asExpr() instanceof CredentialExpr } // 3: no need to specify 'override'
//   predicate isSink(DataFlow::Node sink) { sinkNode(sink, "log-injection") }

//   predicate isBarrier(DataFlow::Node sanitizer) {  // 4: 'isBarrier' replaces 'isSanitizer'
//     sanitizer.asExpr() instanceof LiveLiteral or
//     sanitizer.getType() instanceof PrimitiveType or
//     sanitizer.getType() instanceof BoxedType or
//     sanitizer.getType() instanceof NumberType or
//     sanitizer.getType() instanceof TypeType
//   }

//   predicate isBarrierIn(DataFlow::Node node) { isSource(node) } // 4: isBarrierIn instead of isSanitizerIn

// }

// module SensitiveLoggerFlow = TaintTracking::Global<SensitiveLoggerConfig>; // 2: TaintTracking selected 

// import SensitiveLoggerFlow::PathGraph  // 7: the PathGraph specific to the module you are using

// from SensitiveLoggerFlow::PathNode source, SensitiveLoggerFlow::PathNode sink  // 8 & 9: using the module directly
// where SensitiveLoggerFlow::flowPath(source, sink)  // 9: using the flowPath from the module 
// select sink.getNode(), source, sink, "This $@ is written to a log file.", source.getNode(),
//   "potentially sensitive information"