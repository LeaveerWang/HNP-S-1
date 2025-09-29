/**
 * pyhnp.ql
 * Detect Host header / URL poisoning flows …
 */

import python
// 切到“新数据流 API”
import semmle.python.dataflow.new.DataFlow
import semmle.python.dataflow.new.TaintTracking

/** 
 * 新 API：用 module 实现 ConfigSig（别再用 class extends …）
 */
module HNPConfig implements DataFlow::ConfigSig {
  predicate isSource(DataFlow::Node source) {
    // —— 这里仅把 “e = source” 改成桥接：DataFlow::exprNode(e) = source ——
    exists(Expr e | DataFlow::exprNode(e) = source and (
      // ↓↓↓ 你的原有表达式判定一字不改 ↓↓↓
      exists(Attribute a | a = e and (
        a.getAttr() = "host" or a.getAttr() = "host_url" or a.getAttr() = "url_root" or
        a.getAttr() = "base_url" or a.getAttr() = "url" or a.getAttr() = "scheme" or
        a.getAttr() = "netloc" or a.getAttr() = "hostname" or a.getAttr() = "uri" or
        a.getAttr() = "urlparts"
      ))
      or exists(Call call | call = e and (
        exists(Name n | n = call.getFunc() and (
          n.getId() = "reverse" or n.getId() = "reverse_lazy" or n.getId() = "url_for" or
          n.getId() = "full_url" or n.getId() = "reverse_url" or n.getId() = "route_url" or
          n.getId() = "URL" or n.getId() = "build_absolute_uri"
        ))
        or exists(Attribute af | af = call.getFunc() and (
          af.getAttr() = "reverse" or af.getAttr() = "reverse_lazy" or af.getAttr() = "url_for" or
          af.getAttr() = "full_url" or af.getAttr() = "reverse_url" or af.getAttr() = "route_url" or
          af.getAttr() = "build_absolute_uri"
        ))
      ))
      or exists(Attribute a | a = e and (
        a.getAttr() = "headers" and
        exists(Attribute a2 | a2 = a.getObject() and a2.getAttr() = "host")
      ))
      or exists(Attribute a | a = e and (
        a.getAttr() = "env" and
        exists(Attribute a2 | a2 = a.getObject() and a2.getAttr() = "http_host")
      ))
    ))
  }

  // 放在 module HNPConfig implements DataFlow::ConfigSig { ... } 内部
  predicate isAdditionalFlowStep(DataFlow::Node pred, DataFlow::Node succ) {
    // 统一把 Node 映射为表达式
    exists(Expr pe, Expr se |
      DataFlow::exprNode(pe) = pred and
      DataFlow::exprNode(se) = succ and (

        // format: "{}{}".format(x, y)  —— 接收者与任一参数都会影响结果
        exists(Call c, Attribute f |
          se = c and f = c.getFunc() and f.getAttr() = "format" and
          (pe = f.getObject() or pe = c.getAnArg())
        )
        or
        // join: sep.join(parts) —— 分隔符与被拼接序列都会影响结果
        exists(Call c2, Attribute f2 |
          se = c2 and f2 = c2.getFunc() and f2.getAttr() = "join" and
          (pe = f2.getObject() or pe = c2.getAnArg())
        )

        // 可选：某些代码把 format 当作普通函数使用：format(x, y)
        or
        exists(Call c3, Name n3 |
          se = c3 and n3 = c3.getFunc() and n3.getId() = "format" and
          pe = c3.getAnArg()
        )
      )
    )
  }



  predicate isSink(DataFlow::Node sink) {
    // 把 sink 绑定到“调用的参数表达式”，而不是调用表达式本身
    exists(Call call, Expr arg |
      arg = call.getAnArg() and
      DataFlow::exprNode(arg) = sink and
      (
        // 1) 发送邮件类 API（函数/方法）——参数任意位置都算 sink
        exists(Name n | n = call.getFunc() and (
          n.getId() = "send_reset_email" or
          n.getId() = "send_reset_email_async" or
          n.getId() = "async_send_reset_email" or
          n.getId() = "send_mail" or
          n.getId() = "send" or
          n.getId() = "send_message" or
          n.getId() = "sendmail"
        ))
        or exists(Attribute af | af = call.getFunc() and (
          af.getAttr() = "send" or
          af.getAttr() = "send_message" or
          af.getAttr() = "send_mail" or
          af.getAttr() = "sendmail"
        ))

        // 2) 邮件内容写入（EmailMessage 等）：真正承载 URL 的是这些内容参数
        or exists(Attribute msgf | msgf = call.getFunc() and (
          msgf.getAttr() = "add_alternative" or
          msgf.getAttr() = "set_content" or
          msgf.getAttr() = "attach" or
          msgf.getAttr() = "set_payload"
        ))

        // 3) 重定向类（如果你的示例里也有）
        or exists(Name r | r = call.getFunc() and r.getId() = "redirect")
        or exists(Attribute rr | rr = call.getFunc() and rr.getAttr() = "redirect")

        // 4) URL 构造直接作为参数传出（可选，保持你原逻辑）
        or exists(Name b | b = call.getFunc() and (
          b.getId() = "url_for" or b.getId() = "build_absolute_uri" or
          b.getId() = "reverse" or b.getId() = "reverse_lazy" or
          b.getId() = "full_url" or b.getId() = "reverse_url" or
          b.getId() = "route_url"
        ))
        or exists(Attribute bf | bf = call.getFunc() and (
          bf.getAttr() = "url_for" or bf.getAttr() = "build_absolute_uri" or
          bf.getAttr() = "reverse" or bf.getAttr() = "reverse_lazy" or
          bf.getAttr() = "full_url" or bf.getAttr() = "reverse_url" or
          bf.getAttr() = "route_url"
        ))
      )
    )
  }


  // 新 API 下，isBarrier / isAdditionalFlowStep 都是可选。
  // Python 的 taint 传播已覆盖常见拼接/format/join/f-string，保持空即可。
}

// 把配置应用到“全局污点跟踪”
module HNPFlow = TaintTracking::Global<HNPConfig>;

/** -------- Main query -------- */
from DataFlow::Node source, DataFlow::Node sink
where HNPFlow::flow(source, sink)
select source, sink,
  "Host header poisoning: $@ flows to email generation at $@", source, sink
