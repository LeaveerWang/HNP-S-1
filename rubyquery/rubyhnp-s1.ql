import codeql.ruby.AST
import codeql.ruby.DataFlow
import codeql.ruby.TaintTracking

/** Host 相关来源 -> URL 构造点 的污点跟踪配置 */
module HostUrlCfg implements DataFlow::ConfigSig {

  /** Source：读取 Host 相关的调用/下标/取 Header/ENV */
  predicate isSource(DataFlow::Node src) {
    // A) request.host / hostname / host_with_port
    exists(MethodCall m |
      src.asExpr().getExpr() = m and
      m.getMethodName().regexpMatch("^(host|hostname|host_with_port)$")
    )
    or
    // B) env["HTTP_HOST"] / env["host"] / env["X-Forwarded-Host"] / 也含 APP_HOST
    exists(ElementReference er, StringLiteral lit |
      src.asExpr().getExpr() = er and
      lit = er.getAChild() and
      lit.getConstantValue().toString().toLowerCase()
        .regexpMatch("^(base_host|app_host|http_host|host|x-forwarded-host)$")
    )
    or
    // C) request.get_header("HTTP_HOST" / "X-Forwarded-Host")
    exists(MethodCall m, StringLiteral lit |
      src.asExpr().getExpr() = m and
      m.getMethodName() = "get_header" and
      lit = m.getArgument(0) and
      lit.getConstantValue().toString().toLowerCase()
        .regexpMatch("^(http_host|x-forwarded-host)$")
    )

  // ==================================== 以下为防御配置 ====================================
/*
    or
    // D) ENV["APP_HOST"] Ruby 的 进程环境变量
    exists(ConstantReadAccess env, ElementReference ref |
      env.getName() = "ENV" and
      ref.getReceiver() = env and
      // ElementReference 继承自 Call，用 getArgument(0) 取索引实参
      ref.getArgument(0).(StringLiteral).getConstantValue().toString() = "APP_HOST" and
      // 把该表达式绑定为数据流源
      src.asExpr().getExpr() = ref
    )
    or
    // E) Rails.application.config.x.app_host Rails 提供的自定义配置命名空间 人为配置/白名单
    exists(ElementReference er, MethodCall m |
      src.asExpr().getExpr() = er and
      er.getReceiver() = m and
      m.getMethodName() = "default_url_options" and
      // [:host] / ["host"] 都兜住
      er.getArgument(0).toString().regexpMatch("^:host$|^host$") and
      m.getReceiver().toString().regexpMatch("^ActionMailer::Base$")
    )
    or
    // —— Rails.application.config.action_mailer.default_url_options[:host] Rails 对 Action Mailer 提供的全局默认 URL 选项。
    // 邮件上下文里调用 *_url / url_for 等，会优先用这里的 host/protocol 人为配置/白名单
    exists(ElementReference er, MethodCall m_do, MethodCall m_am, MethodCall m_cfg |
      src.asExpr().getExpr() = er and
      er.getReceiver() = m_do and
      m_do.getMethodName() = "default_url_options" and
      er.getArgument(0).toString().regexpMatch("^:host$|^host$") and
      // 链：Rails.application.config.action_mailer.default_url_options
      m_do.getReceiver() = m_am and
      m_am.getMethodName() = "action_mailer" and
      m_am.getReceiver() = m_cfg and
      m_cfg.getMethodName() = "config" and
      m_cfg.getReceiver().toString().regexpMatch("^Rails\\.application$")
    )
    or
    // Controller 级别默认主机（有些项目也会读这里）Controller 可以定义/覆写 default_url_options（类方法或实例方法），
    // 用于控制器上下文里 URL helper 的默认项。
    exists(ElementReference er, MethodCall m_do, MethodCall m_ac, MethodCall m_cfg |
      src.asExpr().getExpr() = er and
      er.getReceiver() = m_do and
      m_do.getMethodName() = "default_url_options" and
      er.getArgument(0).toString().regexpMatch("^:host$|^host$") and
      // 链：Rails.application.config.action_controller.default_url_options
      m_do.getReceiver() = m_ac and
      m_ac.getMethodName() = "action_controller" and
      m_ac.getReceiver() = m_cfg and
      m_cfg.getMethodName() = "config" and
      m_cfg.getReceiver().toString().regexpMatch("^Rails\\.application$")
    )
    or
    // F) ActionMailer::Base.default_url_options = { host: ... } 
    // 直接对 Mailer 基类设置默认 URL 选项。等价于在配置里写 config.action_mailer.default_url_options，只是写法不同
    exists(MethodCall set |
      set.getMethodName() = "default_url_options=" and
      exists(MethodCall recv |
      recv = set.getReceiver() and
      recv.getMethodName() = "action_mailer"
      ) and
      src.asExpr().getExpr() = set.getArgument(0)
      )
    or
    // ActionMailer::Base.default_url_options = { host: ... }
    // 直接对 Mailer 基类设置默认 URL 选项。等价于在配置里写 config.action_mailer.default_url_options，只是写法不同
    exists(MethodCall set |
      src.asExpr().getExpr() = set.getArgument(0) and
      set.getMethodName() = "default_url_options=" and
      set.getReceiver().toString() = "ActionMailer::Base"
      )
    or
    // Read: Rails.application.config.action_mailer.default_url_options[:host]
    // Action Mailer 生成绝对 URL 时要用到的默认 host
    exists(ElementReference er, MethodCall mDo, MethodCall mAm, MethodCall mCfg, MethodCall mApp, Expr key |
      src.asExpr().getExpr() = er and
      key = er.getArgument(0) and
      // [:host] 或 ["host"] 都兜住（SymbolLiteral 或 StringLiteral）
      key.toString().regexpMatch("^:host$|^['\"]host['\"]$") and

      er.getReceiver() = mDo and mDo.getMethodName() = "default_url_options" and
      mDo.getReceiver() = mAm and mAm.getMethodName() = "action_mailer" and
      mAm.getReceiver() = mCfg and mCfg.getMethodName() = "config" and
      mCfg.getReceiver() = mApp and mApp.getMethodName() = "application" and
      mApp.getReceiver().toString() = "Rails"
      )
    or
    // Read: ActionMailer::Base.default_url_options[:host]
    // Action Mailer 生成绝对 URL 时要用到的默认 host
    exists(ElementReference er, MethodCall mDo, Expr key |
      src.asExpr().getExpr() = er and
      key = er.getArgument(0) and
      key.toString().regexpMatch("^:host$|^['\"]host['\"]$") and
      er.getReceiver() = mDo and mDo.getMethodName() = "default_url_options" and
      mDo.getReceiver().toString() = "ActionMailer::Base"
    )
    or
    // ★ NEW: 通用 —— 把任何 `default_url_options=({ ... :host ... })` 的整个实参当作源
    //广义地说，只要你看到给某个对象（可能是 ActionMailer::Base、某个 Mailer 类、Rails.application.routes、某个 Controller 类/实例）写入 default_url_options= 且包含 :host，
    //这就是在设定该上下文里的 URL 默认 host
    exists(MethodCall set, Expr arg |
      set.getMethodName() = "default_url_options=" and
      arg = set.getArgument(0) and
      exists(Expr key |
        key = arg.getAChild*() and
        key.toString().regexpMatch("^:host$|^['\"]host['\"]$")
      ) and
      src.asExpr().getExpr() = arg
    )
*/
        
  }

  /** 关键桥接：default_url_options -> URL 构造（当未显式传 host 时）*/
  predicate isAdditionalFlowStep(DataFlow::Node pred, DataFlow::Node succ) {
    // —— 隐式读取默认 host：default_url_options=  ->  *_url/url_for/... 调用
    exists(MethodCall m, MethodCall set, MethodCall recv |
      // sink 侧：命中 URL 构造调用
      succ.asExpr().getExpr() = m and
      (
        m.getMethodName().regexpMatch(".*_url$") or
        m.getMethodName() = "url_for" or
        m.getMethodName() = "full_url_for" or
        m.getMethodName() = "polymorphic_url" or
        m.getMethodName() = "redirect_to"
      ) and
      // 若显式传入了 host:，则不走“默认 host”桥（用文本匹配避免依赖特定 AST 类型）
      not exists(Expr arg |
        arg = m.getAnArgument() and
        arg.toString().regexpMatch("(^|\\W)host\\s*:")
      ) and
      // source 侧：config.action_mailer/controller.default_url_options = <右值>
      set.getMethodName() = "default_url_options=" and
      recv = set.getReceiver() and
      recv.getMethodName().regexpMatch("^(action_mailer|action_controller)$") and
      // 把赋值右值作为 pred
      pred.asExpr().getExpr() = set.getArgument(0)
      )
     or
    // ★ NEW: 更宽松的默认 host 桥接（任何 default_url_options= → 任意 *_url 调用）
    exists(MethodCall set2, MethodCall helper |
      set2.getMethodName() = "default_url_options=" and
      pred.asExpr().getExpr() = set2.getArgument(0) and
      helper.getMethodName().regexpMatch(".*_url$|^url_for$|^full_url_for$|^polymorphic_url$|^redirect_to$") and
      not exists(Expr arg2 | arg2 = helper.getAnArgument() and arg2.toString().regexpMatch("(^|\\W)host\\s*:")) and
      succ.asExpr().getExpr() = helper
    )
    
    // ==================================== Rodauth ====================================
    or
    // 对于Rodauth的reset_password_email_link的桥接（比如 merge/reverse_merge）……保持不动
    exists(MethodCall m |
      m.getMethodName().regexpMatch("^(merge|reverse_merge)$") and
      succ.asExpr().getExpr() = m and
      (
        pred.asExpr().getExpr() = m.getReceiver() or
        pred.asExpr().getExpr() = m.getArgument(0)
      )
    )

    // ========================= ★ NEW: 通用跨过程桥（MethodCall 版） =========================
    or exists(Method outerM, MethodCall inner, MethodCall outer |
      // inner 出现在某个方法 outerM 的方法体里
      inner.getEnclosingCallable() = outerM and
      pred.asExpr().getExpr() = inner and
      // succ 是“对这个方法（按名字匹配）的任何一次调用”
      outer.getMethodName() = outerM.getName() and
      succ.asExpr().getExpr() = outer
    )
    

    // ========================= ★ NEW: 通用跨过程桥（super 调用也算） =========================
    or exists(Method outerM, SuperCall inner, MethodCall outer |
      inner.getEnclosingCallable() = outerM and
      pred.asExpr().getExpr() = inner and
      outer.getMethodName() = outerM.getName() and
      succ.asExpr().getExpr() = outer
    )

    // ========================= ★ NEW: 左侧接法（帮助把“接收者”传给调用结果） =========================
    // 让“receiver（点左边）”的污点流到“这个调用表达式”的值上，更通用
    or exists(MethodCall call |
      pred.asExpr().getExpr() = call.getReceiver() and
      succ.asExpr().getExpr() = call
    )
  }




predicate isSink(DataFlow::Node sink) {
  // 1) 所有调用的任意实参
  exists(Call c, Expr arg |
    arg = c.getAnArgument() and
    sink.asExpr().getExpr() = arg
  )
  or
  // 2) 任何方法调用的接收者
  exists(MethodCall mc |
    sink.asExpr().getExpr() = mc.getReceiver()
  )
  or
  // 3) super(...) 的任意实参
  exists(SuperCall sc, Expr a |
    a = sc.getAnArgument() and
    sink.asExpr().getExpr() = a
  )
}
}



/** 全局污点跟踪：Host 源头 -> URL 构造点 */
module HostUrlFlow = TaintTracking::Global<HostUrlCfg>;

/** 展示所有“Host-ish 源 -> URL 构造点”的路径 */
from DataFlow::Node src, DataFlow::Node dst
where HostUrlFlow::flow(src, dst)
select dst, "URL here is polluted by", src, "This Host"
