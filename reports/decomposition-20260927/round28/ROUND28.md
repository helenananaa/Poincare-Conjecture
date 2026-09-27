# 第二十八轮：把最后一个延拓任务冻结拆成三路独立证明

## 已完成的数学拆分

沿用 round27 的 42 项已验收固定叶子，不把后来同一命题的原工人交卷重复计数。
固定显式 radialDirection、cylinderCutoff 和 radialCylinderExtension。
radialDirection 在原点取任意单位球面点，截断函数在原点的开邻域为零，因此不要求径向归一化在原点连续。
radialDirection_coe 与 radialDirection_unit 已编译并通过传递公理审计。

三个新叶子：RadialLocalSmoothStatement、CylinderCutoffGlueStatement、CylinderCutoffSupportStatement。
它们分别证明局部径向光滑延拓、离轴 C1 映射的截断拼接，以及固定表达式的紧支撑与精确一致性。
每个叶子使用同一组冻结定义，不独立选择不兼容的最终延拓见证。
cylinder_extension_of_radial_leaves 已实际消费三个声明，构造原 CylinderCompactExtensionStatement。
public_of_radial_extension_frontier 将这份延拓接回不变的原 V1 结论。
父组合只证明三个输入充分，不证明这三个尚未交卷的输入已经存在。

两个新模块共四个声明已编译，重新导入精确产物的传递公理检查通过。
公理仅含 propext、Classical.choice、Quot.sound，无 sorryAx。
证据：RadialExtensionLeaves-check.json、RadialExtensionConstruction-check.json、final-import-audit.json。

## 本轮派工

项目 poincare-refinement-round28-20260927，精确模型均为 gpt-6-luna。
d27r28-radial-local-smooth：max。
d27r28-cylinder-cutoff-glue：xhigh。
d27r28-cylinder-cutoff-support：high。
三个固定声明预检通过，入队并启动有限批次；没有 watch、自动集成或推送。
第一次入队被优先级范围校验拒绝。原 cards.json 和数学冻结锁保留不变。
dispatch-cards.json 只将 priority 从 1200 修正为 1000；逐项核对所有其他字段完全相同。
dispatch-metadata.lock.json 记录两版哈希和唯一允许的配置变更；实际入口为 run_dispatch.py。

## 状态检查纠正与保留措施

最初误查了用户级 systemd，inactive/dead 不能说明系统级工人已经退出。
/proc 的 cgroup 路径确认这些工人属于 /system.slice/lean-swarm-*.service。
改用不带 --user 的 systemctl show，并逐项核对模型 PID、任务 UUID 和 cgroup。
最后确认新批三路工人实际运行，原延拓整题工人也仍在运行，共四路；详情见 final-status.json。
原球面限制任务后来也通过了调度器验收，但其命题已由 round27 修复证明接入，不再重复计数。
没有改动或终止原工人，也没有手工更改原任务队列状态。
仅停止了协调者自己在本轮启动的两次冗长诊断编译，原始源码与诊断日志均保留。

## 完成边界

本轮新增验收固定叶子为零，累计仍为 42；四个新声明包含定义性质和条件组合，不计作四个研究缺口已解决。
紧支撑 C1 延拓仍未完成；它现在具有已核验的三路并行分解。
原候选中较强的解析阶数和实数/非负实数归一化识别问题没有通过修改冻结目标来回避。
新任务明确要求 C-infinity 局部光滑性、同一公式及精确一致性。
三角剖分、PL 光滑化、真实受控手术流、好扫掠仍有开放义务，smoothing 与 geometric_trace 未闭合。
本轮及前序冻结来源和产物哈希核对通过，V1 的 13 个冻结文件保持不变。
没有全量重建、Git 提交、推送、上游 PR 或蓝图完成标记变更。
