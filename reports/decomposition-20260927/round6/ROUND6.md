# 第六轮：全局初始度量与真实 Ricci 区间到事件预算

## 已完成

DoCarmo 的 `Riemannian.exists_riemannianMetric` 已读取关键完整证明，并从原始源码独立重编译。
它由切丛局部正定型及光滑单位分解构造全局度量，不要求原流形是球。
`metric-source-check.json` 记录源 SHA256、源码重编和传递公理结果，均通过。

`MetricInitialization.lean` 三个声明通过源码编译及传递公理检查：
- `global_initial_metric`：对原有光滑图册产生实际全局黎曼度量。
- `global_initial_scalar_bound`：用紧致标量曲率最小值产生非负 C 和全局下界 -C。
- `metric_initialData_exists`：将同一个度量及其下界组合为实际初始数据。
这不包含手术流所需的曲率/单位球体积归一化，也不构造 Ricci 流。

`RicciVolumeBudget.lean` 七个声明源码编译及传递公理检查通过。
其中直接完成的内容包括：从实际黎曼测度构造有限 measured slice、由真实时间标签覆盖推出样本基数上界。
其他为明确消费新端点引理的条件组合：
1. `RicciIntervalBridge` 含实际度量族、闭区间 Ricci PDE、初始标量下界和两端保测度可测同构。允许空间不连通。
2. `ricci_interval_volume_growth` 利用端点传播和已有紧致体积定理，推出 Y.volume ≤ exp(C*T)*X.volume。
3. `RicciMeasuredHistory.toMeasured` 从上述实际区间构造原预算的 smooth_growth 字段，不再把它作为输入字段。
4. `AnchoredRicciBudget` 对同一事件集的任意有限样本，提供含实际事件时间标签的历史，并将初态固定为同一初始度量的 measured slice。
5. `anchored_budget_to_uniform` 证明它足以提供旧的统一预算。
6. `public_of_ricci_budget_frontier` 把新的前沿组合回原始 V1 TopologicalPoincareStatement。

以上十个新审计声明及原度量存在性目标的公理均只含 propext、Classical.choice、Quot.sound。
新文件首次编译的名称歧义已在冻结前修复，保留 MetricInitialization-first-failure.log；失败结果不计证明。

## 新工人

`poincare-refinement-round6-20260927` 已通过共享 CLI 注册并实际启动一个有限批次。
`d27r6-closed-scalar-propagation` 使用精确 `gpt-6-luna`、`xhigh`，最后观察为 RUNNING。
它要求从实际闭区间 Ricci 流的初始标量下界推得包含终点 T 的全区间下界。
既有 Ico 定理不能直接用在终点，既有内部 slab 定理也不能忽略 interior 条件。
给定证明策略是限制到 Ico，复用标量最小值单调性，再以同一函数在 Icc 上的连续性补终点。
父组合已编译通过；任务模板中的 sorry 只用于声明预检，不是已完成证明。
本轮只有这一项通过新派工门槛，不把任务数量当并发上限。

## 数学边界

新总组合仍是条件定理，四个前沿输入为三项研究任务和一个待证端点引理。
初始度量存在性已经实际提供，但全局短时解、手术控制、归一化、正体积损失、消解与穷尽丢弃分类仍开放。
实际区间的度量和两端测度在桥内一致；完整物理手术历史与拓扑投影各时刻逐项对应尚未冻结，仍必须由几何生产者证明。
跨手术保持统一标量下界、每次正损失、任意有限样本可由实际历史覆盖都未被自动得到。
固定 initial measured slice 不意味着已构造整条从该张量开始的全局 Ricci 手术流。

光滑化方面重新阅读 Lange arXiv:1507.02395v2 的 §3.2、§3.4、§3.6，确认局部边邻域调整与顶点附近相对构造仍需具体实现。
原文文本可读；PDF 截图两次返回 Internal Error，没有声称复核图示。只研究三维非等变存在性，不扩展到四维或有限群分类。
一个额外径向辅助源码的写入被安全检查拦截，未换入口重试，未计作已编译成果。

## 保存与验证

`MetricInitialization-check.json`、`RicciVolumeBudget-check.json`：十个声明通过。
`metric-source-check.json`：原库的全局度量存在性从源码重编并审计通过。
`frontier.dag.json`、`frontier.lock.json`：16 节点的新适配图和四个显式开放输入；旧版本未修改。
此前九项验收成果继续复用；旧冻结源哈希检查通过，本轮不声称重新全量验证旧九项。
公开 V1 的 13 文件结构检查通过；smoothing/geometric_trace 未绑定，complete=false。
没有全量重建、Git 集成、提交、推送、上游 PR 或自动持续派工。
