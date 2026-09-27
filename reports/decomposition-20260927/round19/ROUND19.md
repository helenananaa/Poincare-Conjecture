# 第十九轮：修复管状邻域父组合，复用紧集单射定理，派发指定局部逆拼接

## 上一轮失败已修复

保留 round18 原始候选与失败日志不变。在 round19 新副本中将不存在的
`metric.toTopologicalSpace` 改为实际层级
`metric.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace`。
四个新模块的最终源码均已编译和审计：CompactTubularData、CompactTubularReuse、TubularApproximation、TubularRoot。
共 10 个审计声明，公理仅含 propext、Classical.choice、Quot.sound。
这些包括复用、条件组合，不是 10 个大型研究缺口已经完成。

## 不重复证明已有定理

固定版本 mathlib 的 `Set.InjOn.exists_isOpen_superset` 已直接给出需要的紧集统一单射邻域。
源码位于 Topology/Separation/Hausdorff.lean；完整相关证明已读取。
`checked_compact_injective_neighborhood` 消费它，已编译，无须为这一项再开 Luna。
`compact_euclidean_embedding_exists` 复用固定 compact Whitney 定理，实际产生光滑闭嵌入与微分单射性。
这里不宣称已经由嵌入构造出法丛、局部逆或全局管状邻域。

## 新固定任务

`d27r19-tubular-inverse-assembly`，精确模型 gpt-6-luna / xhigh。
输入为同一个 total、zero、project、endpoint、局部逆图册，以及包含 zero 像的开单射邻域 U。
任务要输出 R 并证明：R.embed=e.map；R.domain=endpoint '' U；对 x∈U，R.localRetract(endpoint x)=project x。
不能只给一个不带对应公式的任意回缩。局部光滑性仅在声明的开域内要求，不要求全空间回缩。
证明路线：限制 endpoint 到 U，使用局部图册证明它是开嵌入，构造到其像的逆，再与同一 project 复合。
目标声明预检、注册、入队和有限批次启动成功；最终进程/队列以 final-status.json 为准。
旧 round17 系数场任务未被中断或重启，两项互无待证明依赖。

## 从子任务到原始目标

`local_tubes_retraction_of_assembly` 已消去紧集单射邻域参数，只剩真正的局部逆拼接输入。
`TubularApproximationData.toRetraction` 同时保留原参考映射及原嵌入的等式；所有环境导数和逼近序列沿同一嵌入搬运。
`TubularIntrinsicProfile.toRetraction` 接入旧能量逼近与扫掠消解链。
`RetractionIntrinsicProfile.toTubular` 是回归适配：旧路线无须追加新假设。
`public_of_tubular_frontier` 已编译返回原 V1 `TopologicalPoincareStatement`。
其显式开放输入为三项研究义务、旧 form 叶子和本次 assembly 叶子。

## 冻结和未完成部分

派工前核对 round1 至 round17 的已冻结源码/产物；round18 是失败且未冻结的候选，未作为可信依赖导入。
新声明在冻结前加强了输出中的精确像域与逆公式，并重新编译全部四模块；只记录最后通过的源码哈希。
`frontier.lock.json` 与独立 ops 副本保存新来源、产物、任务卡、旧版本引用和复用的两份 mathlib 源哈希。
`frontier.dag.json` 是经人工审查的依赖摘要，实际充分性由 Lean 根组合证明。
复用固定依赖缓存，无全量重建；本轮没有改变旧冻结声明、V1 绑定、Git 提交、远程推送或上游 PR。

本轮没有新增独立验收的工人叶子；此前累计 25 项隔离验收记录保持，不把复用引理或条件包装算成新工人交卷。
实际法丛/端点映射、局部法向逆的几何存在、相对一阶光滑逼近、真实手术流与好扫掠构造仍未完成。
欧氏嵌入存在不等于管状邻域存在；局部图册记录的存在也没有被本轮定义代替证明。
三角剖分、PL 光滑化和几何生产者仍是研究级义务，当前不是完整庞加莱证明。
