# 第二十轮：验收两项交卷，冻结法向局部逆分解，三路 Luna 并行

## 已完成的证明验收

重新读取 round17 和 round19 的交卷，并核对捕获哈希、目标声明和证明体边界。
两份源码在 round20 独立输出目录重编译，随后 import 精确编译产物并检查目标传递公理。
`d27r17-smooth-retraction-form` 与 `d27r19-tubular-inverse-assembly` 均通过。
公理仅含 `propext`、`Classical.choice`、`Quot.sound`，无 `sorryAx`。
人工复核了连续系数场的链式法则，以及同一端点映射、像域、投影的局部逆构造。
`AcceptedTwentySeven.public_after_twenty_seven` 已消费这两个实际证明，去掉原来的两个开放参数。
本次新增验收工人叶子 2 项；此前 25 项，本次累计 27 项。尚未写入主线或提交 Git。

## 已冻结的新分解

`NormalTubeLeaves` 固定三个独立命题：切空间与正交补的线性同构、零纤维端点导数、参数图中的光滑局部逆。
`NormalCoordinateTube.toLocal` 真正使用这三个命题，构造同一总空间、零截面、投影和端点映射的 `LocalTubularData`。
参数数据没有预设端点映射局部逆、端点微分或全局单射性；参数图本身及光滑法向传输的几何存在仍是开放义务。
`NormalApproximation` 保留原参考映射、嵌入、一阶逼近与能量比较，不用无关的存在性替换它们。
`NormalTubeRoot.public_of_normal_frontier` 返回原 V1 `TopologicalPoincareStatement`。
新路径保留旧 Tubular/Retraction/Regularized/Approximate 入口，旧路线没有追加新假设。
五个新模块共 12 个声明通过编译与公理审计；其中包含条件组合和复用，不是 12 个研究缺口已经解决。

## 本地有限批次

项目：`poincare-refinement-round20-20260927`。模型精确为 `gpt-6-luna`。
`d27r20-normal-linear-equiv` 使用 xhigh；`d27r20-normal-endpoint-jet` 使用 high；`d27r20-tubular-chart-inverse` 使用 max。
三个固定声明均预检通过、入队并启动，已观察到三个独立运行中的模型进程；不是仅生成任务卡。
固定依赖为空，各自写入不同的证明文件；模型并发不设人为上限，编译槽 6、验收槽 2。
运行方式为有限批次，无 watch、自动集成、提交、推送或上游 PR。最终状态见 `final-status.json`。

## 已验证可复用的法丛基础

发现 LeeRiemannian `NormalBundle.lean` 的头部注释过时：末尾实际已有 `contMDiffVectorBundle_normalSpace`。
对该模块的 11 个 LeeRiemannian 依赖源码建立隔离快照并逐一重编译，没有复用该库的旧对象文件。
`exists_orthonormalFrame_normalSpace`、`hasLocalSubframes_normalSpace`、`contMDiffVectorBundle_normalSpace`
和 `subContMDiffVectorBundle` 的传递公理审计均通过，仅使用三个标准公理。
证据在 `reuse-normal-bundle/source-manifest.json`、`compile-results.json`、`audit-result.json` 和 `audit.log`。
这些是既有证明的复用验收，不计为新的 Luna 工人叶子，也尚未自动视为满足当前 `NormalCoordinateTube` 合同。
不应再次派发“从零证明光滑法丛存在”的笼统任务；应优先桥接其总空间拓扑/度量、欧氏法向参数图、零截面端点公式与投影光滑性。

## 冻结、安全边界与未完成部分

V1 13 个冻结文件检查通过；旧 round1–17、round19 及新 round20 来源和产物哈希均经核对。
round18 失败草稿没有混入可信依赖。新的固定源码只读，并另存可信 ops 锁文件。
主线、V1 绑定、旧冻结源、蓝图标记和 Git HEAD 未修改；未做全量重建。
当前仍有 `smoothing`、`geometric_trace` 两个根接口未绑定完整实现。
三角剖分、PL 到光滑图册、真实受控手术流、好扫掠与相对一阶光滑逼近等研究义务仍开放。
条件根定理证明“这些输入充分”，不证明全部输入已经存在，更不构成无条件庞加莱证明。
