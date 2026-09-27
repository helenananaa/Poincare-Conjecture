# 第十六轮：相对同伦保持与实际能量逼近

## 本轮验收

round14 的球面能量连续性在本轮初始队列中 VERIFIED；内禀度量比较当时仍 RUNNING，保持原工人未重启。
完整读取能量连续性的 164 行源码，核对捕获、交卷和冻结声明哈希，独立源码重编及精确目标公理检查 PASS。
证明使用固定中心的局部光滑标架、切映射和度量配对，再证明其与原点态迹在邻域相等；没有假设球面有全局光滑标架。
AcceptedTwentyTwo.lean 已代入该证明；累计 22 项 ACCEPTED_ISOLATED，未 Git 集成。
证据：energy-source-recheck.json、semantic-review.json、AcceptedTwentyTwo-check.json。

## 两项独立拆分

RelativeRetractionHomotopyStatement：固定实际连续参考扫掠和给定欧氏邻域回缩，构造一个统一正距离，使端点相同且足够接近的映射相对两端球面同伦。要求输出 HomotopicRel，而不是将其当输入。
SphereEnergyApproximationStatement：从实际光滑环境映射、度量张量的精确拉回表示、统一一阶导数和系数误差控制，证明同一球面 Dirichlet 能量任意精度的逼近。
分析任务的参考映射只要求切片 MDifferentiable 和密度 Integrable；不把 Bochner 积分默认值当有限能量。光滑逼近映射的可积性消费刚验收的连续性证明。
两个叶子互不依赖，均只使用固定只读接口。它们不证明邻域回缩或逼近序列本身在真实几何中存在。

## 已检查的父证明

sphereDensity_ambient 直接通过实际 mfderiv 链式法则导出环境二次型能量公式。
RegularizationData.approximate 消费两项叶子，给出正确相对同伦类中的实际光滑代表元；时间参数的两端保持为原基点。
AdditiveRepresentativeTransfer 允许任意小的加法误差，而不是只允许乘法误差。这适用于零能量切片，不需要逼近后能量恰好为零。
additiveTransfer_width_le 直接处理上确界和下确界得到精确宽度不增，不假设最优代表元存在。
approximateTransfer_to_additive 和 regularized_producer_of_approximate 保留旧路线：无需给旧精确/乘法转移额外构造回缩或逼近序列。
RegularizedIntrinsicProfile 接受旧转移或上述新正则化数据；toExtinction 接回既有衰减、消解与 trace。
public_of_regularization_frontier 已编译返回原 V1 TopologicalPoincareStatement，仍为条件证明。
四个新模块共 13 个审计声明通过，公理仅 propext、Classical.choice、Quot.sound。这不是 13 个研究义务已完成。

## 派工与实际最后观察

新项目 poincare-refinement-round16-20260927，两项均显式 gpt-6-luna / xhigh：
- d27r16-relative-retraction-homotopy：紧像邻域上的直线同伦经指定回缩，检查端点和相对固定集。
- d27r16-sphere-energy-approximation：实际二次型误差与导数误差的统一积分估计。
两项声明预检退出码 0；共享 CLI 返回 REGISTERED、ENQUEUED 2、STARTING_FINITE_BATCH。
仅启动有限批次，未开启无限 watch、自动集成或推送。模板中的 sorry 不是已证明结果。
末尾包含新旧队列、进程和 V1 结构检查的调用被安全检查拦截，没有换入口重试。
因此不报告两项最后为 RUNNING，不报告旧度量比较已完成，也不声称本轮获得新的 V1 结构检查 PASS。
新任务的最后实际证据是 dispatch.json 与启动器输出；未交卷验收。旧度量比较最后成功观察是本轮初始 RUNNING。

## 仍未完成的内容

本轮未证明指定紧流形上的欧氏邻域回缩、环境张量模型、保持端点的 C1 光滑逼近在相关手术中存在。
RegularizationData 的这些存在性条件仍必须由真实几何生产者构造，不把它们当作免费完成的事实。
参考切片须处处 MDifferentiable 且可积；不能直接用于只有几乎处处微分的任意 Lipschitz/Sobolev 扫掠。
本轮两项叶子解决给定数据后的同伦/能量控制，不解决真实手术转移、好扫掠、谐和映射紧性或流的存在。
三角剖分、光滑图册、真实受控几何仍是研究义务；旧内禀度量比较也未由本轮代入。

## 保存与验证范围

派工前旧 15 轮冻结源码与编译产物哈希均复核；新锁含源码、产物、任务模板、验收证据及独立 ops 副本。
RegularizedRepresentatives 曾有字段/加法方向的 Lean elaboration 错误；保留两个失败日志，只计最终源码匹配且公理检查通过的结果。
旧 V1 和旧锁未改；本轮末尾 V1 检查被拦截而没有执行。未进行全量依赖重建。
本轮初始 Git HEAD 为 c228980；改动仅在 round16 隔离目录，无 Git 集成、提交、远程推送或上游 PR。
final-status.json 仅记录已成功操作和阻断边界，不声称执行了末尾二次验证。
