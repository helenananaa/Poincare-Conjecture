# 第十七轮：三项实收；从局部光滑回缩产生能量模型

## 接续与独立验收

本轮开始：内禀度量比较及相对回缩同伦两项 VERIFIED，能量逼近 RUNNING。
完整读取前两份返回源码（296/66 行），核对冻结声明前后缀、捕获哈希和验收哈希；从源码重编并导入精确目标审计，全部通过。
期间能量逼近任务返回 VERIFIED；随后完整读取其 191 行源码、核对声明/哈希并独立重编审计，通过。
未中断、重启或重复派发旧任务；共享队列的 VERIFIED 未冒充 INTEGRATED。
三项都仅依赖 propext、Classical.choice、Quot.sound；累计 ACCEPTED_ISOLATED 从 22 增为 25。
证据：two-source-recheck.json、energy-approximation-recheck.json、semantic-review.json。

## 实际消费

AcceptedTwentyFour 和 AcceptedTwentyFive 将三项真正代入原根组合。
public_after_twentyFive 仍只有原路线的三个研究级输入：三角剖分、有限光滑图册和真实几何生产者。
这些输入没有完成，本轮不是无条件庞加莱证明，也没有给出完成比例。

## 新局部构造入口

SmoothRetractionData 记录原来的 AmbientRetraction、光滑嵌入、同一回缩的函数表示，以及它仅在声明的开邻域上光滑的证明。
不要求整个欧氏空间回缩到目标，也不要求邻域外光滑。
SmoothRetractionFormStatement 是新固定叶子：由上述数据和实际目标度量，构造连续的环境双线性系数场，并证明通过同一嵌入微分拉回等于目标度量。
建议公式：A_p(v,w)=g_p(D retract_(embed p) v, D retract_(embed p) w)。需处理基点等式、局部光滑性、链式法则和双线性场连续性。
没有把待构造的系数场、系数连续性或其度量实现等式藏进输入。

AmbientEnergyModel.uniform_form_control 已直接证明：目标紧致性给统一系数范数界；紧致像上的一致连续性将环境位置误差变为系数误差。
因此 RetractionApproximationData 不要求预先提供能量模型、Q 界或系数逼近证明，只记录同一回缩和实际环境一阶逼近。
toRegularization 已检查：新叶子完成后，它构造旧 RegularizationData，并显式保留 reference 等式和 retraction 等式。
旧精确、近似和已有 RegularizedClassTransfer 都仍作为可选分支；旧 profile 的适配已通过检查，不强迫旧路线提供新回缩。
public_of_smooth_retraction_frontier 已编译返回原始 V1 TopologicalPoincareStatement。

## 新派工

唯一新任务 d27r17-smooth-retraction-form，指定 gpt-6-luna / max。
固定声明不依赖其他未完成新叶子，具有上述已编译的父消费者；从共享 lean_swarm CLI 注册并派发有限批次。
没有重开任何旧任务，没有无限 watch、自动 Git 集成或推送。
声明模板中的 sorry 仅用于待证明任务预检，不作为证明导入父模块。
实际派工回执及最后运行观察分别以 dispatch.json、final-status.json 为准。

## 编译与完整性

五个新增模块共 14 个审计声明通过；包括绑定、直接证明和条件组合，不是 14 个大型研究义务完成。
所有审计声明仅含白名单三公理，没有新增 axiom 或 sorryAx。
RetractionApproximationData 初版的参数类型推断错误已修正为明确 SweepParameter；失败日志保存，不计失败产物为证明。
冻结时检查此前十六轮源和产物哈希，新冻结记录包含三项返回源、五模块、任务卡及依赖快照，ops 留存独立副本。
未全量重建外部库；实际重编范围是三个返回目标与本轮新模块，固定传递依赖复用。
frontier.dag.json 是人工审核的依赖摘要，真正的充分性证据是已编译的精确 Lean 根定理。

## 仍然开放

没有证明每个目标都已拥有所需光滑嵌入和邻域回缩，未把已给管状邻域后的回缩定理当成管状邻域存在性。
没有构造保持端点的一阶光滑逼近序列；新原始逼近数据仍需几何提供，不是从仅 C0 接近推出 C1 或能量控制。
没有构造真实受控手术流、好扫掠、非平凡类或各物理切片的全部度量对应。
三角剖分与 PL 光滑化仍是大型研究输入，不能由局部叶子计数估算完成百分比。
旧 V1 未修改；公开结构检查结果以 public-freeze-check.json 为准。
没有 Git 集成、提交、推送或上游 PR，所有本轮成果均在 round17 隔离目录。
