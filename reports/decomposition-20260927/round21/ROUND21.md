# 第二十一轮：验收两项交卷，冻结实际法向坐标构造，四路独立 Luna

## 已验收并接入的实际证明

对 `d27r20-normal-linear-equiv` 和 `d27r20-normal-endpoint-jet` 的交卷重新读取、核对捕获哈希和声明边界。
在 round21 的独立输出目录重新编译两份源码，再 import 精确产物审计目标传递公理，均只有 propext、Classical.choice、Quot.sound。
语义复核：线性同构由实际切向映射的像与其正交补构造；导数由函数复合与连续线性映射求值得出，零纤维交叉项确实消失。
`public_after_twenty_nine` 已实际使用两项证明，不再将它们列作待证明参数。
本轮新增已验收工人叶子 2 项，累计 29 项。此统计限于当日冻结拆分流水线，不是庞加莱完成百分比。

## 新分解不再假设法向坐标已经存在

`EmbeddedNormalTotal e` 固定为原嵌入微分的正交补构成的实际子空间，使用诱导的乘积拓扑。
`EmbeddedNormalFrameAt` 只要求普通底空间图与局部法向正交标架，不含总空间参数图或端点映射局部逆。
`normalFrameForward`、`normalFrameBackward` 固定为同一标架的有限和，没有用任意存在的同构替换。
四个独立叶子分别是：嵌入到法向标架存在性；有限和纤维传输性质；实际总空间参数化；指定参数公式的光滑性。
`embedded_normal_coordinates_of_leaves` 已编译，真正从这四项构造任意给定嵌入的 `NormalCoordinateTube`。
`embedded_retraction_of_frame_leaves` 再接入已验收线性与导数证明以及尚在运行的局部逆任务，返回同一嵌入的局部回缩。

`EmbeddingApproximationData` 删除了此前的 normalTube 输入，只保留原嵌入、参考映射、一阶导数界和逼近序列。
`EmbeddingApproximationData.toNormal` 构造缺失的 normalTube，所有导数和能量比较仍沿同一个嵌入，不更换参考映射。
`public_of_embedded_frontier` 返回原 V1 TopologicalPoincareStatement；旧 normal/tubular/retraction 等入口均保留。
五个新模块共 12 个声明通过编译和公理检查，其中包括条件组合和复用，不计作 12 个研究缺口解决。

## 派工

项目 `poincare-refinement-round21-20260927`，全部精确模型 gpt-6-luna。
embedded-normal-frames：max；normal-frame-transport：xhigh；normal-bundle-parametrization：max；normal-parametrization-regularity：high。
四项任务没有待证明依赖，各自写不同文件；父证明先验收，随后冻结声明、哈希、输入和依赖图，再派发。
旧 d27r20-tubular-chart-inverse 的 max 工人保留，不中断、不重启、不重复派发。
当前实际队列及进程状态以 final-status.json 为准；任务进行中不是已验收结果。

## 依赖复用与冻结保护

嵌入到局部法向标架任务直接获得上一轮已重编译和审计的 LeeRiemannian 正交标架与法丛基础。
新增 LeeLib 输入命名空间单独放在 lee-inputs，不修改原 PoincareConjecture 编译基线标记，也不覆盖旧对象。
所有新增名称与原有效路径的同名模块经过冲突检查；补充输入的逐文件哈希记录在 lee-inputs/manifest.json。
原先发现的“对象目录已绑定另一基线”保护正常生效，配置已恢复原基线，随后采用独立补充目录；没有修改保护逻辑。
当前任务的预检和编译仍使用固定 Lean 4.32.1 和原编译选项，无依赖升级、缓存清空或全量重建。

父定理与两份验收源码的哈希已冻结，可信副本另存 ops 目录；旧 round1–17、19、20 冻结来源与产物逐项核对。
V1 的 13 个文件保持不变，smoothing 和 geometric_trace 仍未绑定完整无条件实现。
三角剖分、PL 光滑化、真实受控手术流、好扫掠和相对一阶光滑逼近仍有研究义务。
本轮证明的是新四叶子足以构造所需法向坐标，再与其余研究输入一起推出 V1 目标；不是所有输入已存在。
没有更改蓝图完成标记、Git HEAD、远程仓库或上游 PR；已验收结果仍在隔离报告目录，尚未提交主线。
