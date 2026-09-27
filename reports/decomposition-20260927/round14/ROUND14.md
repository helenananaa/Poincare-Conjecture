# 第十四轮：四项实收、实际球面 Dirichlet 能量与固定相对同伦类

## 已验收的四项

round12 和 round13 的四项任务均返回 VERIFIED；本轮完整读取其证明源码，核对冻结 proof-marker 外声明、捕获/交卷哈希，独立从源码重编并导入精确目标检查传递公理。
- 统一近最大切片 Taylor 比较：54 行源码，统一时间半径及高低能量二分。
- minimax Dini 极限：80 行源码，固定 h 先取序列极限，再取右差商极限。
- 紧空间二次型正下界：76 行源码，单位球面紧致最小值及齐次缩放。
- 紧空间时间一致变化：23 行源码，对实际闭条带应用一致连续性。
四项均 ACCEPTED_ISOLATED，未作 Git 集成；本拆分路线累计 21 项隔离验收。
证据：four-source-recheck.json、semantic-review.json、四组 compile/audit 日志。
AcceptedTwentyOne.lean 真正把四项代入原条件父组合，不把任务状态当作证明。

## 新构造不是自由能量函数

IntrinsicSphereEnergy.lean 定义固定的单位圆球黎曼测度 sphereEnergyMeasure，并证明其有限性。
sphereEnergyDensity 使用实际球面映射 f 的 mfderiv，将目标度量在 df(e_i) 上的二次型求和再乘 1/2。
e_i 在每个点是单位圆球度量的正交标架；没有假设这组逐点选择随基点光滑。
sphereEnergyDensity_local_frame 直接证明可在邻域改用固定中心的光滑局部标架计算同一密度，复用已有迹的正交基不变性。
非负性直接证明；密度可积性的条件父证明由新连续性叶子加球面紧致性给出，未利用非可积 Bochner 积分默认值冒充有限能量。

SphereEnergySpectrum.lean 用 SmoothBasedSweepout 记录真正的 R × S2 -> M 光滑映射及两端均固定到基点的等式。
BasedSphereClass.reference 和 nontrivial 使用实际 ContinuousMap.HomotopicRel，而不是一个命名为 valid 的谓词。
索引是该参考映射固定相对同伦类中的全部参数光滑代表元；不是随意挑选的数值能量序列。
intrinsicSpectrum 将上述能量积分转换成旧 SweepoutSpectrum。单个扫掠的切片能量连续、有界由条件父证明导出，不另设有界能量字段。

## 到根目标的组合

intrinsic_energy_relative 从全局实际度量张量比较，对固定映射的实际微分积分得到统一能量比较。
intrinsic_width_continuous 复用已检查的 inf-sup 正因子夹逼，不假定最优扫掠存在。
IntrinsicEnergyRoot.lean 把同一同伦类、同一目标度量族的谱送入原 minimax/消解/trace 链。
public_of_intrinsic_sphere_frontier 已编译为原始 V1 TopologicalPoincareStatement，具有两项新正则性参数及三项研究级输入。
四个新模块共 16 个审计声明通过；包括绑定、直接证明和条件组合，不等于完成 16 个开放研究义务。
所有被审计声明传递公理仅含 propext、Classical.choice、Quot.sound。

## 两项新固定任务

- d27r14-sphere-energy-continuity，gpt-6-luna / xhigh：对实际光滑 R × S2 映射证明所定义能量密度的联合连续性。复用本轮局部换基及 MorganTianLib.Ch01.OrthoFrame 的光滑局部标架，不允许假设逐点所选标架连续。
- d27r14-intrinsic-metric-comparison，gpt-6-luna / max：从紧流形上实际度量族在闭时间条带的光滑性，证明对所有点和切向量统一的相对比较；不能假设全局切丛标架或额外时间延拓。可复用已验收紧二次型/时间比较叶子，经过有限局部图册拼接。
两项互不依赖，均有已编译的父消费者；有限批次，无自动集成或推送。
实际预检、启动及末次观察分别以 cards.json、dispatch.json、final-status.json 为准；不把模板中的 sorry 计作已证明。

## 没有完成的内容

没有证明所需非平凡相对同伦类在每个相关存活分量中存在。
当前索引使用可全局光滑延拓的参数化代表元；与连续/Sobolev 扫掠宽度的等价、必要的光滑逼近及 bubble compactness 均未完成。
没有证明正宽度、极小球面/谐和映射存在、好扫掠生产、近最大能量导数估计或跨手术转移的几何构造。
Profile 中的实际目标空间和度量族仍须与受控手术流的分量、时刻及度量建立完整对应；此对应未因能量定义具体化自动完成。
三角剖分、PL 光滑化和真实受控手术/消解生产者仍是研究义务。

## 保存和验收边界

旧 V1、旧 13 轮冻结源码及锁没有改写。派工前核对旧来源和对象哈希，新锁保留四项交卷、四个新模块及独立 ops 副本。
固定外部依赖缓存复用；本轮未重新编译整个外部库，SmoothOrthoFrame/OrthoFrame 的源哈希已记录。
中间曾遇到球面别名实例、紧支撑 API 和类型推断错误；最终四模块均源码哈希匹配且编译成功，失败产物不计为证明。
本轮所有新成果保持在 round14 隔离目录；无全量重建、Git 集成、提交、推送或上游 PR。

末次观察：两项新任务均 RUNNING，实际进程明确使用 gpt-6-luna/max 与 gpt-6-luna/xhigh。原 V1 13 文件结构检查 PASS；最终新冻结源和产物哈希复核 PASS。新工人尚未交卷验收。
