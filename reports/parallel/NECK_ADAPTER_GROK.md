# Grok 并行：有限 neck 与原始 epsilon-neck 到光滑 collar 的适配

起点：`bd6dc4e`。本批仅使用 Grok，模型级并发不设配额；主批最多 10 个工作任务，首批 6 项就绪任务并行。

## 已证明的连接

1. 对任意有限轴区间 (a,b) 内的切面 c，构造正宽度的子 neck；允许正、反两个轴向。通过显式光滑仿射变换，规范化为 X × (-1,1)，并精确保留中心切面。
2. 从实际切割集合的局部图像等式推出点态单侧关系，再产生给定原光滑结构上的双向光滑 collar。没有从 epsilon-接近圆柱的度量估计中凭空推出切割方向。
3. 在原有标准球面与一维欧氏轴上，构造实轴和原生轴、有限开放子空间及三维线性传输模型间的微分同胚。
4. 有限有向 neck 切割数据覆盖实际继续区域的 frontier 时，调用已有闭包构造，得到实际补分量闭包的光滑结构、包含映射的光滑嵌入、内在边界识别和正则开性。

## 与原始参考库的连接

在私有编译目录实际构建了 279 个参考库依赖模块，并导入 `MorganTianLib.Ch02.EpsilonNeck`。`ReferenceShapes.lean` 用定义等同性检查 Sphere2、原生圆柱模型与有限参数域确实对应原库类型。`MorganTianBridge.lean` 的输入是实际的 `MorganTianLib.EpsilonNeckStructure`，使用其 `phi` 字段，对真实开放 neck 区域 Q 到环境 N 的包含进行适配；不是把另造的结构命名为 epsilon-neck。

原库含 Riemannian 依赖；为避免主拓扑包循环依赖或引入无关构建负担，直接原库适配文件置于 `tests/NeckAdapter/` 并单独编译审计，不由主包入口导入。主包中的通用适配与闭包定理正常导出。

## 验证目标

| 任务 | 模型 | 秒数 | 集成提交 |
|---|---|---:|---|
| `affine-axis` | grok | 80.9 | `209680a` |
| `finite-cut-closure` | grok | 173.8 | `2ccf2f7` |
| `image-cut` | grok | 119.4 | `03eb9f2` |
| `interval-orientation` | grok | 201.7 | `47746ef` |
| `native-axis` | grok | 433.4 | `a5e020d` |
| `native-collar` | grok | 132.2 | `320b479` |
| `native-cut-closure` | grok | 409.0 | `5345212` |
| `native-domain` | grok | 310.7 | `7fd626a` |
| `native-finite-chart` | grok | 464.2 | `8ca4a5d` |
| `native-sphere-reverse-sanity` | grok | 389.9 | `299dea0` |
| `normalize-chart` | grok | 337.7 | `598b396` |
| `offcenter-reverse-sanity` | grok | 387.6 | `a9b1d39` |
| `open-domain` | grok | 526.5 | `21ae50c` |
| `oriented-collar` | grok | 76.9 | `acd0169` |
| `restrict-partial` | grok | 150.3 | `29bab98` |
| `reference-native-collar` | grok | 125.7 | `51ddbe7` |

本批 16 个目标均已验证并集成。额外的源码形状一致性检查为协调器提交的 rfl 证明，不计作 Grok 任务。单次模型运行时间不含排队、源库构建和集成，不能相加后声称是串行基准或整体加速倍数。

## 非空及方向性检验

回归覆盖：在有限区间 (-2,3) 的非中心切面 c=1、反方向 s=-1 上构造 collar；另在真正的标准球面截面及原生三维传输模型上，以 epsilon=1/2 和反向非中心切割检查完整适配。前向映射、中心点和侧向关系都在 Lean 中证明，而非仅检查类型可构造。

## 仍保留的数学义务

这一批不证明实际 Ricci 手术产生所有需要的 neck，不证明这些 neck 自动满足切割集合等式或覆盖全部相关 frontier，也不提供 Ricci 流延拓、有限灭绝或最终庞加莱定理。原库直接适配保留其任意原始环境模型 I；全局补闭包接口目前仍采用固定的二维向量空间 × Real 环境模型，将特定三维源工程模型与它连接仍需明示相容性。epsilon-接近性和曲率估计未被用来替代任何拓扑切割条件。主 blueprint 节点没有因此标完成。

## 信任边界

所有交卷只提取证明正文，放回固定定义与声明，独立编译并审计目标传递公理，允许集为 {propext, Classical.choice, Quot.sound}。前置提交均是后续任务基准的祖先。主包复用固定 Mathlib 缓存，参考源库单独构建；这不是整个外部依赖栈的独立第三方认证。

本批与同一工作区中的另一个基础接口/调度器改进批次并存，保留其已提交成果，但上表仅统计本批注册的任务，不把其他会话的工作或重复内容计入新增任务数量。

只推送个人 fork，不向上游提交 PR。

## 集成回归维护

全包严格回归发现另一个并行基础模块的正宽度参数未使用警告。保持冻结的调用陈述与原构造分支，仅显式排除 r=0 的不可能分支，再编译确认没有警告。原始与维护后的哈希单独记录；这不计作本批新增数学任务。

## 最终回归与复现

主包构建、22 组 sanity 测试、364 项既有公理依赖审计及原验证门全部通过。15 项本批主包目标与 1 项实际原库适配目标另外独立重编译、审计通过；源码形状一致性也再次检查。调度器当前 31 项单元测试通过。主包是增量构建，参考库的 279 个依赖首次在独立目录编译；没有宣称 Mathlib 全量从零重建。

原库适配可在提供本机固定环境配置后重现：
```bash
python3 tools/lean_swarm/check_neck_reference.py \
  --config /path/to/swarm.local.json --output /path/to/private-reference-build \
  --check-adapters
```

本机配置和原始模型会话留在仓库外；该命令不调用模型。
