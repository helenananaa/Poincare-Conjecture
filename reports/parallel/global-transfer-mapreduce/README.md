# 任意面积、真实黎曼距离与非平凡 C1 映射的并行汇总

本轮将既有点态面积、速度、宽度和同伦接口继续接向实际几何对象。只统计本批两个注册项目，不重复统计同时进行的其他批次。

## 完成规模

**21 个不同的正式目标，10 个初始独立节点，4 条数学线。** 实际 Grok 服务调用 24 次、服务区间峰值 10；Luna 调用为零。服务并发包括模型工具使用和提供方等待，不是 GPU 推理占用率。没有把源码检查、定义预检、协调器实例测试算成数学证明。

## 数学结果

**面积线。** 在代数双线性形式上，先独立证明三角换基的 Gram 面积公式、退化向量对的零面积、二维正交化。汇总得到二次型双边界对任意向量对的面积控制，不再要求原始 v,w 正交归一，也不排除微分秩不足二的点。再从实际 MorganTianLib.EpsilonClose 得到切向量对的面积界，代入实际 mfderiv 的两个坐标列，证明参数化面积密度及其非负扩展积分比较。最后从参考密度可积和新密度可测推导新密度可积，再传给非空固定曲面族的面积下确界，不假设存在最小曲面。

**长度/距离线。** 显式选择给定 g 的 RiemannianBundle，将原始 Manifold.pathELength 读回真实速度积分，将 Manifold.riemannianEDist 读回同一 C1 端点连接曲线族的下确界。然后得到 sqrt(1−ε) 与 sqrt(1+ε) 两侧常数的长度和距离比较。没有把背景坐标范数当作 g，也没有把某个外加的 metric-space 距离相容性假设替代要证明的结论。允许无有限长度连接曲线、扩展距离为无穷的情形。

**时间/宽度线。** 将先前全实数时间的连续性限制改成只要求闭时间区间内的控制，证明端点在内的相对连续性。另证明逐参数统一 Lipschitz 控制能传给真正 infimum–supremum 值。不要求任一极值达到，也不要求参数类型紧致。

**同伦线。** 使用真实 ContinuousMap 的同伦和到常值映射的定义，而不是抽象的“保持非平凡”标签。给定 p 的左同伦逆，证明 p 保留/反映非空同伦类；仅与 p 同伦的 q 也保留它们。建立实际非零同伦映射子类型上的 least-cost 传递，再进一步用 ContMDiff.comp 保留 C1 正则性，形成 C1 非零同伦映射族的传递定理。这里仍需提供真正的比较映射/左同伦逆和成本估计；没有假装从任意手术自动产生它们。

## 一个被拦截并修正的语义错误

协调器最初写的两个 metricPathLength / metricEDist 包装虽然安装了 RiemannianBundle 数据，却漏了激活其 scoped Bundle 范数实例。检查展开后的 Lean 定义发现，g 参数被忽略，实际使用了背景 E 范数。这不是普通证明语法错误：在那个定义上完成估计也不能算几何目标完成。

因此停止了两个受影响的工作任务，保留原始定义、冻结交卷和失败记录；修正为明确的 Bundle 实例选择，用独立的新对象缓存和新任务编号重做四个长度/距离目标。没有改写历史，也没有静默替换运行中任务的依赖缓存。其余不依赖错误长度定义的分支继续运行。最终所有21个目标再对修正后的 Core 源码重建、重编译和公理审计。新增检查确认两个不同的度量不能再仅靠 rfl 被判成同一长度/距离，并验证真实欧氏例子。

另外一次 minmax Lipschitz 任务的原交卷有两个局部不等式问题；保留原失败，向 Grok 提供原代码及编译目标局部修复。以上失败/重做不计为新的不同数学目标。

## 精确任务图

| 目标 | 数学线 | 角色 | 前置 | 提交 |
|---|---|---|---|---|
| `gram-shear` | 任意微分二平面与实际参数化面积 | map | 独立 | `2b71784` |
| `gram-degenerate` | 任意微分二平面与实际参数化面积 | map | 独立 | `3b54d12` |
| `gram-frame` | 任意微分二平面与实际参数化面积 | map | 独立 | `bb0642c` |
| `gram-allpairs` | 任意微分二平面与实际参数化面积 | reduce | `gram-shear`, `gram-degenerate`, `gram-frame` | `7865970` |
| `epsilon-allpairs` | 任意微分二平面与实际参数化面积 | reduce | `gram-allpairs` | `73ee796` |
| `epsilon-surface-area` | 任意微分二平面与实际参数化面积 | reduce | `epsilon-allpairs` | `9e90199` |
| `epsilon-least-surface` | 任意微分二平面与实际参数化面积 | reduce | `epsilon-area-integrable` | `15a9caf` |
| `local-time-infimum` | 有限时间区间及定量 minmax | map | 独立 | `8b3138d` |
| `local-time-minmax` | 有限时间区间及定量 minmax | reduce | `local-time-infimum` | `29d18ca` |
| `nonnull-invariant` | 实际同伦类与 C1 可容许族 | map | 独立 | `61c789a` |
| `homotopy-left-inverse` | 实际同伦类与 C1 可容许族 | map | 独立 | `3bbb6ab` |
| `homotopy-width-transport` | 实际同伦类与 C1 可容许族 | reduce | `homotopy-left-inverse` | `60c5d2e` |
| `homotopic-transport` | 实际同伦类与 C1 可容许族 | reduce | `nonnull-invariant`, `homotopy-left-inverse` | `e196251` |
| `integral-domination` | 任意微分二平面与实际参数化面积 | map | 独立 | `144d518` |
| `epsilon-area-integrable` | 任意微分二平面与实际参数化面积 | reduce | `epsilon-surface-area`, `integral-domination` | `a981f08` |
| `length-readback-v2` | 原始黎曼长度与扩展距离 | map | 独立 | `b4ea7f2` |
| `distance-readback-v2` | 原始黎曼长度与扩展距离 | map | 独立 | `21f89c5` |
| `epsilon-length-v2` | 原始黎曼长度与扩展距离 | reduce | `length-readback-v2` | `b3b9782` |
| `epsilon-distance-v2` | 原始黎曼长度与扩展距离 | reduce | `distance-readback-v2`, `epsilon-length-v2` | `337424a` |
| `uniform-minmax-lipschitz-repair` | 有限时间区间及定量 minmax | map | 独立 | `e6532d5` |
| `c1-nonnull-width` | 实际同伦类与 C1 可容许族 | cross-branch-reduce | `homotopy-left-inverse` | `b88c226` |

## 验收与具体实例

21 个目标分别放回固定陈述，独立重编译并检查传递公理仅在 {propext, Classical.choice, Quot.sound} 内。主包构建通过，调度器 37 项单元测试通过。ReferenceBridges 不属于默认 Lake 主包 glob，因此另外明确编译，不能用一次默认构建冒充其通过。固定 Mathlib 与参考库缓存复用，不声称重建全部外部依赖或完成第三方数学审阅。

具体检验包括标准正交平面的面积1、向量(2,0),(1,3)的面积6、共线向量的面积0、常值映射不属于非平凡同伦子类型、真实欧氏度量自距0，以及欧氏平面恒等参数化的实际 mfderiv 面积密度1。旧/新度量包装定义的语义检查另列。

GramFrame 的既有对称性参数在初次证明中未被显式使用。协调器只重写正交性那一步，通过对称性反转两次并利用已证明的正交关系，保持原始命题与主要构造不变。原始和维护后哈希在 proof-maintenance.json；不计作额外模型任务，没有关闭 linter。独立参考桥有冗余 section-variable 的编译警告，这不影响内核通过；未宣称所有参考桥零警告。

## 仍未完成的几何工作

paramAreaDensity 是实际 mfderiv 坐标列的 Gram 面积，不是完整的闭曲面图册拼接/几何面积形式定理。其对非光滑映射也遵循 mfderiv 的默认定义，几何用途应是 C1/光滑参数化。曲面族非空性、参考密度可积性与目标密度可测性仍需实际应用提供；目标密度可积性在此已推出。

同伦逆和成本界尚未从真实 Ricci 手术结构中产生；局部区间宽度估计也没有代替几何宽度演化或极小曲面存在。没有据此宣称完整庞加莱形式化、手术存在、全部有限灭绝，也未修改主 blueprint 完成标记。

## 复核

先用 build_math_references.py 建立所需固定参考库缓存，再提供本机配置：
```bash
python3 tools/lean_swarm/check_global_transfer.py \
  --repo /path/to/your/fork \
  --config /path/to/swarm.references.local.json \
  --output /path/to/private-global-transfer-check
```

这个入口先从现有已审核源码重建包装定义和实际本地引用，再独立验证 canonical-tasks.json 中21项目标及显式实例。它不调用模型，也不读取会员认证。原始会员会话、本机数据库和登录信息未公开。

所有属于本批的模型服务已结束。旧版被替换的两项未运行下游及失败记录仍保留于私有任务账本，canonical-tasks.json 才是本次21项完成目标清单。只向个人 fork 推送，不向上游创建 PR。
