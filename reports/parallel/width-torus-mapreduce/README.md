# 面积、变分宽度与映射环面：独立数学任务的 Map–Reduce

本批 19 个不同目标，10 个初始独立节点；全部由 Grok 尝试，实测服务区间峰值 10。不统计并行的其他批次，不把类型预检、巡检或协调器实例测试当成新增模型证明。

## 数学工作线

| 工作线 | 独立构件与最终汇总 |
|---|---|
| 变分下确界与 minmax | 不假设极值达到的近似、可容许族映射、上确界传递、统一扰动，汇总成 inf-sup 转移和统一指数控制下的连续性。 |
| 成本的时间变化 | 不除以可能为零的成本，从绝对导数界推出双边指数控制，再传到整个可容许族的下确界。 |
| 面积比较 | 二维二次型判别式、平面 Jacobian、实际积分比较，最后将矩阵误差接到最小面积比较。 |
| 拓扑收尾 | 实际映射环面的圆投影、绕圈路径、球面对径同胚，汇总成任意非空道路连通纤维映射环面的非单连通性及对径球面情形的同胚排除。 |

## 关键结论与条件

面积汇总：在每一点给定相对于正交参考二平面的真实二次型界 `(1-ε)|v|² ≤ g(v,v) ≤ (1+ε)|v|²` 且 `0≤ε<1` 时，得到 Jacobian 的 `[1-ε,1+ε]` 界；经所写出的积分和下确界，得到整个可容许族的最小面积界。实际曲面的存在、所有点的正交标架和几何 Jacobian 识别没有被暗中当作已证明。

宽度汇总：外层可容许对象的映射无需满射；内层参数映射必须覆盖目标参数，才能控制 supremum。下确界与 supremum 的有限性来自明示的非负性、非空性及有界性，不要求出现最优对象。统一指数控制的连续性版本当前以全部实数时间为域；局部时间区间的几何应用需进一步适配。

拓扑汇总：对任意非空道路连通 X 和自同胚 φ，实际 quotient MappingTorus.Space φ 1 上存在映向圆上一周绕圈的闭路，因此该空间不是单连通。它不要求 φ 恒等，故覆盖对径映射这一具体扭曲球面情形。没有宣称证明了所有 sphere diffeomorphisms 的分类，也没有宣称计算任意纤维的完整基本群。

## 目标与依赖

| 目标 | 角色 | 依赖 | 提交 |
|---|---|---|---|
| `infimum-approximation` | map | 无本批前置 | `3585666` |
| `admissible-transfer` | map | 无本批前置 | `71291df` |
| `peak-distortion` | map | 无本批前置 | `9dd6149` |
| `infimum-additive` | map | 无本批前置 | `57b4af5` |
| `cost-growth` | map | 无本批前置 | `3d133ad` |
| `integral-jacobian` | map | 无本批前置 | `82e5517` |
| `quadratic-discriminant` | map | 无本批前置 | `98abe15` |
| `plane-area-distortion` | reduce | quadratic-discriminant | `9998a75` |
| `minmax-transfer` | reduce | admissible-transfer, peak-distortion | `2585b8d` |
| `width-continuity` | reduce | admissible-transfer, infimum-approximation | `cb8f30c` |
| `least-area-reduce` | reduce | integral-jacobian, admissible-transfer | `6d1de56` |
| `width-growth-reduce` | reduce | cost-growth, admissible-transfer | `fe49551` |
| `torus-projection` | map | 无本批前置 | `c2e1ae6` |
| `torus-generator` | map | 无本批前置 | `8c91d83` |
| `sphere-antipodal` | map | 无本批前置 | `8d50960` |
| `torus-obstruction` | reduce | torus-projection, torus-generator | `ea43072` |
| `twisted-bundle-reduce` | reduce | sphere-antipodal, torus-obstruction | `9e95857` |
| `area-to-width-reduce` | cross-branch-reduce | plane-area-distortion, least-area-reduce | `09775b1` |
| `minmax-continuity-reduce` | cross-branch-reduce | peak-distortion, width-continuity | `948ed1a` |

## 验证

19 个最终源码被放回可信任务陈述独立编译，并逐个检查传递公理只包含 propext、Classical.choice、Quot.sound。主包构建通过，独立参考适配也显式重编译。标准缓存复用，不是全部外部依赖从零重建。

实例检查包含正半轴上的成本：下确界为零，但不存在达到零的对象；其单参数 minmax 版本也成立。另检查单点纤维的映射环面确实不是单连通，从而排除只在空域上通过的情况。

## 边界与复核

这些是庞加莱形式化所需的可复用组成部分，不是完整的几何宽度演化、手术存在、有限灭绝或最终庞加莱证明。所有未完成的实际几何输入仍明确保留，没有修改主 blueprint 完成标记。

参考拓扑文件位于 ReferenceBridges/WidthTorus，避免默认主包无意引入整套 Hatcher 依赖；使用固定本机 reference 配置可通过 tools/lean_swarm/verify_cards.py 和本批 JSON 卡片复核。不公开认证文件、本机配置或原始 agent 会话。

只向个人 fork 发布，不向上游提交 PR。本批自身模型任务结束，不设置持续后台派单。
