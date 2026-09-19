# 数学任务图的 Map–Reduce 拓宽

本轮扩宽数学依赖图，不是只增加并发参数。所有正式证明尝试使用 Grok；不把源码巡检、报告生成或编译任务算作数学证明。

## 任务图

**20 个不同的数学目标，12 个初始独立节点，五条主线。** 中间结果和汇总定理只在所需前置证明独立核验并集成后运行；跨项目输入另外核对 Git 祖先关系。

| 主线 | 可独立做的 map | 接回主线的 reduce |
|---|---|---|
| 有限灭绝的标量分析 | 积分因子候选的导数、精确积分恒等式、初值敏感性、幂函数比较解的导数/最终负性、有限次跳跃比较 | 解的存在唯一性；允许有限次向下跳跃的非负量的有限时限障碍 |
| 手术映射的距离控制 | 有限链三角不等式、相容局部映射的拼接、近最短长度误差消除 | 在明确短链逼近条件下推出全局 Lipschitz 估计 |
| 度量/曲率控制的张量基础 | 有限正交坐标中的二次型与 Frobenius 范数估计 | 小系数误差给出双边度量界及严格二次型正性 |
| 拓扑收尾 | 实际 S² 与圆的已有基本群定理适配 | π₁(S²×S¹)≅Z；单连通空间不能同胚于该乘积 |
| 典型邻域/演化 neck | 时间族统一 epsilon-close 常数的重索引 | 缩短实际演化 neck 深度，并保持中心 neck；深度至少 1 导出 strong neck |

这些主线不依赖本轮 collar 构造。标量时限定理跨越两个独立分支：比较函数的导数/最终负性，与有限次向下跳跃的比较原理。它的 Reduce 是可编译 Lean 定理，不是自然语言汇总。

## 执行与验收

- 正式模型服务调用：22 次，均为 Grok；完成并独立重验的不同目标：20。
- 实测本批模型服务区间峰值：10；数学任务图有 12 个初始独立节点。服务区间包含工具调用/服务端等待，不等于 GPU 推理并发。
- 模型失败或超时后保留原记录的尝试：2 次；局部修复使用原交卷和错误，不让模型重新做无关检索。
- 非负 Lipschitz 常数的 Lean 记法在执行前发现作用域问题，改为显式 NNReal，旧任务版本保留且没有启动模型；依赖重接也使用新任务编号，不修改已注册目标。
- 20 项目标均重新放回可信陈述，独立编译并检查传递公理。允许集合为 propext、Classical.choice、Quot.sound。没有在生产证明中使用占位证明。

## 结果与依赖

| 目标 | 角色 | 依赖数 | 提交 |
|---|---|---:|---|
| `ode-explicit-derivative-repair` | map | 0 | `6b1ae7b` |
| `ode-initial-sensitivity` | map | 0 | `bf367eb` |
| `ode-integrating-identity` | map | 0 | `c7048ab` |
| `ode-interface-v2` | reduce | 3 | `bdc7d6a` |
| `power-barrier-derivative` | map | 0 | `d39c45e` |
| `power-barrier-negative-repair` | map | 0 | `2c82806` |
| `tensor-contraction` | map | 0 | `25e1e1d` |
| `metric-quadratic-comparison` | map | 1 | `0c82244` |
| `metric-positive-definite` | reduce | 1 | `d619bcd` |
| `metric-chain-triangle` | map | 0 | `c91f362` |
| `metric-glued-map` | map | 0 | `de742ef` |
| `metric-epsilon-removal` | map | 0 | `21a4db8` |
| `metric-length-gluing-v2` | reduce | 3 | `b7e51aa` |
| `dini-finite-jumps` | map | 0 | `2db7106` |
| `epsilon-family-reindex` | map | 0 | `432cc67` |
| `evolving-depth-restriction` | map | 1 | `d9af121` |
| `strong-neck-reduce` | reduce | 1 | `20c8a1f` |
| `sphere-circle-group` | map | 0 | `b452593` |
| `sphere-circle-obstruction` | reduce | 1 | `5fcfdbf` |
| `scalar-extinction-reduce` | cross-branch-reduce | 3 | `1b94d79` |

## 数学范围，不把条件结论当成整项猜想

标量 ODE 和有限时限障碍已经证明，但实际 Ricci 流中的几何宽度、曲率下界、跳跃方向以及在有限时间内只有有限次相关手术等输入仍要另外建立。普通系数公式针对连续 q；有限跳跃比较使用来源中明确的 C¹ 系数合同。

距离拼接定理显式要求由片内成本构成的有限链逼近环境距离；尚未证明任意球面切割都满足该几何条件。张量估计在有限正交坐标中成立；还没有把其 Frobenius 范数与实际 EpsilonClose 的全部几何定义直接等同。

拓扑结果只覆盖 S²×S¹ 这一乘积球面丛，不覆盖扭曲球面丛或整个连通和分类。强 neck 结果从已有 EvolvingEpsilonNeck 数据中限制出子区间，不证明真实 Ricci 流一定具有这些 neck。

这些是正式形式化的主线组成部分；未据此宣称完整庞加莱形式化，也未增加对应主 blueprint 的完成标记。

## 下一批可继续拓宽的接口

把当前有限维张量界接到 EpsilonClose 的实际正交标架收缩；把标量比较接到几何宽度演化；建立从具体切割几何到短链逼近的输入；处理扭曲球面丛的基本群；从实际演化与紧性数据产生 neck。这些需继续做精确陈述和依赖审查，而不是先标成已就绪。

## 复核

```bash
python3 tools/lean_swarm/build_math_references.py \
  --repo /path/to/fork --config /path/to/swarm.main.local.json \
  --output /path/to/private-reference-build
python3 tools/lean_swarm/verify_cards.py \
  --config /path/to/private-reference-build/swarm.references.local.json \
  --cards tools/lean_swarm/examples/mathematical-mapreduce.json \
          tools/lean_swarm/examples/reference-mapreduce.json
```

参考构建按各包原有编译选项区分处理：Hatcher 用其默认选项，MorganTian/DoCarmo 使用其原有设置。只编译实际依赖闭包，固定缓存复用与源码哈希列于 reference-build.json。独立重验不调用模型。

原始会话、认证状态和本机数据库不公开。只向自己的 fork 发布，不向上游提交 PR。本轮所有归属本批的模型会话已经结束。
