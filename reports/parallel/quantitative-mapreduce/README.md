# 三条独立数学分支：ε-close 度量、长度空间拼接、曲率系数比较

本轮不是继续拆同一条 collar 链。19 个不同形式化目标分属三条互不依赖的数学分支，任务图有 12 个独立起点；其中两个起点用于实际自反性/非空模型验证。所有模型任务使用 Grok。

## 已完成的三个 Reduce

**原库 ε-close → 实际黎曼度量比较。** 从 MorganTianLib.EpsilonClose 的真实定义提取零阶范数，将原始 Fin(2) 多指标收缩严格重索引为正交标架矩阵误差，并在原始 g0 正交标架中证明 Parseval 与双线性展开。随后得到 (1−ε)g0(v,v) ≤ g(v,v) ≤ (1+ε)g0(v,v)，混合误差 |g(v,w)−g0(v,w)|² ≤ ε²g0(v,v)g0(w,w)，以及平方根常数的切向速度比较。没有假设矩阵误差就是原始范数，也没有把背景欧氏内积替换成 g0。

**实际长度空间 + 开覆盖 → 全局 Lipschitz 拼接。** 从 Shared.LengthSpace 的路径长度下确界定义真正提取近最短路径，再利用紧路径区间上的开覆盖细分和实际总变差界，产生上一批尚需作为假设的短片链。由此消去近似片链输入，推出统一局部 Lipschitz 常数的相容映射可全局拼接。实数直线的 LengthSpace 结构另行证明，并由此得到实轴上的统一局部 Lipschitz 性推出全局 Lipschitz 性。

**曲率系数下界 → 有限次向下跳跃的标量时限障碍。** 不再要求实际系数恰好等于 α/(t+c)。从 q(t) ≥ −α/(t+c) 和非负宽度，把原始前向差商不等式弱化为已证明的比较障碍，并调用有限跳跃比较。q 不额外要求光滑。

## 执行和校验

- 不同新目标：19；真实 Grok 会话：19；源码巡检不计数。
- 任务图独立起点：12；实际服务区间峰值：11。实轴模型是开工后补入的独立节点，不把图宽度冒充开工瞬间并发。
- 前置任务在通过独立验收并集成后才解锁汇总目标，Git 基准祖先关系已检查。
- 19 个新目标逐一重新编译并检查传递公理；另外重查了所用的 20 个上批目标，但不把它们计为本轮新增。
- 允许公理仅为 propext、Classical.choice、Quot.sound；固定环境复用外部依赖缓存，不是重建全部 Mathlib。

## 数学结果清单

| 目标 | 分支 | 角色 | 提交 |
|---|---|---|---|
| `epsilon-c0` | actual-epsilon-metric | map | `73d3f75` |
| `epsilon-matrix` | actual-epsilon-metric | map | `5efcf53` |
| `frame-parseval` | actual-epsilon-metric | map | `00f9be4` |
| `frame-expansion` | actual-epsilon-metric | map | `9f04219` |
| `epsilon-reflexive` | actual-epsilon-metric | nonvacuity | `2dfab48` |
| `bilinear-frobenius` | actual-epsilon-metric | map | `dbb1386` |
| `sqrt-metric` | actual-epsilon-metric | map | `c849e82` |
| `short-path` | length-space-gluing | map | `e151256` |
| `path-subdivision` | length-space-gluing | map | `f228583` |
| `variation-partition` | length-space-gluing | map | `0382152` |
| `coefficient-domination` | curvature-coefficient-extinction | map | `50e9085` |
| `epsilon-metric-reduce` | actual-epsilon-metric | reduce | `c0141b8` |
| `epsilon-mixed-reduce` | actual-epsilon-metric | reduce | `8798ba0` |
| `epsilon-speed-reduce` | actual-epsilon-metric | reduce | `7037f19` |
| `piece-chains-reduce` | length-space-gluing | reduce | `bd214ae` |
| `lipschitz-open-cover-reduce` | length-space-gluing | reduce | `63bed5c` |
| `curvature-extinction-reduce` | curvature-coefficient-extinction | reduce | `cdf8d14` |
| `real-line-lengthspace` | length-space-gluing | nonvacuity | `5f2f5f9` |
| `real-local-global` | length-space-gluing | reduce | `811261e` |

## 未完成的几何输入

度量比较目前是点态切向量结论；沿路径积分、实际距离及体积比较需要后续连接。长度空间定理要求开覆盖，不能宣称任意带边界手术片自动符合。标量障碍仍要求几何宽度的演化不等式、适当曲率下界和有限分段/跳跃条件由实际 Ricci 手术产生。没有据此宣称完整庞加莱形式化或增加主 blueprint 完成标记。

## 验收器修复

短路径证明中的英文注释包含 axiom 一词，旧策略扫描误将其当作新增公理。加入识别 Lean 行注释及嵌套块注释的扫描，保留代码和字符串；原固定交卷与哈希未修改，重编译及传递公理检查仍完整执行。新增回归测试确认真实占位证明仍被拒绝。此过程没有重新调用模型，也没有从失败代码中删除数学假设。另有实数长度空间任务在写出完整证明后触及 Grok CLI 轮数上限并以非零码退出；原冻结交卷独立核验通过，按明确记录的客户端失败审查理由重验并集成。该失败记录保留，不声称所有会话都以成功码退出。

## 旧模块回归维护

严格全包验证额外发现旧 PowerNegative 与另一并行分支 AdmissibleTransfer 的未使用假设警告。保持原定理陈述和构造分支，显式排除违背既有假设的不可能输入，独立重编译并审计通过。原始和维护后哈希在 lint-maintenance.json；不计作本批新增目标，也没有关闭 linter。旧零边数测试的冗余 simpa 已由同一工作区的维护提交 ac5a7f2 改为直接使用原引理；保留该修改，不覆盖。测试文件不在 39 个生产/回归目标中，逐一确认这 39 个源码哈希不变后，复用刚完成的独立核验记录，再完整运行主包回归。

## 复核入口

参考环境沿用 tools/lean_swarm/build_math_references.py 生成的固定库闭包，并重新编译上批 FiniteDini 与 FiniteExtinctionObstruction；精确本机配置保存在仓库外。
```bash
python3 tools/lean_swarm/verify_cards.py \
  --config /path/to/swarm.quantitative.local.json \
  --cards tools/lean_swarm/examples/mathematical-mapreduce.json \
          tools/lean_swarm/examples/reference-mapreduce.json \
          tools/lean_swarm/examples/quantitative-mapreduce.json \
          tools/lean_swarm/examples/quantitative-mapreduce-nonvacuity.json
```

ReferenceBridges/Quantitative 中原库适配使用明确的独立编译入口，不悄悄加入主包依赖图。原始会员会话、认证状态与私有数据库未发布。只推送自己的 fork，不向上游创建 PR。本轮所有归属本批的模型会话已结束。

## 最终回归

主包构建、24 组 sanity 测试、364 项既有公理依赖检查和原验证门通过；本批 19 个目标独立重验通过。调度器全部单元测试通过。
