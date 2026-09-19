# 实际距离、退化面积、局部变分宽度与覆盖空间的 Map–Reduce

本批基准：`5b77ac1`。四条互不等待的数学线，23 个不同目标、12 个初始独立节点。全部使用 Grok，实际服务区间峰值 12；本批工作预算为 16，Grok 无模型级上限。模型服务区间包含工具交互与等待，不等于 GPU 推理并发。

## 本批完成的汇总

**实际 Riemannian 路径与内在距离。** 从原始 EpsilonClose 定义已有的切向速度比较出发，证明实际 metricPathIntegral、C1 路径下确界 metricIntrinsicEDist 的平方根常数双边界，得到球半径夹逼。任意固定可容许路径子类也可用；空类按 ENNReal 保持无穷而不产生实数 sInf 空集的零值。另用原库的真实等式验证这是相应范数下的 canonical riemannianEDist。若定义域是一个 neck，该结论是 neck 内在距离，而非允许路径离开 neck 的环境距离。

**无需正交归一或非退化的面积控制。** 独立证明 2×2 半正定形式的混合行列式非负和 Loewner 行列式单调性，再得到任意参考 Gram 矩阵的相对面积界，包括秩 0/1。由实际 EpsilonClose 推出任意切向量对的 Gram 面积界，再从参考面积的可积性及目标的可测性导出目标可积性和积分界，最后得到固定可容许族下确界的比较。没有假设最小面积达到，也没有把目标可积性当作输入。

**真正局部时间的宽度控制。** 成本导数只需在开时间段内存在，端点只用连续性；把比较传给参数上确界和对象下确界后，得到闭时间段上的 minmax 连续性。另独立证明已达最小值的 Dini 估计和不达最小值的近似竞争者版本；后者与局部连续性、显式跳跃处的对象映射、已有标量障碍合成变分下确界的有限时限。几何候选的短时估计与手术诱导映射仍须由几何证明产生。

**真正的映射环面覆盖。** 从原始 integer-deck quotient 出发，构造连续整数作用和两两分离的短条带，证明商投影 IsCoveringMap。另一独立任务把纤维显式枚举为整数 deck 轨道。二者合并后，对单连通截面给出单连通总空间的覆盖数据；标准 Sphere2 实例实际核验。没有把局部同胚误当作覆盖，也没有声称已得到完整 pi1 同构的群运算公式。

## 任务与依赖

| 目标 | 分支 | 前置数 | 集成提交 |
|---|---|---:|---|
| `extended-infimum` | 实际路径、内在距离和球 | 0 | `1d1cd1d` |
| `extended-balls` | 实际路径、内在距离和球 | 0 | `c5aff00` |
| `epsilon-path-integrals` | 实际路径、内在距离和球 | 0 | `f373592` |
| `epsilon-intrinsic-distance` | 实际路径、内在距离和球 | 2 | `f052a7f` |
| `epsilon-admissible-paths` | 实际路径、内在距离和球 | 2 | `6d18dca` |
| `epsilon-ball-reduce` | 实际路径、内在距离和球 | 2 | `854ec47` |
| `psd-mixed` | 退化 Gram 面积、积分和下确界 | 0 | `a1905ad` |
| `psd-det-monotone` | 退化 Gram 面积、积分和下确界 | 1 | `94b4798` |
| `relative-gram-area` | 退化 Gram 面积、积分和下确界 | 1 | `a81b7e7` |
| `dominated-integrability` | 退化 Gram 面积、积分和下确界 | 0 | `e6a0850` |
| `epsilon-arbitrary-pair` | 退化 Gram 面积、积分和下确界 | 1 | `dc56eda` |
| `epsilon-integrated-area` | 退化 Gram 面积、积分和下确界 | 2 | `aa5ba26` |
| `cost-open-derivative` | 局部时间宽度、近似极小者和时限 | 0 | `a1421c6` |
| `width-local-continuity` | 局部时间宽度、近似极小者和时限 | 0 | `a7984ab` |
| `peak-local-control` | 局部时间宽度、近似极小者和时限 | 0 | `c5e3bf2` |
| `dini-inf-minimizer` | 局部时间宽度、近似极小者和时限 | 0 | `c197e3d` |
| `dini-inf-approximate` | 局部时间宽度、近似极小者和时限 | 0 | `7bd3d72` |
| `minmax-local-reduce` | 局部时间宽度、近似极小者和时限 | 3 | `6d06b59` |
| `torus-covering` | 实际映射环面的覆盖空间 | 0 | `e7dfa4f` |
| `torus-fiber-integers` | 实际映射环面的覆盖空间 | 0 | `a45b537` |
| `torus-universal-reduce` | 实际映射环面的覆盖空间 | 2 | `3995c3c` |
| `epsilon-least-area-reduce` | 退化 Gram 面积、积分和下确界 | 1 | `bbf8d27` |
| `variational-extinction-reduce` | 局部时间宽度、近似极小者和时限 | 2 | `c0c87dd` |

各任务只填写冻结命题中的证明正文。所有 Reduce 都是实际调用前置证明的 Lean 结果，父提交须已验证集成并是所用 Git 基准的祖先。巡检、编译、协调器实例测试及其他并行会话都不计作这 23 项模型证明。

## 验证

23 个目标均重新组装到可信声明，独立重编译并逐项审计传递公理只包含 propext、Classical.choice、Quot.sound。主包构建、25 组既有和新增 sanity、364 项既有公理检查及验证门通过；调度器 37 项测试通过。参考依赖闭包为 355 个模块，复用固定版本缓存，不宣称重建全部 Mathlib。

具体实例覆盖：秩一但不为零的参考形式、无穷的空路径类、无最小值的正半轴成本、闭区间内的 minmax、无极小者的 Dini 估计、单点和标准球面截面的真实覆盖，以及 explicit/canonical Riemannian extended distance 的一致性。实例测试由协调器补充，未计入模型目标数量。

一个路径积分参考声明保留了未用到的自动包含 section 变量警告；冻结接口未改，未关闭 linter。私人预检查曾遇到命名空间缓存并发创建和 unitInterval 的 I 记法冲突，均在真实任务登记前修复。预检查的占位对象不在 worker 或独立验证环境。并行工作区短暂不干净导致若干已验证结果暂缓集成，之后使用原封交卷重新集成，没有重新算作新证明。

## 增量验证范围

历史默认验证基准会把报告目录中的 .lean 测试识别为全工程变更，从而重建全部参考包。这次保留了中止的历史宽范围运行日志，把测试原字节移动到 PoincareConjecture/tests/Transport/ReferenceChecks.lean，给原检查器增加可审计的 --base-ref 参数（默认值不变、必须为 HEAD 祖先），然后从本批已检查起始提交重新运行相同依赖选择门。主包测试、364 项旧公理检查和23项新目标核验未削减；并非声称全部历史参考工程重新构建完成。

## 剩余边界

此处面积是已指定切向量对的实际 Gram 密度。要称为完整几何曲面面积，仍需接入具体曲面参数化、积分测度、图册和可容许同伦类；最小曲面存在、真实宽度演化、手术跳跃的拓扑保持和有限手术次数并未被省略。覆盖空间数据也不是完整 sphere-bundle 分类。这些主节点不标完成。

## 复核入口

```bash
python3 tools/lean_swarm/prepare_transport_environment.py \
  --repo /path/to/fork --config /path/to/swarm.base.local.json \
  --output /path/to/private-build
python3 tools/lean_swarm/verify_cards.py \
  --config /path/to/private-build/swarm.transport.local.json \
  --cards tools/lean_swarm/examples/intrinsic-area-mapreduce.json \
          tools/lean_swarm/examples/intrinsic-area-reduce.json
```

配置、原始 agent 日志与认证状态留在本机；报告只发布数学和校验记录。本批归属的模型服务全部结束，不设持续后台派单；只推送个人 fork，不创建上游 PR。
