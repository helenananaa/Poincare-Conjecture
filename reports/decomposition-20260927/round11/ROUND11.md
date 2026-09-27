# 第十一轮：有限消解的解析前沿与同一事件历史的组合

## 当前验收边界

本轮最初的共享队列读取成功：round10 的 local-patch-density 和 open-patch-assembly 两项均 VERIFIED，旧工人已结束。
随后读取两个 attempt 验收元数据的命令被安全检查拦截。未更换入口重试该读取、未重复启动它们、未独立验收或计入已接受叶子。
累计已独立验收的本次分解路线局部叶子仍为 13 项。两个旧结果保持 VERIFIED_UNREVIEWED_THIS_TURN。

## 先查现有实现，避免重复派工

旧 2026-09-26 研究记录提出过 C3 初值无法直接消费 C-infinity 差商定理的失配。
本轮实际源码检查发现 `SmoothNormalizedSixMetricCoordinates`、`SmoothManifoldChartClassicalInitialSolution` 及若干平移/差商后续模块已存在。
已完整阅读 `exists_manifold_chart_smooth_initial_solution`：它的声明保留实际紧支撑 C-infinity 初值和局部 C2 解。
因此没有按过时研究记录再派相同光滑初值任务。本轮没有重编这些现有 PDE 文件，不据此增加验收计数。
局部初值光滑仍不等于全局解光滑或多个坐标解可以直接粘接。

## 新的、已编译的父组合

新增 `ExtinctionBarrier.lean` 和 `WidthExtinctionRoot.lean`，七个审计声明编译及传递公理检查 PASS。
公理均仅为 propext、Classical.choice、Quot.sound。它们包含直接组合与条件定理，不是七个大型研究义务完成。

使用实际 ForwardDiffQuotientLE 定义（右侧差商上极限），没有假设未知宽度可微。
令 Phi(t,w)=w/(t+c)^(3/4)+4*a*(t+c)^(1/4)，其中 a,c>0。
独立子任务一证明连续区间内的上 Dini 不等式 w' <= -a+3*w/(4*(t+c)) 使 Phi 不增。
独立子任务二证明：固定 a,c,w0 后，存在 T>0 使 4*a*(T+c)^(1/4)>Phi(0,w0)。

父证明已完成以下实际连接：
- 对同一事件集，幅度在事件时只允许向下跳变，区间端点与同一 pre/post 函数匹配。
- 复用已有有限事件排序/拼接定理，把逐区间 Phi 不等式与跳跃不等式合成全段界。
- 终点幅度非负与足够晚的 T 矛盾，得到 `extinctionProfile_impossible`。
- `patch_budget_events_finite` 只使用体积预算，在不知道终态为空时先证明事件有限，避免用消解证明有限性又反过来证明消解。
- `empty_end_of_width_comparison` 对同一个 LocatedProjection H 推出 H.pre H.horizon=[]，不把它作为输入。
- `geometric_of_width_control` 选择一个由初值幅度确定的时间，再把该 H 的空终态和同一预算代入已有 trace 重建。
- `public_of_width_frontier` 返回完全相同的 V1 TopologicalPoincareStatement。

## 不把几何构造藏进解析定理

`ExtinctionProfile` 是待由几何实现的解析证书，不是已经形式化的 min-max width。
`WidthControlledGeometryProducerStatement` 仍是大型 RESEARCH 输入，需构造真实受控手术流、宽度对象及其估计。
尤其：初始幅度上界必须在请求时间前固定；手术前后要有可追踪的宽度/分量对应；连续时间段的上 Dini 不等式、跳跃不增和终点非负都必须来自真实构造。
这些不是由给函数取一个 width 名称自动成立。本轮没有证明最小曲面存在、扫掠收紧、Gauss–Bonnet 到宽度导数的推导或跨手术宽度单调性。
三角剖分、光滑图册、全局 PDE 和手术控制仍未完成。最终根仍是条件组合。

## 文献核对

Colding–Minicozzi, arXiv:0707.0108v1, Theorem 1.7, equations (1.8)–(1.10), PDF page 4。
本轮通过公开网页的 PDF 解析及该页截图核对了右差商上极限不等式、3/4 积分因子及其有限时间矛盾。
原文常数为 a=4*pi；本轮解析任务推广为任意 a>0，几何常数的来源仍需真正证明。
原文对手术情形的扩展不能直接充当本项目 LocatedProjection/真实 metric history 的 Lean 对应证明。
文献只用来审查路线，不作为 Lean 公理；检索失败的 arXiv HTML 没有被当成证据。

## 派工与冻结

新项目 `poincare-refinement-round11-20260927`，有限批次，没有无限 watch、自动集成或推送。
`d27r11-width-dini-comparison`：gpt-6-luna / xhigh。
`d27r11-width-finite-horizon`：gpt-6-luna / high。
两项均有精确声明、编译通过的父消费者，且互不依赖。最终观察状态写入 final-status.json，不预先计为完成。

证据：ExtinctionBarrier-check.json、WidthExtinctionRoot-check.json、frontier.lock.json、cards.json、dispatch.json。
派工前复核此前十轮冻结源码和对象哈希，通过；旧源未改写。新模块已只读，并在 ops 保存独立锁副本。
初次 ExtinctionBarrier 证明中的加法不等式命名问题已修正并保留失败日志；只计最终成功源码。
本轮没有全量重建、Git 提交、远程推送或上游 PR。公开冻结及进程的最终状态以最后工具观察为准。
