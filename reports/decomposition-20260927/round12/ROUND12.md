# 第十二轮：四项实收、inf-sup 扫掠比较与新前沿

## 本轮实际验收

round10、round11 的四项工人任务均 VERIFIED。本轮成功读取并完整审查所有证明源码。
冻结目标的 proof-marker 外前后缀不变，源码哈希与捕获/验收哈希一致，随后独立从源码重新编译到 round12 私有产物，并导入精确目标审计传递公理。

| 任务 | 源码审查重点 | 结果 |
|---|---|---|
| d27r10-local-patch-density | 同一映射的微分链式法则、Gram 共轭、行列式和密度平方根；不要求全局满射 | ACCEPTED_ISOLATED |
| d27r10-open-patch-assembly | 可数源/目标图册分割、开放嵌入的像可测性、变量代换和不交求和 | ACCEPTED_ISOLATED |
| d27r11-width-dini-comparison | 真实右差商比较、初值匹配的显式屏障；不假设宽度可微 | ACCEPTED_ISOLATED |
| d27r11-width-finite-horizon | 常数先固定，再显式构造 q 和 T=q^4-c | ACCEPTED_ISOLATED |

`AcceptedSeventeen.lean` 已代入四项到精确父证明，累计 17 个局部叶子隔离验收。不是 Git 集成，队列仍可显示 VERIFIED。
证据：`four-source-recheck.json`、四组 compile/audit 日志、`semantic-review.json`、`AcceptedSeventeen-check.json`。
本轮未重新编译之前全部 13 项及整个外部库，复用了固定依赖缓存和此前已验收产物。

## 新的必要连接

文献：Colding–Minicozzi arXiv:0707.0108v1，§1.5、公式 (1.25)–(1.28)。实际读取 PDF 提取文本；两次截图均 Internal Error，不声称读到图示。
原文的比较不要求最优扫掠存在：先从好扫掠序列得到统一小时间估计，对固定 h 取序列极限，再取右差商极限。
对近最大切片使用几何导数估计，对其余切片使用到最大值的统一间隙和粗导数上界；Taylor 余项必须对序列及切片统一。

`SweepoutSpectrum` 给定非空索引族、非负切片能量及每个扫掠的有限上界。width 实际定义为所有切片上确界的下确界。
本轮直接证明能量到 peak 的上界、peak/width 非负、width 到 peak 的上界。
`SweepoutTransfer` 要给出每个旧扫掠到新扫掠的映射及逐切片能量控制；`width_le` 据此证明跳变不增，而不是把 width 不增当字段。
这一层是抽象能量谱，还没有与真实流形上的 Dirichlet 能量/面积及固定同伦类建立对应。
`GoodSweepoutAt` 明确保存近极小序列收敛、各切片实际导数、统一 Taylor 界，以及几何上需要证明的近最大导数控制。
`width_dini_of_good_sweepouts` 已编译证明两个新叶子足以产生上轮要求的 Dini 估计。
`MinimaxSurvivalProfile.toExtinction` 将同一事件集上的谱、转移和区间证书转换为已检查的 ExtinctionProfile。
`public_of_sweepout_frontier` 返回原始 V1 TopologicalPoincareStatement，旧冻结源及第九轮位置修正均保留。

## 新固定任务

两个精确声明相互独立，统一 `gpt-6-luna` / `xhigh`，固定资源槽和共享调度器。
- `d27r12-uniform-near-max`：近最大/低能量切片二分，给所有 j 和切片统一的小时间 h0；建议 h0=min(H,delta/(L+Q+1))。
- `d27r12-minimax-dini-limit`：对固定 h 先取 j 极限，再控制 eta+K*h 并得到真实右差商上界。
两项均有源码编译通过的父消费者；任务模板中的 sorry 仅为待填证明，不导入已验收父模块。
派工和最终运行状态分别见 `dispatch.json`、`final-status.json`；不预先把入队算作 RUNNING 或 VERIFIED。

## 尚未解决的几何核心

没有构造真实好扫掠、能量与面积宽度等价、极小球面/谐和映射及其紧性，也没有证明穿过手术的扫掠转移保持指定同伦意义。
这些是数学研究任务；抽象谱和 GoodSweepoutAt 的字段不是这些存在性定理的证明。
全局受控手术流、与实际度量和切割数据的完整对应、三角剖分及光滑图册仍未完成。
特别不能把对抽象 inf-sup 的两个实分析引理称为“几何宽度定理已证明”。

## 验收与保存

四个新模块 15 个审计声明全部编译通过，传递公理只含 propext、Classical.choice、Quot.sound。
其中含直接证明、绑定和条件组合；15 不等于完成了 15 个根研究缺口。
旧 11 轮冻结源码/产物哈希均复核通过；新锁包含源码、编译产物、四项验收来源及独立 ops 副本。
原 V1 13 文件本轮结构检查通过；结构检查本身不是全量依赖验收。
全部新增代码留在 round12 隔离目录。无全量重建、Git 集成、提交、推送或上游 PR。
