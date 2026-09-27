# 第九轮：修正切割见证的位置丢失，按实际切割绑定体积模型

## 必须纠正的先前表述

旧 `closedCut_of_neck` 的返回类型只有 `RegularClosedCut M`，函数通过 `Classical.choice` 从 `Nonempty (RegularClosedCut M)` 取值。
构造这个非空命题的证明虽然使用了输入领圈，但返回类型没有保存领圈及其位置性质。不同非空证明在 Lean 中不可区分。
本轮定理 `old_cut_choice_independent_of_collar` 已用 `rfl` 编译证明：固定同一个 M 后，任意两组合法领圈输入的旧选择结果相等。
因此此前将旧对象称为“同一条实际颈的切割”过强。这是几何对应的规格缺口，不是 Lean 内核接受了错误命题。
旧条件根定理仍是正确的充分性蕴含，已验收的局部叶子也没有因此失效；但旧的任意切割结果不能直接充当实际流的指定切割。
证据：`CutChoiceAudit.lean`、`CutChoiceAudit-check.json`、`choice-audit-and-repair.json`。
旧冻结源码没有改写，新的几何适配路线明确替换有问题的见证使用。

## 已完成的修正

`LocatedClosedCut f p` 在类型中保存原始领圈，并要求：
- 左右闭子集分别等于指定正、负分量的闭包。
- 两侧边界映射都等于原始领圈的中央切片。
- 两侧半领圈的参数公式分别为原参数的 t/2 和 -t/2。
`locatedNeckCut` 同时构造这些性质。选择操作现在选的是满足全部位置条件的对象，不能再丢失这些条件。
`locatedCut_connectedSum` 复用已完成的封帽/连通和证明，无须重做局部拓扑。

`LocationRegression.lean` 检查实际输出的子集等式；还证明指定负侧闭包不同会强制所选切割不同。
这是一条条件回归定理，并非声称任意两条领圈都给不同区域。

## 逐切割关联，不再只匹配数量

`LocatedCutSite` 记录同一切割的来源、metric neck、指定点、左右输出和相对于 LocatedClosedCut 的封帽对应。
`LocatedMove` / `LocatedChain` 以完整 cut-site 列表为索引。`LocatedProjection.operations` 保留这个实际列表，不能从纯 Prop 中任意重选颈。
`MatchedNeckHistory.model_identity` 强制第 j 个体积损失模型与第 j 个切割使用完全相同的 region、metric、center、epsilon、EpsilonNeckStructure 数据。
分量数、丢弃数、事件有效性由同一个操作列表推出；同一有限样本、同一事件集、同一初始度量继续传入既有 Ricci/体积预算。
`locatedProjection_trace` 从这些实际操作的逆向标准分解重建得到精确 `FiniteExtinctionTrace [M]`，不需要调用旧的任意切割对象。
`public_of_matched_frontier` / `public_after_thirteen` 已返回原始 V1 `TopologicalPoincareStatement`，未更换最终目标。

## ε-颈嵌入验收

本轮开始该任务仍 RUNNING，保持原进程未重启。随后交卷 VERIFIED。
完整读取 55 行证明、核对冻结声明前后缀和交卷哈希，并独立从源码重编、导入精确目标审计，PASS。
证明只针对明确的 `closedParameter` / `closedCollar` 映射；连续单射加紧致源到 Hausdorff 嵌入，不使用有问题的旧 cut choice。
`AcceptedThirteen.lean` 已将其代入 LocatedClosedCut 和修正版根组合；累计 13 个局部叶子 ACCEPTED_ISOLATED，未 Git 集成。
证据：`embedding-source-recheck.json`、`semantic-review.json`、`AcceptedThirteen-check.json`。

## 验收和冻结

六个新模块共 18 个审计声明通过。这包括缺陷确认、回归和条件组合，不是 18 个大型研究义务完成。
全部本轮审计目标的公理仅为 propext、Classical.choice、Quot.sound。
初次 AcceptedThirteen 的 universe 标注问题已修正并保存失败日志；只计最终源码哈希匹配且编译成功的结果。
`frontier.dag.json` 是人工审查的依赖摘要，真正的充分性由 Lean 根组合给出，不将 JSON 节点数量当进度。
旧八轮冻结源码与编译产物哈希复核 PASS；原 V1 13 文件结构检查 PASS。
新 `frontier.lock.json` 和独立 ops 副本保留来源、产物、验收源码及旧版本引用；旧声明和旧锁未改。

## 真实缺口与运行状态

三项大型研究输入仍未完成：任意流形的 PL 表示、有限光滑图册、真实手术/消解的匹配几何生产者。
本轮已同步颈数据和切割位置，但不宣称实际包含映射与保测度映射、真实帽模型和输出中的对应、所有时刻的度量张量兼容已经构造。
这些属于下一层需要具体研究的几何条件，不可当免费假设，也不把更强记录结构的存在算成已完成。
本轮新增工人数为零；现有 ε-颈嵌入任务已验收，当前就绪卡为空，没有为了并发而重复已完成任务。
所有新代码保存在 round9 隔离目录；无全量重建、Git 集成、提交、推送或上游 PR。最终运行状态以 final-status.json 为准。
