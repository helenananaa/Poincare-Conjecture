# 第十轮：从指定映射的度量拉回证明体积保持

## 本轮实际结果

新增四个模块共 13 个审计声明，源码编译与传递公理检查通过：
- MetricPatchTransport：2 个，局部密度与跨图册拼接组合成像集体积及限制测度保持。
- RecordedMetricPatch：2 个，将实际度量测度经指定拓扑实现传入记录切片。
- MetricPatchReplacement：5 个，包括实际颈区域可测、损失模型生成、颈身份保持、保留区域体积不增和替换分片生成。
- PatchGeometryBudget：4 个，将以上结果传入第九轮的位置修正版和精确 V1 根。
审计公理均仅 propext、Classical.choice、Quot.sound。
这些是直接证明及条件父组合，不是新完成 13 个开放叶子。此前已验收叶子仍为 13，本轮尚无新工人交卷验收。

## 可独立并行的两项数学任务

1. LocalPatchDensityStatement：对指定光滑映射，以点态度量拉回等式推出坐标 Jacobian/体积密度恒等式。保留两侧 chart source 条件；不要求全局可逆。
2. OpenPatchAssemblyStatement：从同一映射的局部密度证书和 IsOpenEmbedding，经过可数图册分割推出任意可测集合的像集体积等式。不要求映射满射，也不要求总体积有限。
两者之间没有待证明的任务依赖。第二项证明的是从给定局部证书出发的蕴含，第一项负责产生这个证书。
共同父 theorem metric_patch_preserves_restrict 已编译，输出的 MeasurePreserving 针对原先指定的 f，而不是重新选择映射。

## 实际来源复验

完整读取 MorganTianLib/Ch02/NeckVolume/PullbackMeasure.lean（452 行），并对原源码重编、导入精确目标审计，PASS。
它原先针对全局 Diffeomorph；不能把“到颈/帽的较大环境中的嵌入”错误当作满射。
局部 hlocal 块和后半部图册分割提供两个任务可复用的具体证明路线。
来源复验只重编该源，传递依赖使用固定缓存；不声称全量重建。
证据：pullback-source-check.json 及 compile/audit 日志。

## 比上一轮少了哪些假设

MetricPatchReplacement 不含 old_preserves / new_preserves 字段。输入为指定的光滑开放嵌入、点态拉回度量关系、规范记录测度及准确像集覆盖；toModel 由两个叶子构造这些保测度结论。
MetricReplacementPartition 不含数值 core_nonincrease；它由同一度量模型上的保留区域或完全删除分支生成。
完全删除分支允许空最终切片；capCount=0 时不要求构造不存在的新帽目标。存在帽时，度量模型应选取可嵌入的实际模型邻域，不能把整个无限体积欧氏空间默认为能等距嵌入紧切片。
旧的 LocatedClosedCut 位置证书与逐切割 NeckIdentity 保留，toModel_identity 和 toMatched 实际保证转换不更换颈数据。
public_of_metric_patch_frontier 已通过编译，返回原始 TopologicalPoincareStatement；有五个显式开放输入：两个新证明叶子和三项大型研究输入。

## 已发出的有限批次

项目：poincare-refinement-round10-20260927。
- d27r10-local-patch-density：gpt-6-luna / xhigh。
- d27r10-open-patch-assembly：gpt-6-luna / xhigh。
启动器原始进程 PID 36740 返回声明预检成功、REGISTERED、ENQUEUED 2、STARTING_FINITE_BATCH。
声明模板中的 sorry 仅用于预检；不计作交卷证明，也没有导入父模块作为无条件叶子。
批次使用共享调度器，jobs unlimited、编译6/验收2槽位，无 watch、自动集成或推送。
随后用于读取队列末状态、进程和公开冻结检查的组合命令被工具安全检查拦截。没有变换入口重试；没有获得最后运行状态，也没有新交卷验收。
原本已启动的进程输出读取只用于取得其既有启动回执，不替代被拦截的状态查询。

## 仍然开放，不能误记为完成

PatchGeometryProducerStatement 仍须实际构造 Ricci/手术流、消解、统一尺度和帽控制，以及新模型和度量实现。
MetricSlicePresentation.measure_eq 是实际记录的规范体积一致性条件；本轮没有为任意已有记录自动构造它。
每个度量实现使用的拓扑与 preTopology/postTopology 的拓扑，还需要一致性证明；相同 Borel sigma algebra 本身不能冒充相同拓扑。
新指定嵌入与原事件中真正包含映射的交换关系，尤其经过多次局部操作的中间分量，仍需由几何构造给出。
因此本轮是度量到测度的数学连接，不是全部物理历史对应已经冻结。三角剖分和有限光滑图册生产者也未完成。

## 保存与检查范围

frontier.lock.json 已记录四模块、编译产物、任务卡及前九轮来源；独立 ops 副本已写入，父源码设为只读。
派工前检查了本轮编译记录和前九轮锁定源码/产物哈希，全部通过。
公开 V1 未被修改；本轮收尾的13文件结构检查因上述工具拦截没有执行成功，不能冒称本轮新获得 PASS。
保存 RecordedMetricPatch-first-failure.log；其中的可测等价强制转换问题已修复，最终相同源码哈希对应的编译成功。
无全量重建、Git 集成、提交、推送或上游 PR。当前运行状态限定以已得到的启动回执为准。
