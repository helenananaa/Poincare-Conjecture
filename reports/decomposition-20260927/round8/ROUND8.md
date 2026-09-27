# 第八轮：十二叶验收、实际度量颈、投影计数与切片拓扑

## 本轮实际验收

round7 两任务的完整源码已经阅读、核对冻结声明前后缀及交卷哈希，并在本轮私有产物目录重新编译。
分别导入实际编译目标审计公理，全部通过：
- `d27r7-finite-cap-scaling`：实际度量缩放、紧致区域有限测度、所有帽的有限求和，包括空族。
- `d27r7-uniform-neck-allowance`：同一实际 epsilon-neck 及其参考度量、依赖总 B 的统一正阈值；不假设颈已经存在。
证据：`two-source-recheck.json`、各 compile/audit 日志、`semantic-review.json`。
累计十二个局部叶子为 ACCEPTED_ISOLATED_NOT_INTEGRATED；队列 VERIFIED 不等于 Git 集成。
`AcceptedTwelve.lean` 实际代入这两个定理，局部损失与总组合不再接收它们为开放参数。

## 新的实际数学连接

`GeometricNeck.lean` 固定一个真实 `AmbientMetricNeck`：局部光滑区域上的度量 epsilon-neck，及该区域到原闭流形的开放嵌入。
闭领圈不是任意选择，而是精确函数
`inclusion (neck.phi (sphere, axialCoordinate / (2 * epsilon)))`。
定义证明了参数仍在原开放颈内；`central_formula` 证明中心切片使用原颈的同一参数。
待证的新叶子只需证明这个精确闭领圈是嵌入。其父节点已经把它接入实际切割及连通和构造。

`CountedSurgery.lean` 定义携带实际证据的操作：代表元同胚/重排、sphere-cover 丢弃、handle 丢弃、上述真实 metric-neck 切割。
有限操作字的 cuts/discards 是类型索引，不是无约束计数。
已直接证明分量守恒：`after.length + discards = before.length + cuts`。
`ActiveMetricEvent` 展示至少一项实际切割或丢弃，允许其前后有普通变化；因此推导 `1 <= cuts + discards`，不把活动性不等式假设为字段。
操作字可降至既有 `RelabeledSurgeryStep`，没有改变旧 V1 拓扑改写语义。

`SynchronizedBudget.lean` 在同一 H 的真实事件时刻取前后列表：
- ordinary 区间连接 H.post(time i) 与 H.pre(time(i+1))；
- 同时刻 actual operations 连接 H.pre(time(i+1)) 与 H.post(time(i+1))；
- 记录的时间必须属于 H.events；
- measured slice 的拓扑必须与相应列表的实际不交并同胚，measurable 必须等于该拓扑的 Borel；
- components 定义成同一 H.post 列表长度。
`CountedNeckHistory.toControlled` 因而实际生成原来的 component_step 和 event_active，两个字段不再独立假设。
`counted_budget_to_anchored` 和 `public_of_counted_frontier` 编译检查了新输入回到原 V1 公共目标的充分性。

## 新派工

`poincare-refinement-round8-20260927` 是共享 CLI 中的有限批次；没有 watch、自动集成或推送。
唯一新就绪任务 `d27r8-epsilon-neck-embedding` 使用 `gpt-6-luna` / `xhigh`。
证明策略：精确参数映射连续且单射；结合 neck.phi 和 inclusion，或用紧定义域到 Hausdorff 的连续单射得到嵌入。
不要求闭流形本身是 epsilon-neck，不增加单连通性，不换成不明存在的领圈。
最后实际观察为 RUNNING；任务模板的 sorry 只用于声明预检，尚未计为证明。
本轮其余常规计数归纳由协调者直接完成，没有派重复任务。

## 严格保留的缺口

这不是整条物理手术流已经同步或构造完毕。
局部 `neckModels` 与 `MetricSurgeryMove.neck` 内的每一个 epsilon-neck，目前只共享事件和数量，尚未建立逐项指认/双射。
`ComponentRealization` 固定了全局切片拓扑，但它的同胚与 `RicciIntervalBridge` 中保测度可测同构的拓扑/张量兼容仍须由真实构造证明。
旧/新区域的保测度映射是否就是同一物理手术的包含映射、无修改核心的度量识别、所有过渡区是否完整计入，仍是研究义务。
新 CountedGeometryProducerStatement 是更具体但仍未构造的生产者；未宣称它与旧弱生产者双向等价，只证明它足以推出旧义务。
统一正尺度、全部帽体积界、真实 Ricci 手术存在、有限时间消解、穷尽丢弃分类仍开放。
三角剖分与光滑化未在本轮新增完成证明。

## 检查与保存

四模块 21 个审计声明源码编译及传递公理检查通过：AcceptedTwelve 4、GeometricNeck 3、CountedSurgery 10、SynchronizedBudget 4。
全部传递公理仅 propext、Classical.choice、Quot.sound；这包含直接证明及条件组合，不是 21 个大型根义务完成。
CountedSurgery 第一次 simp 失败已在冻结前修复，保留首轮失败日志；失败产物不计成果。
`frontier.lock.json` 保存新源、两项验收源、产物及旧版本引用哈希；独立 ops 目录存有快照。
旧 V1 的 13 文件检查通过；smoothing/geometric_trace 未绑定，complete=false。
无全量重建，无 Git 集成、提交、远程推送或上游 PR。此前已验收十二项仅作为隔离基线使用，不伪称 INTEGRATED。
