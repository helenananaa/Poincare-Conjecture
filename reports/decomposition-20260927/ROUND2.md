# 第二轮：真实封帽流形与闭覆盖重建

## 本轮实际结果

- 新增 `CapManifold.lean` 和 `ClosedCut.lean`，均在新模块中；没有编辑上一轮冻结的三个接口模块或公开 V1。
- 两个源模块的 8 个审计声明全部编译通过；传递公理仅 `propext`、`Classical.choice`、`Quot.sound`。
- `actual_cap_connected` 直接证明：连通原块沿真实非空球面封帽后，实际商空间连通。
- `actual_cap_atlas` 是条件组合：消费上一轮 `CapChartStatement` 与新增 `CapInteriorOpenStatement`，将帽坐标和原块内部图册覆盖整个实际商空间。
- `cappedManifold` 复用已有商空间紧致/Hausdorff 证明，并由紧致加图册推出第二可数性，构造完整 `ClosedThreeManifold`。
- `cappedIdentification` 在同一底层空间和拓扑上构造恒等同胚，不是额外假设一个未构造的封帽流形。
- `RegularClosedCut` 只含原流形的真实闭子集、边界与半领圈、内部图册及覆盖/交叠条件；不含封帽图册或商空间重建结论。
- `rawCut_of_closedCut` 消费新增闭覆盖重建义务，返回上一轮精确 `RawCutPresentation`。
- `refined_frontier_implies_public` 将八个显式前沿义务组合回原始 `TopologicalPoincareStatement`。这是条件充分性证明，不是庞加莱的无条件证明。

## 新派工（有限批次，无自动集成）

项目：`poincare-refinement-round2-20260927`。
两个任务都指定 `gpt-6-luna`、`xhigh`；相互无待证明依赖；没有重启上一轮任务。

| 任务 | 精确输出 | 本轮最后观察 |
|---|---|---|
| `d27r2-cap-interior-open` | 原块去除边界后的实际包含映射，是到封帽商空间的开放嵌入 | RUNNING；attempt c27150ed-4ab4-45e2-a192-5d4afce45093 |
| `d27r2-closed-cover-gluing` | 由实际闭覆盖和精确公共边界，构造原空间到 raw seam 商空间的同胚 | RUNNING；attempt a59be193-c03d-4f6b-afb4-a75f15331c7b |

声明预检中的 `sorry` 仅是任务模板的未填证明体；没有被计作已验收证明，也未导入父组合源码。返回结果仍必须通过独立源码、公理和数学语义验收。

## 保留的重大数学义务

八个接口义务中，原三项工人结果尚未在本轮刷新；两项是本轮新任务；三项仍是研究级：拓扑到有限 PL、PL 到光滑结构、真实几何到有限 `CollaredDecomposition`。节点数不是完成百分比。

尤其不能把 `cappedManifold` 的拓扑图册当成光滑图册。后续真实手术流必须提供自身的光滑结构及到该固定拓扑模型的适配，或一次性搬运完整的有限手术历史；不得直接假定新帽具有 `IsSmooth`。

几何下一层应从同一个实际颈构造 `RegularClosedCut`：复用 `ClosedSphereCutData` / `ClosedSideHalfCollar` 的实际闭包及正半领圈，反射领圈参数得到负侧；把去边界内部与原流形开分量识别以继承图册；核对两侧公共边界正好是原中心球面。此生产者尚未写成验收通过的新任务，不计作完成。

真实流、延拓/手术控制、有限事件、消解、丢弃分类和其到有限切割树的对应仍须继续拆解。`CollaredGeometricProducerStatement` 明确保留这一义务，没有用改名宣称它已解决。

## 证据和操作边界

- 源码/公理日志：`CapManifold-check.json`、`ClosedCut-check.json`。
- 版本化记录：`round2-frontier.dag.json`（21 节点，8 个接口义务）、`round2-frontier.lock.json`。保留上一轮 v1 原快照。
- 任务和启动记录：`round2-cards.json`、`round2-dispatch.json`。
- 公开边界检查：`round2-public-freeze.json`，13 文件 PASS；本次是结构冻结检查，不是四个既有绑定的重新 Lean 验收。
- 本轮最初查询上一批任务状态的复合命令被安全检查拦截；未重试或换入口查询这批结果。故上一批三项不标记完成、不重启、不集成。
- 新模块编译和新批次操作正常完成。新批次 `cli.py status` 返回两项 RUNNING。
- 不运行全量重建；没有提交、推送或上游 PR；没有无限派单监督循环。
- 额外的前沿检查脚本未在本轮尝试补写；没有将哈希记录冒充完整的自动语义检查器。
