# 第四轮：同一投影的有限事件、真实封帽换参数

## 已完成的源码检查

新增两个模块，未编辑前三轮冻结源码或公开 V1：
- `SurgeryProjection.lean`：9 个审计声明源码编译及传递公理检查通过。
- `CapRelabeling.lean`：6 个审计声明源码编译及传递公理检查通过。
全部目标的公理均限于 `propext`、`Classical.choice`、`Quot.sound`。
这些包含直接证明和条件组合，不是 15 个开放根义务已经完成。

## 实质数学连接

1. `standardDecomposition_homeomorph` 直接证明有限标准分解对同胚不变，复用现有覆盖映射与连通和定义，没有再派泛化搬运任务。
2. `RepresentativeStep` 只允许真实同胚更换代表元和列表重排；普通时间区间不隐藏手术。
3. `ProjectedSurgeryStep` 的切颈使用同一个实际嵌入领圈。允许真正的手术输出 A/B 与规范封帽同胚，而非要求 Lean 对象严格相同。
4. `projected_step_reconstruct` / `projected_block_reconstruct` 从后态的标准分解反向重建前态；保留所有真实覆盖、handle 和连通和证据。
5. `SurgeryProjection` 允许尚未证明有限的实数事件集。初态、前后状态、事件跳跃、无事件区间和时域属于同一个对象。
6. `projection_events_finite` 复用既有 `finite_event_set_of_measured_histories`。它消费同一事件集的任意有限样本、统一正损失及统一时域预算；没有先假设全部事件可有限枚举。
7. `projection_trace` 将事件有限性、待证明的有限时序拼接与明确的空终态组合为原始 `FiniteExtinctionTrace [M]`。有限时间本身不代替事件有限性。
8. `RelabeledCap` 记录原始块的同胚、边界重参数化、另一个真实封帽商空间到手术输出的同胚。`relabeled_cap_identifies` 在新叶子成立时构造到规范封帽的对应。
9. `public_of_relabeled_projection` 编译检查了七个显式开放输入到原始 `TopologicalPoincareStatement` 的充分性。

## 新派工

项目 `poincare-refinement-round4-20260927`，有限批次、无自动集成或推送。
两个任务都显式使用 `gpt-6-luna` / `xhigh`，相互没有待证明依赖：
| 任务 | 目标 | 最后实际观察 |
|---|---|---|
| d27r4-finite-timeline | 从有限实数事件集、逐事件跳跃与事件间区间连接推出全程连接 | RUNNING |
| d27r4-cap-relabeling | 用已有 Alexander 延拓构造实际封帽商空间的换参数同胚，保持原块包含公式 | RUNNING |

声明预检的 `sorry` 仅位于工人任务模板，未作为证明导入父模块；新工人尚未验收。

## 前批次与重大缺口

本轮最初的共享队列查询成功：round3 的负侧半领圈、内部图册两项均 VERIFIED。
随后读取其验收元数据的命令被安全检查拦截；未更换入口重试该读取，未重新启动它们，未将它们标记为本轮已验收或集成。
所以本版本七个开放输入为：三项研究义务、前轮两项 VERIFIED 待复核、两项新派工。

`SurgeryProjection` / `RelabeledProjection` 是真实几何必须生产的拓扑投影证书，不是 Ricci 流定义。
投影生产者仍必须证明 PDE/手术存在、实际颈与封帽识别、穷尽丢弃分类、空终态、同一事件集的统一测度预算。
尤其预算接口的测度证书尚未从真实度量构造；不能从条件预算定理声称真实流的事件有限性已完成。
前后状态统一，但光滑度量、重新起流及规范帽拓扑图册与真实光滑结构的兼容仍是生产者工作。
公开根 `smoothing` 和 `geometric_trace` 均仍未完成；未产生无条件庞加莱证明。

## 证据与冻结范围

- 编译：`SurgeryProjection-check.json`、`CapRelabeling-check.json`；15 声明公理检查通过。
- 早期源码错误已修复，仅涉及新文件；保留 `SurgeryProjection-first-failure.log`，不计失败产物为证明。
- 新版本：`frontier.dag.json`（22 个节点的这一版适配图）、`frontier.lock.json`；旧 28 节点版本未改写。图大小不可跨版本当进度比例。
- 只读源与独立 ops 快照保留哈希；新工人通过共享 CLI 注册和派发，无无限 watch。
- V1 13 文件结构检查 PASS；此检查不是重新完整验收全部外部库。
- 使用固定依赖缓存与此前已验收五项的隔离产物。没有全量重建、Git 提交、集成、远程推送或上游 PR。
