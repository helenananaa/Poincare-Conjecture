# 第七轮：标量传播实收、颈到多帽的真实局部体积损失

## 新验收

`d27r6-closed-scalar-propagation` 已完整阅读 69 行返回源码，核对冻结声明前后缀、交卷哈希、独立验证哈希，再从源码重编及审计精确目标。
结果 PASS，公理只有 `propext`、`Classical.choice`、`Quot.sound`。
`AcceptedTen.lean` 将其实际代入 `checked_ricci_interval_growth` 和 `public_after_ten`；累计本次拆分路线已有 10 个局部叶子接受为隔离成果。
该数字不是整个项目的成果数，更不是根目标完成比例。共享队列仍显示 VERIFIED，未进行 Git 集成。
证据：`scalar-source-recheck.json`、`semantic-review.json`、`AcceptedTen-check.json`。

## 真实几何来源与接口修正

完整读取并从原源码复验 `MorganTianLib/Ch02/NeckVolume/CompactCapGap.lean`，其固定紧帽与长颈比较定理通过，白名单公理检查通过。
这是直接来源重编，不是其全部传递依赖的全量重建。
既有定理只处理一个固定帽，不能直接替代任意总帽体积上界下的统一颈估计。

- 颈模型 `SmoothVolumeRegion` 允许非紧区域。`EpsilonNeckStructure.phi` 把有限开圆柱识别为颈区域，不能假装该区域就是整个闭流形。
- `CompactCapModel` 存实际光滑模型、度量和紧集，baseVolume 从真实黎曼测度计算，不是假设体积值。
- 新帽用任意有限个模型和互不相交的实际测度区域覆盖，包含一次切割插入两个帽的情况。
- 旧颈补丁只要求包含在移除区域内，不错误要求两者完全相等。
- 新旧记录测度通过 `MeasurePreserving` 与模型的限制黎曼测度关联；这些对应必须由真实几何提供。

## 已检查的父组合

`NeckLoss.lean` 先从保测度映射和分片覆盖推出记录体积与模型体积的关系，然后在两个新叶子成立时证明：

```text
旧颈体积 ≥ r³(B+1)，全部新帽体积 = r³ ΣVᵢ ≤ r³B，r ≥ rho > 0
                         ⇒  rho³ + 新区域体积 ≤ 旧区域体积
```
`NeckControlledHistory` 不再包含 `local_loss` 假设；`toRicci` 由同一次替换的 neckModels 生成它，损失取 `rho³`。
每个有限样本之前先固定 B、epsilon0、rho；不能为各样本或各帽任意更换统一常数。
`public_of_neck_loss_frontier` 已编译回精确 V1 `TopologicalPoincareStatement`。
三模块共 9 个审计声明均通过，只含白名单三公理；这些包含条件组合，并非九个重大生产者已证明。

## 两项实际派工

| 任务 | 模型与档位 | 冻结目标 |
|---|---|---|
| d27r7-uniform-neck-allowance | gpt-6-luna / max | 任意非负总帽体积上界 B 的统一真实颈体积下界 |
| d27r7-finite-cap-scaling | gpt-6-luna / xhigh | 任意有限个实际紧帽的总体积三次缩放公式，包含 n=0 与多个帽 |

二者独立，父消费者已检查。共享 CLI 项目：`poincare-refinement-round7-20260927`。
运行方式是有限批次，无 watch、自动集成或推送；最后状态以 `final-status.json` 为准，派工时均实际 RUNNING。
任务模板的占位证明只用于声明预检，不是已证明结果，也未用于父模块的无条件叶子绑定。

## 仍需证明的真实构造

真实手术流、光滑帽及其统一归一化体积上界、正尺度下界、测度对应、分量记账与同一拓扑历史的完整对应仍须构造。
本轮没有宣称 EpsilonNeckStructure 已被生产：其参考圆柱曲率条件仍是后续实际颈存在性的输入。
构造还必须证明被删除的旧区域包含用于下界的颈补丁，并证明所有插入部分确被帽区域覆盖；不能漏算连接过渡区。
`NeckLossGeometryProducerStatement` 仍是研究任务，不能把统一尺度或测度对应当成免费假设。
三角剖分、PL 光滑化没有新增证明，本轮没有冻结虚构的光滑过渡。
检查了固定 Mathlib 的 PreAbstractSimplicialComplex：其面要求非空，旧 link 条件不包含空面；未据此声称三角剖分路线已完成。

## 保存与验收边界

保留早期新文件类型错误日志 `NeckLoss-first-failure.log`；只修新接口，未改旧 V1 或之前六轮冻结文件。
`frontier.lock.json` 记录三模块、接受的标量源码、新产物、重编来源、旧快照引用及两张任务卡哈希；ops 保存独立副本。
公开 13 文件冻结结构检查 PASS；没有全量重建或重新完整验收所有外部依赖。
所有新增代码仍在隔离报告目录，未导入主包、改公开绑定、提交、推送或创建上游 PR。
