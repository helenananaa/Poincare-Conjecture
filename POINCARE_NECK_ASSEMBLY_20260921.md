# 庞加莱主线推进：实际颈体积与测度手术历史

核对时间（机器时区）：2026-09-21T11:19:38+0800。
已验收数学源码提交：`5440ba462561a555f11caa3128ba044ad3289dcb`。本轮未推送。

## 本轮成果

**度量拉回的体积自然性**：在同一有限维实模型向量空间、同一 Haar 归一化下，拉回度量的微分同胚保持任意可测集合的黎曼体积。保留 ENNReal 测度，不要求总量有限。证明经过坐标 Jacobian、Gram 行列式及可数图册分片，不把测度保持作为假设。

**真实颈体积的三次缩放与双边比较**：对已给定的 `EpsilonNeckStructure`，实际体积等于 h³ 乘归一化拉回体积；并证明

`h³ sqrt((1-epsilon)^3) V_ref(A) <= V_g(phi(A)) <= h³ sqrt((1+epsilon)^3) V_ref(A)`。

这里的颈参数化、参考圆柱度量和 epsilon-close 数据由结构提供；没有声称已从 Ricci 流奇点构造出颈。

**从可测替换到有限事件预算**：新增 `MeasuredSlice`、`MeasuredReplacement` 和 `MeasuredSurgeryHistory`。各次手术可使用不同的底层空间。仅从互不相交的可测分片、保留核心体积不增加、各切割区的局部损失，推出总损失。再结合光滑阶段增长界和组件记账，构造原有 `BudgetTrace`，得到事件数量界与有限性。总量递推不是新结构中的假设。

对任意有限事件样本，仍需几何提供覆盖该样本的测度历史；统一正损失、光滑增长和组件记账也是明确输入。没有预先假设整个事件集局部有限，但也没有证明受控手术流存在。

## 分工与验收

现有 Luna 队列完成了体积自然性；该前置集成后，high 档缩放与双边体积比较任务自动解锁、完成并集成。当前对话助手直接编写了测度历史与其组合证明、非空质量 3 到质量 2 的替换示例，以及独立验收。

本轮两份验收覆盖 8 个不同命名声明，其中包含结构转换定义及辅助声明，不是八个独立大定理。全部传递公理仅为 `propext`、`Classical.choice`、`Quot.sound`；没有 `sorryAx`。非空替换示例也编译通过。

主线 `lake --no-cache build PoincareConjecture` 通过；参考包按实际颈体积模块及其依赖增量构建通过。没有清缓存或全量重建全部参考包。

## 尚未完成

颈体积队列状态：`{"INTEGRATED": 8, "QUEUED": 1, "RUNNING": 1}`。
圆柱固定轴向比例区域的统一体积下界仍需完成；固定紧帽与颈的体积差消费者依赖该结果。已证明一个相关乘积逆图册导数计算并送回工人，未将它冒充体积下界。

统一手术尺度下界、标准帽的实际光滑/曲率控制、跨奇点延续、有限时间灭绝和完整拓扑重建仍是待完成义务。未更改 blueprint 完成标记；未宣称庞加莱猜想的 Lean 证明完成。

## 重复验收

```bash
cd PoincareConjecture
lake --no-cache build PoincareConjecture
lake env lean tests/MeasuredHistoryAudit20260921.lean
cd ../formalized-sources/MorganTian
lake --no-cache build MorganTianLib.Ch02.NeckVolume.ActualVolumeComparison
lake env lean tests/NeckActualVolumeAudit20260921.lean
```

新增源码位于 `PoincareConjecture/CriticalPath/SurgeryBudget/MeasuredPieces.lean` 和 `MeasuredHistory.lean`；参考几何源码位于 `MorganTianLib/Ch02/NeckVolume/PullbackMeasure.lean`、`CubicRescaling.lean`、`ActualVolumeComparison.lean`。

本轮原始日志和源码检查点：`/home/helenanana/projects/poincare-ops-20260919/neck-assembly-20260921-105133`。
