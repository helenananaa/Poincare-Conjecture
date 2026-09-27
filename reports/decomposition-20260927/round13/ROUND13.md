# 第十三轮：从同一度量系数的变化推出宽度连续

## 本轮边界

初始旧队列/进程/Git 状态组合查询被安全检查拦截。本轮未更换入口重新查询旧任务状态，未重启或重复派发 round12 任务，未读取其交卷作新验收。
独立数学源码读取、新模块定向编译及新 round13 派工正常完成。
此前 17 个已验收隔离叶子是继承记录，本轮新增验收为 0。两个旧分析叶子在新根组合中仍显式保留。

## 发现的下一处必要条件

round12 的 MinimaxSurvivalProfile.intervals 直接要求 ContinuousOn F.width。
本轮在新版本中替换这一假设：用固定的二次积分表示及紧致度量比较实际构造宽度连续性。
旧冻结定义没有编辑，适配器回到同一个原始 V1 根目标。

## 已经编译的推导

1. `CompactMetricComparison.lean`：点态二次型误差由算子范数控制；给定两项紧致性子结果，得到同一系数族在整个紧空间上的相对比较。
2. `EnergyWidthContinuity.lean`：对同一个谱使用不随时间改变的积分测度、基点映射与向量字段；积分逐点比较得到全部扫掠和切片的统一能量比较。
3. `width_sandwich`：直接对上确界和下确界处理两侧乘法比较，不假设存在达到宽度的最优扫掠，也不选最小化序列。
4. `width_continuous_of_quadratic_energy`：由上述比较证明闭时间区间上的宽度连续，包含端点和零宽度情形。
5. `EnergyContinuityRoot.lean`：构造旧 MinimaxSurvivalProfile 所需的连续性字段，再接到完全相同的 TopologicalPoincareStatement。

三个模块共 8 个审计声明编译通过。传递公理仅为 propext、Classical.choice、Quot.sound；无 sorryAx。
这是直接证明与条件组合的计数，不是八个大型研究义务完成。
证据为 CompactMetricComparison-check.json、EnergyWidthContinuity-check.json、EnergyContinuityRoot-check.json。

## 两项新派工

项目 poincare-refinement-round13-20260927；有限批次，无无限 watch、自动集成或推送。
- d27r13-compact-quadratic-lower：gpt-6-luna / xhigh。对紧空间上的连续正定系数，从单位球面紧性构造统一正下界，而不将该下界当输入。
- d27r13-compact-time-variation：gpt-6-luna / high。由实际闭区间乘紧空间上的连续性得到对所有点统一的时间范围，不要求时间区间外的延拓。

两项声明预检通过、共享 CLI 注册入队成功；只查询新 round13 队列，最后观察均 RUNNING。没有复查被拦截的旧队列。
它们相互没有待证明依赖，已有从实际类型到父证明、再到原始根目标的检查链。
现有 NeckC2Control 接收统一下界，并未代替此次下界构造；没有重派已有矩阵扰动证明。

## 不省略的几何内容

QuadraticEnergyRepresentation 是固定二次积分表示，不是已经实现的 Dirichlet 能量或谐和扫掠。
真实流形上的能量需要构造同一紧参数空间、适当坐标/局部平凡化、时间不变的积分测度和向量字段，并证明精确能量等式与可积性。
本模型不假设全局切向量标架；如何从有限局部平凡化得到该表示仍是研究任务，不由命名解决。
连续性仅在声明给定的闭时间区间上证明；并未构造全局 Ricci 流、光滑化、好扫掠序列或跨手术的实际转移。
三项大型研究输入仍为三角剖分、光滑图册、含具体能量表示的几何生产者。
另保留两个本轮未重新验收的 round12 输入；两个新任务也未计为完成。

## 保存与验证范围

新 frontier.lock.json 包含三个源码模块、编译产物、任务模板和 DAG 哈希，并在独立 ops 目录保留副本。
派工前旧各轮冻结源码及编译产物哈希复核通过；旧文件没有改写。
本轮独立运行公开冻结结构检查，13 个 V1 文件 PASS；这不是 --lean --require-complete 审计。
所有新源码留在 round13 隔离目录；无 Git 集成、提交、推送或全量依赖重建。
初始 Git 状态读取未成功，所以不声称本轮重新确认了当前 HEAD 或工作树状态。
新任务最后队列观察见 new-task-status.json，最终本轮证据摘要见 final-status.json。

## 末尾操作限制说明

末尾的二次哈希复核及 final-status.json 生成命令被安全检查拦截，没有更换入口重试，也没有生成该最终摘要文件。
因此上文关于 final-status.json 的指引不适用；实际最后队列观察保存在 new-task-status.json，两项均为 RUNNING。
已成功的派工前冻结哈希检查与 public-freeze-check.json 不受影响，但不能称为末尾重新核验通过。
