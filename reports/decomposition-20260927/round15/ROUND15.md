# 第十五轮：固定同伦类的实际能量转移，允许任意小误差

## 接续状态

开始时实际目录已含 round14，不是只到对话中上一份 round13 汇报。
成功查询确认 round12/round13 四任务为 VERIFIED；round14 已有独立重编记录和累计 21 项隔离验收报告。
本轮未重复验收或重复计数那四项，未声称重新从源码编译整个旧依赖库。
开始时 round14 两项为 RUNNING，精确模型分别 gpt-6-luna/max（内禀度量比较）和 gpt-6-luna/xhigh（球面能量连续）。
保留原进程，没有中断、重启或重复派工。
之后包含 PDE 源码、round14 状态和驱动查看的组合读取被安全检查拦截，没有换入口重试该读取。
本轮沿已读取的实际球面能量与同伦接口继续独立工作；末尾不冒充取得了新工人状态。

## 本轮直接完成的证明

1. `SmoothClassMap.send`：指定光滑映射将每个源代表元送进指定的目标相对同伦类，同时保持两个基点端值。目标类必须已具有非平凡性证书。
2. `sphere_density_postcompose_le`：对实际 mfderiv 应用链式法则，逐正交基向量求和，得到密度比较。
3. `sphere_energy_postcompose_le`：借助显式可积性将密度比较积分，得到目标度量拉回有界时的实际 Dirichlet 能量比较。
4. `SmoothClassMap.toTransfer`：精确收缩时构造原有 SweepoutTransfer，而不是读入一个已假设的能量不增结论。
5. `spectrum_transfer_mul_bound`：不假定最优扫掠存在，利用正因子除法和条件下确界得到宽度的乘法估计。
6. `approximateTransfer_width_le`：每个 eta>0 可选择不同转移，只要能量至多放大 1+eta，就推出精确宽度不增；不需要这些映射本身收敛。
7. `almostContracting_to_approximate`：指定类之间的光滑近收缩映射族足以产生上述近似转移。实际手术中这类映射是否存在尚未证明，它只是一个可用构造入口，不是强制所有路线采用的假设。
8. `SmoothClassMap.not_constant`：常值映射不能满足目标非平凡相对同伦类的转移契约，防止用破坏同伦类来虚假降低能量。

## 不是给旧路线增添负担

`SweepoutTransfer.toApproximate` 和 `approximate_producer_of_exact` 已检查：原来的精确转移/生产者可原样接入新接口。
新 ApproximateIntrinsicProfile 与原来保留相同实际球面能量、固定类、事件时间、连续区间和好扫掠数据，只放宽跳跃转移为任意小误差。
`toExtinction` 用已证明的精确宽度不增以及原 Dini 估计生成 ExtinctionProfile。
`public_of_approximate_transfer_frontier` 已返回原始 V1 TopologicalPoincareStatement。

## 编译、公理与保存

四个新模块共 15 个审计声明通过源码编译与传递公理检查，仅含 propext、Classical.choice、Quot.sound。
其中包括定义、条件组合、回归证明，不能当作完成 15 个大型开放研究义务。
具体证据为四个 `*-check.json`、`frontier.lock.json`、`frontier.dag.json`。
中途 sum 分配、光滑复合隐式参数、函数复合形式出现过编译错误，已修正；两份失败日志保留，只有最终源码哈希匹配的成功结果被冻结。
新源设为只读，ops 另存独立冻结副本；旧 14 轮来源和产物哈希在 freeze.py 中复核通过，未改写旧接口。
本轮另行运行 V1 结构检查，结果在 public-freeze-check.json；此检查不等于全量源码重建。

## 尚未完成、派工边界

实际手术的类保持转移、非平凡类的存在、好扫掠的几何构造、张量与实际受控流的全部对应仍是研究义务。
对于几何上只能得到 Lipschitz 或分片光滑转移的情况，还需证明光滑逼近保持相对类且满足任意小能量误差；本轮没有假设这一逼近自动成立。
没有宣称构造出全局手术流、三角剖分或光滑化，两个公开根义务仍开放。
本轮新增待派卡为空，新增工人 0；没有将可直接完成的小组合拆成重复工人任务，也没有取消原运行批次。
此前第十四轮的 21 项累计隔离验收是已有记录，本轮新增工人独立验收为 0。
不重新声称两项旧工人的末尾状态；最后成功查询状态在初始读取中均 RUNNING，之后的状态复查被拦截。
没有 Git 集成、提交、推送、上游 PR 或全量重建。本轮文件均保存在独立 round15 目录。
