# 第十八轮修复包验收结果

2026-09-27 17:35（Asia/Shanghai）完成。结论：**修复包通过实际 Lean 编译；现有第十九轮已包含对应修复，其完整消费者链也通过了本次独立重编译。**

## 实际处理

- 读取用户指定的 `I:\sys\下载\poincare_round18_repair_candidate.zip`，核对原文、候选和压缩包 SHA-256。
- 在 WSL 隔离副本中执行 `git apply --check`、应用补丁，并确认结果与包内完整候选逐字节一致。
- 使用项目固定 Lean 4.32.1 和原编译选项，串行重编译包内两个文件，以及第十九轮四个实际消费者模块。编译输出写到独立目录。
- 核对现有第十九轮与修复包的差异：四处拓扑投影已修正；紧集单射定理在 `CompactTubularReuse.lean` 中复用，父组合已经消去该待证参数。第十九轮在拓扑投影修正后，原 `rw` 证明也编译通过，无须再改写为包内的等式传递形式。
- 保留第十九轮更强的拼接接口：除原嵌入等式外，还要求精确像域 `R.domain = T.endpoint '' U` 及逆／投影公式。未用旧包覆盖它。

## 验证

| 检查对象 | 本次结果 |
| --- | --- |
| 包内独立紧性适配证明 | 编译通过，1 个声明公理审计通过 |
| 包内修复后的父组合 | 编译通过，4 个声明公理审计通过 |
| 第十九轮 CompactTubularData | 编译通过，2 个声明公理审计通过 |
| 第十九轮 CompactTubularReuse | 编译通过，2 个声明公理审计通过 |
| 第十九轮 TubularApproximation | 编译通过，2 个声明公理审计通过 |
| 第十九轮 TubularRoot | 编译通过，4 个声明公理审计通过 |
| 既有冻结文件、产物和来源 | 167 个文件哈希复核通过，前后未改变 |
| V1 公开边界 | 13 文件结构检查通过 |

合计 **6 个模块、15 个声明**；传递公理只含 `propext`、`Classical.choice`、`Quot.sound`，没有 `sorryAx`。15 是审计声明数量，包含复用和条件组合，不是新增 15 个已解决研究缺口。依赖使用固定缓存，未全量重建依赖库。V1 检查为结构检查，并非完整证明验收。

## 保存位置和边界

WSL 证据目录：
`/home/helenanana/projects/poincare-parallel/reports/repair-package-20260927/`

- `result.json`：本次汇总。
- `package-integrity.json`：原文哈希与补丁应用验证。
- `candidate/`：已应用修复并独立编译的包内候选。
- `round19-recheck/`：现有第十九轮源码快照和本次重新生成的编译产物。
- `*-check.json`、`*.log`：精确命令、源码哈希、公理列表及编译输出。
- `candidate-vs-round19.diff`：旧包与较新冻结版本的差异。
- `frozen-before.json`、`frozen-after.json`：未修改既有冻结内容的证据。

第十八轮原始失败记录作为历史证据保留；后续证明继续使用已修复的第十九轮。没有修改既有冻结源码、V1 绑定或运行中的工人，没有 Git 提交或推送。

本轮查询时，`d27r17-smooth-retraction-form` 与 `d27r19-tubular-inverse-assembly` 均为 RUNNING；这只是运行状态，不是证明验收。本轮未新增工人、未验收新工人叶子。

**庞加莱完整证明仍未完成**：`smoothing`、`geometric_trace` 仍未绑定；局部逆拼接和实际几何数据存在性仍属于后续工作。
