# Luna 进度检查与推进记录

检查时间（远程主机当地）：2026-09-20T19:05:18+0800。
仓库仍为 `integration` / `e5217db`。没有提交、没有推送，索引为空，`git diff --check` 通过。

## 本次实际验收并集成

PBW 的 12 个模块在独立目录从源码重编译，11 个关键声明传递公理审计通过；随后并入生产目录并再次构建、审计。内容涵盖 Jacobi 作用关系、有序单项式的求值、线性独立性和 PBW 基。它复用了此前 Grok 构造、Luna l03 复核的候选，不记作 Luna 新写的全部证明。上游许可证、版本记录和新增文件的来源说明保留在 External/TauCetiPBW。

Theorem 7.7、Problem 4.12、Problem 6.9 的修复已并入，7 个关键声明审计通过。7.7 明确使用 C∞ 及源空间宇宙，而不是错误地从光滑输入宣称解析覆盖；另两项保留原结论，修复局部实例与模型条件。

标准半空间的正维正则原像版本独立重编译 8 个模块、审计 5 个关键声明后集成。它实际构造图册、证明光滑嵌入及精确的边界对应等式。新入口是 RegularPreimageWithBoundaryCorrected.lean；要求普通半空间模型、m≤n、标准分离/可数性及边界切方向的正则性。原 Problem_5_23.lean 完全保留，没有通过注释或删除旧命题降低计数。

三套验收合计 23 个关键声明，仅含 propext、Classical.choice、Quot.sound，没有 sorryAx；这不是“23 个原始 sorry 都已消除”的说法。

## 拦下与重新分派

Exercise 4.9 候选给半空间目标增加了不可能的 Boundaryless 假设，未集成。已启动 l11-LocalDiffeomorphBoundary（Luna xhigh）直接补局部图册证明，不把模型无边界当作前提。

l04 幂零表示候选虽能编译，但将关键重排结论作为 HighWeightOrderedRewrite 假设，不能视为完整幂零 Ado。已启动 l10-WeightedPBWRewrite（Luna max），使用本次已验证的 PBW 源码证明该重排，不再沿用旧的 PBW sorry 快照。

l09 留下的 Whitney/横截稳定性相关边界接口未修完，已启动 l12-StabilityBoundaryConsumers（Luna xhigh）处理三个具体消费者。一般 Ado 的宽泛任务没有重复重开；目前先补明确的中间依赖，避免无目标地重复消耗 max 额度。

## 仍未完成

生产源码显式 sorry/admit 仍有 6 个，分布在 4 个文件。这只是源码计数，不能替代完整依赖与声明范围验收。

针对上一轮失败的 11 个模块进行了定向增量复检，当前仍失败 8 个，3 个已修复。没有清缓存或全库重建。尚未通过的模块为：

`LeeSmoothLib.Ch08.Sec08_56.Proposition_8_15`
`LeeSmoothLib.Ch08.Sec08_63.Problem_8_18`
`LeeSmoothLib.Ch04.Sec04_22.Exercise_4_9`
`LeeSmoothLib.Ch05.Sec05_36.Theorem_5_48`
`LeeSmoothLib.Ch08.Sec08_58.Proposition_8_23`
`LeeSmoothLib.Ch06.Sec06_40.Corollary_6_17`
`LeeSmoothLib.Ch06.Sec06_45.Problem_6_11`
`LeeSmoothLib.Ch06.Sec06_45.Problem_6_16`

## 运行状态与保护

原来 9 个任务中，检查时 6 个已返回，3 个运行中；返回不等于证明完成。新增 3 个明确分工的后续任务，检查时合计 6 个 Luna 客户端运行。全部显式使用 gpt-5.6-luna 和 high/xhigh/max，不重试 Grok，不回退 SOL。

庞加莱主线保护范围内 908 个 Lean 文件哈希未变，主线增量构建通过。主 blueprint 完成标记未修改，未声称完成庞加莱形式化。

## 复核入口

在 formalized-sources/LeeSmooth 下运行 tests/PBWAudit20260920.lean、tests/LunaInterfaceAudit20260920.lean、tests/BoundaryPreimageCompanionAudit20260920.lean。

本次源码快照、独立构建日志、生产构建日志、公理输出、接受清单及回归结果都在：
`/home/helenanana/projects/poincare-ops-20260919/luna-handoff-20260920-180603/review-20260920`。
