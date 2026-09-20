# Luna 继续推进与验收记录

核对时间：2026-09-20T21:09:16+0800。分支 `integration`，HEAD `e5217db`。没有提交、推送或上游 PR；索引为空，`git diff --check` 通过。

## 本轮已接入并验收

Sard 的标准带边界流形版本已接入 `SardBoundaryManifolds.lean`。它证明实际临界值集合在目标流形中零测，不是假设局部延拓已经给定的条件版本。源为标准半空间模型的光滑流形，源维数正；目标维数允许为零，允许空流形。独立重编译、生产构建、传递公理检查都通过。

Proposition 8.23 的向量场限制定理通过一般开集限制的浸入引理修复，公开结论和假设未变。

Problem 8.18 的向量场下推接口已修复，并明确增加源流形内禀无边界条件 `BoundarylessManifold I M`，不是给半空间模型伪造 `I.Boundaryless`。原先允许任意带边界源的下推结论过宽：把两个半直线分别映到实线正半轴、负半轴，两个源场系数取 `t` 和 `-t`，下推系数为绝对值，在零点不光滑。原有名称含 lieBracket 的声明仍只表达纤维常值条件，没有据此声称额外证明了 Lie 括号判据。

我直接补了这个反例的标量障碍证明：满足两条半轴取值规则的函数必须是绝对值，因而不可能在零点可微。它已编译并通过公理检查；这是标量部分的形式化，不冒充整个流形和切丛反例已编码。

本轮三份新增验收合计覆盖 8 个不同声明，均只使用 propext、Classical.choice、Quot.sound。这个数量包含修复结果、既有辅助声明回归和标量反例，不等于新证明了八道原始题目。

## 重要基础的复核

幂零 Ado 的生产接口已真正不带额外 PBW 或重排前提：任意特征零域上的有限维幂零 Lie 代数，具有由幂零自同态给出的有限维忠实表示。本轮复核其六个关键声明，公理检查通过。一般 Ado 的非分裂/环境扩张步骤仍未完成。

一般三维无边界环境模型下的原生颈闭包适配也再次通过生产构建与公理检查。它仍以明确的切割、侧别和边界覆盖数据为输入，不包含 Ricci 流、手术或灭绝存在性证明，不是完整庞加莱证明。

## 当前未完成状态

生产源码还剩 6 个显式证明洞，分布在 4 个文件。旧的宽泛/有缺陷声明仍明确保留，没有靠注释掉它们降低数量。

定向回归剩 4 个失败模块：

- `LeeSmoothLib.Ch08.Sec08_56.Proposition_8_15`
- `LeeSmoothLib.Ch05.Sec05_36.Theorem_5_48`
- `LeeSmoothLib.Ch06.Sec06_40.Corollary_6_17`
- `LeeSmoothLib.Ch06.Sec06_45.Problem_6_16`

这些是对已知失败集合的复检，不是整个 Lee 库没有其他问题的保证。

## 新的执行安排

本轮新开三个 Luna xhigh 任务：标准半空间投影稠密性及紧源嵌入逼近；正则域局部定义协向量的正权重拼接；允许参数带角的统一局部单射估计。任务直接针对已定位的数学缺口，不重复证明已验收的 PBW 或欧氏 Sard。

核对时仍在运行：l02-BoundaryRank（max）；l19-NilpotentDerivationStable（max）；l20-BoundaryProjectionDensity（xhigh）；l21-RegularDomainDefiningFunction（xhigh）；l22-ParametricInjectivityCorners（xhigh）。

本轮没有新开 Grok、SOL 或低于 high 的档位，也没有重复启动一般 Ado 的宽泛任务。任务运行状态不是完成证明的证据。

原先保护范围内 908 个 Lean 文件哈希未变。既有的两份新主线桥接源码另行构建检查；主 blueprint 完成标记未改。

## 复核入口

在 `formalized-sources/LeeSmooth` 下运行：

```bash
lake env lean tests/Continuation2042Audit20260920.lean
lake env lean tests/VectorFieldDescentAudit20260920.lean
lake env lean tests/VectorFieldDescentObstructionAudit20260920.lean
lake env lean tests/NilpotentRepresentationAudit20260920.lean
```

主线复核位于 `PoincareConjecture/tests/NativeGeneralAmbientClosureAudit20260920.lean`。

原始快照、源码差异、构建输出、公理检查和任务记录：`/home/helenanana/projects/poincare-ops-20260919/luna-handoff-20260920-180603/continue-20260920-2042`。
