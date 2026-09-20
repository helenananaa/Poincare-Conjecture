# Lee Smooth 本轮收尾报告

日期：2026-09-20。仓库：`/home/helenanana/projects/poincare-parallel`。
分支仍为 `integration`，HEAD 仍为 `e5217db`。没有提交、没有推送、没有向上游提 PR；索引为空，成果保留为工作区修改。

## 指定四项

| 文件 | 已完成内容 | 明确的类型范围 |
| --- | --- | --- |
| Proposition 4.1 | 局部浸没与局部浸入两个结论 | 浸没版不增加假设；浸入版明确 `[I.Boundaryless] [J.Boundaryless]` |
| Proposition 5.3 | 切片的像、切片光滑嵌入、诱导流形结构 | 后两项增加固定因子 `[J.Boundaryless]`，移动因子仍可有边界 |
| Proposition 5.38 | 子流形切空间等于局部定义映射导数的核 | 增加显式余维等式；原 `IsLocalDefiningMapOn` 定义不变 |
| Proposition 4.6 | 有限依赖乘积、坐标判定；保留原复合证明 | 乘积版不增加假设；坐标版明确两侧无边界、相应光滑图册、`Continuous f` |

四个目标文件均不再含 `sorry`。验收涉及九个声明，其中复合命题是先前已有成果。

5.38 新增条件为 `Module.finrank 𝕜 E' + Module.finrank 𝕜 F = Module.finrank 𝕜 E`，作为独立参数 `hcodim`，不是把切空间等式当作前提。
这修复了原类型遗漏的余维约定。原先允许任意带边界模型的宽泛版本有反例：在上半平面 `y ≥ 0` 上取 `Φ(x,y)=x²+y`、零纤维 `S={(0,0)}`，导数满射，但 `T₀S=0` 而 `ker dΦ₀` 是 x 轴。

## 验收结果

- 152 个受影响的 Lee 模块及其依赖增量构建通过。Lake 日志显示 8937 个构建图任务；这不是重编译了 8937 个文件，没有清缓存或全量重建。
- `tests/Closeout20260920.lean` 对九个声明执行传递公理检查，九项全部通过；仅允许 `propext`、`Classical.choice`、`Quot.sound`，遇到 `sorryAx`、其他公理或缺失声明会失败。
- `lake build PoincareConjecture` 通过；745 个主线导入声明的公理审计没有发现非标准公理。
- PoincareConjecture 与 MorganTian 保护范围内 908 个 Lean 文件逐一 SHA-256 核对，全部未变；其他应保留的 40 个快照文件字节一致。
- `git diff --check` 通过。主 blueprint 完成标记未修改。这仍不是庞加莱猜想的形式化证明。

## 同步修复的集成问题

5.38 的余维条件已同步到 5.39、5.40、6.25、6.9、6.16；需要的维数等式在具体情形中实际证明。5.39、5.40 的通用接口明确增加相应余维参数；6.25、6.9、6.16 的最终结论没有为此增加假设。

新鲜依赖构建还暴露并修复了：4.28 及 Problem 4.6 缺少源模型无边界条件；5.41 的导数化简错误；5.2 与 5.49 的同名辅助声明冲突；5.4 固定 `∞` 与解析调用不兼容（现已推广到任意正则性）；6.16 与 4.8 重复声明连续线性映射可逆性辅助引理；8.22 未同步 5.37 的有限维和 Hausdorff 条件。
这些修改均属于 Lee 证明与其下游接口，没有修改已通过的庞加莱主线。

## 必须保留的遗留说明

对先前那 18 个改动模块的当前版本审计了 205 个公开定理，发现一个非标准公理依赖：`torus_revolution_map_isImmersion`（Example 4.2）。它调用仍含 `sorry` 的 `Manifold.is_immersion_iff_forall_injective_mfderiv`，因此传递依赖 `sorryAx`。
该旧声明不属于本轮指定四项，未计入本轮完成项，也未改写。其余 Lee 模块仍有原有 `sorry`，包括 Exercise 5.40 的旧辅助命题；构建通过不意味着整个 Lee 库无证明洞。

## 重复验收

使用固定的 Lean 4.32.1 工具链，在 `formalized-sources/LeeSmooth` 下运行：

```bash
xargs lake --no-cache build < tests/Closeout20260920.targets
lake env lean tests/Closeout20260920.lean
```

日志、原始未提交成果快照与保护检查位于：
`/home/helenanana/projects/poincare-ops-20260919/lee-closeout-20260920-102327`。
主要证据文件为 `affected-final-build-2.log`、`final-core-axioms.log`、`poincare-incremental.log`、`poincare-axioms.log`、`prior-lee-axioms.log`、`preservation.json`。
起始快照为 `preexisting-worktree.tar.gz`，未向工作仓库写入临时试验目录。
