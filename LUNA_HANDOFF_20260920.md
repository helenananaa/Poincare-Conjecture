# Luna 接力记录｜2026-09-20

## 当前默认

Codex 默认模型已设为 `gpt-5.6-luna`，默认推理档位为 `high`。每个项目工人仍显式指定模型和档位，不依赖默认值。
只允许 `high`、`xhigh`、`max`；不调用 Grok，不回退 SOL 或其他模型。旧配置已备份，原 Grok 源码与日志保留。

## 本次接力

| 任务 | 档位 | 来源 |
| --- | --- | --- |
| Sard 证明及移植 | max | h01-SardCompletion |
| 一般非线性带边界常秩 | max | h09-BoundaryRankNonlinear |
| PBW：Jacobi 作用、单项式独立性 | max | h18-PBWJacobi + h19-PBWEvaluation |
| 幂零 Lie 代数的有限维忠实模 | max | h20-NilpotentPBWTruncation |
| 一般 Ado 的环境扩张与完整结论 | max | h21-AdoAmbientExtension |
| 带边界正则原像的图册与总定理 | xhigh | verify-h23-BoundaryNeatSlice |
| 局部微分同胚、覆盖映射接口回归 | high | 当前工作树三个失败模块 |
| 正则域、向量场的边界接口回归 | xhigh | 当前工作树四个失败模块 |
| 切空间、横截性接口及编译超时 | high | 当前工作树四个失败模块 |

九个任务的真实启动日志均记录 `model: gpt-5.6-luna` 和相应档位，并已执行工具操作。没有新开 Grok。工作区隔离；只复制源代码，不信任旧工人的 `.olean`。已验证重复启动保护，重跑同一尝试会被拒绝。

交接时，生产源码还有 6 个显式 `sorry`/`admit`，分布于 4 个文件；最近一次较广的增量构建另有 11 个模块失败。源码占位符数不是传递公理审计结果，不能将任务启动或候选代码视作完整证明。

## 保全与验收边界

庞加莱主线保护范围内 908 个 Lean 文件哈希未变。`lake --no-cache build PoincareConjecture` 增量构建通过（日志中的 8880 是依赖任务数，不是全量重编译文件数）。未清除缓存，主 blueprint 完成标记未修改。
仍在 `integration`，HEAD 为 `e5217db`，没有提交、没有推送，索引为空。新工人的产物必须独立编译、审阅声明变化、检查传递公理之后才能并入；本记录不把正在进行的九项算作已完成。

运行目录：`/home/helenanana/projects/poincare-ops-20260919/luna-handoff-20260920-180603`。
`tasks.json` 记录任务与档位；`startup-verification.json` 记录真实模型头和进程；`workers/*/seed-manifest.json` 记录源码来源及哈希；`baseline` 保存本次交接前源码。
`provider-policy.json` 和项目 `AGENTS.md` 保存最新规则。`run_worker.py` 明确拒绝其他模型、低档位及重复启动；没有自动降档或跨提供方回退。
