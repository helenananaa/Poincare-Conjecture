# 并行证明环境交付与验收记录

日期：2026-09-19。仓库：`helenananaa/Poincare-Conjecture`。

## 仓库与成果保全

先建立自己的 fork，再发布本地已经验证的 17 个提交。原始快照为 `5e9b6c9`，保存在 `snapshot/20260919-local-proof` 和标签 `proof-baseline-20260919`。未向上游创建 PR。
九个旧 worktree 的源码、文档、未提交改动及 Git 状态均有私有本机备份，压缩包校验和与完整历史 bundle 均验证通过。旧目录和依赖缓存路径保留；主工作流改用独立 integration 工作区，未清理或覆盖旧草稿。上游 push URL 已在本机禁用。
原证明包重新构建，通过 19 组 sanity 测试、364 项目标传递公理审计及原有依赖感知验证门。Mathlib 缓存沿用固定版本，不声称每个外部依赖都从零重建。

## 已实现的并发闭环

全局 SQLite 原子领取与持久化；Luna 默认 4、硬配置上限 8，Grok 默认 4；前置证明必须先集成才解锁下游；固定陈述、独立 worktree；系统服务 cgroup 约束；每个 Grok 任务使用独立 leader；冻结交卷、停止后台进程、独立 Lean 校验；单写者集成队列；崩溃恢复与额度暂停。
并发上限只统计本工具管理的任务，不能把用户另外启动的 CLI 自动计入。任务卡、公共定义和验证器仍需可信审查；这不是无人监督、能够自行设计全部数学架构的系统。

## 测试结果

- 21 项单元测试通过，含跨两个项目/多个 OS 进程的共享并发上限、不可重复领取、依赖只在集成后解锁、不可变任务、额度暂停、陈述篡改拒绝和缓存隔离。
- 真实进程故障测试通过：双重 fork 后脱离父进程的写入者，在超时冻结后不再写入；整个 cgroup 停止后才释放槽位；失联调度器恢复遵守同一顺序。故障测试未调用真实模型。
- 三个工程验收任务、三个真实项目任务均已独立验证并集成。下游提交确实以两个前置提交为祖先，实际导入并使用前置引理。

| 项目 | 任务 | 模型 | 模型运行秒数 | 集成提交 |
|---|---|---|---:|---|
| 工程验收 | `consumer` | luna | 54.1 | `1e762fe` |
| 工程验收 | `period` | grok | 69.4 | `a2bde74` |
| 工程验收 | `transport` | luna | 78.3 | `bb83eba` |
| 真实 collar 子任务 | `collar-closure` | luna | 92.1 | `2bf0f2f` |
| 真实 collar 子任务 | `collar-negative` | grok | 169.1 | `35be5d5` |
| 真实 collar 子任务 | `collar-positive` | luna | 68.9 | `73eba37` |

耗时只对应客户端运行，不含排队、重新验证和项目构建；不用于推算整个项目完成时间。

## 实际发现并修复的问题

第一次真实项目验收中，新增 `.olean` 目录遮住了相同 Lean 命名空间的原有缓存。模型提交本身未因此被修改；修复为完整的文件级链接缓存视图后，使用原始冻结交卷重验通过。原失败记录仍保留，数据库增加重验事件，没有让模型重新做同一道题。

## 新的数学产物与边界

新增 `CollarPositiveSide.lean`、`CollarNegativeSide.lean`、`CollarClosureHalfSpace.lean`。给定真实单侧 collar 及某中心点与补分量边界的接触，证明补分量在 collar 内恰对应正参数半边，补分量闭包恰对应非负参数半边。
这些结果仍以给定 collar 为输入，不构造 collar 的存在性、全局带边界光滑图册、强 Ricci neck、手术流或完整庞加莱形式化。没有因此新增 blueprint 完成标记。

## 复现

本机的账户、路径配置、原始会话与数据库保留在仓库外。通过 `tools/lean_swarm/cli.py status PROJECT` 查看状态；通过 `verify_cards.py` 在固定环境重编译已集成目标，不调用模型。
```bash
python3 -m unittest discover -s tools/lean_swarm -p 'test_*.py' -v
python3 tools/lean_swarm/verify_cards.py --config /path/to/swarm.local.json \
  --cards tools/lean_swarm/examples/acceptance.json tools/lean_swarm/examples/collar-closure.json
```

本轮批次已经结束，没有设置定时任务或持续花费额度的后台派单服务。独立服务停止状况及各目标公理集合见 `setup-report.json`。

## 最终回归确认

新模块已从主包入口导出。合并后再次通过完整主包构建、原有 19 组 sanity 测试、364 项既有公理依赖审计和上游验证门；六个新增目标在独立的固定缓存视图中全部重编译并审计通过。见 `final-regression-verification.json` 与 `six-target-recheck.json`。
