# Lean Swarm：固定目标的并行证明调度

本工具使用本机已登录的 Codex / Grok 会员 CLI，不需要 API key。它不自动推送、不创建上游 PR，也不宣称完成庞加莱形式化。

## 已实现的边界

所有 CLI 调度进程共用 `~/.local/state/lean-swarm/control.sqlite3`。SQLite 原子事务负责领取任务、跨项目和跨进程的并发上限、依赖检查、额度暂停和失败记录。Luna 默认 4、可配置上限 8；Grok 默认不设置模型级并发上限（数据库中 0 表示 unlimited）。上限只统计本系统管理的任务，不统计用户另行启动的会话。过期心跳本身不会释放一个可能仍在执行的任务。

任务卡注册后不可修改；依赖必须达到 INTEGRATED 才能解锁下游。每次尝试创建独立 Git worktree。worker 只允许填充固定定理的 proof body，不允许改定义、依赖版本、公共接口或现有生产文件。需要改变架构的任务必须先单独审查。

每个实际模型任务在独立 systemd service/cgroup 中运行，Grok 使用独立 leader socket。超时先冻结进程组、保存候选快照，再终止整个进程组。不能确认已停止时，保留 RUNNING 槽位，不自动启动替代任务。超时结果不会因为事后能编译就自动视作成功。

验收方从候选中提取 proof body，放回原始导入、定义、陈述和后文，重新编译并检查目标声明的传递公理。允许集合仅为 `{propext, Classical.choice, Quot.sound}`。已完成的前置任务从记录的 Git 基准重新读取并编译，不信任 worker 修改的依赖源码。

集成采用单写者锁，检查工作区干净和分支正确，复核依赖及 proof，执行配置中的项目构建检查，再仅提交已验收的新文件到 integration。失败不会对整个仓库执行 reset/clean。

## 本机使用

在 fork 根目录：

```bash
python3 tools/lean_swarm/cli.py status poincare-acceptance-20260919
python3 tools/lean_swarm/cli.py limits --luna 4 --grok unlimited
python3 tools/lean_swarm/cli.py run poincare-acceptance-20260919 --jobs 4 --integrate
```

`run` 执行有限批次，不是后台定时服务。命令退出后不会自行继续派发新任务。所有生产 CLI 使用同一固定的用户级注册表。

新项目需要本机配置 JSON，字段为 `repo`, `integration_branch`, `package_dir`, `lean_bin`, `lean_path`, `mathlib_source`, `codex`, `grok`，以及可选的 `luna_model`, `grok_model`, `integration_command`。路径指向经过验证的固定 Lean/Mathlib 缓存。`repo` 必须是检出的集成工作区；不允许把 main 直接作为集成分支。本机配置放在仓库外，不能上传会员登录文件。

```bash
python3 tools/lean_swarm/cli.py init PROJECT /path/to/config.json
python3 tools/lean_swarm/cli.py enqueue PROJECT /path/to/tasks.json
python3 tools/lean_swarm/cli.py recover PROJECT
python3 tools/lean_swarm/cli.py retry PROJECT TASK
python3 tools/lean_swarm/cli.py resume-model grok
```

任务卡是 JSON 列表，每项包含 `id`, `depends_on`, `source`, `target_name`, `target_path`；`model` 可选，省略时为 `grok`，也可显式指定 `luna`。另可提供 `hint` 和 `timeout_seconds`。路径相对 Lean package。source 内恰有一对 `/- SWARM_PROOF_BEGIN -/`、`/- SWARM_PROOF_END -/`。需要改变陈述时使用新任务编号，不修改已注册的目标。

示例 `examples/acceptance.json` 是工程验收题，不是新的庞加莱里程碑；consumer 实际导入两个已集成的 producer 文件，检验依赖编译和串行集成。

## 信任和环境要求

需要 Linux/systemd，以及机器上已经具备的免交互 systemd-run/单元控制权限。本工具不会新增宽泛的 sudo 规则。模型服务以普通用户运行，设置 NoNewPrivileges、系统/家目录只读和独立临时目录；仅工作目录与 CLI 自身状态目录可写。

这不是针对恶意 agent 的完备安全证明。认证 CLI 仍须访问自己的账户状态，因此不要给 worker 未审查的插件、外部工具或额外秘密。它隔离仓库写入和后台进程，但不能替代对任务语义和新公共定义的审查。

每题复用固定依赖缓存，重新编译新前置引理和目标；不是每题从零重建整个 Mathlib。崩溃恢复先核对调度器 PID 和启动时间，再终止其真实进程组，最后才释放任务。集成失败保留可审查状态，不盲目改代码重试。

## 测试

```bash
python3 -m unittest discover -s tools/lean_swarm -p 'test_*.py' -v
```

单元测试不需要模型账户、网络、Lean 或 sudo；实际模型验收和 cgroup 故障测试另外记录在 `reports/parallel/SETUP_REPORT.md`。原始会话日志留在本机，不上传。

## 固定交卷的基础设施重验

若任务因为验证环境错误成为 FAILED，可在修复验证器后运行 `cli.py reverify PROJECT TASK`。此操作校验原冻结交卷哈希、重编译并记录重验事件，不调用模型，不覆盖原失败证据。TIMEOUT 任务不能通过这个入口晋升成功。

完整命名空间缓存视图采用文件级链接，输出目录私有；写新的 `.olean` 前断开相应文件链接，不修改被固定的依赖缓存。这避免新模块局部目录遮住原有同名命名空间。

本仓库已验证的固定目标可用 `verify_cards.py --config CONFIG --cards CARDS...` 在不调用模型的情况下重新检查。`fault_checks.py` 和 `containment_checks.py` 是真实 systemd/cgroup 故障测试，接受 `--config CONFIG --output NEW_DIRECTORY`，只启动合成进程，不消耗模型额度。

## Grok 优先与无模型级上限

新任务省略 `model` 时默认使用 Grok；已注册任务保持原分配。`limits --luna 4 --grok unlimited` 取消 Grok 的模型级上限，但不会取消 `run --jobs N` 的实际工作进程预算、依赖门或额度暂停。不要一次启动超过本机内存与编译能力的任务。Luna 仍有最多 8 个受管理并发的限制。
