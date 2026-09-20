# Lean Swarm：依赖驱动的证明流水线

默认使用 gpt-5.6-luna，并显式选择 high、xhigh 或 max。历史 Grok 记录保留，但当前额度策略暂停新的 Grok 任务，不自动回退其他模型。

## 并行与资源

模型并发和派发预算均以 0 或 unlimited 表示不设人为数量上限，默认无限。取消旧的 Luna 最大 8、派发器最大 32 限制。显式正数仍可用于用户临时指定的预算。

这不代表无限内存。可用内存和启动中的预留量不足时暂停新领取，不终止已有工作。模型、编译、验收、集成分别调度；默认共享编译槽为 6、验收槽为 2，Git 集成是单写者。集成期间继续派发无关就绪任务。

固定任务流程：冻结目标与依赖 → 隔离工作区 → 模型交卷 → 独立编译及传递公理检查 → 集成 → 解锁下游。

探索任务流程：接管旧工人 → 确认进程退出 → 冻结源码快照 → 独立验证 → 显式语义审查 → 核对实际提交 → 发布接受门。进程退出成功不等于证明成立。

调度优先考虑明确优先级，再考虑未完成下游关键链及解锁范围。前置依赖必须真实集成；仅通过单文件编译、没有文字 sorry 或报告称完成都不会解锁任务。

## 统一状态

所有正式任务、探索交卷和接受门都登记在用户级 control.sqlite3。事务领取避免重复任务。旧批次的导入是幂等操作，不重启已有模型；它也不会把旧报告自动转换成已完成定理。

固定声明的 proof-body 验收保留全部原始定义、导入和结论。多文件探索允许发现错误陈述，但改动需要额外语义审查，不能自行宣称修正后的命题就是原题。

## 使用入口

在仓库根目录执行：

```bash
python3 tools/lean_swarm/cli.py limits --luna unlimited
python3 tools/lean_swarm/cli.py pause-model grok --reason 'Quota exhausted; Luna only'
python3 tools/lean_swarm/cli.py init PROJECT /absolute/config.local.json
python3 tools/lean_swarm/cli.py enqueue PROJECT /absolute/frozen-cards.json
python3 tools/lean_swarm/cli.py run PROJECT --jobs unlimited --integrate
python3 tools/lean_swarm/status_report.py --project PROJECT
```

本机配置包含 repo、integration_branch、package_dir、lean_bin、lean_path、mathlib_source、codex、grok；luna_model 必须等于 gpt-5.6-luna。模型认证文件只留在本机，不上传仓库。使用固定工具链和已验证基线，不自动清缓存或升级依赖。

任务卡字段保留 id、source、target_path、target_name、depends_on；source 只允许 SWARM_PROOF_BEGIN/END 之间的证明体由工人编辑。省略 model 默认 luna。可显式指定 reasoning_effort，或 difficulty 为 integration/proof/foundation，分别选 high/xhigh/max。无效模型或档位直接失败，不回退。

新增 write_paths、resource_locks 用于禁止冲突工作同时领取；estimated_seconds 只是排序权重，不是给用户的完成时间承诺。integrated_gates 用于依赖已经审查并实际提交的探索成果。

## 接管已有批次

```bash
python3 tools/lean_swarm/cli.py adopt PROJECT /absolute/old-batch
python3 tools/lean_swarm/cli.py research-status PROJECT --poll
python3 tools/lean_swarm/cli.py run PROJECT --jobs unlimited --integrate --watch \
  --handoff-root /absolute/old-batch --verification-plan /absolute/trusted-targets.json
```

普通 run 是有限批次；只有显式 --watch 才运行本机持续监督循环，直到收到停止信号。它不会跨对话由聊天助手偷偷重新派单。已有工人只登记和观察，不重新启动；新固定任务由统一队列领取。监督器有单实例锁，独立验证结果和失败记录持久保存，失败交卷不会无限自动重试。

trusted-targets.json 是由协调者审阅后提供的对象，键为研究 job_id 或 task_id，值为非空列表，每项包含 path 和 name。自动验证可以收集、编译与审计，但不会自动批准数学语义或集成多文件探索结果。

```bash
python3 tools/lean_swarm/cli.py research-verify JOB_ID /absolute/targets.json
python3 tools/lean_swarm/cli.py research-approve JOB_ID --manifest SHA256 \
  --reviewer NAME --notes 'signature and definitions reviewed: ...'
python3 tools/lean_swarm/cli.py research-integrated JOB_ID COMMIT
```

最后一步只核对已经存在的提交，要求全部冻结源码逐字匹配、提交属于集成分支历史、独立编译及目标公理检查成功。它不会代替人工审查，不会帮忙把尚未证明的假设改成已完成。部分文件通过必须作为独立审查成果处理，不能把整份交卷标成完成。

## 正确性、缓存和恢复

只允许标准公理 propext、Classical.choice、Quot.sound。源码包含显式证明洞的整份探索交卷不能获批。即使目标文件无 sorry，只要依赖链含 sorryAx，也会拒绝。

固定前置证明的可信缓存使用源码、递归依赖、模块标识、固定工具链、编译选项及基线信息形成内容键，并校验完整对象文件组合；不采用工人的缓存。新 Lean 输出目录私有，写入前断开依赖缓存的文件链接。

编译资源锁位于用户 state root 的 locks/resources，不能使用 systemd PrivateTmp 中彼此隔离的临时锁。工人只获该锁目录的额外写权限，不获整个调度数据库和可信缓存的写权限。

超时、崩溃及未知进程状态保留证据，不因心跳超时就擅自释放并重复启动。历史任务和显式 Grok 分配保持原样。对已经损坏的数学陈述仍需协调者判断；本工具不宣称完备的恶意模型安全隔离，也不会自动发现完整庞加莱证明。

## 测试

```bash
python3 -m unittest discover -s tools/lean_swarm -p 'test_*.py' -v
```

单元测试不消耗模型额度。真实 Lean/Git 流水线及反例验收使用独立临时仓库，明确记作工程测试，不计入数学成果。
