# 第五轮：九项局部义务实收、有限光滑图册验收接口

## 实际验收

本轮正常读取 round3/round4 的四份验收元数据及完整证明源码。
四项的冻结声明前后缀、交卷哈希、独立验收哈希均匹配；重新从源码编译到本轮私有产物，逐一导入精确编译目标检查公理，全部通过。

| 任务 | 内容 | 本轮状态 |
|---|---|---|
| d27r3-negative-half-collar | 同一颈的负侧反射，精确保留中央切片和半领圈参数 | ACCEPTED_ISOLATED |
| d27r3-side-interior-atlas | 去边界闭侧与实际开放部分的同胚、图册搬运 | ACCEPTED_ISOLATED |
| d27r4-finite-timeline | 有限事件排序、逐跳跃及空隙区间的真实拼接 | ACCEPTED_ISOLATED |
| d27r4-cap-relabeling | Alexander 延拓后的实际封帽商同胚，保留包含公式 | ACCEPTED_ISOLATED |

证据：`four-source-recheck.json`、四组 compile/audit 日志、`semantic-review.json`。
旧五项继续复用其已验收源和产物，并复核源哈希；本轮没有重复宣称全部外部库重新编译。
所有本轮目标的公理均只含 propext、Classical.choice、Quot.sound。
共享调度器仍显示 VERIFIED，因为隔离验收不是 Git 集成。

## 实际消去父节点参数

`AcceptedNine.lean` 的 9 个声明通过源码编译及传递公理检查。
`checked_neck_cut`、`checked_neck_connectedSum`、`checked_neck_factors_simplyConnected` 不再有负侧半领圈或内部图册的开放参数。
`checked_projection_trace` 真正代入时序和封帽重参数化结果；对同一给定投影，仍明确要求空终态和统一事件预算。
`public_after_nine` 只剩三项大型研究输入，返回原始 TopologicalPoincareStatement。
这不是已经构造了实际 Ricci 流，也不是无条件庞加莱证明。

## 光滑化接口的准确范围

`FiniteSmoothingAtlas.lean` 的 5 个声明也通过源码及公理检查。
其中 `FiniteAtlasCandidate` 只记录有限张实际拓扑坐标图及覆盖，不含光滑性。
`SmoothTransition c i j` 固定同一个候选图册 c 的坐标过渡，要求属于标准 C-infinity 结构群胚。
`finiteAtlas_smoothing` 将所有这些过渡证明实际组装为 V1 Smoothing。
反方向 `finiteAtlas_of_smoothing` 通过紧致性提取有限子覆盖。
因此 `smoothing_iff_finite_compatible_atlas` 是已证明的双向等价；有限图册生产者不是新增已完成定理，也不代表三角剖分已经给出可用光滑图册。
不能先选择任意拓扑图册，再假设其坐标过渡可由工人证明为光滑。

## 文献路线复核与减负

公开来源：Christian Lange, arXiv:1507.02395v2，§2.2、§3.2、§3.4；本轮读取了 PDF 提取文本。
原文区分拓扑同胚、分片微分 PD 兼容性与光滑结构，并提示直接径向延拓不能自动保证 PD 非退化性。
项目 `PLAtlasProducerStatement` 的精确结论只有 `Nonempty (Smoothing M)`，不要求原剖分的逐单形光滑/PD 兼容性。
因此不能把完整等变光滑化或所有 PD 延拓工作设为默认必做项。
但拓扑填球也不能直接充当对已有外部光滑结构兼容的填球；重叠区必须由具体构造给出可审查的光滑过渡。
这一减负是对本地目标与文献要求的比较，不是三维光滑化生产者已经证明。
文献截图请求返回 Internal Error；Thurston 书本 PDF 获取没有成功，本轮不声称复核其图示或完整证明细节。

## 未放行的新工作

本轮 `ready-proof-cards.json` 是空列表：没有启动新工人、没有更换默认模型或重启旧任务。
此前四个新返回任务现均已接受为隔离成果。最后进程观察没有在运行的证明工人。
下一批应先研究具体的 PL 图册/相对光滑化构造，确定实际过渡映射，再固定其必要子命题。
同一套 PL/link 定义必须由三角剖分生产者输出并由光滑化生产者消费，不能用普通球面同胚偷换 PL 数据。
几何生产者的 PDE、手术存在、空终态、实际度量测度预算和穷尽终端分类仍未完成。

## 冻结、保存与范围

`frontier.dag.json` 是本轮 16 节点的摘要图，开放研究输入仍为 3 个；节点数不表示数学完成比例。
`frontier.lock.json` 保存两模块、四项新验收源码和产物哈希，并引用既有冻结快照；ops 保留独立副本。
旧 V1 的 13 个文件与前三/四轮已冻结来源均未改写，公开结构冻结检查 PASS。
新代码全部留在 `reports/decomposition-20260927/round5/`，未导入主包、未改公开绑定或 blueprint。
没有全量依赖重建、Git 集成、提交、远程推送或上游 PR。
公理检查证明的是精确形式化声明；仍需后续生产者和图册构造满足相同定义与参数，不能据此声明 Poincare 完成。
