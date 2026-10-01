# 证明完成（第十九批 + 最终核验，2026-10-01）

**定理 1 已在对象 KPω 中得到完整证明。**

```lean
-- KP1Y/OneYMainTheorem.lean
theorem KP1Y.OneYTheorem.theorem1_derivable : KP1Y.Derives mainSentence
theorem KP1Y.OneYTheorem.main_semantic_actual_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory) : MainSemantic M
```

- 无剩余前提：Y05b 由 `terminal_exits_d`（LANE-D）与 `lower_steps_d`（LANE-B/B2/F）解除，经 `canonical_copy_bound` → `copy_descent` → M02/M03 → 闭句。
- [第十九批](../parallel-stage-19.log)：567 模块 PASS；**[冷启动全量复核](../final-cold-stage.log)：567 checked / 0 cached PASS**；[审计](../final-audit.log)：4,216 项声明，公理之并恰为 {propext, Classical.choice, Quot.sound}。
- 忠实性：[Q01 审读](FINAL-STATEMENT-REVIEW.md) 无 FINDING；[复制塔独立复核](review/COPY-TOWER-FIDELITY.md) 无差异，差分 223,952 例 0 不符。
- 最终记录与复现命令：[FINAL-VERIFICATION.md](FINAL-VERIFICATION.md)。

---

以下为完成前的交接历史。

# 当前完整证明交接（第十八批，2026-10-01）

目标仍 active。唯一剩余数学关口为 **Y05b 的两个打包前提**。

## 最新可复查证据

- [第十八批阶段核验](../parallel-stage-18.log)：**524 项冻结根闭包，17 checked / 507 cached，PASS**；[审计](../parallel-audit-18.log)：**3,981 项声明**，仅 propext、Classical.choice、Quot.sound。
- LANE-C 全塔规范性 13 模块已集成：`CanonicalExpansion.canonical_copy_bound_last_d (hExits : TowerCanon.TerminalExits M) (hLower : LowerStepsIn M) : CanonicalCopyBoundLastIn M`。
- 协调者接口修改：`CopyDescent.CanonicalCopyBoundIn` 在 `Successful` 后增加前提 `M.SuccessorOf m last`（Terminal 复制需要；坏根分支调用处本有此事实），`bad_branch_d` 相应传入。
- 汇合模块 `KP1Y/OneYMainAssemblyCanonical.lean`：

```lean
theorem main_derivable_of_steps
    (hExits : ∀ M : SetTheory.Structure.{0}, M.Models KP1Y.theory → TowerCanon.TerminalExits M)
    (hLower : ∀ M : SetTheory.Structure.{0}, M.Models KP1Y.theory → CanonicalExpansion.LowerStepsIn M) :
    KP1Y.Derives mainSentence
```

- **剩余**：`terminal_exits_d`（LANE-D：H2、H3 已落地，H1、H4 进行中）与 `lower_steps_d`（LANE-B 汇总；B2 阻挡/nonroot 已交付、bottom/down 进行中；F 助手 PseudoTopBound/extract 进行中）。
- Q01 忠实性审读与复制塔独立复核均无差异（见 FINAL-STATEMENT-REVIEW.md、review/COPY-TOWER-FIDELITY.md）。

## 当前通道

| 通道 | 状态 |
|---|---|
| B | Y05b Lower：深度/Key/伪父链/TopBound 及 `lower_layer_step_d`（OneYLowerCanon*、OneYLowerLayer*） |
| B2 | Y05b Lower 阻挡 DecoratedBlockers 与底行恢复/运输（OneYLowerBlock*、OneYLowerBottom*） |
| C | 已完成并集成（第十八批）：全塔汇合 canonical_copy_bound_last_d |
| E | Q01 已完成：无 FINDING（tracker/FINAL-STATEMENT-REVIEW.md） |
| A | 独立复核已完成：无算法差异；`tracker/review/kpsim.py 7 6 jsref.cjs` 对 y1/engine.js 差分 223,952 例 0 不符 |
| F | LANE-B 助手：Lower 伪父链与 TopBound（OneYLowerHelp*；lower_layer_pseudo_top_bound_d、lower_layer_extract_d） |
| D | LANE-C 助手：Terminal 底行四出口 H1–H4（OneYCanonHelper*） |

完成后：协调者把 `canonical_copy_bound_d` 接入得到无条件 `main_derivable : KP1Y.Derives mainSentence`，再做 Q02 全量增量核验与审计。

---

以下为更早的历史交接，状态以上方为准。


目标仍 active。本会话（Claude Code）由 root 协调，六个 worker 并行；未达完成判据前不报告完工。

## 最新可复查证据

- [第十二批阶段核验](../parallel-stage-12.log)：**484 项冻结根闭包，21 checked / 463 cached，PASS**。
- [公理审计](../parallel-audit-12.log)：**3,685 项所列声明**，仅 propext、Classical.choice、Quot.sound。
- [本批清单](parallel-stage-12.json)：20 个模块（Splice几何、三分支Nested、Ordinary规范性、Lower值/深度/伪父/TopBound/UpperInputs、Terminal TopBound、Recovery/Extraction、FrameCopy、ExpansionCanonical 首段）。
- `OneYCopySpliceGeometry` 的唯一编译错误（`CopiedFacts` 为存在式，无 `.diagram_d` 字段）已改用 `copied_facts_exists_d`+`CopiedFacts.unique` 修复。Y04d 验收完成。
- 新协调工具：`python3 tracker/integrate_stage.py N 模块…`（或 `--all-unintegrated`）写根 imports、Audit 名单与 parallel-stage-N.json；随后照旧 `check-module.sh KP1Y.lean --emit`、`verify-local-stage.py --root KP1Y`、`refresh.py --audit`。

## 六条通道（文件按前缀独占，交接见 tracker/handoff/LANE-*.md）

| 通道 | 任务 | 独占文件前缀 |
|---|---|---|
| A | Y04b 精确Adm/FR拼接/全部内部N对象归纳 → Y06 引理3 | OneYCopySeams*、OneYCopyDescent* |
| B | Y05b 逐层 Lower：深度/Key/伪父链/TopBound 及 lower_layer_step_d 组装 | OneYLowerCanon*、OneYLowerLayer* |
| B2 | Y05b Lower 阻挡（DecoratedBlockers）与底行恢复/运输 | OneYLowerBlock*、OneYLowerBottom* |
| C | Y05b Terminal 层、k≥K 塔、全塔汇合、A(E_N(s))⊆复制图 | OneYTerminalBase*、OneYTerminalTower*、OneYTowerCanon*、OneYCanonicalExpansion* |
| D | 共享 RankWitness、Y08 计算绝对性、M03 回传 | OneYRankStatement*、OneYInnerAbsoluteness*、OneYRankTransfer* |
| E | M04/M04b 实例化、M05 纯∈闭句与 Derives、Q01 草稿 | OneYTheorem*、OneYWellFounded*、OneYWellOrdering*、FINAL-STATEMENT-REVIEW.md |
| F | Y07a/Y07b 前缀单调、E0可达、字典序下降、种子 | OneYExpansionOrder*、OneYSeeds* |

允许的临时命名接口（必须由协调者最终接上，不能留在主定理中）：A 的 `hCanonical`（Y05b 边包含）；C 的 `∀k<K, LowerLayerStep`（由 B 交付）；D 的 M03 以 M02 精确命题为唯一前提；E 的 `OrderFacts`（由 F 交付）及 RankWitness 回传结果；F 的首接缝值（若 C 未导出）。

已集成文件全部只读；worker 仅新建自己前缀的文件。


以下为第九批及更早的历史交接，状态以上方为准。

# 当前完整证明交接（第九批，2026-09-14）

目标仍 active：完成文稿实际 1-Y 算法在对象 KPω + 存在不可数序数中的完整证明，包括实际 μ、全部内部 N、L 回传和纯 ∈ Hilbert Derives。不能以条件接口或宿主良基性替代。当前回合有实质进展，不标 complete/blocked。

## 最新可复查证据

- [第九批增量核验](../parallel-stage-9.log)：**445 项冻结根闭包，7 checked / 438 cached，PASS**。
- [公理审计](../parallel-audit-9.log)：**3,264 项所列声明**，仅 propext、Classical.choice、Quot.sound。
- [本批模块与声明清单](parallel-stage-9.json)。前两批为第八批 439 / 3,154，第七批 429 / 2,892。
- 根导入和审计证据匹配。源码总数包含 WIP，不等于已集成数。
- 没有 lake build 或第三方重建。日常 `python3 tracker/refresh.py` 不调用 Lean。
- 看板 **90 节点，17 项必要实现工作包未完成**；工作包大小不同，此计数不是进度百分比或工期。

## 用户对 Z₂ 的澄清

用户明确已有任意有限 n-row BMS 在 Z₂ 下可证明终止的结果；相应 0-Y(1,n) 终止性覆盖所有 n。`PTO(BMS)=PTO(Z₂)` 是猜想。详见 [复用记录](Z2-REUSE-REVIEW.md) 和 [基础库报告](../LIBRARY-AND-REUSE.md)。

接入对象推导时核对逐 n 可证明性族与理论内部统一 ∀n 的量词区别、算法版本及初始状态范围，不擅自升级量词，也不加入新公理。当前原 1-Y 有限复制下降调用链消费有限结构引理，不消费 WF(0-Y/BM4) 出口。

## 已完成的主线边界

1. 对象 KPω（含完整集合归纳）、内部算术/有限序列/递归、实际 L 与内部 KPω+V=L、相同 ω/序数、κ≤ν 及统一枚举。
2. 实际 R/FR 表、公式编译、完整反射 (7)/(8)、内部高度迭代和任意根图的初始表示（C01–C12）。
3. 表达式域、森林/路径/深度/选择、真实行/层运行、高度/顶部/提取、有限预算及坏根搜索。
4. 实际规范图 A(s)：稳定按 (层,列,行) 枚举、精确 EdgeAt 双向对应、保留重复、真实全局 E→edgeLists 图。完整山形与规范图前缀局部性已完成。
5. **实际 μ:E→κ**：最小可实现末标签及其图，空值 0、非空 >ω，每个值有实现表示；**实际展开使 μ 下降仍未完成**。
6. 实际有限矩阵展开、父运行全行族、I/S、empty/delete/copy/trim；独立 Top 图及装饰 S 保持现已集成。Top 不插入局部零行。
7. Ordinary/Terminal/Lower 三种单层复制与实际 **CopyTower 源/目标代码家族**均已集成。
8. **实际数值重建**：有限 Grid、Rebuilds、height=0 恒等、原山形恢复、内部逆向塔迭代、唯一性/合法性/前缀；不使用宿主 fold。
9. 源事实/模板逐位置运输、末列模板稳定过滤、ParentCopy 相邻复制块与 MoveColumn 的精确相容已集成。
10. 实际 SourceGraph/Tower 的 **Δ₀ 集合证书**已集成，完整规格由图总性、像覆盖、真实点计算唯一性恢复。
11. **实际全局 EN:E×ω→E** 已集成：Σ₁ 计算证书、总性唯一、空输入固定、N=0恰为删除末项、全部N保留原前缀，horizon明确等于原max(1,maxValue)。
12. **Terminal低根运输** 已集成：源严格根次序、跨seam的内部列归纳、低seam父/根真实源记录及其对控制根的严格界；通用有限路径的全ω图运输也已集成。
13. 实际 Lex 关系图及严格线性次序基础、L 内有限输入/代码/表达式域闭合已完成；无限算法历史与展开绝对性仍待 Y08。

## 当前唯一文件所有权

所有已有冻结文件只读。以下路径均以 KP1Y/ 为前缀。

| 负责人 | 当前任务 | 独占在写文件 |
|---|---|---|
| finite_port_contract | Y04c：精确虚拟边界 CopyNeeds、稳定枚举及 Template/Adm | OneYCopyNeeds.lean |
| ranked_dynamics | Y04x：Lower实际根/源父记录运输 | OneYLowerCopyRoots.lean；OneYCopyPathTransport.lean已冻 |
| relation_atom_code | Y07r：内部有限展开路径与实际Reach集合 | OneYReachability.lean |
| root | Y04x普通复制根运输、审阅、统一集成及看板 | OneYOrdinaryCopyRoots.lean（已冻，待后续批次集成）；KP1Y.lean、Audit.lean、tracker 和全局文档 |

root 的 OneYAtomTransport、OneYCopyInvariant、OneYCopyIterationFacts、OneYCopyTowerCertificates 均已冻结且集成。worker 不改这些文件。Root 不改其他 worker 独占文件。

## 当前交接接口

### 已集成的展开函数与图层比较

- ExpansionCore 238行/17定理、Prefix 208/13、Expansion 884/51，均已冻结并集成。
- `Expansion.expansion_graph_exists_d hM hC hT` 实际构造 Keys=E×ω 与 EN:Keys→E；`Graph.at_iff` 精确读取 Expands。
- 实际 27字段Box、字面 Δ₀ WitnessMatrix14、`expansion_sigmaOne_iff_d`、Σ₁共同收集；不是把收集或计算总性列成额外前提。
- `Graph.empty_iff_d`、`Graph.zero_iff_drop_d`、`Graph.keeps_prefix_d`；`Horizon.original_sequence_bound_d` 明确非空horizon=max且≥1。
- ForestDecoratedOrder 512行/16定理也已集成：全ω父图KeyLE的Δ₀语法/语义、源/目标矩阵双向字典、实际复制/接缝比较。Y03k完成。
- **规范重新提取Y05b和μ下降尚未证明。**
- relation worker续做OneYReachability：实际内部有限展开路径、Reach集合、反身传递/拼接/首步分解，对接O02；不做词序/Seeds。

### 复制根运输（Y04x）

- root `OneYTerminalCopyRoots` **314行/9定理已集成**。`root_at_strict_rows_d` 用真实RowRun/FromRun/正性证明活跃高度内严格根次序。
- `Copies.low_root_parent_copy_d` 对实际目标列作对象ordinal_induction_d，一次处理非root、root/block0、root/后继seam和无父分支，全部内部block均覆盖。
- `Copies.low_seam_source_d` 从真实目标ParentAt/RootAt返回原末列父、相同原根、ParentCopy父映射、根固定与严格小于原控制根。这是finite的active-layer Virtual/Adm输入。
- ranked `OneYCopyPathTransport` **4公开定理已集成**：路径值=末点或祖先、全ω严格图映射实际有限路径/祖先/根，目标宽度由实际末点收紧。root wrapper的NoParent由使用方真实高度解除。
- ranked继续LowerCopyRoots，root的OrdinaryCopyRoots已完成并冻结，待后续批次集成。两者不改上述已冻文件。

- OrdinaryCopyRoots的`Copies.root_parent_copy_d`与`root_parent_copy_iff_d`双向对应普通复制的真实根；`Copies.row_source_d`从任意实际父/根记录恢复完整源记录，child/parent/root用同一ParentCopy。只需真实Data.Valid和Copies，未要求Numeric。最终单模块--emit exit0、日志空；不为此单文件重跑整个阶段。

### CopyNeeds worker

**精确需求不是原末列边的筛选。** 它读取复制塔虚拟边界列 width(b) 的实际 height/parent/root；通过输出宽度 succ(width(b)) 取得该列，并证明已有列前缀一致。

- k<K：r<实际 height；k=K：r<level 且 r<height；K<k：无项。
- 按 (k,row) 稳定枚举 Packet(k,root,parent)，保留重复。
- Lower 边界 height 随 b 增长，需要从实际高度家族另行有限收集行界，不能复用原 max+1。
- 原末列 `OriginalTemplates` 已构造，仅供后续 Virtual 来源证明，不可冒充 CopyNeeds。
- Terminal最低所需出口已集成；Lower由ranked独占，Ordinary由root独占，CopyNeeds不得复制这些根运输证明。

## 剩余依赖主链

CopyNeeds / 全部复制边分类 → 几何 BlockScheme 与真实 R/FR 拼接；
CopyTower + 实际数值展开 + 图层比较 → 规范重新提取；
两支汇合 → 实际 EN 的复制表示下降 → μ 对所有内部 N 严格下降 → 实际计算绝对性 → 从 L 回传同一 μ 集合 → 具体终止与 Desc(s)/G 良序 → 纯 ∈ 闭句及 Hilbert Derives → 忠实性审读与最终核验。

## 不可丢失的忠实性约束

- 最终句形：`KPω ⊢ ∀ν (UncountableOrdinal(ν) → ∃ ordinal χ≤ν ∃ actual graph μ:E→χ, …)`，ν 不得游离。
- E 是空序列或内部有限正自然序列且首项为 1；全部长度/N 均取模型内部 ω，无 ω 标准性。
- N 为额外复制次数，N=0 删除末项，空输入固定。良序对象仅 Desc(s)、G，不能扩大到全部 E。
- 禁用对象 AC、powerset、完整 replacement/separation、宿主 WF(mem)；KP 包含完整 set induction。
- 原 sequenceBound 为 `max 1(maxValue s)`，本项目图预算为 strict max+1；二者不可直接认相等。
- 原 raw source 范围为 (root,last]，ordinary 块范围为 [root,last)；raw seam source=last/block=b 对应 ordinary root/block=b+1。
- Lower 保留 c≤last；Terminal 保留 c<last，高 seam 的父项读取原 root 且不平移。
- 相同 ω 不能单独推出所有无限算法历史绝对；后续要以内部存在 + 向上 Σ₁ 绝对性 + 外部唯一性证明，并回传实际 μ 集合。

## 核验与续派

```bash
./check-module.sh KP1Y/OwnedModule.lean --emit > OwnedModule-check.log 2>&1
# 仅 root 冻结阶段使用，依赖未变项命中缓存
python3 verify-local-stage.py --root KP1Y
python3 tracker/refresh.py --audit
# 日常看板更新，不调用 Lean
python3 tracker/refresh.py
```

第九批 stage/audit 均已结束，无 root 检查进程。所有 worker 已获恢复检查通知。续做先查 collaboration.list_agents；completed/idle 必须 followup_task，send_message 不启动回合。看板是有证据的交接快照，不是实时进程监控。
