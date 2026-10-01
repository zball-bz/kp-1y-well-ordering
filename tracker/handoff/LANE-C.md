# LANE-C 交接（Y05b：Terminal/上层塔、整塔汇合、规范重提取）

状态：汇合链已闭合（除 H1–H4 外无其他缺口；见「最终导出定理」）。LANE-C 现有空闲，可接手 H3/H4 中助手尚未开始的部分（请协调者指定，避免重复）。以下每个模块均按 `./check-module.sh KP1Y/X.lean --emit > X-check.log 2>&1` 单独检查。

## 已完成模块（全部 `./check-module.sh KP1Y/X.lean --emit` exit 0，日志空；公理仅 propext/Classical.choice/Quot.sound）

| 模块 | 内容 |
|---|---|
| `KP1Y/OneYTowerCanonInterface.lean` | 逐层接口：`UpperSelect`、`LowerInputs`、`LowerLayerData`、`LowerLayerStep`（LANE-B 目标） |
| `KP1Y/OneYTowerCanonAssembly.lean` | `LayerCanon`/`SelectNext`/`BaseSelect`；对象归纳 `tower_layers_d`（t 的第k层=(Hr(k),塔码底父图)）、`tower_top_layer_d`（第B层=全1）、`tower_atom_d`（t 的每个 ActualAtom 是复制塔 `CopyDiagram.Atom`；k≥B 层由全1与层值反单调无边） |
| `KP1Y/OneYTowerCanonInduction.lean` | 任意对象公式的有界反向归纳 `backward_induction_d`（对间隔 j 作对象自然数归纳 ∀x∈ω(x+j=top→φ(x))，`Formula.rename`） |
| `KP1Y/OneYTowerCanonSetting.lean` | `Setting` 数据包（源 LayerRun、坐标、`m=last+1`、BadAt、N/Width、SequenceBound/horizon、Tower、重建 Run、全1 Top）及读数引理（`active_lt_d` K<B 等） |
| `KP1Y/OneYTerminalTowerOrdinary.lean` | `Setting.ordinary_values_d`：K<k≤B 时 Hr(k)=源第k层值的普通 `ValueCopies`（反向归纳，字面模式） |
| `KP1Y/OneYTerminalTowerUpper.lean` | k>K 的 `ordinary_canon_d`/`ordinary_select_d`；`terminal_new_top_d`（Hr(K+1)=CopiedTop）；`terminal_canon_d`（k=K 的 LayerCanon） |
| `KP1Y/OneYTerminalBaseTopForest.lean` | 严格高度帧收缩：`select_of_refinements_d`、`actual_top_forest_select_d`、`actual_top_parent_iff_d`；`Setting.terminal_select_d`（k=K 的 SelectNext：Terminal 高度/连通根是普通复制 ⇒ 选择是源 K+1 层父图的普通复制） |
| `KP1Y/OneYTowerCanonLowerFormula.lean` | lower 输入主体 `InputsBody`/`InputsAt`/`RawCopy` 的字面对象公式及 FreeClosed/iff |
| `KP1Y/OneYTowerCanonExits.lean` | Terminal 出口 H1–H4 的精确命题 `TerminalBaseContext`、`TerminalExits`（助手 LANE-D 证明） |
| `KP1Y/OneYTowerCanonLowerSchema.lean` | 模式 `inputsSchema`、`raw_copy_iff_d`、`InputsBody.lower_inputs_d`、`inputs_body_of_d`、`terminal_rebuild_prefix_d` |
| `KP1Y/OneYTowerCanonLowerInduction.lean` | `Setting.lower_inputs_d`：对间隔的对象反向归纳，顶层由 H1–H4、其余由 `LowerLayerStep.bottom/nonroot/down` 与通用前缀保持推出 |
| `KP1Y/OneYTowerCanonLower.lean` | lower 层 `lower_canon_d`/`lower_select_d`、`base_select_d`、全塔 `Setting.tower_canon_d`（三分支全覆盖） |
| `KP1Y/OneYCanonicalExpansion.lean` | 最终出口（见下） |

## 最终导出定理（已检查）

```lean
-- KP1Y.OneYFinite.CanonicalExpansion
def LowerStepsIn (M) : Prop := ∀ E T, E.Valid M → T.Valid M E → ∀ s m last N t (W : Expansion.SuccessData M.Domain),
  Expansion.Successful M E T s m last N t W → ∀ k, M.mem k W.K →
    TowerCanon.LowerLayerStep M E T W.coordinates m W.space W.layers W.K k N W.width
def CanonicalCopyBoundLastIn (M) : Prop := -- = CopyDescent.CanonicalCopyBoundIn 但在 Successful 后多一前提 `M.SuccessorOf m last`
theorem canonical_expansion_diagram_d (hM) (hExits : TowerCanon.TerminalExits M) (hE) (hT) (hD) (hOmega)
  (hS : Expansion.Successful M E T s m last N t W) (hSucc : M.SuccessorOf m last)
  (hLower : ∀ k, M.mem k W.K → LowerLayerStep M E T W.coordinates m W.space W.layers W.K k N W.width)
  (hOld : CopyDiagram.Enumerated M E T D ⟨W.horizon,W.width,W.forests,W.codes,W.tower⟩ Old)
  (hGraph : ExpressionGraph M E T D t n B) :
  n=W.width ∧ ∀ k q p c, Reflection.EdgeAt M D B k q p c → Reflection.EdgeAt M D Old k q p c
theorem canonical_copy_bound_last_d (hM : M.Models KP1Y.theory) (hExits : TowerCanon.TerminalExits M)
  (hLower : LowerStepsIn M) : CanonicalCopyBoundLastIn M
```

**接口修正请求（给协调者/LANE-A）**：`CopyDescent.CanonicalCopyBoundIn` 缺少 `M.SuccessorOf m last`
（`Successful` 本身不蕴含 last 是源末列；Terminal 复制与 `terminal_rebuild_rows_d` 必须 `m=last+1`）。
LANE-A 的调用处 `expand_last_representation_lower_d` 在坏根分支已有 `hSucc : M.SuccessorOf m last`，
只需让 `bad_branch_d` 多收一个 `hSucc` 并把接口改为 `CanonicalCopyBoundLastIn`（上面逐字定义）或在
`Successful M E T s m last N t W →` 之后插入 `M.SuccessorOf m last →`。
H1–H4 落地后我将加 `terminal_exits_d (hM) : TerminalExits M` 与 `canonical_copy_bound_d (hM) (hLower : LowerStepsIn M)`。

## 给 LANE-B 的唯一临时接口：`TowerCanon.LowerLayerStep`

命名空间 `KP1Y.OneYFinite.TowerCanon`，文件 `KP1Y/OneYTowerCanonInterface.lean`（逐字定义见该文件）。
LANE-B 的目标定理形状（环境假设可按需增减，但结论须恰为此结构）：

```lean
theorem lower_layer_step_d (hM : M.Models KP1Y.theory) (hC : C.Valid M) (hT : T.Valid M C)
    (hLayers : LayerRun M C m L V P H) (hA : A.Valid M C)
    (hBad : BadAt M C m L H K level A.last A.root) (hN : CopyCoordinates.Width M C T A N n)
    (hk : M.mem k K) : TowerCanon.LowerLayerStep M C T A m L H K k N n
```

字段（全部对任意满足 `LowerLayerData` 的实际对象全称量化）：

* `LowerLayerData M C T A m L H K k n W Q J oldTop Qnext D Y`：`k∈K`；源第k层 `RowAt L.states H k W Q`、
  `RowRun M C m L.rows W Q J`、`FromRun … D.mountain`、源实际提取 `Extraction M C m W Q oldTop Qnext`；
  `D.coordinates=A`、`D.Valid`、`Y.Valid`、`Lower.Copies M C T D n Y`。
* `LowerInputs M C T D m N n oldTop Qnext newTop Pnext`（原 LowerTowerInputs）：
  `prefixTop : RowsAgreeOn newTop oldTop D.coordinates.last`；
  `fixed : Lower.UpperFixed M C T D oldTop Qnext n newTop`；
  `order : ∀ Pseudo, GraphPseudoForest M C D.mountain Pseudo → Lower.UpperOrder M C T D Pseudo oldTop newTop`；
  `select : UpperSelect M C T D.coordinates m N n oldTop Qnext newTop Pnext`，其中
  `UpperSelect … Vnext Qnext newTop Pnext :=
     (∀ F F', Selects true M C m F Vnext Qnext → FrameCopy.Copies M C T A F N n F' → Selects true M C n F' newTop Pnext) ∧
     (∀ s b c, A.root∈s → s∈A.last → ParentCopy b s c → c∈n → ∀ p, (Pnext(c)=p ↔ ∃ q, Qnext(s)=q ∧ ParentCopy b q p))`。
  原 bound（PseudoTopBound）不再作为输入，改由 LANE-B 在 lower 单层内从 `select`（对伪父帧与严格高度帧两次实例化）导出，
  与原 `badAtLowerCopiedBase_lowerTopBound`/`badAtTerminalBase_lowerTopBound` 的证明路线一致。
* `rows`：输入成立且 `Rebuilds Y newTop Bottom` ⇒ `∃ R P Run, RowRun n R Bottom P Run ∧ FromRun … Y ∧ TopValueGraph … Y.heights newTop`（原 copiedBase_mountain）。
* `extract`：⇒ 对 `GraphPseudoForest M C Y G`，`∃ F F', Selects true m F oldTop Qnext ∧ FrameCopy.Copies A F N n F' ∧ ∀ Q', (Selects n G newTop Q' ↔ Selects n F' newTop Q')`（原 copiedBase_rawExtract）。
* `bottom`：⇒ `Selects true m F W Q → FrameCopy.Copies A F N n F' → Y.parents(0)=P0 → Selects true n F' Bottom P0`（原 restrictedParent_bottom_numeric）。
* `nonroot`：`Y.parents(0)=P0`，`A.root∈s∈A.last`，`ParentCopy b s c`，`c∈n` ⇒ `P0(c)=p ↔ ∃q, Q(s)=q ∧ ParentCopy b q p`。
* `down`：`k=succ j`，j、k 两层数据，k层输入，`Rebuilds Y newTop Bottom` ⇒ j层的 `Lower.UpperFixed M C T D' oldTop' Qnext' n Bottom` 与对一切源j层伪父森林的 `Lower.UpperOrder`（原 badAtLowerCopiedBase_upperFixed/_upperOrder）。

LANE-C 自己负责：Terminal 层 (k=K) 的同类出口（rows 已由 `ExpansionCanonical.terminal_rebuild_rows_d` 给出；
select/nonroot/upperFixed/upperOrder 在 `OneYTerminalBase*`），K 以上普通层，及由 `∀ k∈K, LowerLayerStep` 的对象向下归纳汇合。

## Available for helper（协调者 2026-10-01：可分离子任务，交给助手）

**任务 H：Terminal 底行(k=K)给下层的四个出口**（对应原 TerminalCopyExternal / TerminalCopyExternalSeam /
TerminalCopyBottomRecovery / TerminalCopyBottom / TerminalCopySeamComparison / TerminalCopyTransport /
TerminalCopyUpperOrder / TerminalCopyDepths / TerminalDecoratedRecovery / TerminalFrame*）。
文件前缀：`KP1Y/OneYCanonHelper*.lean`；命名空间建议 `KP1Y.OneYFinite.TerminalBase`。
可 import：`KP1Y.OneYExpansionCanonical`（含 `terminal_rebuild_rows_d`）、`KP1Y.OneYFrameCopy`、
`KP1Y.OneYLowerValueTransport`（`Lower.UpperFixed`/`Lower.UpperOrder`）、`KP1Y.OneYForestDecoratedOrder`
（`seam_key_le_d`/`copied_key_le_d`）、`KP1Y.OneYReconstructionOrder`（`key_iff_value_le_d`）、
`KP1Y.OneYTerminalCopyNesting`、`KP1Y.OneYTerminalCopyHighRoots`、`KP1Y.OneYTerminalCopyRoots`、`KP1Y.OneYSelection*` 等已有冻结模块。
**不要** import 我的 `OneYTowerCanon*`/`OneYTerminalTower*`（避免依赖循环；我会 import 你的模块）。

共同前提（与 `ExpansionCanonical.terminal_rebuild_rows_d` 完全相同；V,P 是源第K层底行/父图，
NewTop=Hr(K+1)，Bottom=Hr(K)=Rebuild(Y,NewTop)）：

```lean
variable (hM : M.Models KP1Y.theory) (hC : C.Valid M) (hT : T.Valid M C)
  {m V P H level index n OldTop NewTop Bottom : M.Domain} {R : RowStateSpace M.Domain}
  (hRun : RowRun M C m R V P H) (hBase : RootedRow M C m V P)
  {X Y : CopiedMountain.Data M.Domain} (hX : X.Valid M C) (hFrom : CopiedMountain.FromRun M C m R V H X)
  (hOldTop : TopValueGraph M C m R H X.heights OldTop)
  {A : CopyCoordinates.Context M.Domain} (hA : A.Valid M C) (hWidth : M.SuccessorOf m A.last)
  (hBad : RowBadAt M C R H level A.last A.root) (hIndex : M.mem index C.omega)
  (hN : CopyCoordinates.Width M C T A index n) (hY : Y.Valid M C)
  (hCopy : CopiedMountain.Terminal.Copies M C T A X level n Y)
  (hTop : CopiedTop M C T A OldTop Y.width NewTop)
  (hRebuild : MountainReconstruction.Rebuilds M C T.addPairs T.plus Y NewTop Bottom)
```

需要的四个定理（结论逐字；前提为上面全部加列出的额外前提）：

```lean
-- H1 原 badAtTerminalBase_select_external / badAtTerminal_restrictedParent_external
theorem terminal_base_select_d … {F F' P0 : M.Domain}
    (hF : Selects true M C m F V P) (hF' : FrameCopy.Copies M C T A F index n F')
    (hP0 : MemPair M Y.parents C.zero P0) : Selects true M C n F' Bottom P0
-- H2 非root副本行0父项（原 parent_parentCopy_nonroot 于行0；可用已有 Terminal.parent_parent_copy_nonroot_d）
theorem terminal_base_nonroot_d … {P0 s b c p : M.Domain} (hP0 : MemPair M Y.parents C.zero P0)
    (hs : M.mem A.root s) (hsx : M.mem s A.last) (hMap : CopyCoordinates.ParentCopy M C T A b s c) (hc : M.mem c n) :
    MemPair M P0 c p ↔ ∃ q, MemPair M P s q ∧ CopyCoordinates.ParentCopy M C T A b q p
-- H3 原 badAtTerminalBase_upperFixed（K-1层lower上下文D只用到其coordinates）
theorem terminal_base_upper_fixed_d … {D : CopiedMountain.Lower.Context M.Domain} (hD : D.coordinates=A) :
    CopiedMountain.Lower.UpperFixed M C T D V P n Bottom
-- H4 原 badAtTerminalBase_upperOrder / badAtTerminalBase_order_of_common_frame（F为任一在V上选出P的继承帧）
theorem terminal_base_upper_order_d … {D : CopiedMountain.Lower.Context M.Domain} (hD : D.coordinates=A)
    {F : M.Domain} (hF : Selects true M C m F V P) : CopiedMountain.Lower.UpperOrder M C T D F V Bottom
```

规则同本车道：任意 `M`、无 sorry/axiom、所有长度/索引为内部 ω、对象归纳须写公式。
单模块检查 `./check-module.sh KP1Y/OneYCanonHelperX.lean --emit`。完成后在本文件下方或
`tracker/handoff/LANE-F.md` 记录逐字类型；我会在最终汇合 `OneYCanonicalExpansion*.lean` 中直接调用 H1–H4。

我（LANE-C）已完成：Terminal 的 SelectNext(K)、lower 输入的对象反向归纳、最终汇合（以 `TerminalExits` 为显式前提）。
助手模块落地后只需一个小模块把 H1–H4 打包成 `TerminalExits M`。

## 可供 LANE-B 复用（`extract` 字段）

`KP1Y/OneYTerminalBaseTopForest.lean`（命名空间 `KP1Y.OneYFinite.TowerCanon`）：
* `select_of_refinements_d`：细帧祖先⊆粗帧祖先且粗帧选择边皆为细帧祖先 ⇒ 两帧选择相同；
* `actual_top_forest_select_d`：任意实际 RowRun 的提取伪父选择 = 严格高度帧 `T`（`Selects false … F Heights T`）上的选择；
* `actual_top_parent_iff_d`：实际 RowRun 的严格高度帧父项 ⇔ 第 h(c)-1 行连通根（`Lower.RootAt`）。
原 `copiedBase_rawExtract` 可取 `F := 源k层严格高度帧`，再由目标 `rows` 字段给出的实际运行套用 `actual_top_forest_select_d`。
