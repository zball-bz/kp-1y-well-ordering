# LANE-B 交接（Y05b：Lower 单层 k<K 规范性）

状态：**完成**。`lower_steps_d : CanonicalExpansion.LowerStepsIn M` 已无条件证明（无剩余假设），见文末"最终出口"。目标结论按协调者冻结的接口 `TowerCanon.LowerLayerStep`（`KP1Y/OneYTowerCanonInterface.lean`）。

## 已完成模块

| 模块 | 检查 | 内容 |
|---|---|---|
| `KP1Y/OneYLowerCanonPaths.lean` | `--emit` exit 0，日志空 | 通用：深度沿实际父路径相加 `depth_path_sum_d`；只运输起点以上边的路径映射 `path_map_above_d`；映射链深度增量 `depth_mapped_diff_d`、映射到根深度相等 `depth_mapped_eq_d`；加法比较 `sum_compare_iff_d`/`sum_pair_compare_iff_d`；`depth_ancestor_lt_d` |
| `KP1Y/OneYLowerCanonOrder.lean` | `--emit` exit 0，日志空 | 内部ω序工具 `nat_*`（命名空间 `LowerCanon`） |
| `KP1Y/OneYLowerCanonDepth.lean` | `--emit` exit 0，日志空 | `Copies.canon_copy_heights_d`（含末列源）、`canon_depth_low_diff_d`、`canon_depth_low_eq_d`、`canon_depth_out_eq_d`、`canon_depth_moved_diff_d`、`canon_depth_lifted_d`、`canon_source_ancestor_lower_d`、`canon_row_parent_iff` 等 |
| `KP1Y/OneYLowerCanonDepthRoot.lean` | `--emit` exit 0，日志空 | `Copies.canon_depth_original_d`、`canon_root_seam_low_d`（对块号对象归纳）、`canon_root_ancestor_low_copy_d`、`canon_good_parent_out_d`、`Copies.canon_depth_good_eq_d` |
| `KP1Y/OneYLowerCanonKeyCore.lean` | `--emit` exit 0，日志空 | Key通用框架：`canon_key_transfer_d`（行对应首差运输）、`canon_key_of_parts`、`canon_key_prepend_d`、`canon_key_of_depth_eq_d`、`canon_parent_rows_propagate_d`（对象归纳）、`canon_pseudo_rows_eq_d`、`canon_upper_top_d`、`canon_row_transfer_d` |
| `KP1Y/OneYLowerCanonKeyRows.lean` | `--emit` exit 0，日志空 | 单行运输：`Copies.canon_row_low_d`、`canon_row_gap_d`、`canon_row_lift_d`、`canon_row_out_d`、`canon_row_floor_d`（含锥状态混合）、`canon_cone_status_eq_d`、`canon_in_cone_iff_anc_d` |
| `KP1Y/OneYLowerCanonKeyStart.lean` | `--emit` exit 0，日志空 | `Copies.canon_key_low_start_d`；辅助 `canon_shift_high_d`、`canon_shift_before_d`、`canon_eq_lt_absurd`、`canon_depth_eq_of_common_parent_d` |
| `KP1Y/OneYLowerCanonKeyHigh.lean` | `--emit` exit 0，日志空 | `Copies.canon_key_floor_start_d`、`canon_key_lifted_start_d`、`canon_key_outside_start_d` |
| `KP1Y/OneYLowerCanonKeyZero.lean` | `--emit` exit 0，日志空 | 行0外部帧比较（原 depth_zero_lt_copy_of_common_frame）：`canon_frame_mono_d`；`Copies.canon_row_zero_d`（`Selects true m F V P`、`ParentRowsEqual F c z` ⇒ 行0 Eq/Lt 运输，floor=0/floor>0 两支） |
| `KP1Y/OneYLowerCanonPreimage.lean` | `--emit` exit 0，日志空 | `LowerCanon.ancestor_preimage_d`（目标祖先沿映射逐边反射的前像，带停止列） |
| `KP1Y/OneYLowerCanonPseudoHigh.lean` | `--emit` exit 0，日志空 | `canon_pseudo_parent_transfer_d`、`Copies.canon_pseudo_cand_lifted_d`、`Copies.canon_pseudo_cand_out_d`、`canon_parent_copy_mono/fun` |
| `KP1Y/OneYLowerCanonPseudoSeam.lean` | `--emit` exit 0，日志空 | 接缝阈值：`canon_selects_ancestor_between_d`、`canon_seam_intermediate_d`、`Copies.canon_low_parent_iff_d`、`Copies.canon_seam_heights_low_d` |
| `KP1Y/OneYLowerCanonPseudoLow.lean` | `--emit` exit 0，日志空 | `LowCopy`、`Copies.canon_pseudo_cand_low_d`（0<H(s)≤floor 的候选对应）；`PseudoCopy`、`canon_pseudo_copy_fun`、`canon_pseudo_copy_mono` |
| `KP1Y/OneYLowerCanonPseudo.lean` | `--emit` exit 0，日志空 | **统一伪父公式 `Copies.canon_pseudo_copy_d`**（原 pseudo_parent_parentCopy；见下文"伪父公式"） |
| `KP1Y/OneYLowerLayerFinal.lean` | `--emit` exit 0，日志空 | **`lower_layer_step_d`**（全部字段无条件实例化：本lane rows、B2 `blockers_part_d`/`bottom_part_d`/`lower_layer_nonroot_d`/`down_part_d`、helper `lower_layer_pseudo_top_bound_d`/`lower_layer_extract_d`）；**`lower_steps_d : CanonicalExpansion.LowerStepsIn M`**；`ExtractPart` |
| `KP1Y/OneYLowerLayerStep.lean` | `--emit` exit 0，日志空 | 汇合骨架（命名空间 `KP1Y.OneYFinite.LowerLayer`）：部分命题 `BlockersPart`/`BoundPart`/`BottomPart`/`DownPart`；**`lower_layer_rows_d`（rows 字段，由 `structural_rebuild_run_exists_d` 实际证明，只需 BlockersPart+BoundPart）**；`lower_layer_step_of_parts_d`（各部分 ⇒ `TowerCanon.LowerLayerStep`，纯组装） |

## 计划（按依赖）

1. Depth：低行同块增量、无根祖先/锥外相等、移动行增量、抬升行相等（Lower 实际复制图）。
2. Key：KeyLE 的行对应运输（low/floor/lifted/outside/good）。
3. Blocker：DecoratedBlockers M C Y newTop（原 LowerCopyCanonical/BadBlocker/Blocker）。
4. Pseudo：目标伪父森林单类收缩及选择等式（原 LowerCopyPseudo*/SingleContraction/TopForest/TopBound），导出 `PseudoTopBound` 与 `extract`。
5. rows：`ReconstructionRecovery.structural_rebuild_run_exists_d`。
6. bottom / nonroot / down（原 BottomRecovery、Transport、Dominance）。
7. 汇总：`lower_layer_step_d : TowerCanon.LowerLayerStep M C T A m L H K k N n`。

## Split with LANE-B2（协调者 2026-10-01 分工）

LANE-B（本人）：Depths、Key/Comparison、Pseudo 链（PseudoSeam/High/Outside/Low/Pseudo、SingleContraction）、
TopForest/TopBound（`PseudoTopBound` 与 `extract` 字段）、`rows` 字段（`structural_rebuild_run_exists_d`）、
最终汇总 `lower_layer_step_d : TowerCanon.LowerLayerStep M C T A m L H K k N n`。文件前缀 `OneYLowerCanon*`/`OneYLowerLayer*`。

LANE-B2：`DecoratedBlockers M C Y newTop`（原 LowerCopyBlocker/BadBlocker/Canonical 的 blocker 部分）与
`bottom`/`nonroot`/`down` 字段（原 LowerCopyBottom/BottomRecovery/Transport/Dominance）。前缀 `OneYLowerBlock*`/`OneYLowerBottom*`。

### LANE-B 提供给 B2 的（可直接 import）
* `KP1Y/OneYLowerCanonPaths.lean`（已 emit）：`LowerCanon.depth_path_sum_d`、`path_map_above_d`、`depth_mapped_diff_d`、
  `depth_mapped_eq_d`、`sum_compare_iff_d`、`sum_pair_compare_iff_d`、`depth_ancestor_lt_d`。
* `KP1Y/OneYLowerCanonDepth.lean`（进行中）：Lower 实际复制的逐行深度运输（低行同块增量、低行无根祖先相等、
  锥外高行相等、移动行增量、抬升行相等、原列相等、root 跨接缝祖先）。
* `KP1Y/OneYLowerCanonKey.lean`（计划）：KeyLE 运输，形状如下（`hUpper : UpperOrder M C T D Pseudo oldTop newTop`，
  `hPseudo : GraphPseudoForest M C D.mountain Pseudo`，源 `hRun/hFrom`，目标 `hCopy/hY`；`c,z` 为源列，root∈z∈c≤last，
  `cc,zz` 为同块 `ParentCopy b` 像，Top 读数 `oldTop c tc, oldTop z tz, newTop cc tcc, newTop zz tzz`）：
  - `Copies.canon_key_low_start_d`：源行 u∈floor 上 `c,z` 有共同父，`ForestOrder.KeyLE M C D.mountain c z t tc tz`（t=u+1）
    ⇒ `ForestOrder.KeyLE M C Y cc zz t tcc tzz`；
  - `Copies.canon_key_floor_start_d`：同上但共同父在 floor 行；
  - `Copies.canon_key_lifted_start_d`：共同父在源行 u（floor≤u），c,z 皆在锥内；目标起点 `(u+b·rise)+1`；
  - `Copies.canon_key_outside_start_d`：共同父在源行 u（floor≤u），c,z 皆在锥外（c∈last）；目标起点 u+1；
  - `canon_key_of_depth_eq_d`（好部父/原列用）：若从起点起每行源深度蕴含目标深度，则 KeyLE 以相同 Top 读数运输；
    配合 `Copies.canon_depth_good_eq_d`（源行 u 父项为好部 g∈root 的非 root 列，行≥u 时目标复制深度=源深度）。

### LANE-B 期望 B2 提供的（lower_layer_step_d 将直接调用；B2 可在假设中使用 `hBound`）
记 `Data := TowerCanon.LowerLayerData M C T A m L H K k n W Q J oldTop Qnext D Y`，`Inputs := TowerCanon.LowerInputs M C T D m N n oldTop Qnext newTop Pnext`，
`hBound : ReconstructionSelection.PseudoTopBound M C Y newTop`（由 LANE-B 从 `Inputs.select` 导出后传入）：
1. `blockers`：`hLayers : LayerRun M C m L V P H` → Data → `Graph M newTop n C.omega` → newTop 正 → Inputs →
   `ReconstructionRecovery.DecoratedBlockers M C Y newTop`。（若需 `hBound` 可加为假设。）
2. `bottom`：与 `LowerLayerStep.bottom` 字段同形，另加 `hLayers` 与 `hBound`。
3. `nonroot`：与 `LowerLayerStep.nonroot` 字段同形（可加 `hLayers`）。
4. `down`：与 `LowerLayerStep.down` 字段同形，另加 `hLayers` 与 k 层的 `hBound`。

## Available for helper（协调者 2026-10-01 请求；建议前缀 `OneYLowerHelp*`）

可分离子块：原 Pseudo 链（LowerCopyPseudoSeam/High/Outside/Low/Pseudo、SingleContraction）与 TopForest/TopBound/LayerTopBound，
产出两条结论，LANE-B 在 `lower_layer_step_d` 中直接调用（不需要 LANE-B 的其他模块，可选 import `KP1Y.OneYLowerCanonDepth*`）：

```lean
-- 统一环境（与 TowerCanon 接口一致）
variable {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory) {C : ExpressionData M.Domain} (hC : C.Valid M)
  {T : MatrixArithmetic M.Domain} (hT : T.Valid M C) {m : M.Domain} {L : LayerStateSpace M.Domain}
  {V P H K level N n : M.Domain} {A : CopyCoordinates.Context M.Domain}
  (hLayers : LayerRun M C m L V P H) (hA : A.Valid M C) (hBad : BadAt M C m L H K level A.last A.root)
  (hN : CopyCoordinates.Width M C T A N n)

-- (H-bound) 原 badAtLowerCopiedBase_lowerTopBound / pseudoTopBound_of_upper_selections
theorem lower_layer_pseudo_top_bound_d
    {k W Q J oldTop Qnext newTop Pnext : M.Domain} {D : CopiedMountain.Lower.Context M.Domain} {Y : CopiedMountain.Data M.Domain}
    (hData : TowerCanon.LowerLayerData M C T A m L H K k n W Q J oldTop Qnext D Y)
    (hNew : Graph M newTop n C.omega) (hPos : ∀ c v, MemPair M newTop c v → M.mem C.zero v)
    (hInputs : TowerCanon.LowerInputs M C T D m N n oldTop Qnext newTop Pnext) :
    ReconstructionSelection.PseudoTopBound M C Y newTop

-- (H-extract) 恰为 TowerCanon.LowerLayerStep.extract 字段（原 copiedBase_rawExtract / pseudo_select_eq_frameCopy）
theorem lower_layer_extract_d
    {k W Q J oldTop Qnext newTop Pnext G : M.Domain} {D : CopiedMountain.Lower.Context M.Domain} {Y : CopiedMountain.Data M.Domain}
    (hData : TowerCanon.LowerLayerData M C T A m L H K k n W Q J oldTop Qnext D Y)
    (hNew : Graph M newTop n C.omega) (hPos : ∀ c v, MemPair M newTop c v → M.mem C.zero v)
    (hInputs : TowerCanon.LowerInputs M C T D m N n oldTop Qnext newTop Pnext) (hG : GraphPseudoForest M C Y G) :
    ∃ F F', Selects true M C m F oldTop Qnext ∧ FrameCopy.Copies M C T A F N n F' ∧
      ∀ Q', Selects true M C n G newTop Q' ↔ Selects true M C n F' newTop Q'
```
说明：二者只依赖 `hInputs.select`（对源伪父帧 Pseudo_k 与严格高度帧两次实例化，见原 LowerCopyLayerTopBound）、
`hInputs.prefixTop` 与真实源提取 `hData.extraction`；不使用目标的规范性（rows）。`PseudoTopBound` 可经已集成的
`CopiedMountain.Lower.pseudo_top_bound_of_decreasing_selection_d`（KP1Y/OneYLowerTopBound.lean）由目标选择边严格降高度得到。
若 helper 发现某字段需额外环境假设，请在本节下方注明。

### Key 运输：已完成的精确出口（供 B2 的 DecoratedBlockers / bottom 使用）

命名空间 `KP1Y.OneYFinite.CopiedMountain.Lower`，import `KP1Y.OneYLowerCanonKeyHigh`。公共参数：
`(hM) (hC) (hT) (hD : D.Valid M C) (hY : Y.Valid M C) (hCopy : Copies M C T D n Y) (hRun : RowRun M C m R V P H) (hFrom : FromRun M C m R V H D.mountain)`，
`(hUpper : UpperOrder M C T D Pseudo oldTop newTop) (hPseudo : GraphPseudoForest M C D.mountain Pseudo)`，源列 `root∈z∈c`、`c=last ∨ c∈last`，
`hMapC : ParentCopy M C T D.coordinates b c cc`、`hMapZ : ParentCopy … b z zz`、`hcc : cc∈Y.width`、Top读数 `oldTop c tc, oldTop z tz, newTop cc tcc, newTop zz tzz`，
`hKey : ForestOrder.KeyLE M C D.mountain c z t tc tz`，结论 `ForestOrder.KeyLE M C Y cc zz t tcc tzz`（lifted 为 t'）：
* `Copies.canon_key_low_start_d`：`(hLow : u∈D.floor) (ht : SuccessorOf t u) (hCommon : ∃p, ParentAt X u c p ∧ ParentAt X u z p)`；
* `Copies.canon_key_floor_start_d`：`(ht : SuccessorOf t D.floor) (hCommon at D.floor)`；
* `Copies.canon_key_lifted_start_d`：`(hHighU : floor≤u) (ht : SuccessorOf t u) (hTimes : MulAt b rise off) (hV : AddAt u off v) (ht' : SuccessorOf t' v) (hConeC hConeZ : InCone) (hCommon at u)` ⇒ 起点 t'；
* `Copies.canon_key_outside_start_d`：`(hHighU : floor≤u) (ht) (hOutC hOutZ : ¬InCone) (hcLast : c∈last) (hCommon at u)`。
好部父/原列：`canon_key_of_depth_eq_d`（相同Top读数）+ `Copies.canon_depth_good_eq_d` / `Copies.canon_depth_original_d`。
底行（共同父在行0、Key从1）：floor>0 用 low_start(u=0)，floor=0 用 floor_start。

### 汇合方式（LANE-B 最终定理）

`lower_layer_step_d : TowerCanon.LowerLayerStep M C T A m L H K k N n` 将定义为
`LowerLayer.lower_layer_step_of_parts_d hM hC hT (B2 blockers) (helper bound) (helper extract) (B2 bottom) (B2 nonroot) (B2 down)`，
其中各部分须恰好给出 `KP1Y/OneYLowerLayerStep.lean` 中的命题（`BlockersPart`、`BoundPart`、`BottomPart`、`DownPart`，
`extract`/`nonroot` 与 `LowerLayerStep` 字段同形），环境假设（`hLayers`、`hA`、`hBad`、`hN`、`hk`）由最终定理提供。

### （历史）LANE-B 进度说明
**更新：已发现 helper（`KP1Y/OneYLowerHelpForest.lean`, 命名空间 `LowerHelp`）在做 Pseudo 链，LANE-B 停止 P1，不再写伪父相关新模块。**
LANE-B 在发现 helper 之前已完成并 emit 的 P1 片段（helper 可直接 import，避免重复）：
* `KP1Y/OneYLowerCanonPreimage.lean`：`LowerCanon.ancestor_preimage_d`（目标祖先沿映射逐边反射的前像，带停止列，对象∈归纳）。
* `KP1Y/OneYLowerCanonPseudoHigh.lean`（命名空间 `CopiedMountain.Lower`）：
  `canon_pseudo_parent_transfer_d`（候选经严格单调关系对应 ⇒ 伪父对应），
  `Copies.canon_pseudo_cand_lifted_d`（锥内源列 s：`GraphPseudoCandidate Y c a ↔ ∃ q, GraphPseudoCandidate D.mountain s q ∧ Encode q b a`，c=Encode s b），
  `Copies.canon_pseudo_cand_out_d`（锥外且 floor∈H(s)：同上，像为 `ParentCopy b q a`），
  `canon_parent_copy_mono`、`canon_parent_copy_fun`。
  尚未做：低高度情形（0<H(s)≤floor，原 LowerCopyPseudoLow 的接缝阈值搜索）与总公式。
（以下为原说明）
Key/Depth 全部完成并 emit；rows 已由 `lower_layer_rows_d` 证明（只待 B2 的 BlockersPart 与 BoundPart）。
**若协调者尚未为 "Available for helper" 指派 helper，LANE-B 现开始该子块的 P1：目标图伪父公式**
（原 LowerCopyPseudoSeam/High/Outside/Low → `pseudo_parent_parentCopy`），文件 `KP1Y/OneYLowerCanonPseudo*.lean`。
若已指派 helper，请通知 LANE-B 停止 P1，helper 可直接从 P1 开始（LANE-B 不会写 `OneYLowerHelp*`）。
P2（单收缩选择等式 `select_eq_single_contraction` ⇒ `extract`）与 P3（`BoundPart`）在 P1 之后。

## 最终出口（2026-10-01 完成；`#print axioms`：propext, Classical.choice, Quot.sound）

`KP1Y/OneYLowerLayerFinal.lean`，命名空间 `KP1Y.OneYFinite.LowerLayer`，`--emit` exit 0、日志空：
```lean
theorem lower_layer_step_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {m : M.Domain} {L : LayerStateSpace M.Domain} {V P H K level N n : M.Domain} {A : CopyCoordinates.Context M.Domain}
    (hLayers : LayerRun M C m L V P H) (hA : A.Valid M C) (hBad : BadAt M C m L H K level A.last A.root)
    (hN : CopyCoordinates.Width M C T A N n) (k : M.Domain) :
    TowerCanon.LowerLayerStep M C T A m L H K k N n
theorem lower_steps_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory) :
    CanonicalExpansion.LowerStepsIn M
```
`lower_steps_d` 由 `Successful` 字段取 `run`、`coordinates`、`bad`（经 `last`/`root` 改写）、`width`；
不需要 `M.SuccessorOf m last`，也不使用 `k∈W.K`（`LowerLayerData.lower` 已含 k∈K）。

组装（`lower_layer_step_of_parts_d`）：rows=本lane `lower_layer_rows_d`；BlockersPart=`LowerBlock.blockers_part_d hM hC hT hLayers`；
BoundPart=`LowerHelp.lower_layer_pseudo_top_bound_d hM hC hT hLayers hA hBad hN …`；ExtractPart=`LowerHelp.lower_layer_extract_d …`；
BottomPart=`LowerBlock.bottom_part_d hM hC hT hLayers hN`；nonroot=`LowerBlock.lower_layer_nonroot_d`；DownPart=`LowerBlock.down_part_d hM hC hT hLayers hN`。

模块依赖顺序（本lane）：`OneYLowerCanonPaths` → `OneYLowerCanonOrder` → `OneYLowerCanonDepth` → `OneYLowerCanonDepthRoot` →
`OneYLowerCanonKeyCore` → `OneYLowerCanonKeyRows` → `OneYLowerCanonKeyStart` → `OneYLowerCanonKeyHigh` → `OneYLowerCanonKeyZero` →
`OneYLowerCanonPreimage` → `OneYLowerCanonPseudoHigh` → `OneYLowerCanonPseudoSeam` → `OneYLowerCanonPseudoLow` → `OneYLowerCanonPseudo` →
`OneYLowerLayerStep` →（B2 `OneYLowerBlock*`/`OneYLowerBottom*`、helper `OneYLowerHelp*`）→ `OneYLowerLayerFinal`。
注意：helper 的 `OneYLowerHelpMain` import `OneYLowerCanonPseudo`；B2 模块 import `OneYLowerLayerStep` 与若干 `OneYLowerCanon*`。
若重新 emit 这些模块，下游须按上序重新 emit。

## 伪父公式（P1 完成，供 helper 的 Bound/Extract 直接 import `KP1Y.OneYLowerCanonPseudo`）
命名空间 `KP1Y.OneYFinite.CopiedMountain.Lower`：
```lean
def PseudoCopy (M) (C) (T) (D : Context M.Domain) (s b q a : M.Domain) : Prop :=
  (q=D.coordinates.root ∧ MemPair M D.mountain.heights s D.floor ∧ a=D.coordinates.root) ∨
  (¬(q=D.coordinates.root ∧ MemPair M D.mountain.heights s D.floor) ∧ ParentCopy M C T D.coordinates b q a)
theorem Copies.canon_pseudo_copy_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {D : Context M.Domain} (hD : D.Valid M C) {Y : Data M.Domain} (hY : Y.Valid M C) {n : M.Domain}
    (hCopy : Copies M C T D n Y) {m : M.Domain} {R : RowStateSpace M.Domain} {V P H : M.Domain}
    (hRun : RowRun M C m R V P H) (hFrom : FromRun M C m R V H D.mountain) {s b c : M.Domain}
    (hRootS : M.mem D.coordinates.root s) (hsLast : s=D.coordinates.last ∨ M.mem s D.coordinates.last)
    (hMap : ParentCopy M C T D.coordinates b s c) (hc : M.mem c Y.width) (a : M.Domain) :
    GraphPseudoParent M C Y c a ↔ ∃ q, GraphPseudoParent M C D.mountain s q ∧ PseudoCopy M C T D s b q a
```
（锥内：像为 Encode；锥外 H(s)>floor：ParentCopy；H(s)=0：两边皆无候选；0<H(s)≤floor：源伪父 root 且 H(s)=floor 时收缩到 root，否则 ParentCopy。）
源列 `s≤root`（原列）情形由 `Copies.original_*` 直接给出，不在此公式内。

**给 helper（`PseudoCopyFormula M C T D Y`；已被 `OneYLowerHelpMain.lower_layer_pseudo_copy_formula_d` 使用）**：同文件另有
```lean
theorem Copies.canon_pseudo_copy_formula_d (hM) (hC) (hT) (hD : D.Valid M C) (hY : Y.Valid M C) (hCopy : Copies M C T D n Y)
    (hRun : RowRun M C m R V P H) (hFrom : FromRun M C m R V H D.mountain) :
    ∀ s b c, M.mem D.coordinates.root s → (s=D.coordinates.last ∨ M.mem s D.coordinates.last) →
      Encode M C T D.coordinates s b c → M.mem c Y.width → M.mem D.coordinates.last c →
      ∀ q, GraphPseudoParent M C Y c q ↔ ∃ p, GraphPseudoParent M C D.mountain s p ∧
        ((MemPair M D.mountain.heights s D.floor ∧ p=D.coordinates.root ∧ q=D.coordinates.root) ∨
          (¬(MemPair M D.mountain.heights s D.floor ∧ p=D.coordinates.root) ∧ ParentCopy M C T D.coordinates b p q))
```
其结论与 `LowerHelp.PseudoCopyFormula M C T D Y` 定义体逐字相同，故
`hFormula := Lower.Copies.canon_pseudo_copy_formula_d hM hC hT hData.context hData.target hData.copies hData.run hData.from_run`

## （已完成）伪父低高度情形
文件 `KP1Y/OneYLowerCanonPseudoLow.lean`（命名空间 `CopiedMountain.Lower`），目标：
```lean
theorem Copies.canon_pseudo_cand_low_d … (hRun) (hFrom) {s b c hs : M.Domain}
    (hRootS : M.mem D.coordinates.root s) (hsLast : M.mem s D.coordinates.last) (hOut : ¬InCone M C D s)
    (hHS : MemPair M D.mountain.heights s hs) (hPos : M.mem C.zero hs) (hLowH : hs=D.floor ∨ M.mem hs D.floor)
    (hMap : ParentCopy M C T D.coordinates b s c) (hc : M.mem c Y.width) (a : M.Domain) :
    GraphPseudoCandidate M C Y c a ↔ ∃ q, GraphPseudoCandidate M C D.mountain s q ∧
      ((q=D.coordinates.root ∧ a=D.coordinates.root) ∨ (q≠D.coordinates.root ∧ ParentCopy M C T D.coordinates b q a))
```
（原 LowerCopyPseudoLow.firstMatch_copy_low/pseudo_parent_low；配合 `canon_pseudo_parent_transfer_d` 得伪父公式。）
