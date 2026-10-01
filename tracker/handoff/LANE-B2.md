# LANE-B2 交接（Y05b：Lower 单层的 DecoratedBlockers 与 bottom/nonroot/down）

状态：**本通道四个出口全部完成**（BlockersPart、nonroot、BottomPart、DownPart）。分工见 `LANE-B.md` 的
"Split with LANE-B2"。所有模块命名空间 `KP1Y.OneYFinite.LowerBlock`。
检查：`./check-module.sh KP1Y/X.lean --emit > X-check.log 2>&1`（项目根目录），以下全部 exit 0 且日志空（最终按依赖序重新 emit 一遍）。
`#print axioms blockers_part_d / lower_layer_nonroot_d / bottom_part_d / down_part_d`：仅 propext, Classical.choice, Quot.sound。
已用临时文件核对：`⟨blockers_part_d hM hC hT hLayers, bottom_part_d hM hC hT hLayers hN, down_part_d hM hC hT hLayers hN⟩`
的类型逐字为 `LowerLayer.BlockersPart ∧ LowerLayer.BottomPart ∧ LowerLayer.DownPart`（LANE-B `OneYLowerLayerStep.lean`），defeq 通过。

## 模块（依赖序）

| 模块 | 行数 | 内容 |
|---|---|---|
| `KP1Y/OneYLowerBlockSource.lean` | 68 | 真实源 RowRun 的逐行装饰阻挡 `source_row_blocker_d` / `source_decorated_blockers_d` |
| `KP1Y/OneYLowerBlockGood.lean` | 311 | `BlockerAt`；`key_of_depth_iff_d`；`depth_at_iff_of_forward_d`；`extracted_parent_bound_d`；`copy_ancestor_d`；`original_depth_iff_d`；`good_depth_iff_d`；`original_blocker_d`；`good_blocker_of_source_d`/`good_blocker_d`（原 restrictedParent_good_copy） |
| `KP1Y/OneYLowerBlockBad.lean` | 107 | `LiftedRow`、`KeyTransport`；`bad_blocker_of_source_d`/`bad_blocker_core_d`（原 restrictedParent_bad_copy_of_blocker） |
| `KP1Y/OneYLowerBlockAssembly.lean` | 194 | `decorated_blockers_of_key_d`：原列/好部/未移动坏部/floor参考/抬升五支汇合 |
| `KP1Y/OneYLowerBlockKey.lean` | 98 | `key_transport_d`（原 keyLE_succ_rowCopy）；`lower_decorated_blockers_d`；**`blockers_part_d`** |
| `KP1Y/OneYLowerBottomRows.lean` | 70 | `zero_parent_copy_iff_d`（原 parent_zero_parentCopy）；**`lower_layer_nonroot_d`** |
| `KP1Y/OneYLowerBottomColumn.lean` | 233 | 两重建网格单列运输 `column_transport_d`；`lower_prefix_data_d`；`extracted_parent_good_zero_d`；`good_bottom_value_d`（原 value_copy_of_good_base_parent） |
| `KP1Y/OneYLowerBottomFrame.lean` | 133 | `frame_copy_ancestor_d`（FrameCopy 祖先运输）；`source_bottom_blocker_d`；`key_value_le_d` |
| `KP1Y/OneYLowerBottomZero.lean` | 102 | 第0行祖先运输 `zero_ancestor_copy_d`；`zero_key_transport_d`（原 keyLE_bottom_parent） |
| `KP1Y/OneYLowerBottomSelect.lean` | 184 | `bottom_original_iff_d`、`bottom_encoded_none_d`、`bottom_encoded_some_d` |
| `KP1Y/OneYLowerBottomPart.lean` | 142 | `width_kept_d`；`bottom_select_d`（原 restrictedParent_bottom_numeric，列号对象归纳）；**`bottom_part_d`** |
| `KP1Y/OneYLowerBottomDown.lean` | 234 | `source_bottom_key_d`；`bottom_order_d`（原 value_copy_le_of_common_frame）；**`down_part_d`** |

## 出口（全部可直接用于 `lower_layer_step_of_parts_d`）

```lean
-- 公共环境
{M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory) {C : ExpressionData M.Domain} (hC : C.Valid M)
{T : MatrixArithmetic M.Domain} (hT : T.Valid M C) {A : CopyCoordinates.Context M.Domain} {m : M.Domain}
{L : LayerStateSpace M.Domain} {V P H K k N n : M.Domain} (hLayers : LayerRun M C m L V P H)

theorem blockers_part_d ... (hLayers) :
    ∀ {W Q J oldTop Qnext newTop Pnext : M.Domain} {D : Lower.Context M.Domain} {Y : Data M.Domain},
      TowerCanon.LowerLayerData M C T A m L H K k n W Q J oldTop Qnext D Y →
      Graph M newTop n C.omega → (∀ c v, MemPair M newTop c v → M.mem C.zero v) →
      TowerCanon.LowerInputs M C T D m N n oldTop Qnext newTop Pnext →
      ReconstructionRecovery.DecoratedBlockers M C Y newTop

theorem lower_layer_nonroot_d ... {H K k n W Q J oldTop Qnext P0 s b c p : M.Domain} {D} {Y}
    (hData : TowerCanon.LowerLayerData M C T A m L H K k n W Q J oldTop Qnext D Y)
    (hP0 : MemPair M Y.parents C.zero P0) (hRoot : M.mem A.root s) (hLast : M.mem s A.last)
    (hMap : ParentCopy M C T A b s c) (hc : M.mem c n) :
    MemPair M P0 c p ↔ ∃ q, MemPair M Q s q ∧ ParentCopy M C T A b q p

theorem bottom_part_d ... (hLayers) (hN : CopyCoordinates.Width M C T A N n) :
    ∀ {W Q J oldTop Qnext newTop Pnext Bottom F F' P0 : M.Domain} {D : Lower.Context M.Domain} {Y : Data M.Domain},
      TowerCanon.LowerLayerData M C T A m L H K k n W Q J oldTop Qnext D Y →
      Graph M newTop n C.omega → (∀ c v, MemPair M newTop c v → M.mem C.zero v) →
      TowerCanon.LowerInputs M C T D m N n oldTop Qnext newTop Pnext →
      ReconstructionSelection.PseudoTopBound M C Y newTop →
      MountainReconstruction.Rebuilds M C T.addPairs T.plus Y newTop Bottom →
      Selects true M C m F W Q → FrameCopy.Copies M C T A F N n F' → MemPair M Y.parents C.zero P0 →
      Selects true M C n F' Bottom P0

theorem down_part_d ... (hLayers) (hN : CopyCoordinates.Width M C T A N n) :
    ∀ {j W Q J oldTop Qnext newTop Pnext Bottom W' Q' J' oldTop' Qnext' : M.Domain}
      {D D' : Lower.Context M.Domain} {Y Y' : Data M.Domain}, M.SuccessorOf k j →
      TowerCanon.LowerLayerData M C T A m L H K j n W' Q' J' oldTop' Qnext' D' Y' →
      TowerCanon.LowerLayerData M C T A m L H K k n W Q J oldTop Qnext D Y →
      Graph M newTop n C.omega → (∀ c v, MemPair M newTop c v → M.mem C.zero v) →
      TowerCanon.LowerInputs M C T D m N n oldTop Qnext newTop Pnext →
      ReconstructionSelection.PseudoTopBound M C Y newTop →
      MountainReconstruction.Rebuilds M C T.addPairs T.plus Y newTop Bottom →
      Lower.UpperFixed M C T D' oldTop' Qnext' n Bottom ∧
        ∀ Pseudo, GraphPseudoForest M C D'.mountain Pseudo → Lower.UpperOrder M C T D' Pseudo oldTop' Bottom
```
用法：`hBlk := blockers_part_d hM hC hT hLayers`，`hBottom := bottom_part_d hM hC hT hLayers hN`，
`hDown := down_part_d hM hC hT hLayers hN`，`hNonroot := fun hData hP0 hRoot hLast hMap hc => lower_layer_nonroot_d hM hC hT hData hP0 hRoot hLast hMap hc`。

## 使用的假设（全部为合法输入，无规范性/NumericRow/RowRun-of-output 假设）
- LowerInputs 字段：`prefixTop`、`fixed`、`order`（三者都用）；**不用 `select`**。
- `PseudoTopBound M C Y newTop`：只在 bottom/down 中经 `structural_reconstruction_selects_d` 使用（BottomPart/DownPart 本身提供）。
- `hLayers`：只取 `(hLayers.at_rooted hM.1 hData.layer)`（源第k行 RootedRow：正值与 RootsOne）；down 另用 `hLayers.at_next` 识别
  第j层提取 `(oldTop', Qnext') = (W, Q)`。
- `hN : Width A N n`：只用于 last⊆n（`width_kept_d`）与构造帧复制 `FrameCopy.copies_exists_d`（down 的深度反证）。
- 源对象：LowerLayerData 的 `run/from_run/extraction/context/target/copies/coordinates/layer`。

## 依赖的他人已 emit 模块（只读 import）
LANE-B：`OneYLowerCanonDepthRoot`（`canon_depth_original_d`、`canon_root_ancestor_low_copy_d`、`canon_good_parent_out_d`、
`canon_depth_good_eq_d`）、`OneYLowerCanonOrder`（nat_*）、`OneYLowerCanonKeyStart`/`KeyHigh`（四个 key start）、
`OneYLowerCanonKeyZero`（`canon_row_zero_d`）、`OneYLowerCanonDepth`（`canon_row_parent_iff`、`canon_source_ancestor_lower_d`）。
若 LANE-B 改动这些签名，B2 的模块需重新 emit。其余为已集成模块（ReconstructionRecovery/Selection/Order/Grid、FrameCopy、
MatrixCopyForest、LowerCopy*、NumericDecoratedOrder 等）。

## 尚未完成（不属于本通道）
`BoundPart`（PseudoTopBound）与 `ExtractPart`（LANE-B）。主定理未完成。
