import KP1Y.OneYLowerLayerStep
import KP1Y.OneYLowerBlockKey
import KP1Y.OneYLowerBottomRows
import KP1Y.OneYLowerBottomPart
import KP1Y.OneYLowerBottomDown
import KP1Y.OneYLowerHelpMain
import KP1Y.OneYCanonicalExpansion

/-! Lower单层出口的最终汇合（原 badAtLowerCopiedBase_* 一族）：
* rows：本lane `lower_layer_rows_d`（`structural_rebuild_run_exists_d`）；
* DecoratedBlockers / bottom / nonroot / down：LANE-B2（`LowerBlock.*`）；
* 伪父Top界 / extract：LANE-F helper（`LowerHelp.*`，用本lane的伪父公式 `Copies.canon_pseudo_copy_formula_d`）。
全部无条件实例化，得 `TowerCanon.LowerLayerStep` 与协调者出口 `CanonicalExpansion.LowerStepsIn`。 -/
namespace KP1Y.OneYFinite.LowerLayer
open YesMetaZFC YesMetaZFC.SetTheory YesMetaZFC.SetTheory.Definitional
open KP1Y.Kuratowski KP1Y.Functions KP1Y.Naturals KP1Y.Bounded
open KP1Y.OneYFinite.CopiedMountain KP1Y.OneYFinite.TowerCanon
universe u

/-- `extract` 字段（原 copiedBase_rawExtract）。 -/
def ExtractPart (M : SetTheory.Structure.{u}) (C : ExpressionData M.Domain) (T : MatrixArithmetic M.Domain)
    (A : CopyCoordinates.Context M.Domain) (m : M.Domain) (L : LayerStateSpace M.Domain) (H K k N n : M.Domain) : Prop :=
  ∀ {W Q J oldTop Qnext newTop Pnext G : M.Domain} {D : Lower.Context M.Domain} {Y : Data M.Domain},
    LowerLayerData M C T A m L H K k n W Q J oldTop Qnext D Y →
    Graph M newTop n C.omega → (∀ c v, MemPair M newTop c v → M.mem C.zero v) →
    LowerInputs M C T D m N n oldTop Qnext newTop Pnext → GraphPseudoForest M C Y G →
    ∃ F F', Selects true M C m F oldTop Qnext ∧ FrameCopy.Copies M C T A F N n F' ∧
      ∀ Q', Selects true M C n G newTop Q' ↔ Selects true M C n F' newTop Q'

/-- Lower 单层 k<K 的完整规范性（`TowerCanon.LowerLayerStep`），环境为实际层运行、坏根与宽度。 -/
theorem lower_layer_step_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {m : M.Domain} {L : LayerStateSpace M.Domain} {V P H K level N n : M.Domain} {A : CopyCoordinates.Context M.Domain}
    (hLayers : LayerRun M C m L V P H) (hA : A.Valid M C) (hBad : BadAt M C m L H K level A.last A.root)
    (hN : CopyCoordinates.Width M C T A N n) (k : M.Domain) :
    LowerLayerStep M C T A m L H K k N n :=
  lower_layer_step_of_parts_d hM hC hT (LowerBlock.blockers_part_d hM hC hT hLayers)
    (fun hData hNew hPos hInputs =>
      LowerHelp.lower_layer_pseudo_top_bound_d hM hC hT hLayers hA hBad hN hData hNew hPos hInputs)
    (fun hData hNew hPos hInputs hG =>
      LowerHelp.lower_layer_extract_d hM hC hT hLayers hA hBad hN hData hNew hPos hInputs hG)
    (LowerBlock.bottom_part_d hM hC hT hLayers hN)
    (fun hData hP0 hRoot hLast hMap hc => LowerBlock.lower_layer_nonroot_d hM hC hT hData hP0 hRoot hLast hMap hc)
    (LowerBlock.down_part_d hM hC hT hLayers hN)

/-- 协调者出口：任意实际成功展开的每个 lower 层都满足 `LowerLayerStep`。无剩余假设。 -/
theorem lower_steps_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory) : CanonicalExpansion.LowerStepsIn M := by
  intro E T hE hT s m last N t W hS k _
  have hBad : BadAt M E m W.space W.layers W.K W.level W.coordinates.last W.coordinates.root := by
    rw [hS.last,hS.root]
    exact hS.bad
  exact lower_layer_step_d hM hE hT hS.run hS.coordinates hBad hS.width k

end KP1Y.OneYFinite.LowerLayer
