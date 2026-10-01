import KP1Y.OneYLowerHelpBound
import KP1Y.OneYLowerCanonPseudo

/-! LANE-B helper 出口：lower 层 k<K 的伪父Top界与 extract 字段，环境与 `TowerCanon` 接口一致。
新列伪父公式取自 LANE-B 的 `Copies.canon_pseudo_copy_formula_d`（KP1Y/OneYLowerCanonPseudo.lean）。
`_hA` 仅为与环境签名一致而保留（坐标有效性已由 `hData.context` 给出）。 -/
namespace KP1Y.OneYFinite.LowerHelp
open YesMetaZFC YesMetaZFC.SetTheory YesMetaZFC.SetTheory.Definitional
open KP1Y.Kuratowski KP1Y.Functions KP1Y.Naturals KP1Y.Bounded
open KP1Y.OneYFinite KP1Y.OneYFinite.CopiedMountain KP1Y.OneYFinite.TowerCanon
universe u

/-- 实际 Lower 复制满足新列伪父公式。 -/
theorem lower_layer_pseudo_copy_formula_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {A : CopyCoordinates.Context M.Domain} {m : M.Domain} {L : LayerStateSpace M.Domain} {H K k n W Q J oldTop Qnext : M.Domain}
    {D : Lower.Context M.Domain} {Y : Data M.Domain}
    (hData : LowerLayerData M C T A m L H K k n W Q J oldTop Qnext D Y) : PseudoCopyFormula M C T D Y :=
  hData.copies.canon_pseudo_copy_formula_d hM hC hT hData.context hData.target hData.run hData.from_run

/-- (H-bound) 原 `badAtLowerCopiedBase_lowerTopBound` / `pseudoTopBound_of_upper_selections`。 -/
theorem lower_layer_pseudo_top_bound_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {m : M.Domain} {L : LayerStateSpace M.Domain} {V P H K level N n : M.Domain} {A : CopyCoordinates.Context M.Domain}
    (hLayers : LayerRun M C m L V P H) (_hA : A.Valid M C) (hBad : BadAt M C m L H K level A.last A.root)
    (hN : CopyCoordinates.Width M C T A N n)
    {k W Q J oldTop Qnext newTop Pnext : M.Domain} {D : CopiedMountain.Lower.Context M.Domain} {Y : CopiedMountain.Data M.Domain}
    (hData : TowerCanon.LowerLayerData M C T A m L H K k n W Q J oldTop Qnext D Y)
    (hNew : Graph M newTop n C.omega) (hPos : ∀ c v, MemPair M newTop c v → M.mem C.zero v)
    (hInputs : TowerCanon.LowerInputs M C T D m N n oldTop Qnext newTop Pnext) :
    ReconstructionSelection.PseudoTopBound M C Y newTop :=
  lower_layer_pseudo_top_bound_of_formula_d hM hC hT hLayers hBad hN hData hNew hPos hInputs
    (lower_layer_pseudo_copy_formula_d hM hC hT hData)

/-- (H-extract) 恰为 `TowerCanon.LowerLayerStep.extract` 字段（原 `copiedBase_rawExtract` / `pseudo_select_eq_frameCopy`）。 -/
theorem lower_layer_extract_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {m : M.Domain} {L : LayerStateSpace M.Domain} {V P H K level N n : M.Domain} {A : CopyCoordinates.Context M.Domain}
    (hLayers : LayerRun M C m L V P H) (_hA : A.Valid M C) (hBad : BadAt M C m L H K level A.last A.root)
    (hN : CopyCoordinates.Width M C T A N n)
    {k W Q J oldTop Qnext newTop Pnext G : M.Domain} {D : CopiedMountain.Lower.Context M.Domain} {Y : CopiedMountain.Data M.Domain}
    (hData : TowerCanon.LowerLayerData M C T A m L H K k n W Q J oldTop Qnext D Y)
    (hNew : Graph M newTop n C.omega) (hPos : ∀ c v, MemPair M newTop c v → M.mem C.zero v)
    (hInputs : TowerCanon.LowerInputs M C T D m N n oldTop Qnext newTop Pnext) (hG : GraphPseudoForest M C Y G) :
    ∃ F F', Selects true M C m F oldTop Qnext ∧ FrameCopy.Copies M C T A F N n F' ∧
      ∀ Q', Selects true M C n G newTop Q' ↔ Selects true M C n F' newTop Q' :=
  lower_layer_extract_of_formula_d hM hC hT hLayers hBad hN hData hNew hPos hInputs hG
    (lower_layer_pseudo_copy_formula_d hM hC hT hData)

end KP1Y.OneYFinite.LowerHelp
