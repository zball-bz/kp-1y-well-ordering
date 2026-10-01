import KP1Y.OneYLowerBlockAssembly
import KP1Y.OneYLowerCanonKeyHigh
import KP1Y.OneYTowerCanonInterface

/-! `KeyTransport` 由 LANE-B 的四种起点运输（低行/floor/抬升/锥外）与上层 `UpperOrder` 实际证明，
从而得到无条件的 Lower 装饰阻挡（`BlockersPart` 字段形状）。 -/
namespace KP1Y.OneYFinite.LowerBlock
open YesMetaZFC YesMetaZFC.SetTheory YesMetaZFC.SetTheory.Definitional
open KP1Y.Kuratowski KP1Y.Functions KP1Y.Naturals KP1Y.Bounded KP1Y.Arithmetic
open KP1Y.OneYFinite KP1Y.OneYFinite.CopyCoordinates KP1Y.OneYFinite.CopiedMountain
open KP1Y.OneYFinite.CopiedMountain.Lower KP1Y.OneYFinite.LowerCanon
universe u

/-- 原 `keyLE_succ_rowCopy`：四种目标行位置各调用一条起点运输。 -/
theorem key_transport_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {D : Lower.Context M.Domain} (hD : D.Valid M C) {Y : Data M.Domain} (hY : Y.Valid M C) {n : M.Domain}
    (hCopy : Copies M C T D n Y) {m : M.Domain} {R : RowStateSpace M.Domain} {V P H : M.Domain}
    (hRun : RowRun M C m R V P H) (hFrom : FromRun M C m R V H D.mountain) {oldTop newTop : M.Domain}
    (hOrder : ∀ Pseudo, GraphPseudoForest M C D.mountain Pseudo → UpperOrder M C T D Pseudo oldTop newTop) :
    KeyTransport M C T D Y oldTop newTop := by
  intro v w sY t t' Q0 s0 a p0 b c x tc ta tc' ta' hSucc hQ0 hS0 hA hBad has hsLast hLifted ht ht' hMap hMapA hc _
    hTC hTA hTC' hTA' hKey
  have hw := omega_isOrdinal_d hM hC.omega
  obtain ⟨Pseudo,hPseudo⟩ := graph_pseudo_forest_exists_d hM hC hD.mountain
  have hUpper := hOrder Pseudo hPseudo
  have hwNat : M.mem w C.omega := (hD.mountain.parents.bounds hM.1 hQ0).1
  have hvNat : M.mem v C.omega := hw.transitive w hwNat v hSucc.predecessor_mem
  have hForest := hD.mountain.forest w Q0 hQ0
  have hp0ω := hw.transitive _ hD.mountain.width p0 (hForest.bounds hM.1 hS0).2
  have hRootP0 := nat_le_of_not_lt hM hC hp0ω hD.coordinates.root hBad
  have haω : M.mem a C.omega := hw.transitive s0 hMap.1 a has
  have hRootA : M.mem D.coordinates.root a := nat_lt_of_le_of_lt hM hC haω hRootP0 (hForest.left a p0 hA)
  have hQ0mem := (hD.mountain.parents.bounds hM.1 hQ0).2
  have hCommon : ∃ p, ParentAt M D.mountain w s0 p ∧ ParentAt M D.mountain w a p :=
    ⟨p0,⟨Q0,hQ0mem,hQ0,hS0⟩,⟨Q0,hQ0mem,hQ0,hA⟩⟩
  have hConeIff (hHigh : D.floor=w ∨ M.mem D.floor w) : InCone M C D s0 ↔ InCone M C D a :=
    (in_cone_ancestor_iff_d hM hC hD hRun hFrom hHigh hQ0 (ancestor_direct_d hM hC hForest hS0)).symm.trans
      (in_cone_ancestor_iff_d hM hC hD hRun hFrom hHigh hQ0 (ancestor_direct_d hM hC hForest hA))
  rcases hLifted with ⟨hNot,hsY⟩ | ⟨⟨hCone,hFloorV⟩,off,_,hMul,hAdd⟩
  · subst sY
    have htt := Structure.SuccessorOf.eq hM.1 ht' ht
    subst htt
    by_cases hLow : M.mem w D.floor
    · exact hCopy.canon_key_low_start_d hM hC hT hD hY hRun hFrom hUpper hPseudo hLow ht hRootA has hsLast hCommon
        hMap hMapA hc hTC hTA hTC' hTA' hKey
    have hHigh := nat_le_of_not_lt hM hC hwNat (hD.floor_nat hM.1) hLow
    by_cases hConeS : InCone M C D s0
    · have hvLow : M.mem v D.floor := by
        rcases nat_le_or_lt hM hC (hD.floor_nat hM.1) hvNat with hle | hlt
        · exact False.elim (hNot ⟨hConeS,hle⟩)
        · exact hlt
      have hwFloor : w=D.floor := by
        rcases nat_succ_le_of_lt hM hC hvNat (hD.floor_nat hM.1) hSucc hvLow with he | hlt
        · exact he
        · exact False.elim (hLow hlt)
      rw [hwFloor] at ht hCommon
      exact hCopy.canon_key_floor_start_d hM hC hT hD hY hRun hFrom hUpper hPseudo ht hRootA has hsLast hCommon
        hMap hMapA hc hTC hTA hTC' hTA' hKey
    · have hOutA : ¬InCone M C D a := fun h => hConeS ((hConeIff hHigh).mpr h)
      have hsLast' := hsLast.resolve_left (fun he => hConeS (he ▸ in_cone_last hD))
      exact hCopy.canon_key_outside_start_d hM hC hT hD hY hRun hFrom hUpper hPseudo hHigh ht hConeS hOutA hRootA has
        hsLast' hCommon hMap hMapA hc hTC hTA hTC' hTA' hKey
  · have hHigh : D.floor=w ∨ M.mem D.floor w := Or.inr (nat_lt_of_le_of_lt hM hC hwNat hFloorV hSucc.predecessor_mem)
    exact hCopy.canon_key_lifted_start_d hM hC hT hD hY hRun hFrom hUpper hPseudo hHigh ht hMul hAdd ht' hCone
      ((hConeIff hHigh).mp hCone) hRootA has hsLast hCommon hMap hMapA hc hTC hTA hTC' hTA' hKey

/-- Lower复制目标Y的装饰阻挡（无条件形式）：源实际运行、上层 `prefixTop/fixed/order` 三项输入。 -/
theorem lower_decorated_blockers_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {D : Lower.Context M.Domain} (hD : D.Valid M C) {Y : Data M.Domain} (hY : Y.Valid M C) {n : M.Domain}
    (hCopy : Copies M C T D n Y) {m : M.Domain} {R : RowStateSpace M.Domain} {V P H : M.Domain}
    (hRun : RowRun M C m R V P H) (hPositive : ∀ c a, MemPair M V c a → M.mem C.zero a)
    (hFrom : FromRun M C m R V H D.mountain) {oldTop Qnext newTop : M.Domain}
    (hExtraction : Extraction M C m V P oldTop Qnext) (hNewTop : Graph M newTop n C.omega)
    (hPrefixTop : RowsAgreeOn M newTop oldTop D.coordinates.last) (hFixed : UpperFixed M C T D oldTop Qnext n newTop)
    (hOrder : ∀ Pseudo, GraphPseudoForest M C D.mountain Pseudo → UpperOrder M C T D Pseudo oldTop newTop) :
    ReconstructionRecovery.DecoratedBlockers M C Y newTop :=
  decorated_blockers_of_key_d hM hC hT hD hY hCopy hRun hPositive hFrom hExtraction hNewTop hPrefixTop hFixed
    (key_transport_d hM hC hT hD hY hCopy hRun hFrom hOrder)

/-- `LowerLayer.BlockersPart` 字段（LANE-B `OneYLowerLayerStep.lean`）的实际证明。
`hLayers` 只用于源第k行的正值性（`LayerRun.at_rooted`）。 -/
theorem blockers_part_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {A : CopyCoordinates.Context M.Domain} {m : M.Domain} {L : LayerStateSpace M.Domain} {V P H K k N n : M.Domain}
    (hLayers : LayerRun M C m L V P H) :
    ∀ {W Q J oldTop Qnext newTop Pnext : M.Domain} {D : Lower.Context M.Domain} {Y : Data M.Domain},
      TowerCanon.LowerLayerData M C T A m L H K k n W Q J oldTop Qnext D Y →
      Graph M newTop n C.omega → (∀ c v, MemPair M newTop c v → M.mem C.zero v) →
      TowerCanon.LowerInputs M C T D m N n oldTop Qnext newTop Pnext →
      ReconstructionRecovery.DecoratedBlockers M C Y newTop := by
  intro W Q J oldTop Qnext newTop Pnext D Y hData hNew _ hInputs
  exact lower_decorated_blockers_d hM hC hT hData.context hData.target hData.copies hData.run
    (hLayers.at_rooted hM.1 hData.layer).positive hData.from_run hData.extraction hNew hInputs.prefixTop hInputs.fixed
    hInputs.order

end KP1Y.OneYFinite.LowerBlock
