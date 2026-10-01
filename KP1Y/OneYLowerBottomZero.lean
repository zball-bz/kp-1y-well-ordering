import KP1Y.OneYLowerBottomFrame
import KP1Y.OneYLowerBlockKey

/-! Lower复制第0行的坏部父运输：共同坏部父的源列在目标第0行的祖先路径与第1行起点KeyLE
（原 `zero_forest_eq_frameCopy` 的祖先部分与 `keyLE_bottom_parent`）。 -/
namespace KP1Y.OneYFinite.LowerBlock
open YesMetaZFC YesMetaZFC.SetTheory YesMetaZFC.SetTheory.Definitional
open KP1Y.Kuratowski KP1Y.Functions KP1Y.Naturals KP1Y.Bounded KP1Y.Arithmetic
open KP1Y.OneYFinite KP1Y.OneYFinite.CopyCoordinates KP1Y.OneYFinite.CopiedMountain
open KP1Y.OneYFinite.CopiedMountain.Lower KP1Y.OneYFinite.LowerCanon
universe u

theorem floor_zero_of_not_low_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {D : Lower.Context M.Domain} (hD : D.Valid M C)
    (h0 : ¬M.mem C.zero D.floor) : D.floor=C.zero :=
  (zero_le_d hM hC (hD.floor_nat hM.1)).elim (fun h => h.symm) (fun h => False.elim (h0 h))

/-- 第0行：源列 s0 与其祖先端 a 共享坏部父 p0；a 到 q0 的源祖先运输为目标第0行祖先。 -/
theorem zero_ancestor_copy_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {D : Lower.Context M.Domain} (hD : D.Valid M C) {Y : Data M.Domain} (hY : Y.Valid M C) {n : M.Domain}
    (hCopy : Copies M C T D n Y) {m : M.Domain} {R : RowStateSpace M.Domain} {V P H : M.Domain}
    (hRun : RowRun M C m R V P H) (hFrom : FromRun M C m R V H D.mountain)
    {Q0 G s0 a q0 p0 b x y : M.Domain}
    (hQ0 : MemPair M D.mountain.parents C.zero Q0) (hG : MemPair M Y.parents C.zero G)
    (hSource : Source M D.coordinates s0) (hS0 : MemPair M Q0 s0 p0) (hAP : MemPair M Q0 a p0)
    (hBad : ¬M.mem p0 D.coordinates.root) (hAnc : Ancestor M C D.mountain.width Q0 a q0) (hq0s : M.mem q0 s0)
    (hMapA : ParentCopy M C T D.coordinates b a x) (hMapQ : ParentCopy M C T D.coordinates b q0 y)
    (hy : M.mem y Y.width) : Ancestor M C Y.width G x y := by
  have hw := omega_isOrdinal_d hM hC.omega
  have hq0Last : q0=D.coordinates.last ∨ M.mem q0 D.coordinates.last :=
    Or.inr (nat_lt_of_lt_of_le hM hC hD.coordinates.last hq0s hSource.2)
  classical
  by_cases h0 : M.mem C.zero D.floor
  · exact hCopy.low_ancestor_parent_copy_d hM hC hT hD hY hRun hFrom h0 hQ0 hG hAnc hq0Last hMapA hMapQ hy
  have hf0 := floor_zero_of_not_low_d hM hC hD h0
  have hHigh : D.floor=C.zero ∨ M.mem D.floor C.zero := Or.inl hf0
  have hForest := hD.mountain.forest C.zero Q0 hQ0
  have hConeIff : InCone M C D s0 ↔ InCone M C D a :=
    (in_cone_ancestor_iff_d hM hC hD hRun hFrom hHigh hQ0 (ancestor_direct_d hM hC hForest hS0)).symm.trans
      (in_cone_ancestor_iff_d hM hC hD hRun hFrom hHigh hQ0 (ancestor_direct_d hM hC hForest hAP))
  by_cases hCone : InCone M C D s0
  · have hConeA := hConeIff.mp hCone
    have hConeQ0 := (in_cone_ancestor_iff_d hM hC hD hRun hFrom hHigh hQ0 hAnc).mp hConeA
    have hEncQ : Encode M C T D.coordinates q0 b y := (parent_copy_bad_iff (hConeQ0.not_good_d hM hC hD)).mp hMapQ
    obtain ⟨off,hOff,hMul⟩ := hT.mul.mul_exists_d hM hC hMapA.2.1 (hD.rise_nat hM.1)
    obtain ⟨u,hShift⟩ := shifted_row_exists_d hM hC hT (hD.floor_nat hM.1) hOff hC.zero_nat
    have hShift' := hShift
    rw [← hf0] at hShift'
    have hu : u=C.zero := (hShift'.floor_value_d hM hC hT).trans hf0
    rw [hu] at hShift
    have hp0ω := hw.transitive D.mountain.width hD.mountain.width p0 (hForest.bounds hM.1 hS0).2
    have hRootP0 := nat_le_of_not_lt hM hC hp0ω hD.coordinates.root hBad
    have hs0ω : M.mem s0 C.omega := hSource.2.elim (fun he => he ▸ hD.coordinates.last)
      (fun h => hw.transitive D.coordinates.last hD.coordinates.last s0 h)
    have hq0ω := hw.transitive s0 hs0ω q0 hq0s
    have hRootA : M.mem D.coordinates.root a :=
      nat_lt_of_le_of_lt hM hC (hw.transitive q0 hq0ω a hAnc.1) hRootP0 (hForest.left a p0 hAP)
    exact hCopy.high_ancestor_copy_d hM hC hT hD hRun hFrom hY ⟨nat_lt_trans hM hC hq0ω hRootA hAnc.1,hq0Last⟩
      hConeQ0 hHigh hMul hShift hEncQ (hCopy.width ▸ hy) hQ0 hG hAnc hMapA
  · exact copy_ancestor_d hM hC hT hD hY hCopy hRun hFrom hC.zero_nat hQ0 hG hAnc hq0Last hMapA hMapQ hy
      (Or.inr (fun h => hCone (hConeIff.mpr h)))

/-- 原 `keyLE_bottom_parent`：第0行共同父（root<a<s0），第1行起点KeyLE运输。 -/
theorem zero_key_transport_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {D : Lower.Context M.Domain} (hD : D.Valid M C) {Y : Data M.Domain} (hY : Y.Valid M C) {n : M.Domain}
    (hCopy : Copies M C T D n Y) {m : M.Domain} {R : RowStateSpace M.Domain} {V P H : M.Domain}
    (hRun : RowRun M C m R V P H) (hFrom : FromRun M C m R V H D.mountain) {oldTop newTop : M.Domain}
    (hOrder : ∀ Pseudo, GraphPseudoForest M C D.mountain Pseudo → UpperOrder M C T D Pseudo oldTop newTop)
    {Q0 s0 a p0 b c x tc ta tc' ta' : M.Domain}
    (hQ0 : MemPair M D.mountain.parents C.zero Q0) (hS0 : MemPair M Q0 s0 p0) (hAP : MemPair M Q0 a p0)
    (hRootA : M.mem D.coordinates.root a) (has : M.mem a s0) (hsLast : s0=D.coordinates.last ∨ M.mem s0 D.coordinates.last)
    (hMap : ParentCopy M C T D.coordinates b s0 c) (hMapA : ParentCopy M C T D.coordinates b a x) (hc : M.mem c Y.width)
    (hTC : MemPair M oldTop s0 tc) (hTA : MemPair M oldTop a ta) (hTC' : MemPair M newTop c tc') (hTA' : MemPair M newTop x ta')
    (hKey : ForestOrder.KeyLE M C D.mountain s0 a C.one tc ta) : ForestOrder.KeyLE M C Y c x C.one tc' ta' := by
  have hw := omega_isOrdinal_d hM hC.omega
  obtain ⟨Pseudo,hPseudo⟩ := graph_pseudo_forest_exists_d hM hC hD.mountain
  have hUpper := hOrder Pseudo hPseudo
  have hForest := hD.mountain.forest C.zero Q0 hQ0
  have hQ0mem := (hD.mountain.parents.bounds hM.1 hQ0).2
  have hCommon : ∃ p, ParentAt M D.mountain C.zero s0 p ∧ ParentAt M D.mountain C.zero a p :=
    ⟨p0,⟨Q0,hQ0mem,hQ0,hS0⟩,⟨Q0,hQ0mem,hQ0,hAP⟩⟩
  classical
  by_cases h0 : M.mem C.zero D.floor
  · exact hCopy.canon_key_low_start_d hM hC hT hD hY hRun hFrom hUpper hPseudo h0 hC.one_succ hRootA has hsLast hCommon
      hMap hMapA hc hTC hTA hTC' hTA' hKey
  have hf0 := floor_zero_of_not_low_d hM hC hD h0
  have hHigh : D.floor=C.zero ∨ M.mem D.floor C.zero := Or.inl hf0
  have hConeIff : InCone M C D s0 ↔ InCone M C D a :=
    (in_cone_ancestor_iff_d hM hC hD hRun hFrom hHigh hQ0 (ancestor_direct_d hM hC hForest hS0)).symm.trans
      (in_cone_ancestor_iff_d hM hC hD hRun hFrom hHigh hQ0 (ancestor_direct_d hM hC hForest hAP))
  by_cases hCone : InCone M C D s0
  · have ht : M.SuccessorOf C.one D.floor := hf0 ▸ hC.one_succ
    have hCommon' : ∃ p, ParentAt M D.mountain D.floor s0 p ∧ ParentAt M D.mountain D.floor a p := hf0 ▸ hCommon
    exact hCopy.canon_key_floor_start_d hM hC hT hD hY hRun hFrom hUpper hPseudo ht hRootA has hsLast hCommon'
      hMap hMapA hc hTC hTA hTC' hTA' hKey
  · have hsLast' := hsLast.resolve_left (fun he => hCone (he ▸ in_cone_last hD))
    exact hCopy.canon_key_outside_start_d hM hC hT hD hY hRun hFrom hUpper hPseudo hHigh hC.one_succ hCone
      (fun h => hCone (hConeIff.mpr h)) hRootA has hsLast' hCommon hMap hMapA hc hTC hTA hTC' hTA' hKey

end KP1Y.OneYFinite.LowerBlock
