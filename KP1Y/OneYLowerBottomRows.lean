import KP1Y.OneYLowerBlockAssembly
import KP1Y.OneYTowerCanonInterface

/-! Lower复制的第0行：任意源列 root<s≤last 的复制在第0行的父项恰为源父项的 ParentCopy
（原 `parent_zero_parentCopy`），给出 `LowerLayerStep.nonroot` 字段。 -/
namespace KP1Y.OneYFinite.LowerBlock
open YesMetaZFC YesMetaZFC.SetTheory YesMetaZFC.SetTheory.Definitional
open KP1Y.Kuratowski KP1Y.Functions KP1Y.Naturals KP1Y.Bounded KP1Y.Arithmetic
open KP1Y.OneYFinite KP1Y.OneYFinite.CopyCoordinates KP1Y.OneYFinite.CopiedMountain
open KP1Y.OneYFinite.CopiedMountain.Lower KP1Y.OneYFinite.LowerCanon
universe u

/-- 第0行没有抬升：移动分支只在 floor=0 时出现，此时平移行恰为0。 -/
theorem zero_parent_copy_iff_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {D : Lower.Context M.Domain} (hD : D.Valid M C) {Y : Data M.Domain} {n : M.Domain}
    (hCopy : Copies M C T D n Y) {s b c p : M.Domain} (hSource : Source M D.coordinates s)
    (hMap : ParentCopy M C T D.coordinates b s c) (hc : M.mem c n) :
    ParentAt M Y C.zero c p ↔ ∃ q, ParentAt M D.mountain C.zero s q ∧ ParentCopy M C T D.coordinates b q p := by
  have hw := omega_isOrdinal_d hM hC.omega
  have hNotGood : ¬M.mem s D.coordinates.root := fun h =>
    nat_irrefl hM _ ((hw.mem hD.coordinates.root).transitive s h _ hSource.1)
  have hEnc : Encode M C T D.coordinates s b c := (parent_copy_bad_iff hNotGood).mp hMap
  have hFloorZero (h : D.floor=C.zero ∨ M.mem D.floor C.zero) : D.floor=C.zero :=
    h.resolve_right (hC.zero_empty D.floor)
  rw [hCopy.encoded_parent_iff_d hM hC hT hD hC.zero_nat hSource hEnc hc]
  constructor
  · rintro (⟨⟨hCone,hHigh⟩,off,_,_,u,_,hShift,q,_,hPq,hEncQ⟩ | ⟨_,q,_,hPq,hMapQ⟩)
    · have hf0 := hFloorZero hHigh
      rw [← hf0] at hShift
      have hu := hShift.floor_value_d hM hC hT
      rw [hu,hf0] at hPq
      have hConeQ := hCone.high_parent_d hM hC hD hHigh hPq
      exact ⟨q,hPq,(parent_copy_bad_iff (hConeQ.not_good_d hM hC hD)).mpr hEncQ⟩
    · exact ⟨q,hPq,hMapQ⟩
  · rintro ⟨q,hPq,hMapQ⟩
    classical
    by_cases hMove : InCone M C D s ∧ (D.floor=C.zero ∨ M.mem D.floor C.zero)
    · have hf0 := hFloorZero hMove.2
      obtain ⟨off,hOff,hMul⟩ := hT.mul.mul_exists_d hM hC hMapQ.2.1 (hD.rise_nat hM.1)
      obtain ⟨u,hShift⟩ := shifted_row_exists_d hM hC hT (hD.floor_nat hM.1) hOff hC.zero_nat
      have hShift' := hShift
      rw [← hf0] at hShift'
      have hu := hShift'.floor_value_d hM hC hT
      have hConeQ := hMove.1.high_parent_d hM hC hD hMove.2 hPq
      have hEncQ : Encode M C T D.coordinates q b p := (parent_copy_bad_iff (hConeQ.not_good_d hM hC hD)).mp hMapQ
      refine Or.inl ⟨hMove,off,hOff,hMul,u,hShift.2.1,hShift,q,hMapQ.1,?_,hEncQ⟩
      rw [hu,hf0]
      exact hPq
    · exact Or.inr ⟨hMove,q,hMapQ.1,hPq,hMapQ⟩

/-- `TowerCanon.LowerLayerStep.nonroot` 字段（原 `parent_zero_parentCopy`）。只用 `LowerLayerData`。 -/
theorem lower_layer_nonroot_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {A : CopyCoordinates.Context M.Domain} {m : M.Domain} {L : LayerStateSpace M.Domain} {H K k n : M.Domain}
    {W Q J oldTop Qnext P0 s b c p : M.Domain} {D : Lower.Context M.Domain} {Y : Data M.Domain}
    (hData : TowerCanon.LowerLayerData M C T A m L H K k n W Q J oldTop Qnext D Y)
    (hP0 : MemPair M Y.parents C.zero P0) (hRoot : M.mem A.root s) (hLast : M.mem s A.last)
    (hMap : ParentCopy M C T A b s c) (hc : M.mem c n) :
    MemPair M P0 c p ↔ ∃ q, MemPair M Q s q ∧ ParentCopy M C T A b q p := by
  have hD := hData.context
  have hA := hData.coordinates
  subst hA
  have hQ0 : MemPair M D.mountain.parents C.zero Q :=
    (hData.from_run.parents C.zero Q).mpr ⟨W,hData.run.initial_row_at_d hM⟩
  rw [← canon_row_parent_iff hM.1 hData.target hP0,
    zero_parent_copy_iff_d hM hC hT hD hData.copies ⟨hRoot,Or.inr hLast⟩ hMap hc]
  simp only [canon_row_parent_iff hM.1 hD.mountain hQ0]

end KP1Y.OneYFinite.LowerBlock
