import KP1Y.ReflectionBinaryCode

/-! 二元原子的大小结构真值直接等于被命名的两个值的等号/序关系。 -/
namespace KP1Y.ReflectionModel
open YesMetaZFC YesMetaZFC.SetTheory
open KP1Y.Kuratowski KP1Y.Functions KP1Y.Satisfaction
universe u

private theorem binary_result_iff {M : SetTheory.Structure.{u}} (he : Extensional M) {C : ArticleData M.Domain}
    {A scope s Atom a u v x y : M.Domain} (strict : Bool) (hSub : M.MemberSubset A C.top) (hS : Graph M s scope A)
    (hu : MemPair M s u x) (hv : MemPair M s v y)
    (hResult : ∃ t, Graph M t (C.numbers (symbolArity (binaryKind strict))) A ∧
      (∀ i z, M.mem z A → (MemPair M t (C.numbers (tupleName (symbolArity (binaryKind strict)) i)) z ↔ MemPair M s (pairValues u v i) z)) ∧
      (MemPair M Atom a s ↔ Body M C (binaryKind strict) t)) :
    MemPair M Atom a s ↔ (if strict then M.mem x y else x=y) := by
  cases strict
  · obtain ⟨t,hT,hRows,hSem⟩ := hResult
    have ht0 : MemPair M t (C.numbers 0) x := (hRows (0 : Fin 2) x (hS.bounds he hu).2).mpr hu
    have ht1 : MemPair M t (C.numbers 1) y := (hRows (1 : Fin 2) y (hS.bounds he hv).2).mpr hv
    exact hSem.trans (binary_body_at he false (hT.mono_values hSub) ht0 ht1)
  · obtain ⟨t,hT,hRows,hSem⟩ := hResult
    have ht0 : MemPair M t (C.numbers 0) x := (hRows (0 : Fin 2) x (hS.bounds he hu).2).mpr hu
    have ht1 : MemPair M t (C.numbers 1) y := (hRows (1 : Fin 2) y (hS.bounds he hv).2).mpr hv
    exact hSem.trans (binary_body_at he true (hT.mono_values hSub) ht0 ht1)

theorem BinaryCode.value_iff_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory) {C : ArticleData M.Domain} (hC : C.Valid M)
    {A : M.Domain} {D : RelationalData M.Domain} (hD : ArticleInterpretation M C A D) {Atom : M.Domain} (hAtom : AtomicTable M D Atom)
    {strict : Bool} {scope u v a s x y : M.Domain} (hSub : M.MemberSubset A C.top) (hb : M.mem scope D.omega)
    (h : BinaryCode strict M (C.numbers 0) (C.numbers 1) (C.numbers 2) D.variables scope u v a)
    (hS : Graph M s scope A) (hu : MemPair M s u x) (hv : MemPair M s v y) :
    MemPair M Atom a s ↔ (if strict then M.mem x y else x=y) :=
  binary_result_iff hM.1 strict hSub hS hu hv
    (((binaryCode_iff_atomCode strict C D scope u v a).mp h).evaluate_d hM hC hD hAtom hb hS)

theorem Height.binary_value_iff_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory) {C : ArticleData M.Domain} (hC : C.Valid M)
    {S : ArticleStructure M.Domain} (hS : S.Valid M C) {δ : M.Domain} {small : EvaluationData M.Domain} (h : Height M C S δ small)
    {strict : Bool} {scope u v a s x y : M.Domain} (hb : M.mem scope S.context.omega)
    (hCode : BinaryCode strict M (C.numbers 0) (C.numbers 1) (C.numbers 2) S.relations.variables scope u v a)
    (hAssign : Graph M s scope small.carrier) (hu : MemPair M s u x) (hv : MemPair M s v y) :
    MemPair M small.atomic a s ↔ (if strict then M.mem x y else x=y) := by
  have hSub : M.MemberSubset small.carrier C.top := by
    intro z hz
    exact Eq.mp (congrArg (M.mem z) hS.carrier) (h.elementary.carrier_subset z hz)
  exact binary_result_iff hM.1 strict hSub hAssign hu hv
    (h.evaluate_atom_d hM hC hS hb ((binaryCode_iff_atomCode strict C S.relations scope u v a).mp hCode) hAssign)

end KP1Y.ReflectionModel
