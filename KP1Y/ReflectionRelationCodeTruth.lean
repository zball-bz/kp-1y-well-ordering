import KP1Y.ReflectionRelationCode

/-! 同一 R/P 原子码在大解释及初等高度小解释上的精确真值。
P 的最后一个语义参数始终是背景 C.top；缩小载域不会改成 δ。 -/
namespace KP1Y.ReflectionModel
open YesMetaZFC YesMetaZFC.SetTheory
open KP1Y.Kuratowski KP1Y.Functions KP1Y.Satisfaction
universe u

private theorem relation_result_iff {M : SetTheory.Structure.{u}} (he : Extensional M) {C : ArticleData M.Domain}
    {A scope s Atom code uk uη ua ub k η a b : M.Domain} (hSub : M.MemberSubset A C.top) (hS : Graph M s scope A)
    (hk : MemPair M s uk k) (hη : MemPair M s uη η) (ha : MemPair M s ua a) (hb : MemPair M s ub b)
    (hResult : ∃ t, Graph M t (C.numbers (symbolArity 2)) A ∧
      (∀ i z, M.mem z A → (MemPair M t (C.numbers (tupleName (symbolArity 2) i)) z ↔ MemPair M s (relationNames uk uη ua ub i) z)) ∧
      (MemPair M Atom code s ↔ Body M C 2 t)) :
    MemPair M Atom code s ↔ KP1Y.Reflection.Query M C.reflection.toIndexData C.table k η a b := by
  obtain ⟨t,hT,hRows,hSem⟩ := hResult
  have ht0 : MemPair M t (C.numbers 0) k := (hRows (0 : Fin 4) k (hS.bounds he hk).2).mpr hk
  have ht1 : MemPair M t (C.numbers 1) η := (hRows (1 : Fin 4) η (hS.bounds he hη).2).mpr hη
  have ht2 : MemPair M t (C.numbers 2) a := (hRows (2 : Fin 4) a (hS.bounds he ha).2).mpr ha
  have ht3 : MemPair M t (C.numbers 3) b := (hRows (3 : Fin 4) b (hS.bounds he hb).2).mpr hb
  exact hSem.trans (relation_body_at he (hT.mono_values hSub) ht0 ht1 ht2 ht3)

private theorem top_result_iff {M : SetTheory.Structure.{u}} (he : Extensional M) {C : ArticleData M.Domain}
    {A scope s Atom code uk uη ua k η a : M.Domain} (hSub : M.MemberSubset A C.top) (hS : Graph M s scope A)
    (hk : MemPair M s uk k) (hη : MemPair M s uη η) (ha : MemPair M s ua a)
    (hResult : ∃ t, Graph M t (C.numbers (symbolArity 3)) A ∧
      (∀ i z, M.mem z A → (MemPair M t (C.numbers (tupleName (symbolArity 3) i)) z ↔ MemPair M s (topNames uk uη ua i) z)) ∧
      (MemPair M Atom code s ↔ Body M C 3 t)) :
    MemPair M Atom code s ↔ KP1Y.Reflection.Query M C.reflection.toIndexData C.table k η a C.top := by
  obtain ⟨t,hT,hRows,hSem⟩ := hResult
  have ht0 : MemPair M t (C.numbers 0) k := (hRows (0 : Fin 3) k (hS.bounds he hk).2).mpr hk
  have ht1 : MemPair M t (C.numbers 1) η := (hRows (1 : Fin 3) η (hS.bounds he hη).2).mpr hη
  have ht2 : MemPair M t (C.numbers 2) a := (hRows (2 : Fin 3) a (hS.bounds he ha).2).mpr ha
  exact hSem.trans (top_body_at he (hT.mono_values hSub) ht0 ht1 ht2)

theorem RelationCode.value_iff_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory) {C : ArticleData M.Domain} (hC : C.Valid M)
    {A : M.Domain} {D : RelationalData M.Domain} (hD : ArticleInterpretation M C A D) {Atom : M.Domain} (hAtom : AtomicTable M D Atom)
    {scope uk uη ua ub code s k η a b : M.Domain} (hSub : M.MemberSubset A C.top) (hs : M.mem scope D.omega)
    (h : RelationCode M (C.numbers 0) (C.numbers 1) (C.numbers 2) (C.numbers 3) (C.numbers 4) D.variables scope uk uη ua ub code)
    (hS : Graph M s scope A) (hk : MemPair M s uk k) (hη : MemPair M s uη η) (ha : MemPair M s ua a) (hb : MemPair M s ub b) :
    MemPair M Atom code s ↔ KP1Y.Reflection.Query M C.reflection.toIndexData C.table k η a b :=
  relation_result_iff hM.1 hSub hS hk hη ha hb
    (((relationCode_iff_atomCode C D scope uk uη ua ub code).mp h).evaluate_d hM hC hD hAtom hs hS)

theorem TopCode.value_iff_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory) {C : ArticleData M.Domain} (hC : C.Valid M)
    {A : M.Domain} {D : RelationalData M.Domain} (hD : ArticleInterpretation M C A D) {Atom : M.Domain} (hAtom : AtomicTable M D Atom)
    {scope uk uη ua code s k η a : M.Domain} (hSub : M.MemberSubset A C.top) (hs : M.mem scope D.omega)
    (h : TopCode M (C.numbers 0) (C.numbers 1) (C.numbers 2) (C.numbers 3) D.variables scope uk uη ua code)
    (hS : Graph M s scope A) (hk : MemPair M s uk k) (hη : MemPair M s uη η) (ha : MemPair M s ua a) :
    MemPair M Atom code s ↔ KP1Y.Reflection.Query M C.reflection.toIndexData C.table k η a C.top :=
  top_result_iff hM.1 hSub hS hk hη ha
    (((topCode_iff_atomCode C D scope uk uη ua code).mp h).evaluate_d hM hC hD hAtom hs hS)

theorem Height.relation_value_iff_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory) {C : ArticleData M.Domain} (hC : C.Valid M)
    {S : ArticleStructure M.Domain} (hS : S.Valid M C) {δ : M.Domain} {small : EvaluationData M.Domain} (h : Height M C S δ small)
    {scope uk uη ua ub code s k η a b : M.Domain} (hs : M.mem scope S.context.omega)
    (hCode : RelationCode M (C.numbers 0) (C.numbers 1) (C.numbers 2) (C.numbers 3) (C.numbers 4) S.relations.variables scope uk uη ua ub code)
    (hAssign : Graph M s scope small.carrier)
    (hk : MemPair M s uk k) (hη : MemPair M s uη η) (ha : MemPair M s ua a) (hb : MemPair M s ub b) :
    MemPair M small.atomic code s ↔ KP1Y.Reflection.Query M C.reflection.toIndexData C.table k η a b := by
  have hSub : M.MemberSubset small.carrier C.top := by
    intro z hz
    exact Eq.mp (congrArg (M.mem z) hS.carrier) (h.elementary.carrier_subset z hz)
  exact relation_result_iff hM.1 hSub hAssign hk hη ha hb
    (h.evaluate_atom_d hM hC hS hs ((relationCode_iff_atomCode C S.relations scope uk uη ua ub code).mp hCode) hAssign)

theorem Height.top_value_iff_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory) {C : ArticleData M.Domain} (hC : C.Valid M)
    {S : ArticleStructure M.Domain} (hS : S.Valid M C) {δ : M.Domain} {small : EvaluationData M.Domain} (h : Height M C S δ small)
    {scope uk uη ua code s k η a : M.Domain} (hs : M.mem scope S.context.omega)
    (hCode : TopCode M (C.numbers 0) (C.numbers 1) (C.numbers 2) (C.numbers 3) S.relations.variables scope uk uη ua code)
    (hAssign : Graph M s scope small.carrier)
    (hk : MemPair M s uk k) (hη : MemPair M s uη η) (ha : MemPair M s ua a) :
    MemPair M small.atomic code s ↔ KP1Y.Reflection.Query M C.reflection.toIndexData C.table k η a C.top := by
  have hSub : M.MemberSubset small.carrier C.top := by
    intro z hz
    exact Eq.mp (congrArg (M.mem z) hS.carrier) (h.elementary.carrier_subset z hz)
  exact top_result_iff hM.1 hSub hAssign hk hη ha
    (h.evaluate_atom_d hM hC hS hs ((topCode_iff_atomCode C S.relations scope uk uη ua code).mp hCode) hAssign)

end KP1Y.ReflectionModel
