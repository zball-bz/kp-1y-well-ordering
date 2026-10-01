import KP1Y.AssignmentTuple

/-! 大小载域之间的函数、赋值更新及元组求值相容性。 -/
namespace KP1Y.Assignments
open YesMetaZFC YesMetaZFC.SetTheory
open KP1Y.Kuratowski KP1Y.Functions
universe u

theorem graph_tighten_values {M : SetTheory.Structure.{u}} {F n A B : M.Domain}
    (hF : Graph M F n B) (hBound : ∀ i a, MemPair M F i a → M.mem a A) : Graph M F n A := by
  refine ⟨?_,?_,hF.unique⟩
  · intro p hp
    obtain ⟨i,hi,a,_,hCode⟩ := hF.support p hp
    exact ⟨i,hi,a,hBound i a ⟨p,hp,hCode⟩,hCode⟩
  · intro i hi
    obtain ⟨a,_,hAt⟩ := hF.total i hi
    exact ⟨a,hBound i a hAt,hAt⟩

theorem updated_enlarge {M : SetTheory.Structure.{u}} (he : Extensional M)
    {t s n A B v x : M.Domain} (hAB : M.MemberSubset A B) (hS : Graph M s n A)
    (hx : M.mem x A) (h : Updated M t s n A v x) : Updated M t s n B v x := by
  classical
  refine ⟨h.graph.mono_values hAB,?_⟩
  intro i hi a _
  by_cases ha : M.mem a A
  · exact h.rows i hi a ha
  · constructor
    · intro hta
      exact False.elim (ha (h.graph.bounds he hta).2)
    · rintro (hNew | hOld)
      · exact False.elim (ha (hNew.2 ▸ hx))
      · exact False.elim (ha (hS.bounds he hOld.2).2)

theorem updated_restrict {M : SetTheory.Structure.{u}} (he : Extensional M)
    {t s n A B v x : M.Domain} (hAB : M.MemberSubset A B) (hS : Graph M s n A)
    (hx : M.mem x A) (h : Updated M t s n B v x) : Updated M t s n A v x := by
  have hTarget : Graph M t n A := graph_tighten_values h.graph (by
    intro i a hta
    have hb := h.graph.bounds he hta
    rcases (h.rows i hb.1 a hb.2).mp hta with hNew | hOld
    · exact hNew.2 ▸ hx
    · exact (hS.bounds he hOld.2).2)
  exact ⟨hTarget,fun i hi a ha => h.rows i hi a (hAB a ha)⟩

theorem tuple_value_enlarge {M : SetTheory.Structure.{u}} (he : Extensional M)
    {t vars s n m A B : M.Domain} (hAB : M.MemberSubset A B)
    (h : TupleValue M t vars s n m A) : TupleValue M t vars s n m B := by
  classical
  refine ⟨h.variables,h.source.mono_values hAB,h.values.mono_values hAB,?_⟩
  intro k hk j hj a _ hVars
  by_cases ha : M.mem a A
  · exact h.rows k hk j hj a ha hVars
  · exact iff_of_false (fun ht => ha (h.values.bounds he ht).2) (fun hs => ha (h.source.bounds he hs).2)

end KP1Y.Assignments
