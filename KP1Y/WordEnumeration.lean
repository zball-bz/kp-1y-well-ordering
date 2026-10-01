import KP1Y.WordEnumerationSyntax

/-! 在任意 KPω 模型内执行字词解码，递归只使用已证明更小的编号。 -/
namespace KP1Y.Naturals
open YesMetaZFC YesMetaZFC.SetTheory
open KP1Y.Kuratowski KP1Y.Functions KP1Y.Sequences
universe u

structure WordTrace (M : SetTheory.Structure.{u}) (ω Words Pairs decode zero F : M.Domain) : Prop where
  graph : Graph M F ω Words
  initial : MemPair M F zero zero
  step : ∀ n next pair j a old value, M.mem n ω → M.SuccessorOf next n →
    MemPair M decode n pair → Codes M pair j a → MemPair M F j old → MemPair M F next value →
      ∃ length, M.mem length ω ∧ Graph M old length ω ∧ Append M value old length a

theorem word_trace_exists_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {ω Words Pairs decode zero : M.Domain} (hω : M.IsOmega ω) (hDecode : NaturalPairing M ω Pairs decode)
    (hWords : ∀ w, M.mem w Words ↔ ∃ n, M.mem n ω ∧ Graph M w n ω)
    (hZero : M.mem zero ω) (hEmpty : ∀ x, ¬M.mem x zero) : ∃ F, WordTrace M ω Words Pairs decode zero F := by
  have hZeroWord := (hWords zero).mpr ⟨zero,hZero,empty_graph hEmpty⟩
  obtain ⟨F,V,Q,hF⟩ := KP1Y.SigmaRecursion.value_recursion_d hM wordMatrix (wordEnv ω Words Pairs decode zero)
    (omega_isOrdinal_d hM hω) (wordMatrix_total_d hM hω hDecode hWords hZeroWord)
    (wordMatrix_functional_d hM hω hDecode)
  have hStep : ∀ i, M.mem i ω → ∀ value, MemPair M F i value →
      ∃ Pref w, Prefix M Pref F i V ∧ WordStep M ω Words Pairs decode zero i Pref value w := by
    intro i hi value hAt
    obtain ⟨Pref,hPV,hQi⟩ := hF.prefixes.total i hi
    obtain ⟨hPrefix,w,_,hState⟩ := hF.obeys i hi Pref hPV value (hF.values.bounds hM.1 hAt).2 hQi hAt
    exact ⟨Pref,w,hPrefix,(wordMatrix_iff hM.1 ω Words Pairs decode zero i Pref value w).mp hState⟩
  have hGraph : Graph M F ω Words := KP1Y.Assignments.graph_tighten_values hF.values (by
    intro i value hAt
    obtain ⟨_,_,_,hState⟩ := hStep i (hF.values.bounds hM.1 hAt).1 value hAt
    exact hState.1)
  refine ⟨F,hGraph,?_,?_⟩
  · obtain ⟨value,_,hAt⟩ := hGraph.total zero hZero
    obtain ⟨_,_,_,hState⟩ := hStep zero hZero value hAt
    rcases hState.2.2 with ⟨_,he⟩ | ⟨n,hn,_⟩
    · subst value
      exact hAt
    · exact False.elim (hEmpty n hn)
  · intro n next pair j a old value hn hSucc hAtDecode hCode hOldAt hValueAt
    have hNext := (hGraph.bounds hM.1 hValueAt).1
    have hOldWord := (hGraph.bounds hM.1 hOldAt).2
    obtain ⟨Pref,w,hPrefix,hState⟩ := hStep next hNext value hValueAt
    rcases hState.2.2 with ⟨hNone,_⟩ | ⟨n',_,pair',_,j',hjNext,a',_,old',_,hSucc',hAtDecode',hCode',hOld',hExt⟩
    · exact False.elim (hNone n hSucc.predecessor_mem)
    · have hnn' := Structure.SuccessorOf.predecessor_eq hM.1 ((omega_isOrdinal_d hM hω).mem hn) hSucc hSucc'
      subst n'
      have hpair := hDecode.graph.unique n pair pair' hAtDecode hAtDecode'
      subst pair'
      obtain ⟨hjj',haa'⟩ := codes_injective hM.1 hCode hCode'
      subst j'
      subst a'
      have hOldAt' := (hPrefix.all_rows hM.1 hF.values j hjNext old').mp hOld'
      have hOldEq := hGraph.unique j old old' hOldAt hOldAt'
      subst old'
      rcases hExt with ⟨_,length,hLength,hOldGraph,hAppend⟩ | ⟨hNot,_⟩
      · exact ⟨length,hLength,hOldGraph,hAppend⟩
      · exact False.elim (hNot hOldWord)

end KP1Y.Naturals
