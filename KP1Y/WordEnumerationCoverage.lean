import KP1Y.WordEnumeration

/-! 用内部序列长度归纳证明字词枚举满射，覆盖非标准模型中的全部有限字词。 -/
namespace KP1Y.Naturals
open YesMetaZFC YesMetaZFC.SetTheory YesMetaZFC.SetTheory.Definitional
open KP1Y.Kuratowski KP1Y.Functions KP1Y.Sequences KP1Y.Iteration KP1Y.Cardinal
universe u

private def wordCoverageSchema : Project.Delta0UnarySchema 3 where
  body := Project.Formula.forallMem (.bound 2) (.imp (graphFormula (.bound 0) (.bound 1) (.bound 4))
    (reachedFormula (.bound 4) (.bound 2) (.bound 0)))
  freeClosed := by
    simp [graphFormula, reachedFormula, memPairFormula, codeFormula, pairFormula,
      Project.Formula.existsMem, Project.Formula.forallMem, Definitional.Formula.FreeClosed]
  delta0 := .forallMem _ (.imp (graphFormula_delta0 _ _ _) (reachedFormula_delta0 _ _ _))

private theorem wordCoverageSchema_iff {M : SetTheory.Structure.{u}} (he : Extensional M) (ω Words F length : M.Domain) :
    Project.Formula.satisfies ((((oneEnv ω).push Words).push F).push length) wordCoverageSchema.body ↔
      ∀ w, M.mem w Words → Graph M w length ω → Reached M ω F w := by
  simp only [wordCoverageSchema, Project.Formula.satisfies_forallMem_iff, Project.Formula.satisfies_imp_iff,
    graphFormula_iff he, reachedFormula_iff he]
  rfl

theorem word_trace_onto_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {ω Words Pairs decode zero F : M.Domain} (hω : M.IsOmega ω) (hDecode : NaturalPairing M ω Pairs decode)
    (hWords : ∀ w, M.mem w Words ↔ ∃ n, M.mem n ω ∧ Graph M w n ω)
    (hZero : M.mem zero ω) (hEmpty : ∀ x, ¬M.mem x zero) (hF : WordTrace M ω Words Pairs decode zero F) :
    Onto M F ω Words := by
  have hAll := natural_induction_d hM wordCoverageSchema.toUnarySchema (((oneEnv ω).push Words).push F) hω
    (fun e he => (wordCoverageSchema_iff hM.1 ω Words F e).mpr (by
      intro w _ hW
      have heq := hM.1.eq_of_same_members e zero (fun x => iff_of_false (he x) (hEmpty x))
      subst e
      have hwz : w=zero := hW.ext hM.1 (empty_graph (V := ω) hEmpty) (fun x hx => False.elim (hEmpty x hx))
      subst w
      exact ⟨zero,hZero,hF.initial⟩))
    (fun length hLength ih next hSucc => (wordCoverageSchema_iff hM.1 ω Words F next).mpr (by
      intro w _ hW
      obtain ⟨old,a,hOld,ha,hAppend⟩ := graph_decompose_d hM hW hSucc
      have hOldWord := (hWords old).mpr ⟨length,hLength,hOld⟩
      obtain ⟨i,hi,hAtOld⟩ := (wordCoverageSchema_iff hM.1 ω Words F length).mp ih old hOldWord hOld
      obtain ⟨pair,hCode⟩ := codes_total hM i a
      have hPair := (hDecode.product pair).mpr ⟨i,hi,a,ha,hCode⟩
      obtain ⟨k,hk,hDecodeAt⟩ := hDecode.onto.2.2.2 pair hPair
      obtain ⟨k',hkSucc,hk'⟩ := hω.1.2 k hk
      obtain ⟨value,_,hAtValue⟩ := hF.graph.total k' hk'
      obtain ⟨length',_,hOld',hAppend'⟩ := hF.step k k' pair i a old value hk hkSucc hDecodeAt hCode hAtOld hAtValue
      have hLengths := KP1Y.Assignments.domain_unique hM.1 hOld' hOld
      subst length'
      have hValue := append_unique hM.1 hAppend' hAppend
      subst value
      exact ⟨k',hk',hAtValue⟩))
  refine ⟨hF.graph.support,hF.graph.total,fun i _ x _ y _ hx hy => hF.graph.unique i x y hx hy,?_⟩
  intro w hw
  obtain ⟨length,hLength,hGraph⟩ := (hWords w).mp hw
  exact (wordCoverageSchema_iff hM.1 ω Words F length).mp (hAll length hLength) w hw hGraph

theorem natural_words_countable_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {ω Words : M.Domain} (hω : M.IsOmega ω)
    (hWords : ∀ w, M.mem w Words ↔ ∃ n, M.mem n ω ∧ Graph M w n ω) : ∃ F, Onto M F ω Words := by
  obtain ⟨Pairs,decode,hDecode⟩ := natural_pairing_exists_d hM hω
  obtain ⟨zero,hEmpty,hZero⟩ := hω.1.1
  obtain ⟨F,hF⟩ := word_trace_exists_d hM hω hDecode hWords hZero hEmpty
  exact ⟨F,word_trace_onto_d hM hω hDecode hWords hZero hEmpty hF⟩

end KP1Y.Naturals
