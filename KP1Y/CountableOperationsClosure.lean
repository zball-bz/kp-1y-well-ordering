import KP1Y.CountableClosure

/-! 对任意实际可数的全定义有限元组操作族构造可数闭包。 -/
namespace KP1Y.Closure
open YesMetaZFC YesMetaZFC.SetTheory
open KP1Y.Kuratowski KP1Y.Functions KP1Y.Cardinal KP1Y.Iteration
universe u

theorem closure_data_exists_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {ω A Ops EOps Tuples Keys G : M.Domain} (hω : M.IsOmega ω) (hOps : Onto M EOps ω Ops)
    (hTuples : ∀ t, M.mem t Tuples ↔ ∃ n, M.mem n ω ∧ Graph M t n A)
    (hKeys : IsProduct M Keys Ops Tuples) (hG : Graph M G Keys A) :
    ∃ P decode Words EWords zero, Valid M ⟨ω,A,P,decode,Words,EWords,Ops,EOps,Tuples,Keys,G,zero⟩ := by
  obtain ⟨P,decode,hPair⟩ := KP1Y.Naturals.natural_pairing_exists_d hM hω
  obtain ⟨Words,hWords⟩ := KP1Y.Sequences.finite_sequences_exist_d hM hω ω
  obtain ⟨EWords,hEWords⟩ := KP1Y.Naturals.natural_words_countable_d hM hω hWords
  obtain ⟨zero,hEmpty,hZero⟩ := hω.1.1
  exact ⟨P,decode,Words,EWords,zero,hω,hPair,hWords,hEWords,hOps,hTuples,hKeys,hG,hZero,hEmpty⟩

theorem countable_operation_hull_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {ω A Ops EOps Tuples Keys G base : M.Domain} (hω : M.IsOmega ω) (hOps : Onto M EOps ω Ops)
    (hTuples : ∀ t, M.mem t Tuples ↔ ∃ n, M.mem n ω ∧ Graph M t n A)
    (hKeys : IsProduct M Keys Ops Tuples) (hG : Graph M G Keys A) (hBase : Graph M base ω A) :
    ∃ X E, M.MemberSubset X A ∧ Onto M E ω X ∧ (∀ x, Reached M ω base x → M.mem x X) ∧
      ∀ op, M.mem op Ops → ∀ n, M.mem n ω → ∀ t, Graph M t n X →
        ∀ key, Codes M key op t → ∀ x, MemPair M G key x → M.mem x X := by
  obtain ⟨P,decode,Words,EWords,zero,hC⟩ := closure_data_exists_d hM hω hOps hTuples hKeys hG
  obtain ⟨X,E,hHull⟩ := countable_hull_exists_d hM hC hBase
  exact ⟨X,E,hHull.subset,hHull.onto,hHull.seed,hHull.closed⟩

end KP1Y.Closure
