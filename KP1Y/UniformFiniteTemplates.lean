import KP1Y.UniformFiniteConjunction
import KP1Y.UniformFiniteQuantifiers
import KP1Y.CompileFiniteTemplates

/-! 先选择同一份有限图模板代码，再对所有解释证明存在／反例语义。 -/
namespace KP1Y.Satisfaction
open YesMetaZFC YesMetaZFC.SetTheory
open KP1Y.Kuratowski KP1Y.Functions
universe u

theorem uniform_formula_seed_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : Context M.Domain} (hC : ContextSpaces M C) {D : RelationalData M.Domain} {bound seed : M.Domain}
    (hb : M.mem bound C.omega) (hCodes : M.MemberSubset D.codes C.operands)
    (hSeed : M.mem seed D.codes) (hScope : ScopedAtom M D seed bound) :
    ∃ p length head, FormulaResult M C D p length head bound := by
  obtain ⟨e,he,heω,_,hE⟩ := empty_program_d hC
  have hEmpty : WellFormedProgram M C D e e bound := ⟨hE,heω,hb,fun i hi => False.elim (he i hi)⟩
  obtain ⟨p,length,hP,_⟩ := uniform_compile_atom_d hM hC hEmpty hSeed (hCodes seed hSeed) hScope
  exact ⟨p,length,e,hP.result⟩

theorem uniform_compile_exists_constraints_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : Context M.Domain} (hC : ContextSpaces M C) {D : RelationalData M.Domain}
    {seq N vars NV bound seed : M.Domain}
    (hSeq : Graph M seq N D.codes) (hN : M.mem N C.omega) (hb : M.mem bound C.omega)
    (hVars : Graph M vars NV bound) (hNV : M.mem NV C.omega)
    (hCodes : M.MemberSubset D.codes C.operands)
    (hScoped : ∀ i, M.mem i N → ∀ a, MemPair M seq i a → ScopedAtom M D a bound)
    (hSeed : M.mem seed D.codes) (hSeedScope : ScopedAtom M D seed bound) :
    ∃ q length head, FormulaResult M C D q length head bound ∧
      ∀ A S B At H, EvaluationInstance M C A S B At H → ∀ s, Graph M s bound A →
        (NodeTrue M (C.withInterpretation A S B At) H q head s ↔
          ExistsConstraints M (C.withInterpretation A S B At) D seq N vars NV s bound) := by
  obtain ⟨p0,n0,j0,h0⟩ := uniform_formula_seed_d hM hC hb hCodes hSeed hSeedScope
  obtain ⟨p1,n1,j1,h1,truth1⟩ := uniform_compile_atom_sequence_d hM hC h0 hSeq hN hCodes hScoped
  obtain ⟨q,length,head,hQ,truth⟩ := uniform_compile_existential_block_d hM hC h1.result hVars hNV
  refine ⟨q,length,head,hQ.result,?_⟩
  intro A S B At H hI s hS
  apply (truth A S B At H hI s hS).trans
  exact ⟨fun ⟨t,ht,hFrame,hTrue⟩ => ⟨t,ht,hFrame,(truth1 A S B At H hI t ht).mp hTrue⟩,
    fun ⟨t,ht,hFrame,hTrue⟩ => ⟨t,ht,hFrame,(truth1 A S B At H hI t ht).mpr hTrue⟩⟩

theorem uniform_compile_counterexample_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : Context M.Domain} (hC : ContextSpaces M C) {D : RelationalData M.Domain}
    {input NI output NO inputVars NVI outputVars NVO bound seed : M.Domain}
    (hInput : Graph M input NI D.codes) (hNI : M.mem NI C.omega)
    (hOutput : Graph M output NO D.codes) (hNO : M.mem NO C.omega) (hb : M.mem bound C.omega)
    (hInputVars : Graph M inputVars NVI bound) (hNVI : M.mem NVI C.omega)
    (hOutputVars : Graph M outputVars NVO bound) (hNVO : M.mem NVO C.omega)
    (hCodes : M.MemberSubset D.codes C.operands)
    (hScopedInput : ∀ i, M.mem i NI → ∀ a, MemPair M input i a → ScopedAtom M D a bound)
    (hScopedOutput : ∀ i, M.mem i NO → ∀ a, MemPair M output i a → ScopedAtom M D a bound)
    (hSeed : M.mem seed D.codes) (hSeedScope : ScopedAtom M D seed bound) :
    ∃ q length head, FormulaResult M C D q length head bound ∧
      ∀ A S B At H, EvaluationInstance M C A S B At H → ∀ s, Graph M s bound A →
        (NodeTrue M (C.withInterpretation A S B At) H q head s ↔
          Counterexample M (C.withInterpretation A S B At) D input NI output NO inputVars NVI outputVars NVO s bound) := by
  obtain ⟨pSeed,nSeed,jSeed,hSeedResult⟩ := uniform_formula_seed_d hM hC hb hCodes hSeed hSeedScope
  obtain ⟨p0,n0,j0,h0,truth0⟩ := uniform_compile_atom_sequence_d hM hC hSeedResult hInput hNI hCodes hScopedInput
  obtain ⟨p1,n1,j1,h1,truth1⟩ := uniform_compile_atom_sequence_d hM hC h0.result hOutput hNO hCodes hScopedOutput
  obtain ⟨p2,n2,j2,h2,truth2⟩ := uniform_compile_existential_block_d hM hC h1.result hOutputVars hNVO
  obtain ⟨p3,n3,h3,truth3⟩ := uniform_compile_negation_d hM hC h2.wellFormed h2.successor.predecessor_mem
  have hBefore := (h1.trans hM.1 h2).trans hM.1 h3
  have hj0 := prefix_domain_subset hM.1 hBefore.prefixGraph hBefore.wellFormed.graph j0 h0.successor.predecessor_mem
  obtain ⟨p4,n4,j4,h4,truth4⟩ := uniform_compile_conjunction_d hM hC h3.wellFormed hj0 h3.successor.predecessor_mem
  have hBody (A S B At H : M.Domain) (hI : EvaluationInstance M C A S B At H)
      (s : M.Domain) (hS : Graph M s bound A) :
      NodeTrue M (C.withInterpretation A S B At) H p4 j4 s ↔
        AllAtoms M (C.withInterpretation A S B At) D input NI s ∧
          ¬ExistsConstraints M (C.withInterpretation A S B At) D output NO outputVars NVO s bound := by
    have hs := (hI.assignments_exact s).mpr ⟨bound,hb,hS⟩
    have hIn := ((hBefore.withInterpretation A S B At).old_node hM (hI.contextSpaces hC) hI.table
      h0.wellFormed.length_nat h0.successor.predecessor_mem hs).symm.trans (truth0 A S B At H hI s hs)
    have hOut : NodeTrue M (C.withInterpretation A S B At) H p2 j2 s ↔
        ExistsConstraints M (C.withInterpretation A S B At) D output NO outputVars NVO s bound := by
      apply (truth2 A S B At H hI s hS).trans
      exact ⟨fun ⟨t,ht,hFrame,hTrue⟩ => ⟨t,ht,hFrame,(truth1 A S B At H hI t ht).mp hTrue⟩,
        fun ⟨t,ht,hFrame,hTrue⟩ => ⟨t,ht,hFrame,(truth1 A S B At H hI t ht).mpr hTrue⟩⟩
    exact (truth4 A S B At H hI s hs).trans
      (and_congr hIn ((truth3 A S B At H hI s hs).trans (not_congr hOut)))
  obtain ⟨p5,n5,j5,h5,truth5⟩ := uniform_compile_existential_block_d hM hC h4.result hInputVars hNVI
  refine ⟨p5,n5,j5,h5.result,?_⟩
  intro A S B At H hI s hS
  apply (truth5 A S B At H hI s hS).trans
  exact ⟨fun ⟨t,ht,hFrame,hTrue⟩ => ⟨t,ht,hFrame,(hBody A S B At H hI t hFrame.target).mp hTrue⟩,
    fun ⟨t,ht,hFrame,hTrue⟩ => ⟨t,ht,hFrame,(hBody A S B At H hI t hFrame.target).mpr hTrue⟩⟩

end KP1Y.Satisfaction
