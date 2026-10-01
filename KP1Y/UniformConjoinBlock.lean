import KP1Y.UniformFiniteConjunction

/-! 在已有公式后统一合取一个内部有限原子块，保留同一代码及全部解释的语义。 -/
namespace KP1Y.Satisfaction
open YesMetaZFC YesMetaZFC.SetTheory
open KP1Y.Kuratowski KP1Y.Functions
universe u

theorem uniform_conjoin_block_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : Context M.Domain} (hC : ContextSpaces M C) {D : RelationalData M.Domain}
    {p length head bound seq N : M.Domain} (hP : FormulaResult M C D p length head bound)
    (hSeq : Graph M seq N D.codes) (hN : M.mem N C.omega) (hCodes : M.MemberSubset D.codes C.operands)
    (hScoped : ∀ i, M.mem i N → ∀ a, MemPair M seq i a → ScopedAtom M D a bound) :
    ∃ q length' head', CompiledExtension M C D p length bound q length' head' ∧
      ∀ A S B At H, EvaluationInstance M C A S B At H → ∀ s, M.mem s S →
        (NodeTrue M (C.withInterpretation A S B At) H q head' s ↔
          NodeTrue M (C.withInterpretation A S B At) H p head s ∧ AllAtoms M (C.withInterpretation A S B At) D seq N s) := by
  obtain ⟨r,rl,rh,hR,hBlock⟩ := uniform_compile_atom_sequence_d hM hC hP hSeq hN hCodes hScoped
  have hHead := prefix_domain_subset hM.1 hR.prefixGraph hR.wellFormed.graph head hP.successor.predecessor_mem
  obtain ⟨q,ql,qh,hQ,hConj⟩ := uniform_compile_conjunction_d hM hC hR.wellFormed hHead hR.successor.predecessor_mem
  refine ⟨q,ql,qh,hR.trans hM.1 hQ,?_⟩
  intro A S B At H hI s hs
  have hOld := (hR.withInterpretation A S B At).old_node hM (hI.contextSpaces hC) hI.table
    hP.wellFormed.length_nat hP.successor.predecessor_mem hs
  exact (hConj A S B At H hI s hs).trans (and_congr hOld.symm (hBlock A S B At H hI s hs))

theorem uniform_compile_two_blocks_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : Context M.Domain} (hC : ContextSpaces M C) {D : RelationalData M.Domain}
    {p length head bound first NF second NS : M.Domain} (hP : FormulaResult M C D p length head bound)
    (hFirst : Graph M first NF D.codes) (hNF : M.mem NF C.omega) (hSecond : Graph M second NS D.codes) (hNS : M.mem NS C.omega)
    (hCodes : M.MemberSubset D.codes C.operands)
    (hScopedF : ∀ i, M.mem i NF → ∀ a, MemPair M first i a → ScopedAtom M D a bound)
    (hScopedS : ∀ i, M.mem i NS → ∀ a, MemPair M second i a → ScopedAtom M D a bound) :
    ∃ q length' head', CompiledExtension M C D p length bound q length' head' ∧
      ∀ A S B At H, EvaluationInstance M C A S B At H → ∀ s, M.mem s S →
        (NodeTrue M (C.withInterpretation A S B At) H q head' s ↔
          AllAtoms M (C.withInterpretation A S B At) D first NF s ∧ AllAtoms M (C.withInterpretation A S B At) D second NS s) := by
  obtain ⟨r,rl,rh,hR,hTruth⟩ := uniform_compile_atom_sequence_d hM hC hP hFirst hNF hCodes hScopedF
  obtain ⟨q,ql,qh,hQ,hBoth⟩ := uniform_conjoin_block_d hM hC hR.result hSecond hNS hCodes hScopedS
  refine ⟨q,ql,qh,hR.trans hM.1 hQ,?_⟩
  intro A S B At H hI s hs
  exact (hBoth A S B At H hI s hs).trans (and_congr (hTruth A S B At H hI s hs) Iff.rfl)

end KP1Y.Satisfaction
