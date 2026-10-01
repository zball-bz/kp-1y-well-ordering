import KP1Y.UniformConjunctionSyntax

/-! 一份代码同时表达各解释中的内部有限合取，保留已有程序。 -/
namespace KP1Y.Satisfaction
open YesMetaZFC YesMetaZFC.SetTheory YesMetaZFC.SetTheory.Definitional
open KP1Y.Kuratowski KP1Y.Functions
universe u

theorem uniform_compile_atom_sequence_from_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : Context M.Domain} (hC : ContextSpaces M C) {D : RelationalData M.Domain}
    {original originalLength originalHead seq N bound : M.Domain}
    (hInitial : FormulaResult M C D original originalLength originalHead bound)
    (hSeq : Graph M seq N D.codes) (hN : M.mem N C.omega)
    (hCodes : M.MemberSubset D.codes C.operands)
    (hScoped : ∀ i, M.mem i N → ∀ a, MemPair M seq i a → ScopedAtom M D a bound) :
    UniformConjunctionFrom M C D original seq N bound := by
  have hAll := KP1Y.Naturals.natural_induction_d hM uniformConjunctionGuard
    (((((syntaxEnv C D).push original).push seq).push bound).push N) hC.omega
    (fun stage hEmpty => (uniformConjunctionGuard_iff hM.1 C D original seq bound N stage).mpr (by
      intro _
      obtain ⟨p,length,hExt,hTrue⟩ := uniform_compile_tautology_d hM hC hInitial.wellFormed hInitial.successor.predecessor_mem
      refine ⟨p,hExt.program_mem hC,length,hExt.wellFormed.length_nat,originalLength,hExt.head_nat,hExt.result,
        hExt.to_subset hM.1,?_⟩
      intro A S B At H hI s hs
      exact ⟨fun _ k hk => False.elim (hEmpty k hk),fun _ => hTrue A S B At H hI s hs⟩))
    (fun stage _ ih next hSucc => (uniformConjunctionGuard_iff hM.1 C D original seq bound N next).mpr (by
      intro hNextN
      have hStageN := hNextN stage hSucc.predecessor_mem
      have hStageSub : M.MemberSubset stage N := fun k hk => hNextN k ((hSucc k).mpr (Or.inl hk))
      obtain ⟨p,_,length,_,head,_,hResult,hSub,hBefore⟩ :=
        (uniformConjunctionGuard_iff hM.1 C D original seq bound N stage).mp ih hStageSub
      obtain ⟨a,ha,hAt⟩ := hSeq.total stage hStageN
      obtain ⟨q,length',head',hExt,hAfter⟩ := uniform_compile_conjoin_atom_d hM hC hResult.wellFormed
        hResult.successor.predecessor_mem ha (hCodes a ha) (hScoped stage hStageN a hAt)
      refine ⟨q,hExt.program_mem hC,length',hExt.wellFormed.length_nat,head',hExt.head_nat,hExt.result,
        fun x hx => hExt.to_subset hM.1 x (hSub x hx),?_⟩
      intro A S B At H hI s hs
      exact (hAfter A S B At H hI s hs).trans
        ((and_congr (hBefore A S B At H hI s hs) Iff.rfl).trans (allAtoms_successor hM.1 hSeq hAt hSucc).symm)))
  exact (uniformConjunctionGuard_iff hM.1 C D original seq bound N N).mp (hAll N hN) (fun _ h => h)

theorem uniform_compile_atom_sequence_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : Context M.Domain} (hC : ContextSpaces M C) {D : RelationalData M.Domain}
    {original originalLength originalHead seq N bound : M.Domain}
    (hInitial : FormulaResult M C D original originalLength originalHead bound)
    (hSeq : Graph M seq N D.codes) (hN : M.mem N C.omega)
    (hCodes : M.MemberSubset D.codes C.operands)
    (hScoped : ∀ i, M.mem i N → ∀ a, MemPair M seq i a → ScopedAtom M D a bound) :
    ∃ q length head, CompiledExtension M C D original originalLength bound q length head ∧
      UniformConjunctionMeaning M C D q head seq N := by
  obtain ⟨q,_,length,_,head,_,hResult,hSub,hTruth⟩ := uniform_compile_atom_sequence_from_d hM hC hInitial hSeq hN hCodes hScoped
  exact ⟨q,length,head,subset_result_extension hM.1 hInitial.wellFormed.graph hResult hSub,hTruth⟩

end KP1Y.Satisfaction
