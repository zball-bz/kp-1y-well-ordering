import KP1Y.ConjunctionExtensionSyntax

/-! 在保留任意已有合法程序的条件下编译内部有限合取。 -/
namespace KP1Y.Satisfaction
open YesMetaZFC YesMetaZFC.SetTheory YesMetaZFC.SetTheory.Definitional
open KP1Y.Kuratowski KP1Y.Functions
universe u

theorem compile_atom_sequence_from_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : Context M.Domain} (hC : ContextSpaces M C) {D : RelationalData M.Domain}
    {H original originalLength originalHead seq N bound : M.Domain} (hH : Evaluation M C H)
    (hInitial : FormulaResult M C D original originalLength originalHead bound)
    (hSeq : Graph M seq N D.codes) (hN : M.mem N C.omega)
    (hCodes : M.MemberSubset D.codes C.operands)
    (hScoped : ∀ i, M.mem i N → ∀ a, MemPair M seq i a → ScopedAtom M D a bound) :
    ConjunctionFrom M C D H original seq N bound := by
  have hAll := KP1Y.Naturals.natural_induction_d hM conjunctionFromGuard
    ((((((syntaxEnv C D).push H).push original).push seq).push bound).push N) hC.omega
    (fun stage hEmpty => (conjunctionFromGuard_iff hM.1 C D H original seq bound N stage).mpr (by
      intro _
      obtain ⟨p,length,hExt,hTrue⟩ := compile_tautology_d hM hC hH hInitial.wellFormed hInitial.successor.predecessor_mem
      refine ⟨p,hExt.program_mem hC,length,hExt.wellFormed.length_nat,originalLength,hExt.head_nat,hExt.result,
        hExt.to_subset hM.1,?_⟩
      intro s hs
      exact ⟨fun _ k hk => False.elim (hEmpty k hk),fun _ => hTrue s hs⟩))
    (fun stage _ ih next hSucc => (conjunctionFromGuard_iff hM.1 C D H original seq bound N next).mpr (by
      intro hNextN
      have hStageN := hNextN stage hSucc.predecessor_mem
      have hStageSub : M.MemberSubset stage N := fun k hk => hNextN k ((hSucc k).mpr (Or.inl hk))
      obtain ⟨p,_,length,_,head,_,hResult,hSub,hBefore⟩ :=
        (conjunctionFromGuard_iff hM.1 C D H original seq bound N stage).mp ih hStageSub
      obtain ⟨a,ha,hAt⟩ := hSeq.total stage hStageN
      obtain ⟨q,length',head',hExt,hAfter⟩ := compile_conjoin_atom_d hM hC hH hResult.wellFormed
        hResult.successor.predecessor_mem ha (hCodes a ha) (hScoped stage hStageN a hAt)
      refine ⟨q,hExt.program_mem hC,length',hExt.wellFormed.length_nat,head',hExt.head_nat,hExt.result,
        fun x hx => hExt.to_subset hM.1 x (hSub x hx),?_⟩
      intro s hs
      exact (hAfter s hs).trans ((and_congr (hBefore s hs) Iff.rfl).trans (allAtoms_successor hM.1 hSeq hAt hSucc).symm)))
  exact (conjunctionFromGuard_iff hM.1 C D H original seq bound N N).mp (hAll N hN) (fun _ h => h)

theorem compile_atom_sequence_extended_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : Context M.Domain} (hC : ContextSpaces M C) {D : RelationalData M.Domain}
    {H original originalLength originalHead seq N bound : M.Domain} (hH : Evaluation M C H)
    (hInitial : FormulaResult M C D original originalLength originalHead bound)
    (hSeq : Graph M seq N D.codes) (hN : M.mem N C.omega)
    (hCodes : M.MemberSubset D.codes C.operands)
    (hScoped : ∀ i, M.mem i N → ∀ a, MemPair M seq i a → ScopedAtom M D a bound) :
    ∃ q length head, CompiledExtension M C D original originalLength bound q length head ∧
      ∀ s, M.mem s C.assignments → (NodeTrue M C H q head s ↔ AllAtoms M C D seq N s) := by
  obtain ⟨q,_,length,_,head,_,hResult,hSub,hTruth⟩ := compile_atom_sequence_from_d hM hC hH hInitial hSeq hN hCodes hScoped
  exact ⟨q,length,head,subset_result_extension hM.1 hInitial.wellFormed.graph hResult hSub,hTruth⟩

end KP1Y.Satisfaction
