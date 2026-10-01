import KP1Y.ConjunctionSyntax

/-! 对任意内部有限原子序列构造一个合法合取程序；归纳公式是实际对象 UnarySchema。 -/
namespace KP1Y.Satisfaction
open YesMetaZFC YesMetaZFC.SetTheory YesMetaZFC.SetTheory.Definitional
open KP1Y.Kuratowski KP1Y.Functions
universe u

theorem compile_atom_sequence_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : Context M.Domain} (hC : ContextSpaces M C) {D : RelationalData M.Domain}
    {H seq N bound seed : M.Domain} (hH : Evaluation M C H)
    (hSeq : Graph M seq N D.codes) (hN : M.mem N C.omega) (hb : M.mem bound C.omega)
    (hCodes : M.MemberSubset D.codes C.operands)
    (hScoped : ∀ i, M.mem i N → ∀ a, MemPair M seq i a → ScopedAtom M D a bound)
    (hSeed : M.mem seed D.codes) (hSeedScope : ScopedAtom M D seed bound) :
    ConjunctionResult M C D H seq N bound := by
  have hAll := KP1Y.Naturals.natural_induction_d hM conjunctionGuard
    (((((syntaxEnv C D).push H).push seq).push bound).push N) hC.omega
    (fun stage hEmpty => (conjunctionGuard_iff hM.1 C D H seq bound N stage).mpr (by
      intro _
      obtain ⟨p,length,head,hResult,hTrue⟩ := compile_true_from_atom_d hM hC hH hb hSeed (hCodes seed hSeed) hSeedScope
      refine ⟨p,hResult.program_mem hC,length,hResult.wellFormed.length_nat,head,hResult.head_nat,hResult,?_⟩
      intro s hs
      exact ⟨fun _ k hk => False.elim (hEmpty k hk),fun _ => hTrue s hs⟩))
    (fun stage _ ih next hSucc => (conjunctionGuard_iff hM.1 C D H seq bound N next).mpr (by
      intro hNextN
      have hStageN := hNextN stage hSucc.predecessor_mem
      have hStageSub : M.MemberSubset stage N := fun k hk => hNextN k ((hSucc k).mpr (Or.inl hk))
      obtain ⟨p,_,length,_,head,_,hResult,hBefore⟩ :=
        (conjunctionGuard_iff hM.1 C D H seq bound N stage).mp ih hStageSub
      obtain ⟨a,ha,hAt⟩ := hSeq.total stage hStageN
      obtain ⟨q,length',head',hExt,hAfter⟩ := compile_conjoin_atom_d hM hC hH hResult.wellFormed
        hResult.successor.predecessor_mem ha (hCodes a ha) (hScoped stage hStageN a hAt)
      refine ⟨q,hExt.program_mem hC,length',hExt.wellFormed.length_nat,head',hExt.head_nat,hExt.result,?_⟩
      intro s hs
      exact (hAfter s hs).trans ((and_congr (hBefore s hs) Iff.rfl).trans (allAtoms_successor hM.1 hSeq hAt hSucc).symm)))
  exact (conjunctionGuard_iff hM.1 C D H seq bound N N).mp (hAll N hN) (fun _ h => h)

/-- 非空序列本身供应恒真式所需的合法种子，不附加一个不存在的原子。 -/
theorem compile_nonempty_atom_sequence_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : Context M.Domain} (hC : ContextSpaces M C) {D : RelationalData M.Domain}
    {H seq N bound : M.Domain} (hH : Evaluation M C H)
    (hSeq : Graph M seq N D.codes) (hN : M.mem N C.omega) (hb : M.mem bound C.omega)
    (hCodes : M.MemberSubset D.codes C.operands)
    (hScoped : ∀ i, M.mem i N → ∀ a, MemPair M seq i a → ScopedAtom M D a bound)
    (hNonempty : ∃ i, M.mem i N) : ConjunctionResult M C D H seq N bound := by
  obtain ⟨i,hi⟩ := hNonempty
  obtain ⟨seed,hSeed,hAt⟩ := hSeq.total i hi
  exact compile_atom_sequence_d hM hC hH hSeq hN hb hCodes hScoped hSeed (hScoped i hi seed hAt)

end KP1Y.Satisfaction
