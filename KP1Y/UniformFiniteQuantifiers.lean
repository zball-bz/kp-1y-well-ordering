import KP1Y.UniformQuantifierSyntax

/-! 内部有限量词块的统一编译：量词个数任意，代码对全部解释同时有效。 -/
namespace KP1Y.Satisfaction
open YesMetaZFC YesMetaZFC.SetTheory YesMetaZFC.SetTheory.Definitional
open KP1Y.Kuratowski KP1Y.Functions KP1Y.Assignments
universe u

theorem uniform_compile_variable_block_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : Context M.Domain} (hC : ContextSpaces M C) {D : RelationalData M.Domain}
    {original originalLength originalHead vars N bound : M.Domain}
    (hInitial : FormulaResult M C D original originalLength originalHead bound)
    (hVars : Graph M vars N bound) (hN : M.mem N C.omega) :
    UniformQuantificationResult M C D original originalHead vars N bound := by
  have hAll := KP1Y.Naturals.natural_induction_d hM uniformQuantificationGuard
    ((((((syntaxEnv C D).push original).push originalHead).push vars).push bound).push N) hC.omega
    (fun stage hEmpty => (uniformQuantificationGuard_iff hM.1 C D original originalHead vars bound N stage).mpr (by
      intro _
      refine ⟨original,hInitial.program_mem hC,originalLength,hInitial.wellFormed.length_nat,
        originalHead,hInitial.head_nat,hInitial,fun _ h => h,?_⟩
      intro A S B At H hI s hs hS
      constructor
      · intro hTrue t _ hFrame
        have hst := agreeOutside_empty_eq hM.1 hEmpty hFrame
        subst t
        exact hTrue
      · intro h
        exact h s hs (agreeOutside_refl hS)))
    (fun stage _ ih next hSucc => (uniformQuantificationGuard_iff hM.1 C D original originalHead vars bound N next).mpr (by
      intro hNextN
      have hStageN := hNextN stage hSucc.predecessor_mem
      have hStageSub : M.MemberSubset stage N := fun k hk => hNextN k ((hSucc k).mpr (Or.inl hk))
      obtain ⟨p,_,length,_,head,_,hResult,hSub,hBefore⟩ :=
        (uniformQuantificationGuard_iff hM.1 C D original originalHead vars bound N stage).mp ih hStageSub
      obtain ⟨v,hv,hAt⟩ := hVars.total stage hStageN
      obtain ⟨q,length',hExt,hAfter⟩ := uniform_compile_universal_d hM hC hResult.wellFormed hResult.successor.predecessor_mem hv
      refine ⟨q,hExt.program_mem hC,length',hExt.wellFormed.length_nat,length,hExt.head_nat,hExt.result,
        fun x hx => hExt.to_subset hM.1 x (hSub x hx),?_⟩
      intro A S B At H hI s _ hS
      apply (hAfter A S B At H hI s hS).trans
      apply Iff.trans ?_ (quantified_successor_d hM hVars hAt hSucc hS)
      constructor
      · intro h x hx u hu
        exact (hBefore A S B At H hI u ((hI.assignments_exact u).mpr ⟨bound,hResult.wellFormed.bound_nat,hu.graph⟩) hu.graph).mp (h x hx u hu)
      · intro h x hx u hu
        exact (hBefore A S B At H hI u ((hI.assignments_exact u).mpr ⟨bound,hResult.wellFormed.bound_nat,hu.graph⟩) hu.graph).mpr (h x hx u hu)))
  exact (uniformQuantificationGuard_iff hM.1 C D original originalHead vars bound N N).mp (hAll N hN) (fun _ h => h)

theorem uniform_compile_universal_block_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : Context M.Domain} (hC : ContextSpaces M C) {D : RelationalData M.Domain}
    {original originalLength originalHead vars N bound : M.Domain}
    (hInitial : FormulaResult M C D original originalLength originalHead bound)
    (hVars : Graph M vars N bound) (hN : M.mem N C.omega) :
    ∃ q length head, CompiledExtension M C D original originalLength bound q length head ∧
      UniformQuantificationMeaning M C q head original originalHead vars N bound := by
  obtain ⟨q,_,length,_,head,_,hResult,hSub,hTruth⟩ := uniform_compile_variable_block_d hM hC hInitial hVars hN
  exact ⟨q,length,head,subset_result_extension hM.1 hInitial.wellFormed.graph hResult hSub,hTruth⟩

theorem uniform_compile_existential_block_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : Context M.Domain} (hC : ContextSpaces M C) {D : RelationalData M.Domain}
    {original originalLength originalHead vars N bound : M.Domain}
    (hInitial : FormulaResult M C D original originalLength originalHead bound)
    (hVars : Graph M vars N bound) (hN : M.mem N C.omega) :
    ∃ q length head, CompiledExtension M C D original originalLength bound q length head ∧
      ∀ A S B At H, EvaluationInstance M C A S B At H → ∀ s, Graph M s bound A →
        (NodeTrue M (C.withInterpretation A S B At) H q head s ↔ ∃ t, M.mem t S ∧
          AgreeOutside M vars N s t bound A ∧ NodeTrue M (C.withInterpretation A S B At) H original originalHead t) := by
  classical
  obtain ⟨p1,n1,h1,truth1⟩ := uniform_compile_negation_d hM hC hInitial.wellFormed hInitial.successor.predecessor_mem
  obtain ⟨p2,_,n2,_,j2,_,h2,hSub,truth2⟩ := uniform_compile_variable_block_d hM hC h1.result hVars hN
  obtain ⟨p3,n3,h3,truth3⟩ := uniform_compile_negation_d hM hC h2.wellFormed h2.successor.predecessor_mem
  have hAllSub : M.MemberSubset original p3 :=
    fun x hx => h3.to_subset hM.1 x (hSub x (h1.to_subset hM.1 x hx))
  refine ⟨p3,n3,n2,subset_result_extension hM.1 hInitial.wellFormed.graph h3.result hAllSub,?_⟩
  intro A S B At H hI s hS
  have hs := (hI.assignments_exact s).mpr ⟨bound,hInitial.wellFormed.bound_nat,hS⟩
  have hAllMeaning : NodeTrue M (C.withInterpretation A S B At) H p2 j2 s ↔
      ∀ t, M.mem t S → AgreeOutside M vars N s t bound A →
        ¬NodeTrue M (C.withInterpretation A S B At) H original originalHead t := by
    apply (truth2 A S B At H hI s hs hS).trans
    constructor
    · intro h t ht hFrame
      exact (truth1 A S B At H hI t ht).mp (h t ht hFrame)
    · intro h t ht hFrame
      exact (truth1 A S B At H hI t ht).mpr (h t ht hFrame)
  apply (truth3 A S B At H hI s hs).trans
  apply (not_congr hAllMeaning).trans
  constructor
  · intro hNot
    apply Classical.byContradiction
    intro hNone
    exact hNot (fun t ht hFrame hTrue => hNone ⟨t,ht,hFrame,hTrue⟩)
  · rintro ⟨t,ht,hFrame,hTrue⟩ h
    exact h t ht hFrame hTrue

end KP1Y.Satisfaction
