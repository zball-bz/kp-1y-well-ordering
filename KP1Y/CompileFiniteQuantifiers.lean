import KP1Y.QuantifierBlockSyntax
import KP1Y.CompileDerived

/-! 内部任意有限量词块的编译与完整赋值语义，允许重复变量号。 -/
namespace KP1Y.Satisfaction
open YesMetaZFC YesMetaZFC.SetTheory YesMetaZFC.SetTheory.Definitional
open KP1Y.Kuratowski KP1Y.Functions KP1Y.Assignments
universe u

theorem compile_variable_block_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : Context M.Domain} (hC : ContextSpaces M C) {D : RelationalData M.Domain}
    {H original originalLength originalHead vars N bound : M.Domain} (hH : Evaluation M C H)
    (hInitial : FormulaResult M C D original originalLength originalHead bound)
    (hVars : Graph M vars N bound) (hN : M.mem N C.omega) :
    QuantificationResult M C D H original originalHead vars N bound := by
  have hAll := KP1Y.Naturals.natural_induction_d hM quantificationGuard
    (((((((syntaxEnv C D).push H).push original).push originalHead).push vars).push bound).push N) hC.omega
    (fun stage hEmpty => (quantificationGuard_iff hM.1 C D H original originalHead vars bound N stage).mpr (by
      intro _
      refine ⟨original,hInitial.program_mem hC,originalLength,hInitial.wellFormed.length_nat,
        originalHead,hInitial.head_nat,hInitial,fun _ h => h,?_⟩
      intro s hs hS
      constructor
      · intro hTrue t _ hFrame
        have hst := agreeOutside_empty_eq hM.1 hEmpty hFrame
        subst t
        exact hTrue
      · intro h
        exact h s hs (agreeOutside_refl hS)))
    (fun stage _ ih next hSucc => (quantificationGuard_iff hM.1 C D H original originalHead vars bound N next).mpr (by
      intro hNextN
      have hStageN := hNextN stage hSucc.predecessor_mem
      have hStageSub : M.MemberSubset stage N := fun k hk => hNextN k ((hSucc k).mpr (Or.inl hk))
      obtain ⟨p,_,length,_,head,_,hResult,hSub,hBefore⟩ :=
        (quantificationGuard_iff hM.1 C D H original originalHead vars bound N stage).mp ih hStageSub
      obtain ⟨v,hv,hAt⟩ := hVars.total stage hStageN
      obtain ⟨q,length',hExt,hAfter⟩ := compile_universal_d hM hC hH hResult.wellFormed hResult.successor.predecessor_mem hv
      refine ⟨q,hExt.program_mem hC,length',hExt.wellFormed.length_nat,length,hExt.head_nat,hExt.result,
        fun x hx => hExt.to_subset hM.1 x (hSub x hx),?_⟩
      intro s _ hS
      apply (hAfter s hS).trans
      apply Iff.trans ?_ (quantified_successor_d hM hVars hAt hSucc hS)
      constructor
      · intro h x hx u hu
        exact (hBefore u ((hC.assignments u).mpr ⟨bound,hResult.wellFormed.bound_nat,hu.graph⟩) hu.graph).mp (h x hx u hu)
      · intro h x hx u hu
        exact (hBefore u ((hC.assignments u).mpr ⟨bound,hResult.wellFormed.bound_nat,hu.graph⟩) hu.graph).mpr (h x hx u hu)))
  exact (quantificationGuard_iff hM.1 C D H original originalHead vars bound N N).mp (hAll N hN) (fun _ h => h)

theorem compile_universal_block_extended_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : Context M.Domain} (hC : ContextSpaces M C) {D : RelationalData M.Domain}
    {H original originalLength originalHead vars N bound : M.Domain} (hH : Evaluation M C H)
    (hInitial : FormulaResult M C D original originalLength originalHead bound)
    (hVars : Graph M vars N bound) (hN : M.mem N C.omega) :
    ∃ q length head, CompiledExtension M C D original originalLength bound q length head ∧
      ∀ s, M.mem s C.assignments → Graph M s bound C.carrier →
        (NodeTrue M C H q head s ↔ Quantified M C H original originalHead vars N s bound) := by
  obtain ⟨q,_,length,_,head,_,hResult,hSub,hTruth⟩ := compile_variable_block_d hM hC hH hInitial hVars hN
  exact ⟨q,length,head,subset_result_extension hM.1 hInitial.wellFormed.graph hResult hSub,hTruth⟩

theorem compile_existential_block_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : Context M.Domain} (hC : ContextSpaces M C) {D : RelationalData M.Domain}
    {H original originalLength originalHead vars N bound : M.Domain} (hH : Evaluation M C H)
    (hInitial : FormulaResult M C D original originalLength originalHead bound)
    (hVars : Graph M vars N bound) (hN : M.mem N C.omega) :
    ∃ q length head, CompiledExtension M C D original originalLength bound q length head ∧ ∀ s, Graph M s bound C.carrier →
      (NodeTrue M C H q head s ↔ ∃ t, M.mem t C.assignments ∧
        AgreeOutside M vars N s t bound C.carrier ∧ NodeTrue M C H original originalHead t) := by
  classical
  obtain ⟨p1,n1,h1,truth1⟩ := compile_negation_d hM hC hH hInitial.wellFormed hInitial.successor.predecessor_mem
  obtain ⟨p2,_,n2,_,j2,_,h2,hSub,truth2⟩ := compile_variable_block_d hM hC hH h1.result hVars hN
  obtain ⟨p3,n3,h3,truth3⟩ := compile_negation_d hM hC hH h2.wellFormed h2.successor.predecessor_mem
  have hAllSub : M.MemberSubset original p3 :=
    fun x hx => h3.to_subset hM.1 x (hSub x (h1.to_subset hM.1 x hx))
  refine ⟨p3,n3,n2,subset_result_extension hM.1 hInitial.wellFormed.graph h3.result hAllSub,?_⟩
  intro s hS
  have hs := (hC.assignments s).mpr ⟨bound,hInitial.wellFormed.bound_nat,hS⟩
  have hAllMeaning : NodeTrue M C H p2 j2 s ↔ ∀ t, M.mem t C.assignments →
      AgreeOutside M vars N s t bound C.carrier → ¬NodeTrue M C H original originalHead t := by
    apply (truth2 s hs hS).trans
    constructor
    · intro h t ht hFrame
      exact (truth1 t ht).mp (h t ht hFrame)
    · intro h t ht hFrame
      exact (truth1 t ht).mpr (h t ht hFrame)
  apply (truth3 s hs).trans
  apply (not_congr hAllMeaning).trans
  constructor
  · intro hNot
    apply Classical.byContradiction
    intro hNone
    exact hNot (fun t ht hFrame hTrue => hNone ⟨t,ht,hFrame,hTrue⟩)
  · rintro ⟨t,ht,hFrame,hTrue⟩ h
    exact h t ht hFrame hTrue

end KP1Y.Satisfaction
