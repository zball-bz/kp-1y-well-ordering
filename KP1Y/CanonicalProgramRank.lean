import KP1Y.CanonicalSetSyntax
import KP1Y.CountableSyntax
import KP1Y.CountableRank

/-! 针对给定规范Context本身构造全部程序的ω枚举和排名，不换成另一个未识别Context。 -/
namespace KP1Y.SetLanguage
open YesMetaZFC YesMetaZFC.SetTheory
open KP1Y.Kuratowski KP1Y.Satisfaction KP1Y.Cardinal KP1Y.Ranking
universe u

private theorem instruction_product_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : Context M.Domain} (hC : ContextSpaces M C) : ∃ Tags,
      M.MemberSubset Tags C.omega ∧ M.mem C.atomTag Tags ∧ IsProduct M C.instructions Tags C.pairs := by
  obtain ⟨A,hA⟩ := SetTheory.KP.exists_pair (KP1Y.models_weakKP hM) C.atomTag C.negTag
  obtain ⟨B,hB⟩ := SetTheory.KP.exists_pair (KP1Y.models_weakKP hM) C.impTag C.allTag
  obtain ⟨Tags,hU⟩ := SetTheory.KP.exists_unionOfTwo (KP1Y.models_weakKP hM) A B
  have hTags (x : M.Domain) : M.mem x Tags ↔ x=C.atomTag ∨ x=C.negTag ∨ x=C.impTag ∨ x=C.allTag := by
    rw [hU x,hA x,hB x]
    exact or_assoc
  refine ⟨Tags,?_,(hTags C.atomTag).mpr (Or.inl rfl),?_⟩
  · intro x hx
    rcases (hTags x).mp hx with he | he | he | he
    · exact he ▸ hC.tag_naturals.1
    · exact he ▸ hC.tag_naturals.2.1
    · exact he ▸ hC.tag_naturals.2.2.1
    · exact he ▸ hC.tag_naturals.2.2.2
  · intro instr
    constructor
    · intro hInstr
      obtain ⟨args,hArgs,hCode⟩ := (hC.instructions instr).mp hInstr
      rcases hCode with hCode | hCode | hCode | hCode
      · exact ⟨C.atomTag,(hTags _).mpr (Or.inl rfl),args,hArgs,hCode⟩
      · exact ⟨C.negTag,(hTags _).mpr (Or.inr (Or.inl rfl)),args,hArgs,hCode⟩
      · exact ⟨C.impTag,(hTags _).mpr (Or.inr (Or.inr (Or.inl rfl))),args,hArgs,hCode⟩
      · exact ⟨C.allTag,(hTags _).mpr (Or.inr (Or.inr (Or.inr rfl))),args,hArgs,hCode⟩
    · rintro ⟨op,hop,args,hArgs,hCode⟩
      apply (hC.instructions instr).mpr
      refine ⟨args,hArgs,?_⟩
      rcases (hTags op).mp hop with he | he | he | he
      · subst op
        exact Or.inl hCode
      · subst op
        exact Or.inr (Or.inl hCode)
      · subst op
        exact Or.inr (Or.inr (Or.inl hCode))
      · subst op
        exact Or.inr (Or.inr (Or.inr hCode))

theorem canonical_program_enumerator_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : Context M.Domain} {D : RelationalData M.Domain} {zero one two : M.Domain} (h : CanonicalSyntax M C D zero one two) :
    ∃ E, Onto M E C.omega C.programs := by
  have hω := h.interpretation.spaces.omega
  have hSymbols : M.MemberSubset D.symbols D.omega := by
    intro r hr
    rcases (h.interpretation.symbols r).mp hr with he | he
    · exact he ▸ h.interpretation.naturals.zero_nat
    · exact he ▸ h.interpretation.naturals.one_nat
  obtain ⟨ES,hES⟩ := subset_surjection_d hM hSymbols ((h.interpretation.symbols zero).mpr (Or.inl rfl))
  obtain ⟨EV,hEV⟩ := KP1Y.Naturals.natural_words_countable_d hM hω h.interpretation.spaces.variables
  obtain ⟨EC,hEC⟩ := countable_existing_product_d hM hω hES hEV h.interpretation.spaces.codes
  obtain ⟨EN,hEN⟩ := identity_onto_d hM D.omega
  obtain ⟨O,EO,hO,hEO⟩ := countable_union_d hM hω hEN hEC
  have hOps : M.IsUnionOfTwo C.operands D.omega D.codes :=
    Eq.mp (congrArg (fun ω => M.IsUnionOfTwo C.operands ω D.codes) h.link.omega_eq) h.operands_exact
  have hOC := hM.1.eq_of_same_members O C.operands (fun x => (hO x).trans (hOps x).symm)
  have hEOC : Onto M EO D.omega C.operands := hOC ▸ hEO
  obtain ⟨EP,hEP⟩ := countable_existing_product_d hM hω hEOC hEOC h.spaces.pairs
  obtain ⟨Tags,hTags,hTag,hInstructions⟩ := instruction_product_d hM h.spaces
  have hTagsD : M.MemberSubset Tags D.omega := by
    intro x hx
    exact Eq.mp (congrArg (M.mem x) h.link.omega_eq) (hTags x hx)
  obtain ⟨ET,hET⟩ := subset_surjection_d hM hTagsD hTag
  obtain ⟨EI,hEI⟩ := countable_existing_product_d hM hω hET hEP hInstructions
  have hPrograms : ∀ p, M.mem p C.programs ↔ ∃ n, M.mem n D.omega ∧ KP1Y.Functions.Graph M p n C.instructions := by
    intro p
    simpa only [h.link.omega_eq] using h.spaces.programs p
  obtain ⟨E,hE⟩ := countable_existing_sequences_d hM hω hEI hPrograms
  exact ⟨E,Eq.mpr (congrArg (fun ω => Onto M E ω C.programs) h.link.omega_eq) hE⟩

theorem canonical_program_rank_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : Context M.Domain} {D : RelationalData M.Domain} {zero one two : M.Domain} (h : CanonicalSyntax M C D zero one two) :
    ∃ R, OrdinalRank M R C.programs C.omega := by
  obtain ⟨E,hE⟩ := canonical_program_enumerator_d hM h
  exact countable_rank_d hM h.spaces.omega hE

end KP1Y.SetLanguage
