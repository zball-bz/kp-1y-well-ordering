import KP1Y.SetLanguageInterpretation
import KP1Y.CountableSyntax
import KP1Y.DefSetMeaning

/-! 在给定载域上实际形成纯集合语言的真值集合和全部带参数定义子集。 -/
namespace KP1Y.SetLanguage
open YesMetaZFC YesMetaZFC.SetTheory
open KP1Y.Kuratowski KP1Y.Functions KP1Y.Satisfaction KP1Y.Definability KP1Y.Cardinal
universe u

structure DefStage (M : SetTheory.Structure.{u}) (C : Context M.Domain) (D : RelationalData M.Domain)
    (zero one two H Raw Sat Def : M.Domain) : Prop where
  interpretation : Interpretation M D zero one two
  spaces : ContextSpaces M C
  link : RelationalContext M D C.atomic C
  atomic : AtomicTable M D C.atomic
  evaluation : Evaluation M C H
  raw : TruthSet M C H Raw
  typed : TypedTruthSet M C D Raw Sat
  subsets : DefSet M C D Sat zero Def

theorem def_stage_for_interpretation_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {D : RelationalData M.Domain} {zero one two : M.Domain} (hI : Interpretation M D zero one two) :
    ∃ C H Raw Sat Def EPrograms,
      DefStage M C D zero one two H Raw Sat Def ∧ Onto M EPrograms C.omega C.programs := by
  have hSymbols : M.MemberSubset D.symbols D.omega := by
    intro r hr
    rcases (hI.symbols r).mp hr with hr | hr
    · exact hr ▸ hI.naturals.zero_nat
    · exact hr ▸ hI.naturals.one_nat
  obtain ⟨ESymbols,hESymbols⟩ := subset_surjection_d hM hSymbols ((hI.symbols zero).mpr (Or.inl rfl))
  obtain ⟨Atom,hAtom⟩ := atomic_table_exists_d hM D
  obtain ⟨C,EPrograms,hLink,hC,hPrograms⟩ := countable_context_exists_d hM hI.spaces hESymbols Atom
  obtain ⟨H,hH⟩ := evaluation_exists_d hM C hC.omega
  obtain ⟨Raw,hRaw⟩ := truth_set_exists_d hM C H
  obtain ⟨Sat,hSat⟩ := typed_truth_set_exists_d hM C D Raw
  obtain ⟨Def,hDef⟩ := def_set_exists_d hM C D Sat zero
  refine ⟨C,H,Raw,Sat,Def,EPrograms,⟨hI,hC,?_,?_,hH,hRaw,hSat,hDef⟩,hPrograms⟩
  · exact ⟨hLink.omega_eq,hLink.carrier_eq,hLink.assignments_eq,rfl,hLink.codes_bound⟩
  · exact hLink.atomic_eq.symm ▸ hAtom

theorem set_def_stage_exists_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {ω : M.Domain} (hω : M.IsOmega ω) (A : M.Domain) :
    ∃ C D zero one two H Raw Sat Def,
      C.omega=ω ∧ C.carrier=A ∧ DefStage M C D zero one two H Raw Sat Def := by
  obtain ⟨D,zero,one,two,hOmega,hCarrier,hI⟩ := interpretation_exists_d hM hω A
  obtain ⟨C,H,Raw,Sat,Def,_,hStage,_⟩ := def_stage_for_interpretation_d hM hI
  exact ⟨C,D,zero,one,two,H,Raw,Sat,Def,hStage.link.omega_eq.trans hOmega,
    hStage.link.carrier_eq.trans hCarrier,hStage⟩

end KP1Y.SetLanguage
