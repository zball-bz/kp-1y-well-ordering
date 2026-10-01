import KP1Y.CountableNamedSpaces
import KP1Y.SatisfactionSpaces

/-! 从可数关系符号集实际构造可数的全部公式程序空间；不把任意 ContextSpaces 假定为可数。 -/
namespace KP1Y.Satisfaction
open YesMetaZFC YesMetaZFC.SetTheory
open KP1Y.Kuratowski KP1Y.Functions KP1Y.Cardinal
universe u

theorem countable_context_exists_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {D : RelationalData M.Domain} (hD : DataSpaces M D) {ESymbols : M.Domain}
    (hSymbols : Onto M ESymbols D.omega D.symbols) (Atom : M.Domain) :
    ∃ C EPrograms, RelationalContext M D Atom C ∧ ContextSpaces M C ∧ Onto M EPrograms C.omega C.programs := by
  obtain ⟨EVariables,hEVariables⟩ := KP1Y.Naturals.natural_words_countable_d hM hD.omega hD.variables
  obtain ⟨ECodes,hECodes⟩ := countable_existing_product_d hM hD.omega hSymbols hEVariables hD.codes
  obtain ⟨EOmega,hEOmega⟩ := identity_onto_d hM D.omega
  obtain ⟨O,EO,hO,hEO⟩ := countable_union_d hM hD.omega hEOmega hECodes
  obtain ⟨Pairs,EPairs,hPairs,hEPairs⟩ := countable_product_d hM hD.omega hEO hEO
  obtain ⟨Tags,a,n,i,q,hDistinct,ha,hn,hi,hq,hTags⟩ := opcode_set_exists_d hM hD.omega
  have hTagsSub : M.MemberSubset Tags D.omega := by
    intro x hx
    rcases (hTags x).mp hx with he | he | he | he
    · exact he ▸ ha
    · exact he ▸ hn
    · exact he ▸ hi
    · exact he ▸ hq
  obtain ⟨ETags,hETags⟩ := subset_surjection_d hM hTagsSub ((hTags a).mpr (Or.inl rfl))
  obtain ⟨Instructions,EInstructions,hInstructions,hEInstructions⟩ := countable_product_d hM hD.omega hETags hEPairs
  obtain ⟨Programs,EPrograms,hPrograms,hEPrograms⟩ := countable_sequences_d hM hD.omega hEInstructions
  obtain ⟨Columns,hColumns⟩ := product_exists hM Programs D.values
  let C : Context M.Domain := ⟨D.omega,D.carrier,O,Pairs,Instructions,Programs,D.values,Columns,Atom,a,n,i,q⟩
  refine ⟨C,EPrograms,⟨rfl,rfl,rfl,rfl,fun x hx => (hO x).mpr (Or.inr hx)⟩,
    ⟨hD.omega,hDistinct,⟨ha,hn,hi,hq⟩,fun x hx => (hO x).mpr (Or.inl hx),
      hPairs,?_,hPrograms,hD.values,hColumns⟩,hEPrograms⟩
  intro instr
  constructor
  · intro hInstr
    obtain ⟨op,hop,args,hArgs,hCode⟩ := (hInstructions instr).mp hInstr
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
  · rintro ⟨args,hArgs,hCode⟩
    rcases hCode with hCode | hCode | hCode | hCode
    · exact (hInstructions instr).mpr ⟨a,(hTags a).mpr (Or.inl rfl),args,hArgs,hCode⟩
    · exact (hInstructions instr).mpr ⟨n,(hTags n).mpr (Or.inr (Or.inl rfl)),args,hArgs,hCode⟩
    · exact (hInstructions instr).mpr ⟨i,(hTags i).mpr (Or.inr (Or.inr (Or.inl rfl))),args,hArgs,hCode⟩
    · exact (hInstructions instr).mpr ⟨q,(hTags q).mpr (Or.inr (Or.inr (Or.inr rfl))),args,hArgs,hCode⟩

end KP1Y.Satisfaction
