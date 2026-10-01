import KP1Y.ElementarySyntax

/-! 程序初等性蕴含原子表一致；显式编译单个原子，避免另假设小结构的解释。 -/
namespace KP1Y.Satisfaction
open YesMetaZFC YesMetaZFC.SetTheory
open KP1Y.Kuratowski KP1Y.Functions
universe u

theorem ProgramElementary.atomic_agreement_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : Context M.Domain} (hC : ContextSpaces M C) {D : RelationalData M.Domain} (hD : DataSpaces M D)
    {small large : EvaluationData M.Domain} (hSmall : small.Valid C) (hLarge : large.Valid C)
    (hCodes : M.MemberSubset D.codes C.operands) (h : ProgramElementary M C D small large) : AtomicAgreement M C D small large := by
  intro a bound hScope hb s hS
  obtain ⟨empty,hEmpty,hEmptyNat,_,hEmptyGraph⟩ := empty_program_d hC
  have hEmptyProgram : WellFormedProgram M C D empty empty bound :=
    ⟨hEmptyGraph,hEmptyNat,hb,fun i hi => False.elim (hEmpty i hi)⟩
  have ha := hScope.code_mem hD
  obtain ⟨p,length,hP,hMeaning⟩ := uniform_compile_atom_d hM hC hEmptyProgram ha (hCodes a ha) hScope
  have hsSmall := (hSmall.assignments_exact s).mpr ⟨bound,hb,hS⟩
  have hsLarge := (hLarge.assignments_exact s).mpr ⟨bound,hb,hS.mono_values h.carrier_subset⟩
  exact (hMeaning small.carrier small.assignments small.columns small.atomic small.table hSmall s hsSmall).symm.trans
    ((h.truth p length empty bound hP.result s hS).trans
      (hMeaning large.carrier large.assignments large.columns large.atomic large.table hLarge s hsLarge))

end KP1Y.Satisfaction
