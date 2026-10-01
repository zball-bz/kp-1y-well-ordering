import KP1Y.DefStageWitness

/-! 规范纯集合语法的额外精确性由KP实际构造：操作数恰为ω∪codes、关系无垃圾成员、原子占位为空。 -/
namespace KP1Y.SetLanguage
open YesMetaZFC YesMetaZFC.SetTheory
open KP1Y.Kuratowski KP1Y.Satisfaction
universe u

structure CanonicalSyntax (M : SetTheory.Structure.{u}) (C : Context M.Domain) (D : RelationalData M.Domain)
    (zero one two : M.Domain) : Prop extends FixedSyntax M C D zero one two where
  carrier_omega : D.carrier=D.omega
  operands_exact : M.IsUnionOfTwo C.operands C.omega D.codes
  relation_support : RelationSupport M D.interpretation D.symbols D.values
  atomic_zero : C.atomic=zero

theorem canonical_context_exists_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {D : RelationalData M.Domain} (hD : DataSpaces M D) (Atom : M.Domain) :
    ∃ C, RelationalContext M D Atom C ∧ ContextSpaces M C ∧ M.IsUnionOfTwo C.operands D.omega D.codes := by
  have hw := KP1Y.models_weakKP hM
  obtain ⟨Tags,a,n,i,q,hDistinct,ha,hn,hi,hq,hTags⟩ := opcode_set_exists_d hM hD.omega
  obtain ⟨O,hO⟩ := SetTheory.KP.exists_unionOfTwo hw D.omega D.codes
  obtain ⟨Pairs,hPairs⟩ := product_exists hM O O
  obtain ⟨Instructions,hInstructions⟩ := product_exists hM Tags Pairs
  obtain ⟨Programs,hPrograms⟩ := KP1Y.Sequences.finite_sequences_exist_d hM hD.omega Instructions
  obtain ⟨Columns,hColumns⟩ := product_exists hM Programs D.values
  let C : Context M.Domain := ⟨D.omega,D.carrier,O,Pairs,Instructions,Programs,D.values,Columns,Atom,a,n,i,q⟩
  refine ⟨C,⟨rfl,rfl,rfl,rfl,fun x hx => (hO x).mpr (Or.inr hx)⟩,
    ⟨hD.omega,hDistinct,⟨ha,hn,hi,hq⟩,fun x hx => (hO x).mpr (Or.inl hx),
      hPairs,?_,hPrograms,hD.values,hColumns⟩,hO⟩
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

theorem canonical_syntax_exists_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {ω : M.Domain} (hω : M.IsOmega ω) :
    ∃ C D zero one two, C.omega=ω ∧ CanonicalSyntax M C D zero one two := by
  obtain ⟨D0,zero,one,two,hOmega,hCarrier,hI⟩ := interpretation_exists_d hM hω ω
  obtain ⟨R,hR⟩ := set_relation_table_exists_d hM D0.carrier zero one two D0.symbols D0.values
  let D := D0.withInterpretation D0.carrier D0.values R
  have hID : Interpretation M D zero one two :=
    ⟨hI.naturals,⟨hI.spaces.omega,hI.spaces.variables,hI.spaces.values,hI.spaces.codes⟩,
      hI.symbols,hI.arity,hI.arity_rows,hR.rows⟩
  obtain ⟨C,hLink,hC,hOps⟩ := canonical_context_exists_d hM hID.spaces zero
  refine ⟨C,D,zero,one,two,hLink.omega_eq.trans hOmega,?_⟩
  refine ⟨⟨hID,hC,⟨hLink.omega_eq,hLink.carrier_eq,hLink.assignments_eq,rfl,hLink.codes_bound⟩⟩,
    hCarrier.trans hOmega.symm,?_,hR.support,hLink.atomic_eq⟩
  simpa only [hLink.omega_eq] using hOps

end KP1Y.SetLanguage
