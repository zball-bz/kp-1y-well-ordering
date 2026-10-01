import KP1Y.SetLanguageSyntax

/-! 由 KPω 的集合运算实际构造二元等号、隶属的元数图和关系解释图。 -/
namespace KP1Y.SetLanguage
open YesMetaZFC YesMetaZFC.SetTheory YesMetaZFC.SetTheory.Definitional
open KP1Y.Kuratowski KP1Y.Functions KP1Y.Naturals KP1Y.Satisfaction
universe u

structure Interpretation (M : SetTheory.Structure.{u}) (D : RelationalData M.Domain)
    (zero one two : M.Domain) : Prop where
  naturals : SmallNaturals M D.omega zero one two
  spaces : DataSpaces M D
  symbols : PairSet M D.symbols zero one
  arity : Graph M D.arity D.symbols D.omega
  arity_rows : ∀ r n, MemPair M D.arity r n ↔ M.mem r D.symbols ∧ n=two
  relation_rows : ∀ r t, MemPair M D.interpretation r t ↔
    M.mem r D.symbols ∧ M.mem t D.values ∧ SetAtom M D.carrier zero one two r t

private def binaryAritySchema : Project.Delta0BinarySchema 1 where
  body := Project.Formula.extensionalEq (.bound 0) (.bound 2)
  freeClosed := by simp
  delta0 := .atom _ _ _

private theorem binaryAritySchema_iff {M : SetTheory.Structure.{u}} (he : Extensional M)
    (two r n : M.Domain) :
    Project.Formula.satisfies (((oneEnv two).push r).push n) binaryAritySchema.body ↔ n=two := by
  rw [binaryAritySchema,Project.Formula.satisfies_extensionalEq_iff_eq he]
  rfl

private def setRelationSchema : Project.Delta0BinarySchema 4 where
  body := setAtomFormula (.bound 2) (.bound 3) (.bound 4) (.bound 5) (.bound 1) (.bound 0)
  freeClosed := by
    simp [setAtomFormula, graphFormula, memPairFormula, codeFormula, pairFormula,
      Project.Formula.forallMem, Project.Formula.existsMem, Definitional.Formula.FreeClosed]
  delta0 := setAtomFormula_delta0 _ _ _ _ _ _

private def setRelationEnv {M : SetTheory.Structure.{u}} (A zero one two : M.Domain) : Env M 4 :=
  ⟨Fin.cases A (Fin.cases zero (Fin.cases one (fun _ => two))),fun _ => A⟩

private theorem setRelationSchema_iff {M : SetTheory.Structure.{u}} (he : Extensional M)
    (A zero one two r t : M.Domain) :
    Project.Formula.satisfies (((setRelationEnv A zero one two).push r).push t) setRelationSchema.body ↔
      SetAtom M A zero one two r t := by
  rw [setRelationSchema,setAtomFormula_iff he]
  rfl

theorem interpretation_for_carrier_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {ω zero one two : M.Domain} (hω : M.IsOmega ω) (hN : SmallNaturals M ω zero one two) (A : M.Domain) :
    ∃ arity rel variables values codes,
      Interpretation M ⟨ω,A,two,arity,rel,variables,values,codes⟩ zero one two := by
  obtain ⟨arity,hSupport,hRawArity⟩ := relation_comprehension_d hM binaryAritySchema (oneEnv two) two ω
  have hArityRows (r n : M.Domain) : MemPair M arity r n ↔ M.mem r two ∧ n=two := by
    have h := hRawArity r n
    rw [binaryAritySchema_iff hM.1] at h
    exact h.trans ⟨fun h => ⟨h.1,h.2.2⟩,fun h => ⟨h.1,h.2.symm ▸ hN.two_nat,h.2⟩⟩
  have hArity : Graph M arity two ω := by
    refine ⟨hSupport,?_,?_⟩
    · intro r hr
      exact ⟨two,hN.two_nat,(hArityRows r two).mpr ⟨hr,rfl⟩⟩
    · intro r n m hn hm
      exact ((hArityRows r n).mp hn).2.trans ((hArityRows r m).mp hm).2.symm
  obtain ⟨variables,values,codes,hSpaces⟩ := data_spaces_exists_d hM hω A two arity zero
  obtain ⟨rel,_,hRawRel⟩ := relation_comprehension_d hM setRelationSchema
    (setRelationEnv A zero one two) two values
  refine ⟨arity,rel,variables,values,codes,hN,
    ⟨hω,hSpaces.variables,hSpaces.values,hSpaces.codes⟩,hN.two_members hM.1,hArity,hArityRows,?_⟩
  intro r t
  simpa only [setRelationSchema_iff hM.1] using hRawRel r t

theorem interpretation_exists_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {ω : M.Domain} (hω : M.IsOmega ω) (A : M.Domain) :
    ∃ D zero one two, D.omega=ω ∧ D.carrier=A ∧ Interpretation M D zero one two := by
  obtain ⟨zero,one,two,hN⟩ := small_naturals_exist hω
  obtain ⟨arity,rel,variables,values,codes,hI⟩ := interpretation_for_carrier_d hM hω hN A
  exact ⟨⟨ω,A,two,arity,rel,variables,values,codes⟩,zero,one,two,rfl,rfl,hI⟩

theorem Interpretation.equality_meaning {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {D : RelationalData M.Domain} {zero one two t x y : M.Domain}
    (hI : Interpretation M D zero one two) (ht : Graph M t two D.carrier)
    (h0 : MemPair M t zero x) (h1 : MemPair M t one y) :
    MemPair M D.interpretation zero t ↔ x=y := by
  rw [hI.relation_rows zero t, equality_atom_iff hM hI.naturals ht h0 h1]
  have hr : M.mem zero D.symbols := (hI.symbols zero).mpr (Or.inl rfl)
  have hValue := (hI.spaces.values t).mpr ⟨two,hI.naturals.two_nat,ht⟩
  exact ⟨fun h => h.2.2,fun h => ⟨hr,hValue,h⟩⟩

theorem Interpretation.membership_meaning {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {D : RelationalData M.Domain} {zero one two t x y : M.Domain}
    (hI : Interpretation M D zero one two) (ht : Graph M t two D.carrier)
    (h0 : MemPair M t zero x) (h1 : MemPair M t one y) :
    MemPair M D.interpretation one t ↔ M.mem x y := by
  rw [hI.relation_rows one t, membership_atom_iff hM hI.naturals ht h0 h1]
  have hr : M.mem one D.symbols := (hI.symbols one).mpr (Or.inr rfl)
  have hValue := (hI.spaces.values t).mpr ⟨two,hI.naturals.two_nat,ht⟩
  exact ⟨fun h => h.2.2,fun h => ⟨hr,hValue,h⟩⟩

end KP1Y.SetLanguage
