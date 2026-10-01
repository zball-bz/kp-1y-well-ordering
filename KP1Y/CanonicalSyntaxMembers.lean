import KP1Y.CanonicalSetSyntax
import KP1Y.ConstructibleSequences
import KP1Y.ConstructibleRelations

/-! 规范纯集合语法的全部24个实际参数都属于由该语法定义的构造类。 -/
namespace KP1Y.Constructible
open YesMetaZFC YesMetaZFC.SetTheory YesMetaZFC.SetTheory.Definitional
open KP1Y.Kuratowski KP1Y.Functions KP1Y.Satisfaction KP1Y.SetLanguage
universe u

private def arityRowSchema : Project.Delta0BinarySchema 1 where
  body := Project.Formula.extensionalEq (.bound 0) (.bound 2)
  freeClosed := by simp
  delta0 := .atom _ _ _

private theorem arityRowSchema_iff {M : SetTheory.Structure.{u}} (he : Extensional M) (two r n : M.Domain) :
    Project.Formula.satisfies (((oneEnv two).push r).push n) arityRowSchema.body ↔ n=two := by
  rw [arityRowSchema,Project.Formula.satisfies_extensionalEq_iff_eq he]
  rfl

private def pureRowSchema : Project.Delta0BinarySchema 4 where
  body := setAtomFormula (.bound 2) (.bound 3) (.bound 4) (.bound 5) (.bound 1) (.bound 0)
  freeClosed := by
    simp [setAtomFormula,graphFormula,memPairFormula,codeFormula,pairFormula,
      Project.Formula.forallMem,Project.Formula.existsMem,Definitional.Formula.FreeClosed]
  delta0 := setAtomFormula_delta0 _ _ _ _ _ _

private def pureRowEnv {M : SetTheory.Structure.{u}} (A zero one two : M.Domain) : Env M 4 :=
  ⟨Fin.cases A (Fin.cases zero (Fin.cases one (fun _ => two))),fun _ => A⟩

private theorem pureRowSchema_iff {M : SetTheory.Structure.{u}} (he : Extensional M) (A zero one two r t : M.Domain) :
    Project.Formula.satisfies (((pureRowEnv A zero one two).push r).push t) pureRowSchema.body ↔
      SetAtom M A zero one two r t := by
  rw [pureRowSchema,setAtomFormula_iff he]
  rfl

theorem canonical_parameters_constructible_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    (env : Env M 24) (h : CanonicalSyntax M (defContext.eval env) (defData.eval env)
      (env.bound 0) (env.bound 1) (env.bound 2)) : ∀ i, InConstructible M env (env.bound i) := by
  let C := defContext.eval env
  let D := defData.eval env
  let zero := env.bound 0
  let one := env.bound 1
  let two := env.bound 2
  have hS := h.toFixedSyntax
  have hDω : InConstructible M env D.omega := ordinal_constructible_d hM env hS
    (KP1Y.Naturals.omega_isOrdinal_d hM h.interpretation.spaces.omega)
  have hCω : InConstructible M env C.omega := Eq.mpr (congrArg (InConstructible M env) h.link.omega_eq) hDω
  have hDA : InConstructible M env D.carrier := Eq.mpr (congrArg (InConstructible M env) h.carrier_omega) hDω
  have hCA : InConstructible M env C.carrier := Eq.mpr (congrArg (InConstructible M env) h.link.carrier_eq) hDA
  have hz : InConstructible M env zero := hDω.mem_closed_d hM env hS h.interpretation.naturals.zero_nat
  have ho : InConstructible M env one := hDω.mem_closed_d hM env hS h.interpretation.naturals.one_nat
  have ht : InConstructible M env two := hDω.mem_closed_d hM env hS h.interpretation.naturals.two_nat
  have hSymbols : InConstructible M env D.symbols := pair_set_constructible_d hM env hS hz ho h.interpretation.symbols
  have hVars : InConstructible M env D.variables := sequence_space_constructible_d hM env hS
    h.interpretation.spaces.omega hDω h.interpretation.spaces.variables
  have hValues : InConstructible M env D.values := sequence_space_constructible_d hM env hS
    h.interpretation.spaces.omega hDA h.interpretation.spaces.values
  have hCodes : InConstructible M env D.codes := product_constructible_d hM env hS hSymbols hVars h.interpretation.spaces.codes
  have hArity : InConstructible M env D.arity := by
    apply relation_constructible_d hM env hS arityRowSchema (oneEnv two) (fun _ => ht)
      hSymbols hDω h.interpretation.arity.support
    intro r n
    rw [arityRowSchema_iff hM.1]
    exact (h.interpretation.arity_rows r n).trans
      ⟨fun hRow => ⟨hRow.1,hRow.2.symm ▸ h.interpretation.naturals.two_nat,hRow.2⟩,fun hRow => ⟨hRow.1,hRow.2.2⟩⟩
  have hRel : InConstructible M env D.interpretation := by
    have hParams : ∀ i, InConstructible M env ((pureRowEnv D.carrier zero one two).bound i) :=
      Fin.cases hDA (Fin.cases hz (Fin.cases ho (fun _ => ht)))
    apply relation_constructible_d hM env hS pureRowSchema (pureRowEnv D.carrier zero one two) hParams
      hSymbols hValues h.relation_support
    intro r t
    simpa only [pureRowSchema_iff hM.1] using h.interpretation.relation_rows r t
  have hOps : InConstructible M env C.operands := union_of_two_constructible_d hM env hS hCω hCodes h.operands_exact
  have hPairs : InConstructible M env C.pairs := product_constructible_d hM env hS hOps hOps h.spaces.pairs
  have hTagA : InConstructible M env C.atomTag := hCω.mem_closed_d hM env hS h.spaces.tag_naturals.1
  have hTagN : InConstructible M env C.negTag := hCω.mem_closed_d hM env hS h.spaces.tag_naturals.2.1
  have hTagI : InConstructible M env C.impTag := hCω.mem_closed_d hM env hS h.spaces.tag_naturals.2.2.1
  have hTagQ : InConstructible M env C.allTag := hCω.mem_closed_d hM env hS h.spaces.tag_naturals.2.2.2
  obtain ⟨Tags01,hTags01,hPair01⟩ := constructible_pair_d hM env hS hTagA hTagN
  obtain ⟨Tags23,hTags23,hPair23⟩ := constructible_pair_d hM env hS hTagI hTagQ
  obtain ⟨Tags,hUnion⟩ := SetTheory.KP.exists_unionOfTwo (KP1Y.models_weakKP hM) Tags01 Tags23
  have hTags := union_of_two_constructible_d hM env hS hTags01 hTags23 hUnion
  have haTags := (hUnion C.atomTag).mpr (Or.inl ((hPair01 C.atomTag).mpr (Or.inl rfl)))
  have hnTags := (hUnion C.negTag).mpr (Or.inl ((hPair01 C.negTag).mpr (Or.inr rfl)))
  have hiTags := (hUnion C.impTag).mpr (Or.inr ((hPair23 C.impTag).mpr (Or.inl rfl)))
  have hqTags := (hUnion C.allTag).mpr (Or.inr ((hPair23 C.allTag).mpr (Or.inr rfl)))
  have hInstructionsProduct : IsProduct M C.instructions Tags C.pairs := by
    intro instr
    constructor
    · intro hInstr
      obtain ⟨args,hArgs,hCode⟩ := (h.spaces.instructions instr).mp hInstr
      rcases hCode with hCode | hCode | hCode | hCode
      · exact ⟨C.atomTag,haTags,args,hArgs,hCode⟩
      · exact ⟨C.negTag,hnTags,args,hArgs,hCode⟩
      · exact ⟨C.impTag,hiTags,args,hArgs,hCode⟩
      · exact ⟨C.allTag,hqTags,args,hArgs,hCode⟩
    · rintro ⟨op,hop,args,hArgs,hCode⟩
      apply (h.spaces.instructions instr).mpr
      refine ⟨args,hArgs,?_⟩
      rcases (hUnion op).mp hop with hop | hop
      · rcases (hPair01 op).mp hop with he | he
        · subst op
          exact Or.inl hCode
        · subst op
          exact Or.inr (Or.inl hCode)
      · rcases (hPair23 op).mp hop with he | he
        · subst op
          exact Or.inr (Or.inr (Or.inl hCode))
        · subst op
          exact Or.inr (Or.inr (Or.inr hCode))
  have hInstructions : InConstructible M env C.instructions := product_constructible_d hM env hS hTags hPairs hInstructionsProduct
  have hPrograms : InConstructible M env C.programs := sequence_space_constructible_d hM env hS h.spaces.omega hInstructions h.spaces.programs
  have hAssignments : InConstructible M env C.assignments := Eq.mpr (congrArg (InConstructible M env) h.link.assignments_eq) hValues
  have hColumns : InConstructible M env C.columns := product_constructible_d hM env hS hPrograms hAssignments h.spaces.columns
  have hAtomic : InConstructible M env C.atomic := Eq.mpr (congrArg (InConstructible M env) h.atomic_zero) hz
  exact Fin.cases hz (Fin.cases ho (Fin.cases ht
    (Fin.cases hCω (Fin.cases hCA (Fin.cases hOps (Fin.cases hPairs (Fin.cases hInstructions
      (Fin.cases hPrograms (Fin.cases hAssignments (Fin.cases hColumns (Fin.cases hAtomic
        (Fin.cases hTagA (Fin.cases hTagN (Fin.cases hTagI (Fin.cases hTagQ
          (Fin.cases hDω (Fin.cases hDA (Fin.cases hSymbols (Fin.cases hArity
            (Fin.cases hRel (Fin.cases hVars (Fin.cases hValues (Fin.cases hCodes (fun i => Fin.elim0 i))))))))))))))))))))))))

end KP1Y.Constructible
