import KP1Y.TypedSatisfaction

/-! 带合法语法过滤的满意度集合存在性，闭合全部实际对象参数。 -/
namespace KP1Y.Satisfaction
open YesMetaZFC YesMetaZFC.SetTheory YesMetaZFC.SetTheory.Definitional
open KP1Y.Kuratowski KP1Y.Functions

def typedSatisfactionCore : Project.Formula 1 21 :=
  .imp (Project.Formula.isOmega syntaxContextParameters.omega)
    (.existsE (.existsE (.existsE
      (.conj (evaluationFormula syntaxContextParameters.weaken.weaken.weaken (.bound 2))
        (.conj (truthFormula syntaxContextParameters.weaken.weaken.weaken (.bound 2) (.bound 1))
          (typedTruthFormula syntaxContextParameters.weaken.weaken.weaken
            syntaxDataParameters.weaken.weaken.weaken (.bound 1) (.bound 0)))))))

def typedSatisfactionSentence : Project.Sentence :=
  Project.Sentence.forallClosure typedSatisfactionCore (by
    simp [typedSatisfactionCore, evaluationFormula, truthFormula, finalTrueFormula,
      typedTruthFormula, validColumnFormula, formulaProgramFormula, wellFormedProgramFormula,
      wellFormedAtFormula, scopedAtomFormula, evalFormula, atomicFormula, negationFormula,
      implicationFormula, universalFormula, instructionAtFormula, Assignments.updatedFormula,
      graphFormula, Bounded.successorFormula, memPairFormula, codeFormula, pairFormula,
      Context.weaken, Context.map, RelationalData.weaken, RelationalData.map,
      syntaxContextParameters, syntaxDataParameters, Project.Formula.isOmega,
      Project.Formula.isInductive, Project.Formula.isEmpty, Project.Formula.isSuccessor,
      Project.Formula.forallMem, Project.Formula.existsMem, Definitional.Formula.FreeClosed])

theorem typedSatisfactionCore_iff {M : SetTheory.Structure} (he : Extensional M) (env : Env M 21) :
    Project.Formula.satisfies env typedSatisfactionCore ↔
      (M.IsOmega (env.bound 0) → ∃ H Raw Sat,
        Evaluation M (syntaxContextParameters.eval env) H ∧ TruthSet M (syntaxContextParameters.eval env) H Raw ∧
          TypedTruthSet M (syntaxContextParameters.eval env) (syntaxDataParameters.eval env) Raw Sat) := by
  simp only [typedSatisfactionCore, Project.Formula.satisfies_imp_iff,
    Project.Formula.satisfies_isOmega_iff, Project.Formula.satisfies_exists_iff,
    Project.Formula.satisfies_conj_iff, evaluationFormula_iff he, truthFormula_iff he,
    typedTruthFormula_iff he, Context.eval_weaken, RelationalData.eval_weaken]
  rfl

theorem typed_satisfaction_derivable : KP1Y.Derives typedSatisfactionSentence := by
  apply KP1Y.derives_of_all_models
  intro M hM free
  apply (Project.Formula.satisfies_forallClosure_iff free typedSatisfactionCore).mpr
  intro bound
  let env : Env M 21 := ⟨bound,free⟩
  apply (typedSatisfactionCore_iff hM.1 env).mpr
  intro hω
  obtain ⟨H,hH⟩ := evaluation_exists_d hM (syntaxContextParameters.eval env) hω
  obtain ⟨Raw,hRaw⟩ := truth_set_exists_d hM (syntaxContextParameters.eval env) H
  obtain ⟨Sat,hSat⟩ := typed_truth_set_exists_d hM (syntaxContextParameters.eval env) (syntaxDataParameters.eval env) Raw
  exact ⟨H,Raw,Sat,hH,hRaw,hSat⟩

universe u
theorem typed_relational_truth_exists_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {ω : M.Domain} (hω : M.IsOmega ω) (A symbols arity interpretation : M.Domain) :
    ∃ variables values codes Atom C H Raw Sat,
      let D : RelationalData M.Domain := ⟨ω,A,symbols,arity,interpretation,variables,values,codes⟩
      DataSpaces M D ∧ AtomicTable M D Atom ∧ RelationalContext M D Atom C ∧ ContextSpaces M C ∧
        Evaluation M C H ∧ TruthSet M C H Raw ∧ TypedTruthSet M C D Raw Sat := by
  obtain ⟨variables,values,codes,Atom,C,H,Raw,hD,hAtom,hRel,hC,hH,hRaw⟩ :=
    relational_truth_exists_d hM hω A symbols arity interpretation
  let D : RelationalData M.Domain := ⟨ω,A,symbols,arity,interpretation,variables,values,codes⟩
  obtain ⟨Sat,hSat⟩ := typed_truth_set_exists_d hM C D Raw
  exact ⟨variables,values,codes,Atom,C,H,Raw,Sat,hD,hAtom,hRel,hC,hH,hRaw,hSat⟩

end KP1Y.Satisfaction
