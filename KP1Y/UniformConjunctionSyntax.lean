import KP1Y.AllInterpretations
import KP1Y.ConjunctionExtensionSyntax

/-! 同一份内部有限合取代码对所有解释正确的实际归纳公式。 -/
namespace KP1Y.Satisfaction
open YesMetaZFC YesMetaZFC.SetTheory YesMetaZFC.SetTheory.Definitional
open KP1Y.Kuratowski KP1Y.Functions
universe u

def UniformConjunctionMeaning (M : SetTheory.Structure.{u}) (C : Context M.Domain) (D : RelationalData M.Domain)
    (p head seq stage : M.Domain) : Prop :=
  ∀ A S B At H, EvaluationInstance M C A S B At H → ∀ s, M.mem s S →
    (NodeTrue M (C.withInterpretation A S B At) H p head s ↔ AllAtoms M (C.withInterpretation A S B At) D seq stage s)

def uniformConjunctionMeaningFormula {n : Nat} (C : Context (Project.Term n)) (D : RelationalData (Project.Term n))
    (p head seq stage : Project.Term n) : Project.Formula 1 n :=
  allInstancesFormula C (Project.Formula.forallMem (.bound 3)
    (.iff (nodeTrueFormula (instanceContext C).weaken (.bound 1)
        p.weaken.weaken.weaken.weaken.weaken.weaken head.weaken.weaken.weaken.weaken.weaken.weaken (.bound 0))
      (allAtomsFormula (instanceContext C).weaken D.weaken.weaken.weaken.weaken.weaken.weaken
        seq.weaken.weaken.weaken.weaken.weaken.weaken stage.weaken.weaken.weaken.weaken.weaken.weaken (.bound 0))))

theorem uniformConjunctionMeaningFormula_iff {M : SetTheory.Structure.{u}} (he : Extensional M) {n : Nat}
    (env : Env M n) (C : Context (Project.Term n)) (D : RelationalData (Project.Term n)) (p head seq stage : Project.Term n) :
    Project.Formula.satisfies env (uniformConjunctionMeaningFormula C D p head seq stage) ↔
      UniformConjunctionMeaning M (C.eval env) (D.eval env) (p.eval env) (head.eval env) (seq.eval env) (stage.eval env) := by
  simp only [uniformConjunctionMeaningFormula, allInstancesFormula_iff he,
    Project.Formula.satisfies_forallMem_iff, Project.Formula.satisfies_iff_iff,
    nodeTrueFormula_iff he, allAtomsFormula_iff he, Context.eval_weaken,
    instanceContext_eval, RelationalData.eval_weaken, Definitional.Term.eval_weaken]
  rfl

def UniformConjunctionFrom (M : SetTheory.Structure.{u}) (C : Context M.Domain) (D : RelationalData M.Domain)
    (original seq stage bound : M.Domain) : Prop :=
  ∃ p, M.mem p C.programs ∧ ∃ length, M.mem length C.omega ∧ ∃ head, M.mem head C.omega ∧
    FormulaResult M C D p length head bound ∧ M.MemberSubset original p ∧ UniformConjunctionMeaning M C D p head seq stage

def uniformConjunctionFromFormula {n : Nat} (C : Context (Project.Term n)) (D : RelationalData (Project.Term n))
    (original seq stage bound : Project.Term n) : Project.Formula 1 n :=
  Project.Formula.existsMem C.programs (Project.Formula.existsMem C.omega.weaken
    (Project.Formula.existsMem C.omega.weaken.weaken
      (.conj (resultFormula C.weaken.weaken.weaken D.weaken.weaken.weaken
          (.bound 2) (.bound 1) (.bound 0) bound.weaken.weaken.weaken)
        (.conj (Project.Formula.subset original.weaken.weaken.weaken (.bound 2))
          (uniformConjunctionMeaningFormula C.weaken.weaken.weaken D.weaken.weaken.weaken
            (.bound 2) (.bound 0) seq.weaken.weaken.weaken stage.weaken.weaken.weaken)))))

theorem uniformConjunctionFromFormula_iff {M : SetTheory.Structure.{u}} (he : Extensional M) {n : Nat}
    (env : Env M n) (C : Context (Project.Term n)) (D : RelationalData (Project.Term n))
    (original seq stage bound : Project.Term n) :
    Project.Formula.satisfies env (uniformConjunctionFromFormula C D original seq stage bound) ↔
      UniformConjunctionFrom M (C.eval env) (D.eval env) (original.eval env) (seq.eval env) (stage.eval env) (bound.eval env) := by
  simp only [uniformConjunctionFromFormula, Project.Formula.satisfies_existsMem_iff,
    Project.Formula.satisfies_conj_iff, Project.Formula.satisfies_subset_iff,
    resultFormula_iff he, uniformConjunctionMeaningFormula_iff he,
    Context.eval_weaken, RelationalData.eval_weaken, Definitional.Term.eval_weaken]
  rfl

private def uniformConjunctionContext : Context (Project.Term 26) :=
  ⟨.bound 5,.bound 6,.bound 7,.bound 8,.bound 9,.bound 10,.bound 11,
    .bound 12,.bound 13,.bound 14,.bound 15,.bound 16,.bound 17⟩
private def uniformConjunctionData : RelationalData (Project.Term 26) :=
  ⟨.bound 18,.bound 19,.bound 20,.bound 21,.bound 22,.bound 23,.bound 24,.bound 25⟩

def uniformConjunctionGuard : Project.UnarySchema 25 where
  body := .imp (Project.Formula.subset (.bound 0) (.bound 1))
    (uniformConjunctionFromFormula uniformConjunctionContext uniformConjunctionData (.bound 4) (.bound 3) (.bound 0) (.bound 2))
  freeClosed := by
    simp [uniformConjunctionFromFormula, uniformConjunctionMeaningFormula, allInstancesFormula,
      evaluationInstanceFormula, KP1Y.Sequences.finiteSequenceSpaceFormula, productExactFormula,
      evaluationFormula, evalFormula, atomicFormula, negationFormula, implicationFormula, universalFormula,
      resultFormula, wellFormedProgramFormula, wellFormedAtFormula, scopedAtomFormula, instructionAtFormula,
      Assignments.updatedFormula, nodeTrueFormula, allAtomsFormula, graphFormula, Bounded.successorFormula,
      memPairFormula, codeFormula, pairFormula, Context.weaken, Context.map, Context.withInterpretation,
      instanceContext, RelationalData.weaken, RelationalData.map, uniformConjunctionContext, uniformConjunctionData,
      Project.Formula.existsMem, Project.Formula.forallMem, Definitional.Formula.FreeClosed]

theorem uniformConjunctionGuard_iff {M : SetTheory.Structure.{u}} (he : Extensional M)
    (C : Context M.Domain) (D : RelationalData M.Domain) (original seq bound N stage : M.Domain) :
    Project.Formula.satisfies ((((((syntaxEnv C D).push original).push seq).push bound).push N).push stage)
        uniformConjunctionGuard.body ↔
      (M.MemberSubset stage N → UniformConjunctionFrom M C D original seq stage bound) := by
  simp only [uniformConjunctionGuard, Project.Formula.satisfies_imp_iff, Project.Formula.satisfies_subset_iff,
    uniformConjunctionFromFormula_iff he]
  rfl

end KP1Y.Satisfaction
