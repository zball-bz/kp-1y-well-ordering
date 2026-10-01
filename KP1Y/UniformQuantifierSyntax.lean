import KP1Y.AllInterpretations
import KP1Y.QuantifierBlockSyntax

/-! 一份内部量词块代码在全部共享语法解释中的语义，写成真实对象公式。 -/
namespace KP1Y.Satisfaction
open YesMetaZFC YesMetaZFC.SetTheory YesMetaZFC.SetTheory.Definitional
open KP1Y.Kuratowski KP1Y.Functions
universe u

def UniformQuantificationMeaning (M : SetTheory.Structure.{u}) (C : Context M.Domain)
    (p head original originalHead vars stage bound : M.Domain) : Prop :=
  ∀ A S B At H, EvaluationInstance M C A S B At H → ∀ s, M.mem s S → Graph M s bound A →
    (NodeTrue M (C.withInterpretation A S B At) H p head s ↔
      Quantified M (C.withInterpretation A S B At) H original originalHead vars stage s bound)

def uniformQuantificationMeaningFormula {n : Nat} (C : Context (Project.Term n))
    (p head original originalHead vars stage bound : Project.Term n) : Project.Formula 1 n :=
  allInstancesFormula C (Project.Formula.forallMem (.bound 3)
    (.imp (graphFormula (.bound 0) bound.weaken.weaken.weaken.weaken.weaken.weaken (.bound 5))
      (.iff (nodeTrueFormula (instanceContext C).weaken (.bound 1)
          p.weaken.weaken.weaken.weaken.weaken.weaken head.weaken.weaken.weaken.weaken.weaken.weaken (.bound 0))
        (quantifiedFormula (instanceContext C).weaken (.bound 1)
          original.weaken.weaken.weaken.weaken.weaken.weaken originalHead.weaken.weaken.weaken.weaken.weaken.weaken
          vars.weaken.weaken.weaken.weaken.weaken.weaken stage.weaken.weaken.weaken.weaken.weaken.weaken
          (.bound 0) bound.weaken.weaken.weaken.weaken.weaken.weaken))))

theorem uniformQuantificationMeaningFormula_iff {M : SetTheory.Structure.{u}} (he : Extensional M) {n : Nat}
    (env : Env M n) (C : Context (Project.Term n)) (p head original originalHead vars stage bound : Project.Term n) :
    Project.Formula.satisfies env (uniformQuantificationMeaningFormula C p head original originalHead vars stage bound) ↔
      UniformQuantificationMeaning M (C.eval env) (p.eval env) (head.eval env) (original.eval env)
        (originalHead.eval env) (vars.eval env) (stage.eval env) (bound.eval env) := by
  simp only [uniformQuantificationMeaningFormula, allInstancesFormula_iff he,
    Project.Formula.satisfies_forallMem_iff, Project.Formula.satisfies_imp_iff,
    Project.Formula.satisfies_iff_iff, graphFormula_iff he, nodeTrueFormula_iff he, quantifiedFormula_iff he,
    Context.eval_weaken, instanceContext_eval, Definitional.Term.eval_weaken]
  rfl

def UniformQuantificationResult (M : SetTheory.Structure.{u}) (C : Context M.Domain) (D : RelationalData M.Domain)
    (original originalHead vars stage bound : M.Domain) : Prop :=
  ∃ p, M.mem p C.programs ∧ ∃ length, M.mem length C.omega ∧ ∃ head, M.mem head C.omega ∧
    FormulaResult M C D p length head bound ∧ M.MemberSubset original p ∧
      UniformQuantificationMeaning M C p head original originalHead vars stage bound

def uniformQuantificationResultFormula {n : Nat} (C : Context (Project.Term n)) (D : RelationalData (Project.Term n))
    (original originalHead vars stage bound : Project.Term n) : Project.Formula 1 n :=
  Project.Formula.existsMem C.programs (Project.Formula.existsMem C.omega.weaken
    (Project.Formula.existsMem C.omega.weaken.weaken
      (.conj (resultFormula C.weaken.weaken.weaken D.weaken.weaken.weaken
          (.bound 2) (.bound 1) (.bound 0) bound.weaken.weaken.weaken)
        (.conj (Project.Formula.subset original.weaken.weaken.weaken (.bound 2))
          (uniformQuantificationMeaningFormula C.weaken.weaken.weaken (.bound 2) (.bound 0)
            original.weaken.weaken.weaken originalHead.weaken.weaken.weaken vars.weaken.weaken.weaken
            stage.weaken.weaken.weaken bound.weaken.weaken.weaken)))))

theorem uniformQuantificationResultFormula_iff {M : SetTheory.Structure.{u}} (he : Extensional M) {n : Nat}
    (env : Env M n) (C : Context (Project.Term n)) (D : RelationalData (Project.Term n))
    (original originalHead vars stage bound : Project.Term n) :
    Project.Formula.satisfies env (uniformQuantificationResultFormula C D original originalHead vars stage bound) ↔
      UniformQuantificationResult M (C.eval env) (D.eval env) (original.eval env) (originalHead.eval env)
        (vars.eval env) (stage.eval env) (bound.eval env) := by
  simp only [uniformQuantificationResultFormula, Project.Formula.satisfies_existsMem_iff,
    Project.Formula.satisfies_conj_iff, Project.Formula.satisfies_subset_iff,
    resultFormula_iff he, uniformQuantificationMeaningFormula_iff he,
    Context.eval_weaken, RelationalData.eval_weaken, Definitional.Term.eval_weaken]
  rfl

private def uniformQuantificationContext : Context (Project.Term 27) :=
  ⟨.bound 6,.bound 7,.bound 8,.bound 9,.bound 10,.bound 11,.bound 12,
    .bound 13,.bound 14,.bound 15,.bound 16,.bound 17,.bound 18⟩
private def uniformQuantificationData : RelationalData (Project.Term 27) :=
  ⟨.bound 19,.bound 20,.bound 21,.bound 22,.bound 23,.bound 24,.bound 25,.bound 26⟩

def uniformQuantificationGuard : Project.UnarySchema 26 where
  body := .imp (Project.Formula.subset (.bound 0) (.bound 1))
    (uniformQuantificationResultFormula uniformQuantificationContext uniformQuantificationData
      (.bound 5) (.bound 4) (.bound 3) (.bound 0) (.bound 2))
  freeClosed := by
    simp [uniformQuantificationResultFormula, uniformQuantificationMeaningFormula, allInstancesFormula,
      evaluationInstanceFormula, KP1Y.Sequences.finiteSequenceSpaceFormula, productExactFormula,
      evaluationFormula, evalFormula, atomicFormula, negationFormula, implicationFormula, universalFormula,
      resultFormula, wellFormedProgramFormula, wellFormedAtFormula, scopedAtomFormula, instructionAtFormula,
      Assignments.updatedFormula, nodeTrueFormula, quantifiedFormula, agreeOutsideFormula, touchedFormula,
      graphFormula, Bounded.successorFormula, memPairFormula, codeFormula, pairFormula,
      Context.weaken, Context.map, Context.withInterpretation, instanceContext,
      RelationalData.weaken, RelationalData.map, uniformQuantificationContext, uniformQuantificationData,
      Project.Formula.existsMem, Project.Formula.forallMem, Definitional.Formula.FreeClosed]

theorem uniformQuantificationGuard_iff {M : SetTheory.Structure.{u}} (he : Extensional M)
    (C : Context M.Domain) (D : RelationalData M.Domain) (original originalHead vars bound N stage : M.Domain) :
    Project.Formula.satisfies (((((((syntaxEnv C D).push original).push originalHead).push vars).push bound).push N).push stage)
        uniformQuantificationGuard.body ↔
      (M.MemberSubset stage N → UniformQuantificationResult M C D original originalHead vars stage bound) := by
  simp only [uniformQuantificationGuard, Project.Formula.satisfies_imp_iff, Project.Formula.satisfies_subset_iff,
    uniformQuantificationResultFormula_iff he]
  rfl

end KP1Y.Satisfaction
