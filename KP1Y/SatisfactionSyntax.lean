import KP1Y.SatisfactionClauses
import KP1Y.RecursionSentence

/-! 实际满意度行算子、整表的有界验证公式及其参数闭合。 -/
namespace KP1Y.Satisfaction
open YesMetaZFC YesMetaZFC.SetTheory YesMetaZFC.SetTheory.Definitional
open KP1Y.Kuratowski
universe u

def EvalStep (M : SetTheory.Structure.{u}) (C : Context M.Domain) (i c H : M.Domain) : Prop :=
  ∃ p, M.mem p C.programs ∧ ∃ s, M.mem s C.assignments ∧ Codes M c p s ∧
    (AtomicCase M C p s i ∨ NegationCase M C p i c H ∨
      ImplicationCase M C p i c H ∨ UniversalCase M C p s i H)

def evalFormula {n : Nat} (C : Context (Project.Term n)) (i c H : Project.Term n) : Project.Formula 1 n :=
  Project.Formula.existsMem C.programs (Project.Formula.existsMem C.assignments.weaken
    (.conj (codeFormula c.weaken.weaken (.bound 1) (.bound 0))
      (.disj (atomicFormula C.weaken.weaken (.bound 1) (.bound 0) i.weaken.weaken)
        (.disj (negationFormula C.weaken.weaken (.bound 1) i.weaken.weaken c.weaken.weaken H.weaken.weaken)
          (.disj (implicationFormula C.weaken.weaken (.bound 1) i.weaken.weaken c.weaken.weaken H.weaken.weaken)
            (universalFormula C.weaken.weaken (.bound 1) (.bound 0) i.weaken.weaken H.weaken.weaken))))))

theorem evalFormula_delta0 {n : Nat} (C : Context (Project.Term n)) (i c H : Project.Term n) :
    (evalFormula C i c H).IsDelta0 :=
  .existsMem _ (.existsMem _ (.conj (codeFormula_delta0 _ _ _)
    (.disj (atomicFormula_delta0 _ _ _ _) (.disj (negationFormula_delta0 _ _ _ _ _)
      (.disj (implicationFormula_delta0 _ _ _ _ _) (universalFormula_delta0 _ _ _ _ _))))))

theorem evalFormula_iff {M : SetTheory.Structure.{u}} (he : Extensional M) {n : Nat}
    (env : Env M n) (C : Context (Project.Term n)) (i c H : Project.Term n) :
    Project.Formula.satisfies env (evalFormula C i c H) ↔
      EvalStep M (C.eval env) (i.eval env) (c.eval env) (H.eval env) := by
  simp only [evalFormula, Project.Formula.satisfies_existsMem_iff,
    Project.Formula.satisfies_conj_iff, Project.Formula.satisfies_disj_iff,
    codeFormula_iff he, atomicFormula_iff he, negationFormula_iff he,
    implicationFormula_iff he, universalFormula_iff he,
    Context.eval_weaken, Definitional.Term.eval_weaken]
  rfl

def parameterTerms : Context (Project.Term 16) :=
  ⟨.bound 3,.bound 4,.bound 5,.bound 6,.bound 7,.bound 8,.bound 9,
    .bound 10,.bound 11,.bound 12,.bound 13,.bound 14,.bound 15⟩

def contextEnv {M : SetTheory.Structure.{u}} (C : Context M.Domain) : Env M 13 where
  bound k := match k.val with
    | 0 => C.omega | 1 => C.carrier | 2 => C.operands | 3 => C.pairs
    | 4 => C.instructions | 5 => C.programs | 6 => C.assignments | 7 => C.columns
    | 8 => C.atomic | 9 => C.atomTag | 10 => C.negTag | 11 => C.impTag | _ => C.allTag
  free _ := C.omega

def evalMatrix : KP1Y.Recursion.StepMatrix 13 where
  body := evalFormula parameterTerms (.bound 2) (.bound 1) (.bound 0)
  freeClosed := by
    simp [evalFormula, atomicFormula, negationFormula, implicationFormula, universalFormula,
      instructionAtFormula, Assignments.updatedFormula, Functions.graphFormula,
      memPairFormula, codeFormula, pairFormula, Context.weaken, Context.map, parameterTerms,
      Project.Formula.forallMem, Project.Formula.existsMem, Definitional.Formula.FreeClosed]
  delta0 := evalFormula_delta0 _ _ _ _

theorem evalMatrix_iff {M : SetTheory.Structure.{u}} (he : Extensional M)
    (C : Context M.Domain) (i c H : M.Domain) :
    evalMatrix.denote (contextEnv C) i c H ↔ EvalStep M C i c H := by
  simp only [KP1Y.Recursion.StepMatrix.denote, evalMatrix, evalFormula_iff he]
  rfl

def Evaluation (M : SetTheory.Structure.{u}) (C : Context M.Domain) (H : M.Domain) : Prop :=
  KP1Y.Recursion.History M (EvalStep M C) H C.omega C.columns

def evaluationFormula {n : Nat} (C : Context (Project.Term n)) (H : Project.Term n) : Project.Formula 1 n :=
  .conj
    (Project.Formula.forallMem H (Project.Formula.existsMem C.omega.weaken
      (Project.Formula.existsMem C.columns.weaken.weaken (codeFormula (.bound 2) (.bound 1) (.bound 0)))))
    (Project.Formula.forallMem C.omega (Project.Formula.forallMem C.columns.weaken
      (.iff (memPairFormula H.weaken.weaken (.bound 1) (.bound 0))
        (evalFormula C.weaken.weaken (.bound 1) (.bound 0) H.weaken.weaken))))

theorem evaluationFormula_delta0 {n : Nat} (C : Context (Project.Term n)) (H : Project.Term n) :
    (evaluationFormula C H).IsDelta0 :=
  .conj (.forallMem _ (.existsMem _ (.existsMem _ (codeFormula_delta0 _ _ _))))
    (.forallMem _ (.forallMem _ (.iff (memPairFormula_delta0 _ _ _) (evalFormula_delta0 _ _ _ _))))

theorem evaluationFormula_iff {M : SetTheory.Structure.{u}} (he : Extensional M) {n : Nat}
    (env : Env M n) (C : Context (Project.Term n)) (H : Project.Term n) :
    Project.Formula.satisfies env (evaluationFormula C H) ↔ Evaluation M (C.eval env) (H.eval env) := by
  simp only [evaluationFormula, Project.Formula.satisfies_conj_iff,
    Project.Formula.satisfies_forallMem_iff, Project.Formula.satisfies_existsMem_iff,
    Project.Formula.satisfies_iff_iff, codeFormula_iff he, memPairFormula_iff he,
    evalFormula_iff he, Context.eval_weaken, Definitional.Term.eval_weaken]
  rfl

def rootParameters : Context (Project.Term 13) :=
  ⟨.bound 0,.bound 1,.bound 2,.bound 3,.bound 4,.bound 5,.bound 6,
    .bound 7,.bound 8,.bound 9,.bound 10,.bound 11,.bound 12⟩

def evaluationCore : Project.Formula 1 13 :=
  .imp (Project.Formula.isOmega rootParameters.omega)
    (.existsE (evaluationFormula rootParameters.weaken (.bound 0)))

def evaluationSentence : Project.Sentence :=
  Project.Sentence.forallClosure evaluationCore (by
    simp [evaluationCore, evaluationFormula, evalFormula, atomicFormula, negationFormula,
      implicationFormula, universalFormula, instructionAtFormula, Assignments.updatedFormula,
      Functions.graphFormula, memPairFormula, codeFormula, pairFormula,
      Context.weaken, Context.map, rootParameters, Project.Formula.isOmega,
      Project.Formula.isInductive, Project.Formula.isEmpty, Project.Formula.isSuccessor,
      Project.Formula.forallMem, Project.Formula.existsMem, Definitional.Formula.FreeClosed])

theorem evaluationCore_iff {M : SetTheory.Structure.{u}} (he : Extensional M) (env : Env M 13) :
    Project.Formula.satisfies env evaluationCore ↔
      (M.IsOmega (env.bound 0) → ∃ H, Evaluation M (rootParameters.eval env) H) := by
  simp only [evaluationCore, Project.Formula.satisfies_imp_iff,
    Project.Formula.satisfies_isOmega_iff, Project.Formula.satisfies_exists_iff,
    evaluationFormula_iff he, Context.eval_weaken]
  rfl

end KP1Y.Satisfaction
