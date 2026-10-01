import KP1Y.UniformDerived

/-! 对共享语法的全部解释作对象全称量化；该包装有无界量词，不声称为 Δ₀。 -/
namespace KP1Y.Satisfaction
open YesMetaZFC YesMetaZFC.SetTheory YesMetaZFC.SetTheory.Definitional
universe u

def instanceContext {n : Nat} (C : Context (Project.Term n)) : Context (Project.Term (n+5)) :=
  C.weaken.weaken.weaken.weaken.weaken.withInterpretation (.bound 4) (.bound 3) (.bound 2) (.bound 1)

theorem instanceContext_eval {M : SetTheory.Structure.{u}} {n : Nat}
    (env : Env M n) (C : Context (Project.Term n)) (A S B At H : M.Domain) :
    (instanceContext C).eval (((((env.push A).push S).push B).push At).push H) =
      (C.eval env).withInterpretation A S B At := by
  simp only [instanceContext, Context.eval_withInterpretation, Context.eval_weaken]
  rfl

def allInstancesFormula {n : Nat} (C : Context (Project.Term n)) (body : Project.Formula 1 (n+5)) : Project.Formula 1 n :=
  .forallE (.forallE (.forallE (.forallE (.forallE
    (.imp (evaluationInstanceFormula C.weaken.weaken.weaken.weaken.weaken
      (.bound 4) (.bound 3) (.bound 2) (.bound 1) (.bound 0)) body)))))

theorem allInstancesFormula_iff {M : SetTheory.Structure.{u}} (he : Extensional M) {n : Nat}
    (env : Env M n) (C : Context (Project.Term n)) (body : Project.Formula 1 (n+5)) :
    Project.Formula.satisfies env (allInstancesFormula C body) ↔
      ∀ A S B At H, EvaluationInstance M (C.eval env) A S B At H →
        Project.Formula.satisfies (((((env.push A).push S).push B).push At).push H) body := by
  simp only [allInstancesFormula, Project.Formula.satisfies_forall_iff,
    Project.Formula.satisfies_imp_iff, evaluationInstanceFormula_iff he, Context.eval_weaken]
  rfl

end KP1Y.Satisfaction
