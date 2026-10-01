import KP1Y.ConstructibleModel
import KP1Y.DefinableClassInduction

/-! 构造类满足每个真正的完整集合归纳公理实例，而不仅是单条Foundation。 -/
namespace KP1Y.Constructible
open YesMetaZFC YesMetaZFC.SetTheory YesMetaZFC.SetTheory.Definitional
open KP1Y.Classes KP1Y.SetLanguage
universe u

theorem inner_induction_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    (env : Env M 24) (hS : FixedSyntax M (defContext.eval env) (defData.eval env)
      (env.bound 0) (env.bound 1) (env.bound 2)) {n : Nat} (φ : Project.UnarySchema n)
    (s : Env (innerModel hM env hS) n)
    (step : ∀ x, (∀ y, (innerModel hM env hS).mem y x → Project.Formula.satisfies (s.push y) φ.body) →
      Project.Formula.satisfies (s.push x) φ.body) :
    ∀ x, Project.Formula.satisfies (s.push x) φ.body :=
  definable_class_induction_d hM (constructible_transitive_class_d hM env hS)
    constructibleSchema env (constructibleSchema_iff hM env) φ s step

theorem inner_setInduction_axiom_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    (env : Env M 24) (hS : FixedSyntax M (defContext.eval env) (defData.eval env)
      (env.bound 0) (env.bound 1) (env.bound 2)) {n : Nat} (φ : Project.UnarySchema n)
    (free : FreeVarId → (innerModel hM env hS).Domain) :
    Project.Formula.satisfies ({bound := Fin.elim0,free := free} : Env (innerModel hM env hS) 0)
      (KP1Y.inductionSentence φ).formula :=
  definable_class_induction_sentence_d hM (constructible_transitive_class_d hM env hS)
    constructibleSchema env (constructibleSchema_iff hM env) φ free

end KP1Y.Constructible
