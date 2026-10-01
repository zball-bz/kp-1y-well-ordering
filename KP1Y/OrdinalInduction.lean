import KP1Y.Completeness
import YesMetaZFC.SetTheory.Ord.Induction

/-! 复用既有序数定义和语义桥，从新的完整集合归纳推出全部公式的序数归纳。 -/
namespace KP1Y
open YesMetaZFC YesMetaZFC.SetTheory YesMetaZFC.SetTheory.Definitional
universe u

def ordinalGuard {n : Nat} (φ : Project.UnarySchema n) : Project.UnarySchema n where
  body := .imp (Project.Formula.isOrdinal (.bound 0)) φ.body
  freeClosed := by
    simp [Project.Formula.isOrdinal, Project.Formula.isTransitive,
      Project.Formula.isWellOrderOn, Project.Formula.isLinearOrderOn,
      Project.Formula.isStrictPartialOrderOn, Project.Formula.isIrreflexiveOn,
      Project.Formula.isTransitiveOn, Project.Formula.isLeastOf,
      Project.Formula.lessOrEqual, Project.Formula.forallMem, Project.Formula.existsMem,
      Project.Formula.subset, Project.Formula.extensionalEq,
      Definitional.Formula.FreeClosed, φ.freeClosed]

theorem ordinalGuard_iff {ℳ : SetTheory.Structure.{u}} {n : Nat}
    (φ : Project.UnarySchema n) (env : Env ℳ n) (x : ℳ.Domain) :
    Project.Formula.satisfies (env.push x) (ordinalGuard φ).body ↔
      (ℳ.IsOrdinal x → Project.Formula.satisfies (env.push x) φ.body) := by
  simp only [ordinalGuard, Project.Formula.satisfies_imp_iff,
    Project.Formula.satisfies_isOrdinal_iff]
  rfl

/-- 在任意模型的内部序数上归纳；不用外部序数或外部良基性。 -/
theorem ordinal_induction_d {ℳ : SetTheory.Structure.{u}} (hKP : ℳ.Models theory)
    {n : Nat} (φ : Project.UnarySchema n) (env : Env ℳ n)
    (step : ∀ x, ℳ.IsOrdinal x →
      (∀ y, ℳ.mem y x → Project.Formula.satisfies (env.push y) φ.body) →
        Project.Formula.satisfies (env.push x) φ.body) :
    ∀ x, ℳ.IsOrdinal x → Project.Formula.satisfies (env.push x) φ.body := by
  have h := induction_d hKP (ordinalGuard φ) env (fun x ih =>
    (ordinalGuard_iff φ env x).mpr (fun hx => step x hx (fun y hy =>
      (ordinalGuard_iff φ env y).mp (ih y hy) (hx.mem hy))))
  exact fun x => (ordinalGuard_iff φ env x).mp (h x)

/-- 原库只在 ZF 全分离下提供的完整模式，现在由 KPω 的集合归纳取得。 -/
theorem ordinal_induction_derivable {n : Nat} (φ : Project.UnarySchema n) :
    Derives φ.inductionSentence := by
  apply derives_of_all_models
  intro M hM free
  apply (Project.Formula.satisfies_forallClosure_iff free
    (.imp φ.progressiveCore φ.inductionCore)).mpr
  intro bound
  let env : Env M n := ⟨bound,free⟩
  apply (Project.Formula.satisfies_imp_iff _ _ _).mpr
  intro hs
  apply (Project.UnarySchema.satisfies_inductionCore_iff env φ).mpr
  exact ordinal_induction_d hM φ env
    ((Project.UnarySchema.satisfies_progressiveCore_iff env φ).mp hs)

end KP1Y
