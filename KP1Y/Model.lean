import KP1Y.Axioms
import YesMetaZFC.SetTheory.Foundation

/-! 任意（也可非标准、外部非良基）KPω 模型中的归纳与基础。 -/
namespace KP1Y
open YesMetaZFC YesMetaZFC.SetTheory YesMetaZFC.SetTheory.Definitional
universe u

/-- 归纳模式的实际语义；这里没有假定宿主层面的 `WellFounded ℳ.mem`。 -/
theorem inductionCore_iff {ℳ : SetTheory.Structure.{u}} {n : Nat}
    (φ : Project.UnarySchema n) (env : Env ℳ n) :
    Project.Formula.satisfies env (inductionCore φ) ↔
      ((∀ x, (∀ y, ℳ.mem y x → Project.Formula.satisfies (env.push y) φ.body) →
        Project.Formula.satisfies (env.push x) φ.body) →
        ∀ x, Project.Formula.satisfies (env.push x) φ.body) := by
  simp only [inductionCore, Project.Formula.satisfies_imp_iff,
    Project.Formula.satisfies_forall_iff, Project.Formula.satisfies_forallMem_iff,
    Project.Formula.satisfies_rename, Env.reindex_push_unaryUnderOne]
  rfl

/-- 从对象理论的完整集合归纳公理实例取得可用的模式归纳。 -/
theorem induction_d {ℳ : SetTheory.Structure.{u}} (hKP : ℳ.Models theory)
    {n : Nat} (φ : Project.UnarySchema n) (env : Env ℳ n)
    (step : ∀ x, (∀ y, ℳ.mem y x → Project.Formula.satisfies (env.push y) φ.body) →
      Project.Formula.satisfies (env.push x) φ.body) :
    ∀ x, Project.Formula.satisfies (env.push x) φ.body := by
  have h := hKP.2 (inductionSentence φ) (.setInduction φ) env.free
  have hc := (Project.Formula.satisfies_forallClosure_iff env.free (inductionCore φ)).mp h
  exact (inductionCore_iff φ env).mp (hc env.bound) step

/-- x 不属于参数集合；用于从类归纳推出集合基础。 -/
def outsideSchema : Project.UnarySchema 1 where
  body := .neg (.mem (.bound 0) (.bound 1))
  freeClosed := by simp [Definitional.Formula.FreeClosed]

/-- 单条 Foundation 是文稿 KPω 的定理，而非附加公理。 -/
theorem foundation_d {ℳ : SetTheory.Structure.{u}} (hKP : ℳ.Models theory)
    (a : ℳ.Domain) (hne : ∃ x, ℳ.mem x a) :
    ∃ x, ℳ.mem x a ∧ ∀ y, ℳ.mem y a → ¬ℳ.mem y x := by
  classical
  apply Classical.byContradiction
  intro hnone
  let env : Env ℳ 1 := ⟨fun _ => a, fun _ => a⟩
  have hout (x : ℳ.Domain) :
      Project.Formula.satisfies (env.push x) outsideSchema.body ↔ ¬ℳ.mem x a := by
    simp only [outsideSchema, Project.Formula.satisfies_neg_iff,
      Project.Formula.satisfies_mem_iff, Definitional.Term.eval, Env.push, env,
      Fin.cases_zero]
    rfl
  have allOutside : ∀ x, ¬ℳ.mem x a := by
    have hi := induction_d hKP outsideSchema env (fun x ih => (hout x).mpr (by
      intro hxa
      apply hnone
      refine ⟨x, hxa, ?_⟩
      intro y hya hyx
      exact (hout y).mp (ih y hyx) hya))
    exact fun x => (hout x).mp (hi x)
  obtain ⟨x, hx⟩ := hne
  exact allOutside x hx

/-- 所有旧弱 KP 引理可安全复用；完整归纳额外由新理论明确提供。 -/
theorem models_weakKP {ℳ : SetTheory.Structure.{u}} (hKP : ℳ.Models theory) :
    ℳ.Models SetTheory.KP := by
  refine ⟨hKP.1, ?_⟩
  intro sentence h
  cases h with
  | extensionality => exact hKP.2 _ .extensionality
  | emptySet => exact hKP.2 _ .emptySet
  | pairing => exact hKP.2 _ .pairing
  | union => exact hKP.2 _ .union
  | infinity => exact hKP.2 _ .infinity
  | separation φ => exact hKP.2 _ (.separation φ)
  | collection φ => exact hKP.2 _ (.collection φ)
  | foundation =>
      intro free
      exact (Axioms.foundation_sat_iff_d free).mpr (foundation_d hKP)

end KP1Y
