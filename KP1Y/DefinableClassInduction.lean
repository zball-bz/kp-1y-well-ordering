import KP1Y.ClassRelativizationTruth
import KP1Y.Model

/-! 可定义传递类继承完整集合归纳：实际构造并调用原KPω中的相对化归纳模式。 -/
namespace KP1Y.Classes
open YesMetaZFC YesMetaZFC.SetTheory YesMetaZFC.SetTheory.Definitional
universe u

def guardedRelativizationSchema {n : Nat} (χ : Project.UnarySchema 24) (φ : Project.UnarySchema n) :
    Project.UnarySchema (n+24) where
  body := .imp (χ.body.rename (predicateSlots (n := n))) (relativize χ φ.body)
  freeClosed := by
    simp only [Definitional.Formula.FreeClosed,Definitional.Formula.freeClosed_rename]
    exact ⟨χ.freeClosed,(relativize_freeClosed χ φ.body).mpr φ.freeClosed⟩

theorem guardedRelativizationSchema_iff {M : SetTheory.Structure.{u}} {P : M.Domain → Prop} {hNe : ∃ x, P x}
    (hP : TransitiveClass M P) (χ : Project.UnarySchema 24) (params : Env M 24)
    (hχ : ∀ x, Project.Formula.satisfies (params.push x) χ.body ↔ P x)
    {n : Nat} (φ : Project.UnarySchema n) (s : Env (classModel M P hNe) n) (x : M.Domain) :
    Project.Formula.satisfies ((joinedEnv (forgetEnv s) params).push x) (guardedRelativizationSchema χ φ).body ↔
      ∀ hx : P x, Project.Formula.satisfies (s.push ⟨x,hx⟩) φ.body := by
  simp only [guardedRelativizationSchema,Project.Formula.satisfies_imp_iff,predicateSlots_iff,hχ]
  constructor
  · intro h hx
    let a : (classModel M P hNe).Domain := ⟨x,hx⟩
    have hEnv := (congrArg (fun e => joinedEnv e params) (forgetEnv_push s a)).trans
      (joinedEnv_push (forgetEnv s) params x)
    apply (relativize_truth hP χ params hχ φ.body (s.push a)).mpr
    rw [hEnv]
    exact h hx
  · intro h hx
    let a : (classModel M P hNe).Domain := ⟨x,hx⟩
    have hEnv := (congrArg (fun e => joinedEnv e params) (forgetEnv_push s a)).trans
      (joinedEnv_push (forgetEnv s) params x)
    have hRel := (relativize_truth hP χ params hχ φ.body (s.push a)).mp (h hx)
    exact hEnv ▸ hRel

theorem definable_class_induction_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {P : M.Domain → Prop} {hNe : ∃ x, P x} (hP : TransitiveClass M P)
    (χ : Project.UnarySchema 24) (params : Env M 24)
    (hχ : ∀ x, Project.Formula.satisfies (params.push x) χ.body ↔ P x)
    {n : Nat} (φ : Project.UnarySchema n) (s : Env (classModel M P hNe) n)
    (step : ∀ x, (∀ y, (classModel M P hNe).mem y x → Project.Formula.satisfies (s.push y) φ.body) →
      Project.Formula.satisfies (s.push x) φ.body) :
    ∀ x, Project.Formula.satisfies (s.push x) φ.body := by
  have hAll := KP1Y.induction_d hM (guardedRelativizationSchema χ φ) (joinedEnv (forgetEnv s) params) (by
    intro x ih
    apply (guardedRelativizationSchema_iff hP χ params hχ φ s x).mpr
    intro hx
    apply step ⟨x,hx⟩
    intro y hy
    exact (guardedRelativizationSchema_iff hP χ params hχ φ s y.val).mp (ih y.val hy) y.property)
  intro x
  exact (guardedRelativizationSchema_iff hP χ params hχ φ s x.val).mp (hAll x.val) x.property

theorem definable_class_induction_sentence_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {P : M.Domain → Prop} {hNe : ∃ x, P x} (hP : TransitiveClass M P)
    (χ : Project.UnarySchema 24) (params : Env M 24)
    (hχ : ∀ x, Project.Formula.satisfies (params.push x) χ.body ↔ P x)
    {n : Nat} (φ : Project.UnarySchema n) (free : FreeVarId → (classModel M P hNe).Domain) :
    Project.Formula.satisfies ({bound := Fin.elim0,free := free} : Env (classModel M P hNe) 0)
      (KP1Y.inductionSentence φ).formula := by
  apply (Project.Formula.satisfies_forallClosure_iff free (KP1Y.inductionCore φ)).mpr
  intro bound
  let s : Env (classModel M P hNe) n := ⟨bound,free⟩
  apply (KP1Y.inductionCore_iff φ s).mpr
  exact definable_class_induction_d hM hP χ params hχ φ s

end KP1Y.Classes
