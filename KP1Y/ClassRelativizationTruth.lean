import KP1Y.ClassRelativizationSyntax
import KP1Y.ClassBoundedTruth

/-! 一般（可含无界量词）公式的类相对化语义，包含自由环境与新binder的精确对应。 -/
namespace KP1Y.Classes
open YesMetaZFC YesMetaZFC.SetTheory YesMetaZFC.SetTheory.Definitional
universe u

theorem relativize_truth {M : SetTheory.Structure.{u}} {P : M.Domain → Prop} {hNe : ∃ x, P x}
    (hP : TransitiveClass M P) (χ : Project.UnarySchema 24) (params : Env M 24)
    (hχ : ∀ x, Project.Formula.satisfies (params.push x) χ.body ↔ P x)
    {n : Nat} (φ : Project.Formula 1 n) (s : Env (classModel M P hNe) n) :
    Project.Formula.satisfies s φ ↔ Project.Formula.satisfies (joinedEnv (forgetEnv s) params) (relativize χ φ) := by
  induction φ with
  | falsum => simp only [relativize,Project.Formula.satisfies_falsum_iff]
  | truth => simp only [relativize,Project.Formula.satisfies_truth_iff]
  | mem a b =>
      change Project.Formula.satisfies s (.mem a b) ↔
        Project.Formula.satisfies (joinedEnv (forgetEnv s) params) ((.mem a b : Project.Formula 1 _).rename frontIndex)
      rw [Project.Formula.satisfies_rename,joinedEnv_reindex_front]
      exact delta0_class_absolute hP (.mem a b) s
  | atom symbol hs args =>
      change Project.Formula.satisfies s (.atom symbol hs args) ↔
        Project.Formula.satisfies (joinedEnv (forgetEnv s) params)
          ((.atom symbol hs args : Project.Formula 1 _).rename frontIndex)
      rw [Project.Formula.satisfies_rename,joinedEnv_reindex_front]
      exact delta0_class_absolute hP (.atom symbol hs args) s
  | neg φ ih =>
      simp only [relativize,Project.Formula.satisfies_neg_iff]
      exact not_congr (ih s)
  | conj φ ψ ihφ ihψ =>
      simp only [relativize,Project.Formula.satisfies_conj_iff]
      exact and_congr (ihφ s) (ihψ s)
  | disj φ ψ ihφ ihψ =>
      simp only [relativize,Project.Formula.satisfies_disj_iff]
      exact or_congr (ihφ s) (ihψ s)
  | imp φ ψ ihφ ihψ =>
      simp only [relativize,Project.Formula.satisfies_imp_iff]
      exact imp_congr (ihφ s) (ihψ s)
  | iff φ ψ ihφ ihψ =>
      simp only [relativize,Project.Formula.satisfies_iff_iff]
      exact iff_congr (ihφ s) (ihψ s)
  | forallE φ ih =>
      simp only [relativize,Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_imp_iff,
        predicateSlots_iff,hχ]
      constructor
      · intro h x hx
        let a : (classModel M P hNe).Domain := ⟨x,hx⟩
        simpa only [forgetEnv_push,joinedEnv_push] using (ih (s.push a)).mp (h a)
      · intro h a
        apply (ih (s.push a)).mpr
        simpa only [forgetEnv_push,joinedEnv_push] using h a.val a.property
  | existsE φ ih =>
      simp only [relativize,Project.Formula.satisfies_exists_iff,Project.Formula.satisfies_conj_iff,
        predicateSlots_iff,hχ]
      constructor
      · rintro ⟨a,h⟩
        refine ⟨a.val,a.property,?_⟩
        simpa only [forgetEnv_push,joinedEnv_push] using (ih (s.push a)).mp h
      · rintro ⟨x,hx,h⟩
        let a : (classModel M P hNe).Domain := ⟨x,hx⟩
        refine ⟨a,(ih (s.push a)).mpr ?_⟩
        simpa only [forgetEnv_push,joinedEnv_push] using h

end KP1Y.Classes
