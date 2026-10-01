import KP1Y.BoundedSyntax

/-! 对象项替换保持字面Δ₀分类，供已有证书的参数化实例使用。 -/
namespace KP1Y
open YesMetaZFC YesMetaZFC.SetTheory YesMetaZFC.SetTheory.Definitional

theorem term_weaken_bind {n m : Nat} (t : Project.Term n) (f : Fin n → Project.Term m) :
    t.weaken.bind (Definitional.Term.liftSubstitution f) = (t.bind f).weaken := by
  cases t <;> rfl

theorem delta0_bind {n : Nat} {φ : Project.Formula 1 n} (h : φ.IsDelta0)
    {m : Nat} (f : Fin n → Project.Term m) : Project.Formula.IsDelta0 (φ.bind f) := by
  induction h generalizing m with
  | falsum => exact .falsum
  | truth => exact .truth
  | mem a b => exact .mem _ _
  | atom s hs args => exact .atom s hs _
  | neg h ih => exact .neg (ih f)
  | conj h1 h2 ih1 ih2 => exact .conj (ih1 f) (ih2 f)
  | disj h1 h2 ih1 ih2 => exact .disj (ih1 f) (ih2 f)
  | imp h1 h2 ih1 ih2 => exact .imp (ih1 f) (ih2 f)
  | iff h1 h2 ih1 ih2 => exact .iff (ih1 f) (ih2 f)
  | @forallMem n t φ h ih =>
      have he : (Project.Formula.forallMem t φ).bind f =
          Project.Formula.forallMem (t.bind f) (φ.bind (Definitional.Term.liftSubstitution f)) := by
        simp only [Project.Formula.forallMem,Definitional.Formula.bind,term_weaken_bind]
        rfl
      rw [he]
      exact .forallMem _ (ih _)
  | @existsMem n t φ h ih =>
      have he : (Project.Formula.existsMem t φ).bind f =
          Project.Formula.existsMem (t.bind f) (φ.bind (Definitional.Term.liftSubstitution f)) := by
        simp only [Project.Formula.existsMem,Definitional.Formula.bind,term_weaken_bind]
        rfl
      rw [he]
      exact .existsMem _ (ih _)

end KP1Y
