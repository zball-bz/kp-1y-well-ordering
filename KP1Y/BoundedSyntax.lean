import KP1Y.Axioms

/-! 有界公式在变量重命名下保持有界，不扩大分离／收集模式。 -/
namespace KP1Y
open YesMetaZFC YesMetaZFC.SetTheory YesMetaZFC.SetTheory.Definitional

private theorem liftRename {n m : Nat} (f : Fin n → Fin m) :
    Definitional.Term.liftSubstitution (Definitional.Term.bound ∘ f) =
      Definitional.Term.bound ∘ BoundEmbedding.lift f := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i <;> rfl

private theorem term_weaken_rename {n m : Nat} (f : Fin n → Fin m)
    (t : Project.Term n) :
    t.weaken.rename (BoundEmbedding.lift f) = (t.rename f).weaken := by
  cases t <;> rfl

/-- 仅重命名变量，不能把无界量词变为 Δ₀。 -/
theorem delta0_rename {n : Nat} {φ : Project.Formula 1 n} (h : φ.IsDelta0)
    {m : Nat} (f : Fin n → Fin m) : Project.Formula.IsDelta0 (φ.rename f) := by
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
      have he : (Project.Formula.forallMem t φ).rename f =
          Project.Formula.forallMem (t.rename f) (φ.rename (BoundEmbedding.lift f)) := by
        simp only [Project.Formula.forallMem, Definitional.Formula.rename,
          Definitional.Formula.bind, liftRename]
        change (.forallE (.imp (.mem (.bound 0) (t.weaken.rename (BoundEmbedding.lift f)))
          (φ.rename (BoundEmbedding.lift f))) : Project.Formula 1 m) = _
        rw [term_weaken_rename]
        rfl
      rw [he]
      exact .forallMem _ (ih _)
  | @existsMem n t φ h ih =>
      have he : (Project.Formula.existsMem t φ).rename f =
          Project.Formula.existsMem (t.rename f) (φ.rename (BoundEmbedding.lift f)) := by
        simp only [Project.Formula.existsMem, Definitional.Formula.rename,
          Definitional.Formula.bind, liftRename]
        change (.existsE (.conj (.mem (.bound 0) (t.weaken.rename (BoundEmbedding.lift f)))
          (φ.rename (BoundEmbedding.lift f))) : Project.Formula 1 m) = _
        rw [term_weaken_rename]
        rfl
      rw [he]
      exact .existsMem _ (ih _)

end KP1Y
