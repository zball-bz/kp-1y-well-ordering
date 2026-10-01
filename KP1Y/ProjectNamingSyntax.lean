import KP1Y.NamedFormula

/-! 将自由闭合的普通集合公式转成有限命名公式，量词和subset展开均分配新名字。 -/
namespace KP1Y.Named
open YesMetaZFC YesMetaZFC.SetTheory YesMetaZFC.SetTheory.Definitional

def termIndex {n k : Nat} (fallback : Fin k) (ρ : Fin n → Fin k) : Project.Term n → Fin k
  | .bound i => ρ i
  | .free _ => fallback

def extraDepth : {n : Nat} → Project.Formula 1 n → Nat
  | _, .falsum => 0
  | _, .truth => 0
  | _, .mem _ _ => 0
  | _, .atom .extensionalEq _ _ => 0
  | _, .atom .subset _ _ => 1
  | _, .neg φ => extraDepth φ
  | _, .conj φ ψ => max (extraDepth φ) (extraDepth ψ)
  | _, .disj φ ψ => max (extraDepth φ) (extraDepth ψ)
  | _, .imp φ ψ => max (extraDepth φ) (extraDepth ψ)
  | _, .iff φ ψ => max (extraDepth φ) (extraDepth ψ)
  | _, .forallE φ => 1+extraDepth φ
  | _, .existsE φ => 1+extraDepth φ

def encode {k : Nat} (fallback : Fin k) : {n : Nat} → (φ : Project.Formula 1 n) → (Fin n → Fin k) →
    (fresh : Nat) → fresh+extraDepth φ≤k → Formula k
  | _, .falsum, _, _, _ => .falsum fallback
  | _, .truth, _, _, _ => .truth fallback
  | _, .mem a b, ρ, _, _ => .member (termIndex fallback ρ a) (termIndex fallback ρ b)
  | _, .atom .extensionalEq _ args, ρ, _, _ => .equal (termIndex fallback ρ (args 0)) (termIndex fallback ρ (args 1))
  | _, .atom .subset _ args, ρ, fresh, h =>
      let v : Fin k := ⟨fresh,by simp only [extraDepth] at h; omega⟩
      .all v (.imp (.member v (termIndex fallback ρ (args 0))) (.member v (termIndex fallback ρ (args 1))))
  | _, .neg φ, ρ, fresh, h => .neg (encode fallback φ ρ fresh h)
  | _, .conj φ ψ, ρ, fresh, h =>
      .conj (encode fallback φ ρ fresh (by simp only [extraDepth] at h; omega))
        (encode fallback ψ ρ fresh (by simp only [extraDepth] at h; omega))
  | _, .disj φ ψ, ρ, fresh, h =>
      .disj (encode fallback φ ρ fresh (by simp only [extraDepth] at h; omega))
        (encode fallback ψ ρ fresh (by simp only [extraDepth] at h; omega))
  | _, .imp φ ψ, ρ, fresh, h =>
      .imp (encode fallback φ ρ fresh (by simp only [extraDepth] at h; omega))
        (encode fallback ψ ρ fresh (by simp only [extraDepth] at h; omega))
  | _, .iff φ ψ, ρ, fresh, h =>
      .iff (encode fallback φ ρ fresh (by simp only [extraDepth] at h; omega))
        (encode fallback ψ ρ fresh (by simp only [extraDepth] at h; omega))
  | _, .forallE φ, ρ, fresh, h =>
      let v : Fin k := ⟨fresh,by simp only [extraDepth] at h; omega⟩
      .all v (encode fallback φ (Fin.cases v ρ) (fresh+1) (by simp only [extraDepth] at h; omega))
  | _, .existsE φ, ρ, fresh, h =>
      let v : Fin k := ⟨fresh,by simp only [extraDepth] at h; omega⟩
      .exists v (encode fallback φ (Fin.cases v ρ) (fresh+1) (by simp only [extraDepth] at h; omega))

theorem termIndex_lt {n k : Nat} (fallback : Fin k) (ρ : Fin n → Fin k) {fresh : Nat}
    (hρ : ∀ i, (ρ i).val<fresh) (t : Project.Term n) (hClosed : t.freeSupport=[]) :
    (termIndex fallback ρ t).val<fresh := by
  cases t with
  | bound i => exact hρ i
  | free i => simp at hClosed

theorem extended_names_bounded {n k : Nat} {ρ : Fin n → Fin k} {fresh : Nat}
    (hρ : ∀ i, (ρ i).val<fresh) (v : Fin k) (hv : v.val=fresh) :
    ∀ i : Fin (n+1), (Fin.cases v ρ i : Fin k).val<fresh+1 := by
  intro i
  refine Fin.cases ?_ (fun i => ?_) i
  · simp only [Fin.cases_zero]
    omega
  · simp only [Fin.cases_succ]
    have hi := hρ i
    omega

theorem old_name_ne_fresh {n k : Nat} {ρ : Fin n → Fin k} {fresh : Nat}
    (hρ : ∀ i, (ρ i).val<fresh) (v : Fin k) (hv : v.val=fresh) (i : Fin n) : ρ i≠v := by
  intro he
  have hi := hρ i
  have heVal := congrArg Fin.val he
  omega

end KP1Y.Named
