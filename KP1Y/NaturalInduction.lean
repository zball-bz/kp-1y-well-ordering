import KP1Y.NaturalNumbers

/-! 模型内部自然数上的全部对象公式归纳；不以宿主 Nat.rec 替代。 -/
namespace KP1Y.Naturals
open YesMetaZFC YesMetaZFC.SetTheory YesMetaZFC.SetTheory.Definitional
universe u

def guardSlots {n : Nat} : Fin (n+1) → Fin (n+2) :=
  Fin.cases 0 (fun i => ⟨i.val+2,by omega⟩)

def naturalGuard {n : Nat} (φ : Project.UnarySchema n) : Project.UnarySchema (n+1) where
  body := .imp (.mem (.bound 0) (.bound 1)) (φ.body.rename guardSlots)
  freeClosed := by simp [Definitional.Formula.FreeClosed, φ.freeClosed]

private theorem guardSlots_env {M : SetTheory.Structure.{u}} {n : Nat}
    (env : Env M n) (ω x : M.Domain) :
    ((env.push ω).push x).reindex guardSlots = env.push x := by
  rw [Env.mk.injEq]
  constructor
  · funext i
    refine Fin.cases ?_ (fun i => ?_) i <;> rfl
  · rfl

theorem naturalGuard_iff {M : SetTheory.Structure.{u}} {n : Nat}
    (φ : Project.UnarySchema n) (env : Env M n) (ω x : M.Domain) :
    Project.Formula.satisfies ((env.push ω).push x) (naturalGuard φ).body ↔
      (M.mem x ω → Project.Formula.satisfies (env.push x) φ.body) := by
  simp only [naturalGuard, Project.Formula.satisfies_imp_iff, Project.Formula.satisfies_mem_iff,
    Project.Formula.satisfies_rename, guardSlots_env]
  rfl

theorem natural_induction_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {n : Nat} (φ : Project.UnarySchema n) (env : Env M n) {ω : M.Domain} (hω : M.IsOmega ω)
    (hEmpty : ∀ e, (∀ x, ¬M.mem x e) → Project.Formula.satisfies (env.push e) φ.body)
    (hSucc : ∀ p, M.mem p ω → Project.Formula.satisfies (env.push p) φ.body →
      ∀ s, M.SuccessorOf s p → Project.Formula.satisfies (env.push s) φ.body) :
    ∀ x, M.mem x ω → Project.Formula.satisfies (env.push x) φ.body := by
  have hAll := KP1Y.induction_d hM (naturalGuard φ) (env.push ω) (fun x ih =>
    (naturalGuard_iff φ env ω x).mpr (by
      intro hx
      rcases natural_cases hM hω hx with he | ⟨p,hp,hs⟩
      · exact hEmpty x he
      · exact hSucc p hp ((naturalGuard_iff φ env ω p).mp (ih p hs.predecessor_mem) hp) x hs))
  exact fun x => (naturalGuard_iff φ env ω x).mp (hAll x)

end KP1Y.Naturals
