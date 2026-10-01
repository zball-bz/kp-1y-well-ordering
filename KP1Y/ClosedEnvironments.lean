import KP1Y.BoundedSyntax

/-! 自由闭合的对象公式仅依赖bound参数，允许自由环境不同。 -/
namespace KP1Y
open YesMetaZFC YesMetaZFC.SetTheory YesMetaZFC.SetTheory.Definitional
universe u

theorem term_bound_congr {M : SetTheory.Structure.{u}} {n : Nat} (s t : Env M n)
    (hBound : ∀ i, s.bound i=t.bound i) (a : Project.Term n) (hClosed : a.freeSupport=[]) : a.eval s=a.eval t := by
  cases a with
  | bound i => exact hBound i
  | free i => simp at hClosed

theorem formula_bound_congr {M : SetTheory.Structure.{u}} {n : Nat} (φ : Project.Formula 1 n)
    (hClosed : φ.FreeClosed) (s t : Env M n) (hBound : ∀ i, s.bound i=t.bound i) :
    Project.Formula.satisfies s φ ↔ Project.Formula.satisfies t φ := by
  induction φ with
  | falsum => simp only [Project.Formula.satisfies_falsum_iff]
  | truth => simp only [Project.Formula.satisfies_truth_iff]
  | mem a b =>
      simp only [Definitional.Formula.FreeClosed] at hClosed
      simp only [Project.Formula.satisfies_mem_iff,term_bound_congr s t hBound a hClosed.1,
        term_bound_congr s t hBound b hClosed.2]
  | atom symbol hs args =>
      simp only [Definitional.Formula.FreeClosed] at hClosed
      have h0 := term_bound_congr s t hBound (args 0) (hClosed 0)
      have h1 := term_bound_congr s t hBound (args 1) (hClosed 1)
      cases symbol with
      | extensionalEq => simp only [Project.Formula.satisfies_atom_extensionalEq_iff,h0,h1]
      | subset => simp only [Project.Formula.satisfies_atom_subset_iff,h0,h1]
  | neg φ ih =>
      simp only [Definitional.Formula.FreeClosed] at hClosed
      simp only [Project.Formula.satisfies_neg_iff]
      exact not_congr (ih hClosed s t hBound)
  | conj φ ψ ihφ ihψ =>
      simp only [Definitional.Formula.FreeClosed] at hClosed
      simp only [Project.Formula.satisfies_conj_iff]
      exact and_congr (ihφ hClosed.1 s t hBound) (ihψ hClosed.2 s t hBound)
  | disj φ ψ ihφ ihψ =>
      simp only [Definitional.Formula.FreeClosed] at hClosed
      simp only [Project.Formula.satisfies_disj_iff]
      exact or_congr (ihφ hClosed.1 s t hBound) (ihψ hClosed.2 s t hBound)
  | imp φ ψ ihφ ihψ =>
      simp only [Definitional.Formula.FreeClosed] at hClosed
      simp only [Project.Formula.satisfies_imp_iff]
      exact imp_congr (ihφ hClosed.1 s t hBound) (ihψ hClosed.2 s t hBound)
  | iff φ ψ ihφ ihψ =>
      simp only [Definitional.Formula.FreeClosed] at hClosed
      simp only [Project.Formula.satisfies_iff_iff]
      exact iff_congr (ihφ hClosed.1 s t hBound) (ihψ hClosed.2 s t hBound)
  | forallE φ ih =>
      simp only [Definitional.Formula.FreeClosed] at hClosed
      simp only [Project.Formula.satisfies_forall_iff]
      apply forall_congr'
      intro x
      apply ih hClosed (s.push x) (t.push x)
      intro i
      exact Fin.cases rfl (fun i => hBound i) i
  | existsE φ ih =>
      simp only [Definitional.Formula.FreeClosed] at hClosed
      simp only [Project.Formula.satisfies_exists_iff]
      apply exists_congr
      intro x
      apply ih hClosed (s.push x) (t.push x)
      intro i
      exact Fin.cases rfl (fun i => hBound i) i

end KP1Y
