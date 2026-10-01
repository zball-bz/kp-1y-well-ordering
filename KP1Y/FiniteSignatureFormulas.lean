import KP1Y.BoundedSyntax

/-! 固定有限签名的元层有限析取。仅用于固定符号数，不将其当作内部ω长度编译。 -/
namespace KP1Y.Signature
open YesMetaZFC YesMetaZFC.SetTheory YesMetaZFC.SetTheory.Definitional
universe u

def finDisjunction {d : Nat} : {n : Nat} → (Fin n → Project.Formula 1 d) → Project.Formula 1 d
  | 0, _ => .falsum
  | _+1, fs => .disj (fs 0) (finDisjunction (fun i => fs i.succ))

theorem finDisjunction_delta0 {n d : Nat} (fs : Fin n → Project.Formula 1 d) (h : ∀ i, (fs i).IsDelta0) :
    (finDisjunction fs).IsDelta0 := by
  induction n with
  | zero => exact .falsum
  | succ n ih => exact .disj (h 0) (ih _ (fun i => h i.succ))

theorem finDisjunction_freeClosed {n d : Nat} (fs : Fin n → Project.Formula 1 d) (h : ∀ i, (fs i).FreeClosed) :
    (finDisjunction fs).FreeClosed := by
  induction n with
  | zero => simp [finDisjunction,Definitional.Formula.FreeClosed]
  | succ n ih =>
      simp only [finDisjunction,Definitional.Formula.FreeClosed]
      exact ⟨h 0,ih _ (fun i => h i.succ)⟩

theorem finDisjunction_iff {M : SetTheory.Structure.{u}} {n d : Nat} (e : Env M d) (fs : Fin n → Project.Formula 1 d) :
    Project.Formula.satisfies e (finDisjunction fs) ↔ ∃ i, Project.Formula.satisfies e (fs i) := by
  induction n with
  | zero =>
      simp only [finDisjunction,Project.Formula.satisfies_falsum_iff]
      exact ⟨False.elim,fun ⟨i,_⟩ => Fin.elim0 i⟩
  | succ n ih =>
      rw [finDisjunction,Project.Formula.satisfies_disj_iff,ih]
      constructor
      · rintro (h | ⟨i,h⟩)
        · exact ⟨0,h⟩
        · exact ⟨i.succ,h⟩
      · rintro ⟨i,h⟩
        exact Fin.cases (fun h => Or.inl h) (fun i h => Or.inr ⟨i,h⟩) i h

def finConjunction {d : Nat} : {n : Nat} → (Fin n → Project.Formula 1 d) → Project.Formula 1 d
  | 0, _ => .truth
  | _+1, fs => .conj (fs 0) (finConjunction (fun i => fs i.succ))

theorem finConjunction_delta0 {n d : Nat} (fs : Fin n → Project.Formula 1 d) (h : ∀ i, (fs i).IsDelta0) :
    (finConjunction fs).IsDelta0 := by
  induction n with
  | zero => exact .truth
  | succ n ih => exact .conj (h 0) (ih _ (fun i => h i.succ))

theorem finConjunction_freeClosed {n d : Nat} (fs : Fin n → Project.Formula 1 d) (h : ∀ i, (fs i).FreeClosed) :
    (finConjunction fs).FreeClosed := by
  induction n with
  | zero => simp [finConjunction,Definitional.Formula.FreeClosed]
  | succ n ih =>
      simp only [finConjunction,Definitional.Formula.FreeClosed]
      exact ⟨h 0,ih _ (fun i => h i.succ)⟩

theorem finConjunction_iff {M : SetTheory.Structure.{u}} {n d : Nat} (e : Env M d) (fs : Fin n → Project.Formula 1 d) :
    Project.Formula.satisfies e (finConjunction fs) ↔ ∀ i, Project.Formula.satisfies e (fs i) := by
  induction n with
  | zero =>
      simp only [finConjunction,Project.Formula.satisfies_truth_iff]
      exact ⟨fun _ i => Fin.elim0 i,fun _ => trivial⟩
  | succ n ih =>
      rw [finConjunction,Project.Formula.satisfies_conj_iff,ih]
      exact ⟨fun h i => Fin.cases h.1 h.2 i,fun h => ⟨h 0,fun i => h i.succ⟩⟩

end KP1Y.Signature
