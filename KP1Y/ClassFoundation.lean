import KP1Y.OrdinalInduction

/-! 完整归纳给出任意公式类的最小元；不误用无界分离。 -/
namespace KP1Y
open YesMetaZFC YesMetaZFC.SetTheory YesMetaZFC.SetTheory.Definitional
universe u

def negateSchema {n : Nat} (φ : Project.UnarySchema n) : Project.UnarySchema n where
  body := .neg φ.body
  freeClosed := by simpa only [Definitional.Formula.FreeClosed] using φ.freeClosed

def classFoundationCore {n : Nat} (φ : Project.UnarySchema n) : Project.Formula 1 n :=
  .imp (.existsE φ.body) (.existsE (.conj φ.body
    (Project.Formula.forallMem (.bound 0) (.neg (φ.body.rename BoundEmbedding.unaryUnderOne)))))

def classFoundationSentence {n : Nat} (φ : Project.UnarySchema n) : Project.Sentence :=
  Project.Sentence.forallClosure (classFoundationCore φ) (by
    simp [classFoundationCore, Project.Formula.forallMem,
      Definitional.Formula.FreeClosed, φ.freeClosed])

theorem class_foundation_d {M : SetTheory.Structure.{u}} (hM : M.Models theory)
    {n : Nat} (φ : Project.UnarySchema n) (env : Env M n)
    (hne : ∃ x, Project.Formula.satisfies (env.push x) φ.body) :
    ∃ x, Project.Formula.satisfies (env.push x) φ.body ∧
      ∀ y, M.mem y x → ¬ Project.Formula.satisfies (env.push y) φ.body := by
  classical
  apply Classical.byContradiction
  intro hNoMin
  have hneg (x : M.Domain) : Project.Formula.satisfies (env.push x) (negateSchema φ).body ↔
      ¬ Project.Formula.satisfies (env.push x) φ.body :=
    Project.Formula.satisfies_neg_iff _ _
  have hall := induction_d hM (negateSchema φ) env (fun x ih => (hneg x).mpr (by
    intro hx
    exact hNoMin ⟨x,hx,fun y hy => (hneg y).mp (ih y hy)⟩))
  obtain ⟨x,hx⟩ := hne
  exact (hneg x).mp (hall x) hx

theorem classFoundationCore_iff {M : SetTheory.Structure.{u}} {n : Nat}
    (φ : Project.UnarySchema n) (env : Env M n) :
    Project.Formula.satisfies env (classFoundationCore φ) ↔
      ((∃ x, Project.Formula.satisfies (env.push x) φ.body) →
        ∃ x, Project.Formula.satisfies (env.push x) φ.body ∧
          ∀ y, M.mem y x → ¬Project.Formula.satisfies (env.push y) φ.body) := by
  simp only [classFoundationCore, Project.Formula.satisfies_imp_iff,
    Project.Formula.satisfies_exists_iff, Project.Formula.satisfies_conj_iff,
    Project.Formula.satisfies_forallMem_iff, Project.Formula.satisfies_neg_iff,
    Project.Formula.satisfies_rename, Env.reindex_push_unaryUnderOne]
  rfl

theorem class_foundation_derivable {n : Nat} (φ : Project.UnarySchema n) :
    Derives (classFoundationSentence φ) := by
  apply derives_of_all_models
  intro M hM free
  apply (Project.Formula.satisfies_forallClosure_iff free (classFoundationCore φ)).mpr
  intro bound
  exact (classFoundationCore_iff φ ⟨bound,free⟩).mpr (class_foundation_d hM φ ⟨bound,free⟩)

/-- 非空可定义序数类有真正的最小序数，不需要先形成整个类的集合。 -/
theorem least_ordinal_d {M : SetTheory.Structure.{u}} (hM : M.Models theory)
    {n : Nat} (φ : Project.UnarySchema n) (env : Env M n) {ν : M.Domain}
    (hOrd : ∀ x, Project.Formula.satisfies (env.push x) φ.body → M.IsOrdinal x)
    (hν : Project.Formula.satisfies (env.push ν) φ.body) :
    ∃ κ, Project.Formula.satisfies (env.push κ) φ.body ∧ M.IsOrdinal κ ∧
      (κ=ν ∨ M.mem κ ν) ∧
      ∀ α, Project.Formula.satisfies (env.push α) φ.body → (κ=α ∨ M.mem κ α) := by
  obtain ⟨κ,hκ,hmin⟩ := class_foundation_d hM φ env ⟨ν,hν⟩
  have hw := models_weakKP hM
  have least : ∀ α, Project.Formula.satisfies (env.push α) φ.body → (κ=α ∨ M.mem κ α) := by
    intro α hα
    rcases Structure.IsOrdinal.trichotomy hM.1 (hOrd κ hκ) (hOrd α hα)
      (SetTheory.KP.difference_exists_d hw) (SetTheory.KP.intersection_exists_d hw κ α) with
      he | hkα | hαk
    · exact Or.inl (hM.1.eq_of_same_members κ α he)
    · exact Or.inr hkα
    · exact False.elim (hmin α hαk hα)
  exact ⟨κ,hκ,hOrd κ hκ,least ν hν,least⟩

end KP1Y
