import KP1Y.ClassFoundation
import KP1Y.RelationComprehension

/-! 有界满射图与不可数序数的实际对象语言定义。 -/
namespace KP1Y.Cardinal
open YesMetaZFC YesMetaZFC.SetTheory YesMetaZFC.SetTheory.Definitional
open KP1Y.Kuratowski
universe u

def Onto (M : SetTheory.Structure.{u}) (f X Y : M.Domain) : Prop :=
  (∀ p, M.mem p f → ∃ x, M.mem x X ∧ ∃ y, M.mem y Y ∧ Codes M p x y) ∧
  (∀ x, M.mem x X → ∃ y, M.mem y Y ∧ MemPair M f x y) ∧
  (∀ x, M.mem x X → ∀ y, M.mem y Y → ∀ z, M.mem z Y →
    MemPair M f x y → MemPair M f x z → y=z) ∧
  (∀ y, M.mem y Y → ∃ x, M.mem x X ∧ MemPair M f x y)

def ontoFormula {n : Nat} (f X Y : Project.Term n) : Project.Formula 1 n :=
  .conj
    (Project.Formula.forallMem f (Project.Formula.existsMem X.weaken
      (Project.Formula.existsMem Y.weaken.weaken (codeFormula (.bound 2) (.bound 1) (.bound 0)))))
    (.conj
      (Project.Formula.forallMem X (Project.Formula.existsMem Y.weaken
        (memPairFormula f.weaken.weaken (.bound 1) (.bound 0))))
      (.conj
        (Project.Formula.forallMem X (Project.Formula.forallMem Y.weaken
          (Project.Formula.forallMem Y.weaken.weaken
            (.imp (.conj (memPairFormula f.weaken.weaken.weaken (.bound 2) (.bound 1))
              (memPairFormula f.weaken.weaken.weaken (.bound 2) (.bound 0)))
              (Project.Formula.extensionalEq (.bound 1) (.bound 0))))))
        (Project.Formula.forallMem Y (Project.Formula.existsMem X.weaken
          (memPairFormula f.weaken.weaken (.bound 0) (.bound 1))))))

theorem ontoFormula_delta0 {n : Nat} (f X Y : Project.Term n) : (ontoFormula f X Y).IsDelta0 :=
  .conj (.forallMem _ (.existsMem _ (.existsMem _ (codeFormula_delta0 _ _ _))))
    (.conj (.forallMem _ (.existsMem _ (memPairFormula_delta0 _ _ _)))
      (.conj (.forallMem _ (.forallMem _ (.forallMem _
        (.imp (.conj (memPairFormula_delta0 _ _ _) (memPairFormula_delta0 _ _ _)) (.atom _ _ _)))))
        (.forallMem _ (.existsMem _ (memPairFormula_delta0 _ _ _)))))

theorem ontoFormula_iff {M : SetTheory.Structure.{u}} (he : Extensional M) {n : Nat}
    (env : Env M n) (f X Y : Project.Term n) :
    Project.Formula.satisfies env (ontoFormula f X Y) ↔ Onto M (f.eval env) (X.eval env) (Y.eval env) := by
  simp only [ontoFormula, Project.Formula.satisfies_conj_iff,
    Project.Formula.satisfies_forallMem_iff, Project.Formula.satisfies_existsMem_iff,
    Project.Formula.satisfies_imp_iff, Project.Formula.satisfies_extensionalEq_iff_eq he,
    codeFormula_iff he, memPairFormula_iff he, Definitional.Term.eval_weaken]
  constructor
  · rintro ⟨h1,h2,h3,h4⟩
    exact ⟨h1,h2,fun x hx y hy z hz hxy hxz => h3 x hx y hy z hz ⟨hxy,hxz⟩,h4⟩
  · rintro ⟨h1,h2,h3,h4⟩
    exact ⟨h1,h2,fun x hx y hy z hz h => h3 x hx y hy z hz h.1 h.2,h4⟩

def UncountableOrdinal (M : SetTheory.Structure.{u}) (ω ν : M.Domain) : Prop :=
  M.IsOrdinal ν ∧ M.mem ω ν ∧ ¬∃ f, Onto M f ω ν

def uncountableFormula {n : Nat} (ω ν : Project.Term n) : Project.Formula 1 n :=
  .conj (Project.Formula.isOrdinal ν) (.conj (.mem ω ν)
    (.neg (.existsE (ontoFormula (.bound 0) ω.weaken ν.weaken))))

theorem uncountableFormula_iff {M : SetTheory.Structure.{u}} (he : Extensional M) {n : Nat}
    (env : Env M n) (ω ν : Project.Term n) :
    Project.Formula.satisfies env (uncountableFormula ω ν) ↔
      UncountableOrdinal M (ω.eval env) (ν.eval env) := by
  simp only [uncountableFormula, Project.Formula.satisfies_conj_iff,
    Project.Formula.satisfies_isOrdinal_iff, Project.Formula.satisfies_mem_iff,
    Project.Formula.satisfies_neg_iff, Project.Formula.satisfies_exists_iff,
    ontoFormula_iff he, Definitional.Term.eval_weaken]
  rfl

def uncountableSchema : Project.UnarySchema 1 where
  body := uncountableFormula (.bound 1) (.bound 0)
  freeClosed := by
    simp [uncountableFormula, ontoFormula, codeFormula, memPairFormula, pairFormula,
      Project.Formula.isOrdinal, Project.Formula.isTransitive, Project.Formula.isWellOrderOn,
      Project.Formula.isLinearOrderOn, Project.Formula.isStrictPartialOrderOn,
      Project.Formula.isIrreflexiveOn, Project.Formula.isTransitiveOn, Project.Formula.isLeastOf,
      Project.Formula.lessOrEqual, Project.Formula.forallMem, Project.Formula.existsMem,
      Project.Formula.subset, Project.Formula.extensionalEq, Definitional.Formula.FreeClosed]

theorem uncountableSchema_iff {M : SetTheory.Structure.{u}} (he : Extensional M) (ω ν : M.Domain) :
    Project.Formula.satisfies ((oneEnv ω).push ν) uncountableSchema.body ↔ UncountableOrdinal M ω ν := by
  rw [uncountableSchema,uncountableFormula_iff he]
  rfl

/-- 用完整类基础取得最小不可数序数，没有先假定不可数序数类可分离成集合。 -/
theorem least_uncountable_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {ω ν : M.Domain} (hν : UncountableOrdinal M ω ν) :
    ∃ κ, UncountableOrdinal M ω κ ∧ (κ=ν ∨ M.mem κ ν) ∧
      ∀ α, UncountableOrdinal M ω α → (κ=α ∨ M.mem κ α) := by
  obtain ⟨κ,hκ,hOrd,hBound,hLeast⟩ := KP1Y.least_ordinal_d hM uncountableSchema (oneEnv ω)
    (fun x hx => ((uncountableSchema_iff hM.1 ω x).mp hx).1)
    ((uncountableSchema_iff hM.1 ω ν).mpr hν)
  exact ⟨κ,(uncountableSchema_iff hM.1 ω κ).mp hκ,hBound,
    fun α hα => hLeast α ((uncountableSchema_iff hM.1 ω α).mpr hα)⟩

/-- 最小性直接给出 ω 以上、κ 以下各序数的满射见证。 -/
theorem countable_above_omega_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {ω κ α : M.Domain} (hκ : UncountableOrdinal M ω κ)
    (hLeast : ∀ β, UncountableOrdinal M ω β → (κ=β ∨ M.mem κ β))
    (hακ : M.mem α κ) (hωα : M.mem ω α) : ∃ f, Onto M f ω α := by
  classical
  apply Classical.byContradiction
  intro hNo
  have hα : UncountableOrdinal M ω α := ⟨hκ.1.mem hακ,hωα,hNo⟩
  rcases hLeast α hα with he | hkα
  · cases he
    exact SetTheory.KP.mem_irrefl_d (KP1Y.models_weakKP hM) κ hακ
  · exact SetTheory.KP.mem_irrefl_d (KP1Y.models_weakKP hM) κ
      (hκ.1.transitive α hακ κ hkα)

end KP1Y.Cardinal
