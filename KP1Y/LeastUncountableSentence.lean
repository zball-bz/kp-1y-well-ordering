import KP1Y.CountableSegments

/-! “存在不可数序数时存在最小者”的实际 KPω 对象推导。 -/
namespace KP1Y.Cardinal
open YesMetaZFC YesMetaZFC.SetTheory YesMetaZFC.SetTheory.Definitional
universe u

def leastUncountableCore {n : Nat} (ω ν : Project.Term n) : Project.Formula 1 n :=
  .imp (uncountableFormula ω ν) (.existsE
    (.conj (uncountableFormula ω.weaken (.bound 0))
      (.conj (.disj (Project.Formula.extensionalEq (.bound 0) ν.weaken) (.mem (.bound 0) ν.weaken))
        (.forallE (.imp (uncountableFormula ω.weaken.weaken (.bound 0))
          (.disj (Project.Formula.extensionalEq (.bound 1) (.bound 0)) (.mem (.bound 1) (.bound 0))))))))

theorem leastUncountableCore_iff {M : SetTheory.Structure.{u}} (he : Extensional M) {n : Nat}
    (env : Env M n) (ω ν : Project.Term n) :
    Project.Formula.satisfies env (leastUncountableCore ω ν) ↔
      (UncountableOrdinal M (ω.eval env) (ν.eval env) →
        ∃ κ, UncountableOrdinal M (ω.eval env) κ ∧ (κ=ν.eval env ∨ M.mem κ (ν.eval env)) ∧
          ∀ α, UncountableOrdinal M (ω.eval env) α → (κ=α ∨ M.mem κ α)) := by
  simp only [leastUncountableCore, Project.Formula.satisfies_imp_iff,
    Project.Formula.satisfies_exists_iff, Project.Formula.satisfies_conj_iff,
    Project.Formula.satisfies_disj_iff, Project.Formula.satisfies_forall_iff,
    Project.Formula.satisfies_mem_iff, Project.Formula.satisfies_extensionalEq_iff_eq he,
    uncountableFormula_iff he, Definitional.Term.eval_weaken]
  rfl

def leastUncountableSentence : Project.Sentence :=
  Project.Sentence.ofFormula (.forallE (.forallE (leastUncountableCore (.bound 1) (.bound 0)))) (by
    simp [leastUncountableCore, uncountableFormula, ontoFormula, Kuratowski.memPairFormula,
      Kuratowski.codeFormula, Kuratowski.pairFormula,
      Project.Formula.isOrdinal, Project.Formula.isTransitive, Project.Formula.isWellOrderOn,
      Project.Formula.isLinearOrderOn, Project.Formula.isStrictPartialOrderOn,
      Project.Formula.isIrreflexiveOn, Project.Formula.isTransitiveOn, Project.Formula.isLeastOf,
      Project.Formula.lessOrEqual, Project.Formula.forallMem, Project.Formula.existsMem,
      Project.Formula.subset, Project.Formula.extensionalEq, Definitional.Formula.FreeClosed])

theorem least_uncountable_derivable : KP1Y.Derives leastUncountableSentence := by
  apply KP1Y.derives_of_all_models
  intro M hM free
  change Project.Formula.satisfies ({bound := Fin.elim0,free := free} : Env M 0)
    leastUncountableSentence.formula
  simp only [leastUncountableSentence, Project.Sentence.ofFormula,
    Project.Formula.satisfies_forall_iff, leastUncountableCore_iff hM.1]
  change ∀ ω ν, UncountableOrdinal M ω ν → ∃ κ, UncountableOrdinal M ω κ ∧
    (κ=ν ∨ M.mem κ ν) ∧ ∀ α, UncountableOrdinal M ω α → (κ=α ∨ M.mem κ α)
  exact fun _ _ hν => least_uncountable_d hM hν

end KP1Y.Cardinal
