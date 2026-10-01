import KP1Y.OrdinalIterationClauses

/-! 连续迭代保持序数性的显式对象归纳证明。 -/
namespace KP1Y.OrdinalIteration
open YesMetaZFC YesMetaZFC.SetTheory YesMetaZFC.SetTheory.Definitional
open KP1Y.Kuratowski KP1Y.Functions KP1Y.Bounded
universe u

def PreservesOrdinals {M : SetTheory.Structure.{u}} {n : Nat} (φ : KP1Y.WitnessMatrix n) (e : Env M n) : Prop :=
  ∀ x, M.IsOrdinal x → ∀ y z, Next φ e x y z → M.IsOrdinal y

def OrdinalAt (M : SetTheory.Structure.{u}) (H Γ V i : M.Domain) : Prop :=
  M.mem i Γ → ∀ T, M.mem T V → MemPair M H i T → M.IsOrdinal T

private def ordinalAtSchema : Project.Delta0UnarySchema 3 where
  body := .imp (.mem (.bound 0) (.bound 1)) (Project.Formula.forallMem (.bound 2)
    (.imp (memPairFormula (.bound 4) (.bound 1) (.bound 0)) (ordinalFormula (.bound 0))))
  freeClosed := by
    simp [ordinalFormula,Project.Formula.isTransitive,memPairFormula,codeFormula,pairFormula,
      Project.Formula.forallMem,Project.Formula.existsMem,Definitional.Formula.FreeClosed]
  delta0 := .imp (.mem _ _) (.forallMem _ (.imp (memPairFormula_delta0 _ _ _) (ordinalFormula_delta0 _)))

private theorem ordinalAtSchema_iff {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory) (H Γ V i : M.Domain) :
    Project.Formula.satisfies ((((oneEnv H).push V).push Γ).push i) ordinalAtSchema.body ↔ OrdinalAt M H Γ V i := by
  simp only [ordinalAtSchema,Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_mem_iff,
    Project.Formula.satisfies_forallMem_iff,memPairFormula_iff hM.1,ordinalFormula_iff hM]
  rfl

theorem history_ordinals_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory) {n : Nat}
    (φ : KP1Y.WitnessMatrix n) (e : Env M (n+1)) (hBase : M.IsOrdinal (e.bound 0))
    (hOp : PreservesOrdinals φ (tailEnv e)) {H Γ V Q : M.Domain} (hΓ : M.IsOrdinal Γ)
    (h : KP1Y.SigmaRecursion.ValueHistory M ((iterationMatrix φ).denote e) H Γ V Q) :
    ∀ i, M.mem i Γ → ∀ T, MemPair M H i T → M.IsOrdinal T := by
  have hAll := KP1Y.ordinal_induction_d hM ordinalAtSchema.toUnarySchema (((oneEnv H).push V).push Γ) (by
    intro i hi ih
    apply (ordinalAtSchema_iff hM H Γ V i).mpr
    intro hiΓ T _ hAt
    have hEarlier (j : M.Domain) (hj : M.mem j i) : OrdinalAt M H Γ V j := (ordinalAtSchema_iff hM H Γ V j).mp (ih j hj)
    rcases KP1Y.ordinal_cases hM.1 hi with hEmpty | ⟨p,_,hs⟩ | hLimit
    · have hEq := history_initial_d hM h hiΓ hEmpty hAt
      exact hEq ▸ hBase
    · have hp := hs.predecessor_mem
      have hpΓ := hΓ.transitive i hiΓ p hp
      obtain ⟨x,hxV,hPrev⟩ := h.values.total p hpΓ
      obtain ⟨z,hNext⟩ := history_next_d hM hΓ h hiΓ hs hAt hPrev
      exact hOp x (hEarlier p hp hpΓ x hxV hPrev) T z hNext
    · obtain ⟨P,_,hPrefix,hStep⟩ := history_step_d hM h hiΓ hAt
      obtain ⟨V',D,hP,hRange,hUnion⟩ := hStep.limit_certificate_d hM hLimit
      apply Structure.IsOrdinal.of_union (KP1Y.models_weakKP hM) hUnion
      intro x hxD
      obtain ⟨j,hj,hPAt⟩ := (hRange.exact hM.1 hP x).mp hxD
      have hHAt := (hPrefix.all_rows hM.1 h.values j hj x).mp hPAt
      have hjΓ := hΓ.transitive i hiΓ j hj
      exact hEarlier j hj hjΓ x (h.values.bounds hM.1 hHAt).2 hHAt)
  intro i hi T hAt
  exact (ordinalAtSchema_iff hM H Γ V i).mp (hAll i (hΓ.mem hi)) hi T (h.values.bounds hM.1 hAt).2 hAt

theorem Value.isOrdinal_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory) {n : Nat}
    (φ : KP1Y.WitnessMatrix n) (e : Env M (n+1)) (hBase : M.IsOrdinal (e.bound 0))
    (hOp : PreservesOrdinals φ (tailEnv e)) {i T : M.Domain} (h : Value φ e i T) : M.IsOrdinal T := by
  obtain ⟨δ,H,V,Q,hs,hH,hAt⟩ := h.history
  have hδ := SetTheory.KP.successor_isOrdinal (KP1Y.models_weakKP hM) h.ordinal hs
  exact history_ordinals_d hM φ e hBase hOp hδ hH i hs.predecessor_mem T hAt

end KP1Y.OrdinalIteration
