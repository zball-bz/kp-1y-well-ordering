import KP1Y.ConstructibleHistory

/-! 用实际对象序数归纳模式证明层级传递且累计，不假定模型外部良基。 -/
namespace KP1Y.Constructible
open YesMetaZFC YesMetaZFC.SetTheory YesMetaZFC.SetTheory.Definitional
open KP1Y.Kuratowski KP1Y.Functions KP1Y.Bounded KP1Y.SetLanguage
universe u

def CumulativeLevel (M : SetTheory.Structure.{u}) (H Γ V i : M.Domain) : Prop :=
  M.mem i Γ → ∀ T, M.mem T V → MemPair M H i T →
    M.TransitiveSet T ∧ ∀ j, M.mem j i → ∀ A, M.mem A V → MemPair M H j A → M.MemberSubset A T

def cumulativeLevelFormula {n : Nat} (H Γ V i : Project.Term n) : Project.Formula 1 n :=
  .imp (.mem i Γ) (Project.Formula.forallMem V
    (.imp (memPairFormula H.weaken i.weaken (.bound 0))
      (.conj (Project.Formula.isTransitive (.bound 0))
        (Project.Formula.forallMem i.weaken (Project.Formula.forallMem V.weaken.weaken
          (.imp (memPairFormula H.weaken.weaken.weaken (.bound 1) (.bound 0))
            (Project.Formula.subset (.bound 0) (.bound 2))))))))

theorem cumulativeLevelFormula_delta0 {n : Nat} (H Γ V i : Project.Term n) :
    (cumulativeLevelFormula H Γ V i).IsDelta0 :=
  .imp (.mem _ _) (.forallMem _ (.imp (memPairFormula_delta0 _ _ _)
    (.conj (transitiveFormula_delta0 _) (.forallMem _ (.forallMem _
      (.imp (memPairFormula_delta0 _ _ _) (.atom _ _ _)))))))

theorem cumulativeLevelFormula_iff {M : SetTheory.Structure.{u}} (he : Extensional M) {n : Nat}
    (env : Env M n) (H Γ V i : Project.Term n) :
    Project.Formula.satisfies env (cumulativeLevelFormula H Γ V i) ↔
      CumulativeLevel M (H.eval env) (Γ.eval env) (V.eval env) (i.eval env) := by
  simp only [cumulativeLevelFormula,Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_mem_iff,
    Project.Formula.satisfies_forallMem_iff,Project.Formula.satisfies_conj_iff,
    Project.Formula.satisfies_isTransitive_iff,Project.Formula.satisfies_subset_iff,
    memPairFormula_iff he,Definitional.Term.eval_weaken]
  rfl

private def cumulativeSchema : Project.Delta0UnarySchema 3 where
  body := cumulativeLevelFormula (.bound 3) (.bound 1) (.bound 2) (.bound 0)
  freeClosed := by
    simp [cumulativeLevelFormula,Project.Formula.isTransitive,memPairFormula,codeFormula,pairFormula,
      Project.Formula.forallMem,Project.Formula.existsMem,Definitional.Formula.FreeClosed]
  delta0 := cumulativeLevelFormula_delta0 _ _ _ _

private theorem cumulativeSchema_iff {M : SetTheory.Structure.{u}} (he : Extensional M) (H Γ V i : M.Domain) :
    Project.Formula.satisfies ((((oneEnv H).push V).push Γ).push i) cumulativeSchema.body ↔ CumulativeLevel M H Γ V i := by
  rw [cumulativeSchema,cumulativeLevelFormula_iff he]
  rfl

theorem history_transitive_and_cumulative_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    (env : Env M 24) (hS : FixedSyntax M (defContext.eval env) (defData.eval env)
      (env.bound 0) (env.bound 1) (env.bound 2)) {H Γ V Q : M.Domain} (hΓ : M.IsOrdinal Γ)
    (h : KP1Y.SigmaRecursion.ValueHistory M (levelStepMatrix.denote env) H Γ V Q) :
    ∀ i, M.mem i Γ → ∀ T, MemPair M H i T →
      M.TransitiveSet T ∧ ∀ j, M.mem j i → ∀ A, MemPair M H j A → M.MemberSubset A T := by
  have hAll := KP1Y.ordinal_induction_d hM cumulativeSchema.toUnarySchema (((oneEnv H).push V).push Γ) (by
    intro i hi ih
    apply (cumulativeSchema_iff hM.1 H Γ V i).mpr
    intro hiΓ T _ hAt
    have hEarlier (j : M.Domain) (hj : M.mem j i) : CumulativeLevel M H Γ V j :=
      (cumulativeSchema_iff hM.1 H Γ V j).mp (ih j hj)
    rcases KP1Y.ordinal_cases hM.1 hi with hEmpty | ⟨p,_,hs⟩ | hLimit
    · have hT := history_empty_value_d hM h hiΓ hEmpty hAt
      exact ⟨fun a ha => False.elim (hT a ha),fun j hj => False.elim (hEmpty j hj)⟩
    · have hp := hs.predecessor_mem
      have hpΓ := hΓ.transitive i hiΓ p hp
      obtain ⟨A,hAV,hPrev⟩ := h.values.total p hpΓ
      have hA := hEarlier p hp hpΓ A hAV hPrev
      have hDef := history_successor_value_d hM hΓ h hiΓ hs hAt hPrev
      obtain ⟨hSub,hTrans⟩ := (hDef.properties_d hM env hS).2 hA.1
      refine ⟨hTrans,?_⟩
      intro j hj B hBV hJB
      rcases (hs j).mp hj with hjp | hSame
      · exact fun x hx => hSub x (hA.2 j hjp B hBV hJB x hx)
      · have hjp := hM.1.eq_of_same_members j p hSame
        subst j
        have hBA := h.values.unique p B A hJB hPrev
        subst B
        exact hSub
    · have hUnion := history_limit_value_d hM h hiΓ hLimit hAt
      refine ⟨?_,?_⟩
      · intro a ha x hx
        obtain ⟨j,hj,A,hJA,haA⟩ := (hUnion a).mp ha
        have hjΓ := hΓ.transitive i hiΓ j hj
        have hA := hEarlier j hj hjΓ A (h.values.bounds hM.1 hJA).2 hJA
        exact (hUnion x).mpr ⟨j,hj,A,hJA,hA.1 a haA x hx⟩
      · intro j hj A _ hJA x hx
        exact (hUnion x).mpr ⟨j,hj,A,hJA,hx⟩)
  intro i hi T hAt
  have hLevel := (cumulativeSchema_iff hM.1 H Γ V i).mp (hAll i (hΓ.mem hi)) hi T (h.values.bounds hM.1 hAt).2 hAt
  exact ⟨hLevel.1,fun j hj A hJA => hLevel.2 j hj A (h.values.bounds hM.1 hJA).2 hJA⟩

end KP1Y.Constructible
