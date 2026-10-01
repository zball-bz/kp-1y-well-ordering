import KP1Y.OrdinalIterationGrowth

/-! 严格连续序数迭代至少达到自己的阶段索引，并保留独立值的极限方程。 -/
namespace KP1Y.OrdinalIteration
open YesMetaZFC YesMetaZFC.SetTheory YesMetaZFC.SetTheory.Definitional
open KP1Y.Kuratowski KP1Y.Functions
universe u

def IndexBoundAt (M : SetTheory.Structure.{u}) (H Γ V i : M.Domain) : Prop :=
  M.mem i Γ → ∀ T, M.mem T V → MemPair M H i T → M.MemberSubset i T

private def indexBoundSchema : Project.Delta0UnarySchema 3 where
  body := .imp (.mem (.bound 0) (.bound 1)) (Project.Formula.forallMem (.bound 2)
    (.imp (memPairFormula (.bound 4) (.bound 1) (.bound 0)) (Project.Formula.subset (.bound 1) (.bound 0))))
  freeClosed := by
    simp [memPairFormula,codeFormula,pairFormula,Project.Formula.forallMem,Project.Formula.existsMem,Definitional.Formula.FreeClosed]
  delta0 := .imp (.mem _ _) (.forallMem _ (.imp (memPairFormula_delta0 _ _ _) (.atom _ _ _)))

private theorem indexBoundSchema_iff {M : SetTheory.Structure.{u}} (he : Extensional M) (H Γ V i : M.Domain) :
    Project.Formula.satisfies ((((oneEnv H).push V).push Γ).push i) indexBoundSchema.body ↔ IndexBoundAt M H Γ V i := by
  simp only [indexBoundSchema,Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_mem_iff,
    Project.Formula.satisfies_forallMem_iff,Project.Formula.satisfies_subset_iff,memPairFormula_iff he]
  rfl

theorem history_index_bounded_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory) {n : Nat}
    (φ : KP1Y.WitnessMatrix n) (e : Env M (n+1)) (hBase : M.IsOrdinal (e.bound 0))
    (hOrd : PreservesOrdinals φ (tailEnv e)) (hGrow : StrictGrowth φ (tailEnv e)) {H Γ V Q : M.Domain} (hΓ : M.IsOrdinal Γ)
    (h : KP1Y.SigmaRecursion.ValueHistory M ((iterationMatrix φ).denote e) H Γ V Q) :
    ∀ i, M.mem i Γ → ∀ T, MemPair M H i T → M.MemberSubset i T := by
  have hOrdinals := history_ordinals_d hM φ e hBase hOrd hΓ h
  have hStrict := history_strict_d hM φ e hBase hOrd hGrow hΓ h
  have hAll := KP1Y.ordinal_induction_d hM indexBoundSchema.toUnarySchema (((oneEnv H).push V).push Γ) (by
    intro i hi ih
    apply (indexBoundSchema_iff hM.1 H Γ V i).mpr
    intro hiΓ T _ hAt
    have hT := hOrdinals i hiΓ T hAt
    rcases Structure.IsOrdinal.trichotomy hM.1 hi hT (SetTheory.KP.difference_exists_d (KP1Y.models_weakKP hM))
      (SetTheory.KP.intersection_exists_d (KP1Y.models_weakKP hM) i T) with hSame | hiT | hTi
    · have hEq := hM.1.eq_of_same_members i T hSame
      exact fun x hx => hEq ▸ hx
    · exact hT.transitive i hiT
    · have hTΓ := hΓ.transitive i hiΓ T hTi
      obtain ⟨U,hUV,hTU⟩ := h.values.total T hTΓ
      have hSubTU := (indexBoundSchema_iff hM.1 H Γ V T).mp (ih T hTi) hTΓ U hUV hTU
      have hUT := hStrict i hiΓ T hAt T hTi U hTU
      exact False.elim (SetTheory.KP.mem_irrefl_d (KP1Y.models_weakKP hM) U (hSubTU U hUT)))
  intro i hi T hAt
  exact (indexBoundSchema_iff hM.1 H Γ V i).mp (hAll i (hΓ.mem hi)) hi T (h.values.bounds hM.1 hAt).2 hAt

theorem value_index_bounded_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory) {n : Nat}
    (φ : KP1Y.WitnessMatrix n) (e : Env M (n+1)) (hBase : M.IsOrdinal (e.bound 0))
    (hOrd : PreservesOrdinals φ (tailEnv e)) (hGrow : StrictGrowth φ (tailEnv e)) {i T : M.Domain}
    (hValue : Value φ e i T) : M.MemberSubset i T := by
  obtain ⟨δ,H,V,Q,hs,hH,hAt⟩ := hValue.history
  have hδ := SetTheory.KP.successor_isOrdinal (KP1Y.models_weakKP hM) hValue.ordinal hs
  exact history_index_bounded_d hM φ e hBase hOrd hGrow hδ hH i hs.predecessor_mem T hAt

theorem Value.limit_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory) {n : Nat}
    (φ : KP1Y.WitnessMatrix n) (e : Env M (n+1)) (hFun : Functional φ (tailEnv e)) {i T : M.Domain}
    (hi : M.IsLimitOrdinal i) (hValue : Value φ e i T) :
    ∀ a, M.mem a T ↔ ∃ j, M.mem j i ∧ ∃ X, Value φ e j X ∧ M.mem a X := by
  obtain ⟨δ,H,V,Q,hs,hH,hAt⟩ := hValue.history
  have hδ := SetTheory.KP.successor_isOrdinal (KP1Y.models_weakKP hM) hi.1 hs
  have hUnion := history_limit_d hM hH hs.predecessor_mem hi hAt
  intro a
  constructor
  · intro ha
    obtain ⟨j,hj,X,hJX,haX⟩ := (hUnion a).mp ha
    have hjδ := hδ.transitive i hs.predecessor_mem j hj
    exact ⟨j,hj,X,value_from_history_d hM hδ hH hjδ hJX,haX⟩
  · rintro ⟨j,hj,X,hX,haX⟩
    have hjδ := hδ.transitive i hs.predecessor_mem j hj
    exact (hUnion a).mpr ⟨j,hj,X,value_agrees_with_history_d hM φ e hFun hδ hH hjδ hX,haX⟩

end KP1Y.OrdinalIteration
