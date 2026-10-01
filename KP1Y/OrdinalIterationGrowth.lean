import KP1Y.OrdinalIterationOrdinals
import KP1Y.BoundedNaturalInduction

/-! 后继运算严格增大序数时，连续迭代严格增长；用实际对象模式归纳证明。 -/
namespace KP1Y.OrdinalIteration
open YesMetaZFC YesMetaZFC.SetTheory YesMetaZFC.SetTheory.Definitional
open KP1Y.Kuratowski KP1Y.Functions
universe u

def StrictGrowth {M : SetTheory.Structure.{u}} {n : Nat} (φ : KP1Y.WitnessMatrix n) (e : Env M n) : Prop :=
  ∀ x, M.IsOrdinal x → ∀ y z, Next φ e x y z → M.mem x y

def GrowingAt (M : SetTheory.Structure.{u}) (H Γ V i : M.Domain) : Prop :=
  M.mem i Γ → ∀ T, M.mem T V → MemPair M H i T → ∀ j, M.mem j i → ∀ X, M.mem X V → MemPair M H j X → M.mem X T

private def growingSchema : Project.Delta0UnarySchema 3 where
  body := .imp (.mem (.bound 0) (.bound 1)) (Project.Formula.forallMem (.bound 2)
    (.imp (memPairFormula (.bound 4) (.bound 1) (.bound 0))
      (Project.Formula.forallMem (.bound 1) (Project.Formula.forallMem (.bound 4)
        (.imp (memPairFormula (.bound 6) (.bound 1) (.bound 0)) (.mem (.bound 0) (.bound 2)))))))
  freeClosed := by
    simp [memPairFormula,codeFormula,pairFormula,Project.Formula.forallMem,Project.Formula.existsMem,Definitional.Formula.FreeClosed]
  delta0 := .imp (.mem _ _) (.forallMem _ (.imp (memPairFormula_delta0 _ _ _)
    (.forallMem _ (.forallMem _ (.imp (memPairFormula_delta0 _ _ _) (.mem _ _))))))

private theorem growingSchema_iff {M : SetTheory.Structure.{u}} (he : Extensional M) (H Γ V i : M.Domain) :
    Project.Formula.satisfies ((((oneEnv H).push V).push Γ).push i) growingSchema.body ↔ GrowingAt M H Γ V i := by
  simp only [growingSchema,Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_mem_iff,
    Project.Formula.satisfies_forallMem_iff,memPairFormula_iff he]
  rfl

theorem history_strict_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory) {n : Nat}
    (φ : KP1Y.WitnessMatrix n) (e : Env M (n+1)) (hBase : M.IsOrdinal (e.bound 0))
    (hOrd : PreservesOrdinals φ (tailEnv e)) (hGrow : StrictGrowth φ (tailEnv e)) {H Γ V Q : M.Domain} (hΓ : M.IsOrdinal Γ)
    (h : KP1Y.SigmaRecursion.ValueHistory M ((iterationMatrix φ).denote e) H Γ V Q) :
    ∀ i, M.mem i Γ → ∀ T, MemPair M H i T → ∀ j, M.mem j i → ∀ X, MemPair M H j X → M.mem X T := by
  have hOrdinals := history_ordinals_d hM φ e hBase hOrd hΓ h
  have hAll := KP1Y.ordinal_induction_d hM growingSchema.toUnarySchema (((oneEnv H).push V).push Γ) (by
    intro i hi ih
    apply (growingSchema_iff hM.1 H Γ V i).mpr
    intro hiΓ T _ hAt
    have hEarlier (j : M.Domain) (hj : M.mem j i) : GrowingAt M H Γ V j := (growingSchema_iff hM.1 H Γ V j).mp (ih j hj)
    rcases KP1Y.ordinal_cases hM.1 hi with hEmpty | ⟨p,_,hs⟩ | hLimit
    · intro j hj
      exact False.elim (hEmpty j hj)
    · have hp := hs.predecessor_mem
      have hpΓ := hΓ.transitive i hiΓ p hp
      obtain ⟨x,hxV,hPrev⟩ := h.values.total p hpΓ
      obtain ⟨z,hNext⟩ := history_next_d hM hΓ h hiΓ hs hAt hPrev
      have hxT := hGrow x (hOrdinals p hpΓ x hPrev) T z hNext
      intro j hj X hXV hJX
      rcases (hs j).mp hj with hjp | hSame
      · exact (hOrdinals i hiΓ T hAt).transitive x hxT X (hEarlier p hp hpΓ x hxV hPrev j hjp X hXV hJX)
      · have hjp := hM.1.eq_of_same_members j p hSame
        subst j
        have hXx := h.values.unique p X x hJX hPrev
        exact hXx ▸ hxT
    · have hUnion := history_limit_d hM h hiΓ hLimit hAt
      intro j hj X hXV hJX
      obtain ⟨k,hk,hjk⟩ := hLimit.2.2 j hj
      have hkΓ := hΓ.transitive i hiΓ k hk
      obtain ⟨T',hT'V,hKT'⟩ := h.values.total k hkΓ
      have hXT' := hEarlier k hk hkΓ T' hT'V hKT' j hjk X hXV hJX
      exact (hUnion X).mpr ⟨k,hk,T',hKT',hXT'⟩)
  intro i hi T hAt j hj X hJX
  exact (growingSchema_iff hM.1 H Γ V i).mp (hAll i (hΓ.mem hi)) hi T (h.values.bounds hM.1 hAt).2 hAt
    j hj X (h.values.bounds hM.1 hJX).2 hJX

theorem value_strict_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory) {n : Nat}
    (φ : KP1Y.WitnessMatrix n) (e : Env M (n+1)) (hBase : M.IsOrdinal (e.bound 0))
    (hFun : Functional φ (tailEnv e)) (hOrd : PreservesOrdinals φ (tailEnv e)) (hGrow : StrictGrowth φ (tailEnv e))
    {i j X T : M.Domain} (hX : Value φ e i X) (hT : Value φ e j T) (hij : M.mem i j) : M.mem X T := by
  obtain ⟨δ,H,V,Q,hs,hH,hAt⟩ := hT.history
  have hδ := SetTheory.KP.successor_isOrdinal (KP1Y.models_weakKP hM) hT.ordinal hs
  have hiδ := hδ.transitive j hs.predecessor_mem i hij
  have hAtX := value_agrees_with_history_d hM φ e hFun hδ hH hiδ hX
  exact history_strict_d hM φ e hBase hOrd hGrow hδ hH j hs.predecessor_mem T hAt i hij X hAtX

theorem value_mono_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory) {n : Nat}
    (φ : KP1Y.WitnessMatrix n) (e : Env M (n+1)) (hBase : M.IsOrdinal (e.bound 0))
    (hFun : Functional φ (tailEnv e)) (hOrd : PreservesOrdinals φ (tailEnv e)) (hGrow : StrictGrowth φ (tailEnv e))
    {i j X T : M.Domain} (hX : Value φ e i X) (hT : Value φ e j T) (hij : M.MemberSubset i j) : M.MemberSubset X T := by
  rcases KP1Y.Naturals.ordinal_subset_cases_d hM hX.ordinal hT.ordinal hij with he | hLess
  · subst j
    have hXT := value_unique_d hM φ e hFun hX hT
    exact fun a ha => hXT ▸ ha
  · exact (hT.isOrdinal_d hM φ e hBase hOrd).transitive X (value_strict_d hM φ e hBase hFun hOrd hGrow hX hT hLess)

end KP1Y.OrdinalIteration
