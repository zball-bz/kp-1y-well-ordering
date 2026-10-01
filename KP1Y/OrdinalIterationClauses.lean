import KP1Y.OrdinalIterationValues

/-! 连续Σ₁迭代的零、后继、极限方程，分别对历史及独立迭代值成立。 -/
namespace KP1Y.OrdinalIteration
open YesMetaZFC YesMetaZFC.SetTheory
open KP1Y.Kuratowski KP1Y.Functions
universe u

theorem limit_no_predecessor_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {i : M.Domain} (hi : M.IsLimitOrdinal i) : NoPredecessor M i := by
  intro p hp hs
  obtain ⟨j,hj,hpj⟩ := hi.2.2 p hp
  rcases (hs j).mp hj with hjp | hSame
  · exact SetTheory.KP.mem_irrefl_d (KP1Y.models_weakKP hM) p ((hi.1.mem hp).transitive j hjp p hpj)
  · have hjp := hM.1.eq_of_same_members j p hSame
    subst j
    exact SetTheory.KP.mem_irrefl_d (KP1Y.models_weakKP hM) p hpj

theorem Step.initial {M : SetTheory.Structure.{u}} {n : Nat} {φ : KP1Y.WitnessMatrix n} {e : Env M (n+1)}
    {i P T w : M.Domain} (h : Step φ e i P T w) (hi : Empty M i) : T=e.bound 0 := by
  obtain ⟨_,_,_,hCases⟩ := h
  rcases hCases with ⟨_,hT⟩ | ⟨p,hp,_,_,_,_,_,_,_⟩ | ⟨⟨hNot,_⟩,_,_,_,_⟩
  · exact hT
  · exact False.elim (hi p hp)
  · exact False.elim (hNot hi)

theorem Step.next_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory) {n : Nat}
    {φ : KP1Y.WitnessMatrix n} {e : Env M (n+1)} {i p P T w : M.Domain} (hi : M.IsOrdinal i)
    (hs : M.SuccessorOf i p) (h : Step φ e i P T w) : ∃ x, MemPair M P p x ∧ ∃ z, Next φ (tailEnv e) x T z := by
  obtain ⟨_,_,_,hCases⟩ := h
  rcases hCases with ⟨hEmpty,_⟩ | ⟨p',hp',x,_,z,_,hs',hAt,hNext⟩ | ⟨⟨_,hNoPred⟩,_,_,_,_⟩
  · exact False.elim (hEmpty p hs.predecessor_mem)
  · have hpp' := Structure.SuccessorOf.predecessor_eq hM.1 (hi.mem hp') hs' hs
    subst p'
    exact ⟨x,hAt,z,hNext⟩
  · exact False.elim (hNoPred p hs.predecessor_mem hs)

theorem Step.limit_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory) {n : Nat}
    {φ : KP1Y.WitnessMatrix n} {e : Env M (n+1)} {i P T w : M.Domain} (hi : M.IsLimitOrdinal i)
    (h : Step φ e i P T w) : RangeUnion M T P i := by
  obtain ⟨_,_,hP,hCases⟩ := h
  rcases hCases with ⟨hEmpty,_⟩ | ⟨p,hp,_,_,_,_,hs,_,_⟩ | ⟨_,_,_,hRange,hUnion⟩
  · obtain ⟨x,hx⟩ := hi.2.1
    exact False.elim (hEmpty x hx)
  · exact False.elim (limit_no_predecessor_d hM hi p hp hs)
  · exact range_union_exact hM.1 hP hRange hUnion

theorem Step.limit_certificate_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory) {n : Nat}
    {φ : KP1Y.WitnessMatrix n} {e : Env M (n+1)} {i P T w : M.Domain} (hi : M.IsLimitOrdinal i)
    (h : Step φ e i P T w) : ∃ V D, Graph M P i V ∧ KP1Y.Sequences.RangeBound M D V P i ∧ M.IsUnionOf T D := by
  obtain ⟨V,_,hP,hCases⟩ := h
  rcases hCases with ⟨hEmpty,_⟩ | ⟨p,hp,_,_,_,_,hs,_,_⟩ | ⟨_,D,_,hRange,hUnion⟩
  · obtain ⟨x,hx⟩ := hi.2.1
    exact False.elim (hEmpty x hx)
  · exact False.elim (limit_no_predecessor_d hM hi p hp hs)
  · exact ⟨V,D,hP,hRange,hUnion⟩

theorem history_step_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory) {n : Nat}
    {φ : KP1Y.WitnessMatrix n} {e : Env M (n+1)} {H Γ V Q i T : M.Domain}
    (h : KP1Y.SigmaRecursion.ValueHistory M ((iterationMatrix φ).denote e) H Γ V Q)
    (hi : M.mem i Γ) (hAt : MemPair M H i T) : ∃ P w, Prefix M P H i V ∧ Step φ e i P T w := by
  obtain ⟨P,hP,hQ⟩ := h.prefixes.total i hi
  obtain ⟨hPrefix,w,_,hStep⟩ := h.obeys i hi P hP T (h.values.bounds hM.1 hAt).2 hQ hAt
  exact ⟨P,w,hPrefix,(iterationMatrix_iff hM φ e i P T w).mp hStep⟩

theorem history_initial_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory) {n : Nat}
    {φ : KP1Y.WitnessMatrix n} {e : Env M (n+1)} {H Γ V Q i T : M.Domain}
    (h : KP1Y.SigmaRecursion.ValueHistory M ((iterationMatrix φ).denote e) H Γ V Q)
    (hi : M.mem i Γ) (hEmpty : Empty M i) (hAt : MemPair M H i T) : T=e.bound 0 := by
  obtain ⟨_,_,_,hStep⟩ := history_step_d hM h hi hAt
  exact hStep.initial hEmpty

theorem history_next_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory) {n : Nat}
    {φ : KP1Y.WitnessMatrix n} {e : Env M (n+1)} {H Γ V Q i p x T : M.Domain} (hΓ : M.IsOrdinal Γ)
    (h : KP1Y.SigmaRecursion.ValueHistory M ((iterationMatrix φ).denote e) H Γ V Q)
    (hi : M.mem i Γ) (hs : M.SuccessorOf i p) (hAt : MemPair M H i T) (hPrev : MemPair M H p x) :
    ∃ z, Next φ (tailEnv e) x T z := by
  obtain ⟨P,_,hPrefix,hStep⟩ := history_step_d hM h hi hAt
  obtain ⟨x',hPAt,z,hNext⟩ := hStep.next_d hM (hΓ.mem hi) hs
  have hAt' := (hPrefix.all_rows hM.1 h.values p hs.predecessor_mem x').mp hPAt
  have hxx' := h.values.unique p x' x hAt' hPrev
  subst x'
  exact ⟨z,hNext⟩

theorem history_limit_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory) {n : Nat}
    {φ : KP1Y.WitnessMatrix n} {e : Env M (n+1)} {H Γ V Q i T : M.Domain}
    (h : KP1Y.SigmaRecursion.ValueHistory M ((iterationMatrix φ).denote e) H Γ V Q)
    (hi : M.mem i Γ) (hLimit : M.IsLimitOrdinal i) (hAt : MemPair M H i T) : RangeUnion M T H i := by
  obtain ⟨P,_,hPrefix,hStep⟩ := history_step_d hM h hi hAt
  have hUnion := hStep.limit_d hM hLimit
  intro a
  constructor
  · intro ha
    obtain ⟨j,hj,x,hAt,hax⟩ := (hUnion a).mp ha
    exact ⟨j,hj,x,(hPrefix.all_rows hM.1 h.values j hj x).mp hAt,hax⟩
  · rintro ⟨j,hj,x,hAt,hax⟩
    exact (hUnion a).mpr ⟨j,hj,x,(hPrefix.all_rows hM.1 h.values j hj x).mpr hAt,hax⟩

theorem value_agrees_with_history_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory) {n : Nat}
    (φ : KP1Y.WitnessMatrix n) (e : Env M (n+1)) (hFun : Functional φ (tailEnv e)) {H Γ V Q i T : M.Domain}
    (hΓ : M.IsOrdinal Γ) (h : KP1Y.SigmaRecursion.ValueHistory M ((iterationMatrix φ).denote e) H Γ V Q)
    (hi : M.mem i Γ) (hValue : Value φ e i T) : MemPair M H i T := by
  obtain ⟨T',_,hAt⟩ := h.values.total i hi
  have hEq := value_unique_d hM φ e hFun (value_from_history_d hM hΓ h hi hAt) hValue
  exact hEq ▸ hAt

theorem Value.initial_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory) {n : Nat}
    {φ : KP1Y.WitnessMatrix n} {e : Env M (n+1)} {i T : M.Domain} (h : Value φ e i T) (hi : Empty M i) : T=e.bound 0 := by
  obtain ⟨_,_,_,_,hs,hH,hAt⟩ := h.history
  exact history_initial_d hM hH hs.predecessor_mem hi hAt

theorem Value.next_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory) {n : Nat}
    (φ : KP1Y.WitnessMatrix n) (e : Env M (n+1)) (hFun : Functional φ (tailEnv e)) {i p x T : M.Domain}
    (hs : M.SuccessorOf i p) (hx : Value φ e p x) (hT : Value φ e i T) : ∃ z, Next φ (tailEnv e) x T z := by
  obtain ⟨δ,H,V,Q,hδi,hH,hAt⟩ := hT.history
  have hδ := SetTheory.KP.successor_isOrdinal (KP1Y.models_weakKP hM) hT.ordinal hδi
  have hpδ := hδ.transitive i hδi.predecessor_mem p hs.predecessor_mem
  have hPrev := value_agrees_with_history_d hM φ e hFun hδ hH hpδ hx
  exact history_next_d hM hδ hH hδi.predecessor_mem hs hAt hPrev

end KP1Y.OrdinalIteration
