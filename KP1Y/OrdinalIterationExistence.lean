import KP1Y.OrdinalIterationSyntax

/-! 连续Σ₁迭代在KPω中的全定义、单值和实际历史存在性。 -/
namespace KP1Y.OrdinalIteration
open YesMetaZFC YesMetaZFC.SetTheory
open KP1Y.Kuratowski KP1Y.Functions KP1Y.Sequences
universe u

def RangeUnion (M : SetTheory.Structure.{u}) (T P i : M.Domain) : Prop :=
  ∀ a, M.mem a T ↔ ∃ j, M.mem j i ∧ ∃ x, MemPair M P j x ∧ M.mem a x

theorem range_union_exact {M : SetTheory.Structure.{u}} (he : Extensional M) {T D V P i : M.Domain}
    (hP : Graph M P i V) (hRange : RangeBound M D V P i)
    (hUnion : ∀ a, M.mem a T ↔ ∃ x, M.mem x D ∧ M.mem a x) : RangeUnion M T P i := by
  intro a
  constructor
  · intro ha
    obtain ⟨x,hx,hax⟩ := (hUnion a).mp ha
    obtain ⟨j,hj,hAt⟩ := (hRange.exact he hP x).mp hx
    exact ⟨j,hj,x,hAt,hax⟩
  · rintro ⟨j,hj,x,hAt,hax⟩
    exact (hUnion a).mpr ⟨x,(hRange.exact he hP x).mpr ⟨j,hj,hAt⟩,hax⟩

theorem step_total_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory) {n : Nat}
    (φ : KP1Y.WitnessMatrix n) (e : Env M (n+1)) (hTotal : Total φ (tailEnv e))
    {i P V : M.Domain} (hP : Graph M P i V) : ∃ T w, Step φ e i P T w := by
  classical
  by_cases hEmpty : Empty M i
  · obtain ⟨w,hw⟩ := SetTheory.KP.exists_pair (KP1Y.models_weakKP hM) V V
    exact ⟨e.bound 0,w,V,(hw V).mpr (Or.inl rfl),hP,Or.inl ⟨hEmpty,rfl⟩⟩
  · by_cases hSucc : ∃ p, M.mem p i ∧ M.SuccessorOf i p
    · obtain ⟨p,hp,hs⟩ := hSucc
      obtain ⟨x,hx,hAt⟩ := hP.total p hp
      obtain ⟨T,z,hNext⟩ := hTotal x
      obtain ⟨w,hw⟩ := SetTheory.KP.exists_pair (KP1Y.models_weakKP hM) V z
      exact ⟨T,w,V,(hw V).mpr (Or.inl rfl),hP,Or.inr (Or.inl
        ⟨p,hp,x,hx,z,(hw z).mpr (Or.inr rfl),hs,hAt,hNext⟩)⟩
    · obtain ⟨D,hD⟩ := range_bound_exists_d hM V P i
      obtain ⟨T,hT⟩ := SetTheory.KP.exists_union (KP1Y.models_weakKP hM) D
      obtain ⟨w,hw⟩ := SetTheory.KP.exists_pair (KP1Y.models_weakKP hM) V D
      exact ⟨T,w,V,(hw V).mpr (Or.inl rfl),hP,Or.inr (Or.inr
        ⟨⟨hEmpty,fun p hp hs => hSucc ⟨p,hp,hs⟩⟩,D,(hw D).mpr (Or.inr rfl),hD,hT⟩)⟩

theorem step_unique_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory) {n : Nat}
    (φ : KP1Y.WitnessMatrix n) (e : Env M (n+1)) (hFun : Functional φ (tailEnv e))
    {i P T T' w w' : M.Domain} (hi : M.IsOrdinal i) (h : Step φ e i P T w) (h' : Step φ e i P T' w') : T=T' := by
  obtain ⟨V,_,hP,hCases⟩ := h
  obtain ⟨V',_,hP',hCases'⟩ := h'
  rcases hCases with ⟨hEmpty,hT⟩ | ⟨p,hp,x,_,z,_,hs,hAt,hNext⟩ | ⟨⟨hNe,hNoPred⟩,D,_,hRange,hUnion⟩
  · rcases hCases' with ⟨_,hT'⟩ | ⟨p,hp,_,_,_,_,_,_,_⟩ | ⟨⟨hNe,_⟩,_,_,_,_⟩
    · exact hT.trans hT'.symm
    · exact False.elim (hEmpty p hp)
    · exact False.elim (hNe hEmpty)
  · rcases hCases' with ⟨hEmpty,_⟩ | ⟨p',_,x',_,z',_,hs',hAt',hNext'⟩ | ⟨⟨_,hNoPred⟩,_,_,_,_⟩
    · exact False.elim (hEmpty p hp)
    · have hpp' := Structure.SuccessorOf.predecessor_eq hM.1 (hi.mem hp) hs hs'
      subst p'
      have hxx' := hP.unique p x x' hAt hAt'
      subst x'
      exact hFun x T T' z z' hNext hNext'
    · exact False.elim (hNoPred p hp hs)
  · rcases hCases' with ⟨hEmpty,_⟩ | ⟨p,hp,_,_,_,_,hs,_,_⟩ | ⟨_,D',_,hRange',hUnion'⟩
    · exact False.elim (hNe hEmpty)
    · exact False.elim (hNoPred p hp hs)
    · have hRows := range_union_exact hM.1 hP hRange hUnion
      have hRows' := range_union_exact hM.1 hP' hRange' hUnion'
      exact hM.1.eq_of_same_members T T' (fun a => (hRows a).trans (hRows' a).symm)

theorem iteration_total_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory) {n : Nat}
    (φ : KP1Y.WitnessMatrix n) (e : Env M (n+1)) (hTotal : Total φ (tailEnv e)) (Γ : M.Domain) :
    KP1Y.SigmaRecursion.Total M Γ ((iterationMatrix φ).denote e) := by
  intro i _ P V hP
  obtain ⟨T,w,hStep⟩ := step_total_d hM φ e hTotal hP
  exact ⟨T,w,(iterationMatrix_iff hM φ e i P T w).mpr hStep⟩

theorem iteration_functional_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory) {n : Nat}
    (φ : KP1Y.WitnessMatrix n) (e : Env M (n+1)) (hFun : Functional φ (tailEnv e)) {Γ : M.Domain} (hΓ : M.IsOrdinal Γ) :
    KP1Y.SigmaRecursion.Functional M Γ ((iterationMatrix φ).denote e) := by
  intro i hi P T T' w w' h h'
  exact step_unique_d hM φ e hFun (hΓ.mem hi)
    ((iterationMatrix_iff hM φ e i P T w).mp h) ((iterationMatrix_iff hM φ e i P T' w').mp h')

theorem iteration_history_exists_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory) {n : Nat}
    (φ : KP1Y.WitnessMatrix n) (e : Env M (n+1)) (hTotal : Total φ (tailEnv e)) (hFun : Functional φ (tailEnv e))
    {Γ : M.Domain} (hΓ : M.IsOrdinal Γ) :
    ∃ H V Q, KP1Y.SigmaRecursion.ValueHistory M ((iterationMatrix φ).denote e) H Γ V Q :=
  KP1Y.SigmaRecursion.value_recursion_d hM (iterationMatrix φ) e hΓ
    (iteration_total_d hM φ e hTotal Γ) (iteration_functional_d hM φ e hFun hΓ)

end KP1Y.OrdinalIteration
