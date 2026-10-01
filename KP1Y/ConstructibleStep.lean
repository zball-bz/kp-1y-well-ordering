import KP1Y.ConstructibleStepSyntax

/-! L一步矩阵对任意函数历史全定义，并在序数阶段输出唯一。 -/
namespace KP1Y.Constructible
open YesMetaZFC YesMetaZFC.SetTheory
open KP1Y.Kuratowski KP1Y.Functions KP1Y.Sequences KP1Y.SetLanguage
universe u

def RangeUnion (M : SetTheory.Structure.{u}) (T P i : M.Domain) : Prop :=
  ∀ x, M.mem x T ↔ ∃ j, M.mem j i ∧ ∃ A, MemPair M P j A ∧ M.mem x A

theorem range_union_of_certificate {M : SetTheory.Structure.{u}} (he : Extensional M)
    {T D V P i : M.Domain} (hP : Graph M P i V) (hRange : RangeBound M D V P i)
    (hUnion : ∀ x, M.mem x T ↔ ∃ A, M.mem A D ∧ M.mem x A) : RangeUnion M T P i := by
  intro x
  constructor
  · intro hx
    obtain ⟨A,hA,hxA⟩ := (hUnion x).mp hx
    obtain ⟨j,hj,hAt⟩ := (hRange.exact he hP A).mp hA
    exact ⟨j,hj,A,hAt,hxA⟩
  · rintro ⟨j,hj,A,hAt,hxA⟩
    exact (hUnion x).mpr ⟨A,(hRange.exact he hP A).mpr ⟨j,hj,hAt⟩,hxA⟩

theorem level_step_total_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    (env : Env M 24) (hS : FixedSyntax M (defContext.eval env) (defData.eval env)
      (env.bound 0) (env.bound 1) (env.bound 2)) {i P V : M.Domain} (hP : Graph M P i V) :
    ∃ T w, LevelStep M env i P T w := by
  classical
  by_cases hEmpty : Empty M i
  · obtain ⟨w,hw⟩ := SetTheory.KP.exists_pair (KP1Y.models_weakKP hM) V V
    exact ⟨i,w,V,(hw V).mpr (Or.inl rfl),hP,Or.inl ⟨hEmpty,hEmpty⟩⟩
  · by_cases hSucc : ∃ p, M.mem p i ∧ M.SuccessorOf i p
    · obtain ⟨p,hp,hs⟩ := hSucc
      obtain ⟨A,hA,hAt⟩ := hP.total p hp
      obtain ⟨T,B,hDef⟩ := def_successor_matrix_total_d hM env hS A
      obtain ⟨w,hw⟩ := SetTheory.KP.exists_pair (KP1Y.models_weakKP hM) V B
      exact ⟨T,w,V,(hw V).mpr (Or.inl rfl),hP,
        Or.inr (Or.inl ⟨p,hp,A,hA,B,(hw B).mpr (Or.inr rfl),hs,hAt,hDef⟩)⟩
    · obtain ⟨D,hD⟩ := range_bound_exists_d hM V P i
      obtain ⟨T,hT⟩ := SetTheory.KP.exists_union (KP1Y.models_weakKP hM) D
      obtain ⟨w,hw⟩ := SetTheory.KP.exists_pair (KP1Y.models_weakKP hM) V D
      exact ⟨T,w,V,(hw V).mpr (Or.inl rfl),hP,
        Or.inr (Or.inr ⟨⟨hEmpty,fun p hp hs => hSucc ⟨p,hp,hs⟩⟩,D,(hw D).mpr (Or.inr rfl),hD,hT⟩)⟩

theorem level_step_unique_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    (env : Env M 24) (hS : FixedSyntax M (defContext.eval env) (defData.eval env)
      (env.bound 0) (env.bound 1) (env.bound 2)) {i P T T' w w' : M.Domain} (hi : M.IsOrdinal i)
    (h : LevelStep M env i P T w) (h' : LevelStep M env i P T' w') : T=T' := by
  obtain ⟨V,_,hP,hCases⟩ := h
  obtain ⟨V',_,hP',hCases'⟩ := h'
  rcases hCases with ⟨hEmpty,hT⟩ | ⟨p,hp,A,_,B,_,hs,hAt,hDef⟩ | ⟨⟨hNonempty,hNoPred⟩,D,_,hRange,hUnion⟩
  · rcases hCases' with ⟨_,hT'⟩ | ⟨p,hp,_,_,_,_,_,_,_⟩ | ⟨⟨hNonempty,_⟩,_,_,_,_⟩
    · exact hM.1.eq_of_same_members T T' (fun x => iff_of_false (hT x) (hT' x))
    · exact False.elim (hEmpty p hp)
    · exact False.elim (hNonempty hEmpty)
  · rcases hCases' with ⟨hEmpty,_⟩ | ⟨p',_,A',_,B',_,hs',hAt',hDef'⟩ | ⟨⟨_,hNoPred⟩,_,_,_,_⟩
    · exact False.elim (hEmpty p hp)
    · have hpp' := Structure.SuccessorOf.predecessor_eq hM.1 (hi.mem hp) hs hs'
      subst p'
      have hAA' := hP.unique p A A' hAt hAt'
      subst A'
      exact def_successor_matrix_functional_d hM env hS hDef hDef'
    · exact False.elim (hNoPred p hp hs)
  · rcases hCases' with ⟨hEmpty,_⟩ | ⟨p,hp,_,_,_,_,hs,_,_⟩ | ⟨_,D',_,hRange',hUnion'⟩
    · exact False.elim (hNonempty hEmpty)
    · exact False.elim (hNoPred p hp hs)
    · have hRows := range_union_of_certificate hM.1 hP hRange hUnion
      have hRows' := range_union_of_certificate hM.1 hP' hRange' hUnion'
      exact hM.1.eq_of_same_members T T' (fun x => (hRows x).trans (hRows' x).symm)

theorem level_step_matrix_total_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    (env : Env M 24) (hS : FixedSyntax M (defContext.eval env) (defData.eval env)
      (env.bound 0) (env.bound 1) (env.bound 2)) (Γ : M.Domain) :
    KP1Y.SigmaRecursion.Total M Γ (levelStepMatrix.denote env) := by
  intro i _ P V hP
  obtain ⟨T,w,h⟩ := level_step_total_d hM env hS hP
  exact ⟨T,w,(levelStepMatrix_iff hM env i P T w).mpr h⟩

theorem level_step_matrix_functional_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    (env : Env M 24) (hS : FixedSyntax M (defContext.eval env) (defData.eval env)
      (env.bound 0) (env.bound 1) (env.bound 2)) {Γ : M.Domain} (hΓ : M.IsOrdinal Γ) :
    KP1Y.SigmaRecursion.Functional M Γ (levelStepMatrix.denote env) := by
  intro i hi P T T' w w' h h'
  exact level_step_unique_d hM env hS (hΓ.mem hi)
    ((levelStepMatrix_iff hM env i P T w).mp h) ((levelStepMatrix_iff hM env i P T' w').mp h')

theorem constructible_history_exists_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    (env : Env M 24) (hS : FixedSyntax M (defContext.eval env) (defData.eval env)
      (env.bound 0) (env.bound 1) (env.bound 2)) {Γ : M.Domain} (hΓ : M.IsOrdinal Γ) :
    ∃ H V Q, KP1Y.SigmaRecursion.ValueHistory M (levelStepMatrix.denote env) H Γ V Q :=
  KP1Y.SigmaRecursion.value_recursion_d hM levelStepMatrix env hΓ
    (level_step_matrix_total_d hM env hS Γ) (level_step_matrix_functional_d hM env hS hΓ)

theorem constructible_history_unique_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    (env : Env M 24) (hS : FixedSyntax M (defContext.eval env) (defData.eval env)
      (env.bound 0) (env.bound 1) (env.bound 2)) {Γ : M.Domain} (hΓ : M.IsOrdinal Γ) :
    ∃ H B, KP1Y.SigmaRecursion.Certificate M (levelStepMatrix.denote env) Γ H B ∧
      ∀ J B', KP1Y.SigmaRecursion.Certificate M (levelStepMatrix.denote env) Γ J B' → J=H :=
  KP1Y.SigmaRecursion.sigma_recursion_unique_d hM levelStepMatrix env hΓ
    (level_step_matrix_total_d hM env hS Γ) (level_step_matrix_functional_d hM env hS hΓ)

end KP1Y.Constructible
