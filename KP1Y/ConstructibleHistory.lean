import KP1Y.ConstructibleStep

/-! 从实际历史表恢复L的零、后继、极限方程及Def后继的集合性质。 -/
namespace KP1Y.Constructible
open YesMetaZFC YesMetaZFC.SetTheory YesMetaZFC.SetTheory.Definitional
open KP1Y.Kuratowski KP1Y.Functions KP1Y.SetLanguage
universe u

def DefLevel (M : SetTheory.Structure.{u}) (env : Env M 24) (A T : M.Domain) : Prop :=
  ∃ B, Project.Formula.satisfies (((env.push A).push T).push B) defSuccessorMatrix.body

theorem DefLevel.properties_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    (env : Env M 24) (hS : FixedSyntax M (defContext.eval env) (defData.eval env)
      (env.bound 0) (env.bound 1) (env.bound 2)) {A T : M.Domain} (h : DefLevel M env A T) :
    M.mem A T ∧ (M.TransitiveSet A → M.MemberSubset A T ∧ M.TransitiveSet T) := by
  obtain ⟨B,hB⟩ := h
  obtain ⟨W,_,hW⟩ := (defSuccessorMatrix_iff hM env A T B).mp hB
  have hStage := hW.stage_d hM hS
  exact ⟨hStage.carrier_member_d hM,fun hA => ⟨hStage.carrier_subset_d hM hA,hStage.transitive_d hM hA⟩⟩

theorem no_predecessor_of_limit_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {i : M.Domain} (hi : M.IsLimitOrdinal i) : NoPredecessor M i := by
  intro p hp hs
  obtain ⟨j,hj,hpj⟩ := hi.2.2 p hp
  rcases (hs j).mp hj with hjp | hSame
  · have hSelf := (hi.1.mem hp).transitive j hjp p hpj
    exact SetTheory.KP.mem_irrefl_d (KP1Y.models_weakKP hM) p hSelf
  · have hjp := hM.1.eq_of_same_members j p hSame
    subst j
    exact SetTheory.KP.mem_irrefl_d (KP1Y.models_weakKP hM) p hpj

theorem LevelStep.empty_value {M : SetTheory.Structure.{u}} {env : Env M 24} {i P T w : M.Domain}
    (h : LevelStep M env i P T w) (hi : Empty M i) : Empty M T := by
  obtain ⟨_,_,_,hCases⟩ := h
  rcases hCases with ⟨_,hT⟩ | ⟨p,hp,_,_,_,_,_,_,_⟩ | ⟨⟨hNot,_⟩,_,_,_,_⟩
  · exact hT
  · exact False.elim (hi p hp)
  · exact False.elim (hNot hi)

theorem LevelStep.successor_value_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {env : Env M 24} {i p P T w : M.Domain} (hi : M.IsOrdinal i) (hs : M.SuccessorOf i p)
    (h : LevelStep M env i P T w) : ∃ A, MemPair M P p A ∧ DefLevel M env A T := by
  obtain ⟨_,_,_,hCases⟩ := h
  rcases hCases with ⟨hEmpty,_⟩ | ⟨p',hp',A,_,B,_,hs',hAt,hDef⟩ | ⟨⟨_,hNoPred⟩,_,_,_,_⟩
  · exact False.elim (hEmpty p hs.predecessor_mem)
  · have hpp' := Structure.SuccessorOf.predecessor_eq hM.1 (hi.mem hp') hs' hs
    subst p'
    exact ⟨A,hAt,B,hDef⟩
  · exact False.elim (hNoPred p hs.predecessor_mem hs)

theorem LevelStep.limit_value_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {env : Env M 24} {i P T w : M.Domain} (hi : M.IsLimitOrdinal i) (h : LevelStep M env i P T w) :
    RangeUnion M T P i := by
  obtain ⟨_,_,hP,hCases⟩ := h
  rcases hCases with ⟨hEmpty,_⟩ | ⟨p,hp,_,_,_,_,hs,_,_⟩ | ⟨_,_,_,hRange,hUnion⟩
  · obtain ⟨x,hx⟩ := hi.2.1
    exact False.elim (hEmpty x hx)
  · exact False.elim (no_predecessor_of_limit_d hM hi p hp hs)
  · exact range_union_of_certificate hM.1 hP hRange hUnion

theorem history_step_at_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {env : Env M 24} {H Γ V Q i T : M.Domain}
    (h : KP1Y.SigmaRecursion.ValueHistory M (levelStepMatrix.denote env) H Γ V Q)
    (hi : M.mem i Γ) (hAt : MemPair M H i T) : ∃ P w, Prefix M P H i V ∧ LevelStep M env i P T w := by
  obtain ⟨P,hP,hQAt⟩ := h.prefixes.total i hi
  obtain ⟨hPrefix,w,_,hStep⟩ := h.obeys i hi P hP T (h.values.bounds hM.1 hAt).2 hQAt hAt
  exact ⟨P,w,hPrefix,(levelStepMatrix_iff hM env i P T w).mp hStep⟩

theorem history_empty_value_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {env : Env M 24} {H Γ V Q i T : M.Domain}
    (h : KP1Y.SigmaRecursion.ValueHistory M (levelStepMatrix.denote env) H Γ V Q)
    (hi : M.mem i Γ) (hEmpty : Empty M i) (hAt : MemPair M H i T) : Empty M T := by
  obtain ⟨_,_,_,hStep⟩ := history_step_at_d hM h hi hAt
  exact hStep.empty_value hEmpty

theorem history_successor_value_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {env : Env M 24} {H Γ V Q i p A T : M.Domain} (hΓ : M.IsOrdinal Γ)
    (h : KP1Y.SigmaRecursion.ValueHistory M (levelStepMatrix.denote env) H Γ V Q)
    (hi : M.mem i Γ) (hs : M.SuccessorOf i p) (hAt : MemPair M H i T) (hPrev : MemPair M H p A) :
    DefLevel M env A T := by
  obtain ⟨P,_,hPrefix,hStep⟩ := history_step_at_d hM h hi hAt
  obtain ⟨A',hPAt,hDef⟩ := hStep.successor_value_d hM (hΓ.mem hi) hs
  have hHAt := (hPrefix.all_rows hM.1 h.values p hs.predecessor_mem A').mp hPAt
  have hAA' := h.values.unique p A' A hHAt hPrev
  subst A'
  exact hDef

theorem history_limit_value_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {env : Env M 24} {H Γ V Q i T : M.Domain}
    (h : KP1Y.SigmaRecursion.ValueHistory M (levelStepMatrix.denote env) H Γ V Q)
    (hi : M.mem i Γ) (hLimit : M.IsLimitOrdinal i) (hAt : MemPair M H i T) : RangeUnion M T H i := by
  obtain ⟨P,_,hPrefix,hStep⟩ := history_step_at_d hM h hi hAt
  have hUnion := hStep.limit_value_d hM hLimit
  intro x
  constructor
  · intro hx
    obtain ⟨j,hj,A,hAt,hxA⟩ := (hUnion x).mp hx
    exact ⟨j,hj,A,(hPrefix.all_rows hM.1 h.values j hj A).mp hAt,hxA⟩
  · rintro ⟨j,hj,A,hAt,hxA⟩
    exact (hUnion x).mpr ⟨j,hj,A,(hPrefix.all_rows hM.1 h.values j hj A).mpr hAt,hxA⟩

end KP1Y.Constructible
