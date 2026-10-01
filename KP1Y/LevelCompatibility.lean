import KP1Y.ConstructibleLevels

/-! 独立层定义与所有历史相容，保留传递性、递归方程及严格层间隶属。 -/
namespace KP1Y.Constructible
open YesMetaZFC YesMetaZFC.SetTheory
open KP1Y.Kuratowski KP1Y.Functions KP1Y.SetLanguage
universe u

theorem level_agrees_with_history_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    (env : Env M 24) (hS : FixedSyntax M (defContext.eval env) (defData.eval env)
      (env.bound 0) (env.bound 1) (env.bound 2)) {Γ H V Q α T : M.Domain} (hΓ : M.IsOrdinal Γ)
    (h : KP1Y.SigmaRecursion.ValueHistory M (levelStepMatrix.denote env) H Γ V Q)
    (hαΓ : M.mem α Γ) (hLevel : IsLevel M env α T) : MemPair M H α T := by
  obtain ⟨U,_,hAt⟩ := h.values.total α hαΓ
  have hU := is_level_from_history_d hM hΓ h hαΓ hAt
  exact (is_level_unique_d hM env hS hU hLevel) ▸ hAt

theorem IsLevel.transitive_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    (env : Env M 24) (hS : FixedSyntax M (defContext.eval env) (defData.eval env)
      (env.bound 0) (env.bound 1) (env.bound 2)) {α T : M.Domain} (h : IsLevel M env α T) : M.TransitiveSet T := by
  obtain ⟨δ,H,V,Q,hs,hH,hAt⟩ := h.history
  have hδ := SetTheory.KP.successor_isOrdinal (KP1Y.models_weakKP hM) h.ordinal hs
  exact (history_transitive_and_cumulative_d hM env hS hδ hH α hs.predecessor_mem T hAt).1

theorem IsLevel.empty_value_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {env : Env M 24} {α T : M.Domain} (h : IsLevel M env α T) (hEmpty : Empty M α) : Empty M T := by
  obtain ⟨_,_,_,_,hs,hH,hAt⟩ := h.history
  exact history_empty_value_d hM hH hs.predecessor_mem hEmpty hAt

theorem level_successor_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    (env : Env M 24) (hS : FixedSyntax M (defContext.eval env) (defData.eval env)
      (env.bound 0) (env.bound 1) (env.bound 2)) {α β A T : M.Domain}
    (hs : M.SuccessorOf β α) (hA : IsLevel M env α A) (hT : IsLevel M env β T) : DefLevel M env A T := by
  obtain ⟨δ,H,V,Q,hδβ,hH,hAt⟩ := hT.history
  have hδ := SetTheory.KP.successor_isOrdinal (KP1Y.models_weakKP hM) hT.ordinal hδβ
  have hαδ := hδ.transitive β hδβ.predecessor_mem α hs.predecessor_mem
  have hPrev := level_agrees_with_history_d hM env hS hδ hH hαδ hA
  exact history_successor_value_d hM hδ hH hδβ.predecessor_mem hs hAt hPrev

theorem level_subset_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    (env : Env M 24) (hS : FixedSyntax M (defContext.eval env) (defData.eval env)
      (env.bound 0) (env.bound 1) (env.bound 2)) {α β A T : M.Domain}
    (hA : IsLevel M env α A) (hT : IsLevel M env β T) (hαβ : M.mem α β) : M.MemberSubset A T := by
  obtain ⟨δ,H,V,Q,hδβ,hH,hAt⟩ := hT.history
  have hδ := SetTheory.KP.successor_isOrdinal (KP1Y.models_weakKP hM) hT.ordinal hδβ
  have hαδ := hδ.transitive β hδβ.predecessor_mem α hαβ
  have hPrev := level_agrees_with_history_d hM env hS hδ hH hαδ hA
  exact (history_transitive_and_cumulative_d hM env hS hδ hH β hδβ.predecessor_mem T hAt).2 α hαβ A hPrev

theorem level_subset_of_ordinal_subset_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    (env : Env M 24) (hS : FixedSyntax M (defContext.eval env) (defData.eval env)
      (env.bound 0) (env.bound 1) (env.bound 2)) {α β A T : M.Domain}
    (hA : IsLevel M env α A) (hT : IsLevel M env β T) (hαβ : M.MemberSubset α β) : M.MemberSubset A T := by
  rcases KP1Y.Naturals.ordinal_subset_cases_d hM hA.ordinal hT.ordinal hαβ with he | hLess
  · subst β
    have hAT := is_level_unique_d hM env hS hA hT
    exact fun x hx => hAT ▸ hx
  · exact level_subset_d hM env hS hA hT hLess

theorem level_member_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    (env : Env M 24) (hS : FixedSyntax M (defContext.eval env) (defData.eval env)
      (env.bound 0) (env.bound 1) (env.bound 2)) {α β A T : M.Domain}
    (hA : IsLevel M env α A) (hT : IsLevel M env β T) (hαβ : M.mem α β) : M.mem A T := by
  obtain ⟨δ,hs⟩ := SetTheory.KP.exists_successor (KP1Y.models_weakKP hM) α
  have hδ := SetTheory.KP.successor_isOrdinal (KP1Y.models_weakKP hM) hA.ordinal hs
  obtain ⟨U,hU⟩ := is_level_exists_d hM env hS hδ
  have hAU := ((level_successor_d hM env hS hs hA hU).properties_d hM env hS).1
  have hδβ : M.MemberSubset δ β := by
    intro x hx
    rcases (hs x).mp hx with hx | hSame
    · exact hT.ordinal.transitive α hαβ x hx
    · exact (hM.1.eq_of_same_members x α hSame) ▸ hαβ
  exact level_subset_of_ordinal_subset_d hM env hS hU hT hδβ A hAU

theorem level_limit_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    (env : Env M 24) (hS : FixedSyntax M (defContext.eval env) (defData.eval env)
      (env.bound 0) (env.bound 1) (env.bound 2)) {β T : M.Domain} (hβ : M.IsLimitOrdinal β)
    (hT : IsLevel M env β T) :
    ∀ x, M.mem x T ↔ ∃ α, M.mem α β ∧ ∃ A, IsLevel M env α A ∧ M.mem x A := by
  obtain ⟨δ,H,V,Q,hδβ,hH,hAt⟩ := hT.history
  have hδ := SetTheory.KP.successor_isOrdinal (KP1Y.models_weakKP hM) hβ.1 hδβ
  have hUnion := history_limit_value_d hM hH hδβ.predecessor_mem hβ hAt
  intro x
  constructor
  · intro hx
    obtain ⟨α,hαβ,A,hA,hxA⟩ := (hUnion x).mp hx
    have hαδ := hδ.transitive β hδβ.predecessor_mem α hαβ
    exact ⟨α,hαβ,A,is_level_from_history_d hM hδ hH hαδ hA,hxA⟩
  · rintro ⟨α,hαβ,A,hA,hxA⟩
    have hαδ := hδ.transitive β hδβ.predecessor_mem α hαβ
    exact (hUnion x).mpr ⟨α,hαβ,A,level_agrees_with_history_d hM env hS hδ hH hαδ hA,hxA⟩

end KP1Y.Constructible
