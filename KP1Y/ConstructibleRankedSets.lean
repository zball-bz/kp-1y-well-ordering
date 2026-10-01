import KP1Y.RankedHistoryComparison
import KP1Y.ConstructibleClass
import KP1Y.CanonicalProgramRank

/-! 每个实际构造层和构造集合拥有对象序数排名；程序排名仅作为全层递归的一个固定参数。 -/
namespace KP1Y.ConstructibleRank
open YesMetaZFC YesMetaZFC.SetTheory YesMetaZFC.SetTheory.Definitional
open KP1Y.Kuratowski KP1Y.Functions KP1Y.Ranking KP1Y.SetLanguage KP1Y.Constructible
universe u

theorem is_level_ranked_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    (env : Env M 24) (hS : FixedSyntax M (defContext.eval env) (defData.eval env) (env.bound 0) (env.bound 1) (env.bound 2))
    {FP π α T : M.Domain} (hP : OrdinalRank M FP (defContext.eval env).programs π) (hLevel : IsLevel M env α T) :
    ∃ Γ R, OrdinalRank M R T Γ := by
  obtain ⟨δ,G,U,Q',hs,hG,hAt⟩ := hLevel.history
  have hδ := SetTheory.KP.successor_isOrdinal (KP1Y.models_weakKP hM) hLevel.ordinal hs
  let e : Env M 26 := (env.push π).push FP
  obtain ⟨H,V,Q,hH⟩ := ranked_history_exists_d hM e hS hP hδ
  have hG' : KP1Y.SigmaRecursion.ValueHistory M (levelStepMatrix.denote (baseEnv e)) G δ U Q' := by
    simpa only [e,baseEnv_extend] using hG
  obtain ⟨Out,_,hOut⟩ := hH.values.total α hs.predecessor_mem
  obtain ⟨Γ,R,hPacket⟩ := ranked_history_carriers_d hM e hS hP hδ hH hG' α Out T hOut hAt
  have hGood := ranked_history_family_d hM e hS hP hH
  exact ⟨Γ,R,(hGood.ranked α Out hOut).rank hM.1 hPacket⟩

theorem rank_subset_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory) {F A Γ X : M.Domain}
    (hRank : OrdinalRank M F A Γ) (hSub : M.MemberSubset X A) : ∃ R, OrdinalRank M R X Γ := by
  obtain ⟨R,hR,hRows⟩ := restrict_graph_d hM hRank.graph hSub
  refine ⟨R,hRank.ordinal,hR,?_⟩
  intro x y a hxa hya
  exact hRank.injective x y a ((hRows x a).mp hxa).2 ((hRows y a).mp hya).2

theorem constructible_set_ranked_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    (env : Env M 24) (hS : FixedSyntax M (defContext.eval env) (defData.eval env) (env.bound 0) (env.bound 1) (env.bound 2))
    {FP π X : M.Domain} (hP : OrdinalRank M FP (defContext.eval env).programs π) (hX : InConstructible M env X) :
    ∃ Γ R, OrdinalRank M R X Γ := by
  obtain ⟨α,T,hT,hXT⟩ := hX
  obtain ⟨Γ,F,hF⟩ := is_level_ranked_d hM env hS hP hT
  obtain ⟨R,hR⟩ := rank_subset_d hM hF (hT.transitive_d hM env hS X hXT)
  exact ⟨Γ,R,hR⟩

theorem canonical_constructible_ranked_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    (env : Env M 24) (hS : CanonicalSyntax M (defContext.eval env) (defData.eval env) (env.bound 0) (env.bound 1) (env.bound 2))
    {X : M.Domain} (hX : InConstructible M env X) : ∃ Γ R, OrdinalRank M R X Γ := by
  obtain ⟨FP,hP⟩ := canonical_program_rank_d hM hS
  exact constructible_set_ranked_d hM env hS.toFixedSyntax hP hX

theorem vl_set_ranked_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    (env : Env M 24) (hS : CanonicalSyntax M (defContext.eval env) (defData.eval env) (env.bound 0) (env.bound 1) (env.bound 2))
    (hVL : ∀ X, InConstructible M env X) (X : M.Domain) : ∃ Γ R, OrdinalRank M R X Γ :=
  canonical_constructible_ranked_d hM env hS (hVL X)

theorem vl_set_wellordered_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    (env : Env M 24) (hS : CanonicalSyntax M (defContext.eval env) (defData.eval env) (env.bound 0) (env.bound 1) (env.bound 2))
    (hVL : ∀ X, InConstructible M env X) (X : M.Domain) : ∃ R, KP1Y.InternalWellOrder M R X := by
  obtain ⟨Γ,F,hRank⟩ := vl_set_ranked_d hM env hS hVL X
  obtain ⟨R,hR,_⟩ := ordinal_rank_wellorder_d hM hRank
  exact ⟨R,hR⟩

end KP1Y.ConstructibleRank
