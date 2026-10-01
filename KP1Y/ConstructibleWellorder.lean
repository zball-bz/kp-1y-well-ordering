import KP1Y.ConstructibleRankedSets
import KP1Y.ConstructibleVL

/-! 已核验的KP构造内模型中，每个集合实际拥有序数排名及内部良序。 -/
namespace KP1Y.Constructible
open YesMetaZFC YesMetaZFC.SetTheory YesMetaZFC.SetTheory.Definitional
open KP1Y.SetLanguage KP1Y.Ranking KP1Y.ConstructibleRank
universe u

theorem inner_set_ranked_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory) (env : Env M 24)
    (h : CanonicalSyntax M (defContext.eval env) (defData.eval env) (env.bound 0) (env.bound 1) (env.bound 2))
    (X : (innerModel hM env h.toFixedSyntax).Domain) :
    ∃ Γ R, OrdinalRank (innerModel hM env h.toFixedSyntax) R X Γ :=
  vl_set_ranked_d (inner_models_kp_d hM env h.toFixedSyntax) (canonicalInnerEnv hM env h)
    (canonical_inner_syntax_d hM env h) (inner_v_equals_l_d hM env h) X

theorem inner_set_wellordered_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory) (env : Env M 24)
    (h : CanonicalSyntax M (defContext.eval env) (defData.eval env) (env.bound 0) (env.bound 1) (env.bound 2))
    (X : (innerModel hM env h.toFixedSyntax).Domain) :
    ∃ R, KP1Y.InternalWellOrder (innerModel hM env h.toFixedSyntax) R X := by
  obtain ⟨Γ,F,hF⟩ := inner_set_ranked_d hM env h X
  obtain ⟨R,hR,_⟩ := ordinal_rank_wellorder_d (inner_models_kp_d hM env h.toFixedSyntax) hF
  exact ⟨R,hR⟩

end KP1Y.Constructible
