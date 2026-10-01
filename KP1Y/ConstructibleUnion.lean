import KP1Y.ConstructiblePair
import KP1Y.SetDefUnion

/-! 构造类对实际并集封闭，恢复其隶属结构中的并集语义。 -/
namespace KP1Y.Constructible
open YesMetaZFC YesMetaZFC.SetTheory
open KP1Y.SetLanguage
universe u

theorem constructible_union_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    (env : Env M 24) (hS : FixedSyntax M (defContext.eval env) (defData.eval env)
      (env.bound 0) (env.bound 1) (env.bound 2)) {a : M.Domain} (ha : InConstructible M env a) :
    ∃ u, InConstructible M env u ∧ M.IsUnionOf u a := by
  obtain ⟨α,A,hA,haA⟩ := ha
  obtain ⟨β,hs⟩ := SetTheory.KP.exists_successor (KP1Y.models_weakKP hM) α
  have hβ := SetTheory.KP.successor_isOrdinal (KP1Y.models_weakKP hM) hA.ordinal hs
  obtain ⟨T,hT⟩ := is_level_exists_d hM env hS hβ
  obtain ⟨B,hB⟩ := level_successor_d hM env hS hs hA hT
  obtain ⟨W,_,hW⟩ := (defSuccessorMatrix_iff hM env A T B).mp hB
  obtain ⟨u,hu,hUnion⟩ := (hW.stage_d hM hS).union_exists_d hM (hA.transitive_d hM env hS) haA
  exact ⟨u,⟨β,T,hT,hu⟩,hUnion⟩

theorem inner_union_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    (env : Env M 24) (hS : FixedSyntax M (defContext.eval env) (defData.eval env)
      (env.bound 0) (env.bound 1) (env.bound 2)) (a : (innerModel hM env hS).Domain) :
    ∃ u, (innerModel hM env hS).IsUnionOf u a := by
  obtain ⟨u,hu,hUnion⟩ := constructible_union_d hM env hS a.property
  refine ⟨⟨u,hu⟩,?_⟩
  intro x
  constructor
  · intro hx
    obtain ⟨b,hba,hxb⟩ := (hUnion x.val).mp hx
    exact ⟨⟨b,a.property.mem_closed_d hM env hS hba⟩,hba,hxb⟩
  · rintro ⟨b,hba,hxb⟩
    exact (hUnion x.val).mpr ⟨b.val,hba,hxb⟩

end KP1Y.Constructible
