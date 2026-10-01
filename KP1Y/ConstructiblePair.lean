import KP1Y.ConstructibleInduction
import KP1Y.SetDefPair

/-! 构造类对实际无序对封闭，因而其隶属结构满足配对的语义。 -/
namespace KP1Y.Constructible
open YesMetaZFC YesMetaZFC.SetTheory
open KP1Y.Kuratowski KP1Y.SetLanguage
universe u

theorem constructible_pair_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    (env : Env M 24) (hS : FixedSyntax M (defContext.eval env) (defData.eval env)
      (env.bound 0) (env.bound 1) (env.bound 2)) {x y : M.Domain}
    (hx : InConstructible M env x) (hy : InConstructible M env y) :
    ∃ p, InConstructible M env p ∧ PairSet M p x y := by
  obtain ⟨α,A,hA,hxA,hyA⟩ := constructible_pair_parameters_d hM env hS hx hy
  obtain ⟨β,hs⟩ := SetTheory.KP.exists_successor (KP1Y.models_weakKP hM) α
  have hβ := SetTheory.KP.successor_isOrdinal (KP1Y.models_weakKP hM) hA.ordinal hs
  obtain ⟨T,hT⟩ := is_level_exists_d hM env hS hβ
  obtain ⟨B,hB⟩ := level_successor_d hM env hS hs hA hT
  obtain ⟨W,_,hW⟩ := (defSuccessorMatrix_iff hM env A T B).mp hB
  obtain ⟨p,hp,hPair⟩ := (hW.stage_d hM hS).pair_exists_d hM hxA hyA
  exact ⟨p,⟨β,T,hT,hp⟩,hPair⟩

theorem inner_pair_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    (env : Env M 24) (hS : FixedSyntax M (defContext.eval env) (defData.eval env)
      (env.bound 0) (env.bound 1) (env.bound 2)) (x y : (innerModel hM env hS).Domain) :
    ∃ p, PairSet (innerModel hM env hS) p x y := by
  obtain ⟨p,hp,hPair⟩ := constructible_pair_d hM env hS x.property y.property
  refine ⟨⟨p,hp⟩,?_⟩
  intro z
  constructor
  · intro hz
    rcases (hPair z.val).mp hz with he | he
    · exact Or.inl (Subtype.ext he)
    · exact Or.inr (Subtype.ext he)
  · rintro (he | he)
    · exact (hPair z.val).mpr (Or.inl (congrArg Subtype.val he))
    · exact (hPair z.val).mpr (Or.inr (congrArg Subtype.val he))

end KP1Y.Constructible
