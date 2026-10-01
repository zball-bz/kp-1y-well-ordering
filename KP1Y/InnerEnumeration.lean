import KP1Y.ConstructibleEnumeration
import KP1Y.ClassCountability

/-! 从原KP模型的不可数序数ν进入同ω构造内模型，并得到κ≤ν及全部正初段的实际统一枚举。 -/
namespace KP1Y.Constructible
open YesMetaZFC YesMetaZFC.SetTheory YesMetaZFC.SetTheory.Definitional
open KP1Y.Classes KP1Y.SetLanguage KP1Y.Cardinal KP1Y.Closure
universe u

theorem inner_least_uncountable_enumeration_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory) (env : Env M 24)
    (h : CanonicalSyntax M (defContext.eval env) (defData.eval env) (env.bound 0) (env.bound 1) (env.bound 2))
    {ω ν : M.Domain} (hω : M.IsOmega ω) (hν : UncountableOrdinal M ω ν) :
    ∃ w κ Keys E : (innerModel hM env h.toFixedSyntax).Domain,
      w.val=ω ∧ (innerModel hM env h.toFixedSyntax).IsOmega w ∧
      UncountableOrdinal (innerModel hM env h.toFixedSyntax) w κ ∧ (κ.val=ν ∨ M.mem κ.val ν) ∧
      (∀ β, UncountableOrdinal (innerModel hM env h.toFixedSyntax) w β → κ=β ∨ (innerModel hM env h.toFixedSyntax).mem κ β) ∧
      UniformEnumeration (innerModel hM env h.toFixedSyntax) w κ Keys E := by
  obtain ⟨w,hwVal,hw⟩ := inner_omega_exists_d hM env h.toFixedSyntax hω
  obtain ⟨v,hvVal,_⟩ := inner_ordinals_cover_d hM env h.toFixedSyntax hν.1
  have hν' : UncountableOrdinal M w.val v.val := by
    rw [hwVal,hvVal]
    exact hν
  have hInnerν := uncountable_into_class hM.1 (constructible_transitive_class_d hM env h.toFixedSyntax) w v hν'
  obtain ⟨κ,Keys,E,hκ,hκv,hLeast,hE⟩ := KP1Y.ConstructibleRank.vl_least_uncountable_enumeration_d
    (inner_models_kp_d hM env h.toFixedSyntax) (canonicalInnerEnv hM env h)
    (canonical_inner_syntax_d hM env h) (inner_v_equals_l_d hM env h) hw hInnerν
  refine ⟨w,κ,Keys,E,hwVal,hw,hκ,?_,hLeast,hE⟩
  rcases hκv with he | hMem
  · exact Or.inl ((congrArg Subtype.val he).trans hvVal)
  · exact Or.inr (Eq.mp (congrArg (M.mem κ.val) hvVal) hMem)

end KP1Y.Constructible
