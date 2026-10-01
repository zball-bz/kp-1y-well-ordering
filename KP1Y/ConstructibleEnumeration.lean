import KP1Y.ConstructibleWellorder
import KP1Y.UniformEnumerationChoice
import KP1Y.CountableSegments

/-! KP+内部V=L实际供给候选集合良序，故最小不可数序数的全局初段枚举无须另加选择前提。 -/
namespace KP1Y.ConstructibleRank
open YesMetaZFC YesMetaZFC.SetTheory YesMetaZFC.SetTheory.Definitional
open KP1Y.Kuratowski KP1Y.Functions KP1Y.SetLanguage KP1Y.Constructible KP1Y.Cardinal KP1Y.Closure
universe u

theorem vl_uniform_enumeration_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    (env : Env M 24) (hS : CanonicalSyntax M (defContext.eval env) (defData.eval env) (env.bound 0) (env.bound 1) (env.bound 2))
    (hVL : ∀ X, InConstructible M env X) {ω κ : M.Domain} (hω : M.IsOmega ω) (hκ : UncountableOrdinal M ω κ)
    (hLeast : ∀ β, UncountableOrdinal M ω β → κ=β ∨ M.mem κ β) : ∃ Keys E, UniformEnumeration M ω κ Keys E := by
  obtain ⟨Candidates,hCandidates⟩ := surjection_witnesses_collected hM hκ hLeast
  obtain ⟨Order,hOrder⟩ := vl_set_wellordered_d hM env hS hVL Candidates
  obtain ⟨zero,_,hZeroNat⟩ := hω.1.1
  have hZeroκ := hκ.1.transitive ω hκ.2.1 zero hZeroNat
  exact uniform_enumeration_from_wellorder_d hM hκ.1 hZeroκ hOrder hCandidates

theorem vl_least_uncountable_enumeration_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    (env : Env M 24) (hS : CanonicalSyntax M (defContext.eval env) (defData.eval env) (env.bound 0) (env.bound 1) (env.bound 2))
    (hVL : ∀ X, InConstructible M env X) {ω ν : M.Domain} (hω : M.IsOmega ω) (hν : UncountableOrdinal M ω ν) :
    ∃ κ Keys E, UncountableOrdinal M ω κ ∧ (κ=ν ∨ M.mem κ ν) ∧
      (∀ β, UncountableOrdinal M ω β → κ=β ∨ M.mem κ β) ∧ UniformEnumeration M ω κ Keys E := by
  obtain ⟨κ,hκ,hκν,hLeast⟩ := least_uncountable_d hM hν
  obtain ⟨Keys,E,hE⟩ := vl_uniform_enumeration_d hM env hS hVL hω hκ hLeast
  exact ⟨κ,Keys,E,hκ,hκν,hLeast,hE⟩

end KP1Y.ConstructibleRank

namespace KP1Y.Constructible
open YesMetaZFC YesMetaZFC.SetTheory YesMetaZFC.SetTheory.Definitional
open KP1Y.SetLanguage KP1Y.Cardinal KP1Y.Closure
universe u

theorem inner_uniform_enumeration_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory) (env : Env M 24)
    (h : CanonicalSyntax M (defContext.eval env) (defData.eval env) (env.bound 0) (env.bound 1) (env.bound 2))
    {ω κ : (innerModel hM env h.toFixedSyntax).Domain} (hω : (innerModel hM env h.toFixedSyntax).IsOmega ω)
    (hκ : UncountableOrdinal (innerModel hM env h.toFixedSyntax) ω κ)
    (hLeast : ∀ β, UncountableOrdinal (innerModel hM env h.toFixedSyntax) ω β →
      κ=β ∨ (innerModel hM env h.toFixedSyntax).mem κ β) :
    ∃ Keys E, UniformEnumeration (innerModel hM env h.toFixedSyntax) ω κ Keys E :=
  KP1Y.ConstructibleRank.vl_uniform_enumeration_d (inner_models_kp_d hM env h.toFixedSyntax)
    (canonicalInnerEnv hM env h) (canonical_inner_syntax_d hM env h) (inner_v_equals_l_d hM env h) hω hκ hLeast

end KP1Y.Constructible
