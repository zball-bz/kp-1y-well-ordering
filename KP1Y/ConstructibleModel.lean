import KP1Y.ConstructibleBounds
import KP1Y.ClassOrdinals

/-! 构造类的实际隶属结构；先核验外延、空集、单条基础及Δ₀／序数绝对性。 -/
namespace KP1Y.Constructible
open YesMetaZFC YesMetaZFC.SetTheory YesMetaZFC.SetTheory.Definitional
open KP1Y.Classes KP1Y.SetLanguage
universe u

theorem constructible_transitive_class_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    (env : Env M 24) (hS : FixedSyntax M (defContext.eval env) (defData.eval env)
      (env.bound 0) (env.bound 1) (env.bound 2)) : TransitiveClass M (InConstructible M env) :=
  fun _ hx _ hy => hx.mem_closed_d hM env hS hy

def innerModel {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    (env : Env M 24) (hS : FixedSyntax M (defContext.eval env) (defData.eval env)
      (env.bound 0) (env.bound 1) (env.bound 2)) : SetTheory.Structure.{u} :=
  classModel M (InConstructible M env) (constructible_nonempty_d hM env hS)

theorem inner_extensional_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    (env : Env M 24) (hS : FixedSyntax M (defContext.eval env) (defData.eval env)
      (env.bound 0) (env.bound 1) (env.bound 2)) : Extensional (innerModel hM env hS) :=
  class_extensional hM.1 (constructible_transitive_class_d hM env hS)

theorem inner_empty_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    (env : Env M 24) (hS : FixedSyntax M (defContext.eval env) (defData.eval env)
      (env.bound 0) (env.bound 1) (env.bound 2)) :
    ∃ e : (innerModel hM env hS).Domain, ∀ x, ¬(innerModel hM env hS).mem x e := by
  obtain ⟨e,he⟩ := SetTheory.KP.exists_empty (KP1Y.models_weakKP hM)
  exact ⟨⟨e,empty_constructible_d hM env hS he⟩,fun x => he x.val⟩

theorem inner_foundation_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    (env : Env M 24) (hS : FixedSyntax M (defContext.eval env) (defData.eval env)
      (env.bound 0) (env.bound 1) (env.bound 2)) (a : (innerModel hM env hS).Domain)
    (hNe : ∃ x, (innerModel hM env hS).mem x a) :
    ∃ x, (innerModel hM env hS).mem x a ∧ ∀ y, (innerModel hM env hS).mem y a → ¬(innerModel hM env hS).mem y x := by
  have hNeM : ∃ x, M.mem x a.val := by
    obtain ⟨x,hx⟩ := hNe
    exact ⟨x.val,hx⟩
  obtain ⟨x,hx,hMin⟩ := KP1Y.foundation_d hM a.val hNeM
  exact ⟨⟨x,a.property.mem_closed_d hM env hS hx⟩,hx,fun y hy => hMin y.val hy⟩

theorem inner_delta0_absolute_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    (env : Env M 24) (hS : FixedSyntax M (defContext.eval env) (defData.eval env)
      (env.bound 0) (env.bound 1) (env.bound 2)) {n : Nat} {φ : Project.Formula 1 n} (hφ : φ.IsDelta0)
    (s : Env (innerModel hM env hS) n) :
    Project.Formula.satisfies s φ ↔ Project.Formula.satisfies (forgetEnv s) φ :=
  delta0_class_absolute (constructible_transitive_class_d hM env hS) hφ s

theorem inner_ordinal_absolute_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    (env : Env M 24) (hS : FixedSyntax M (defContext.eval env) (defData.eval env)
      (env.bound 0) (env.bound 1) (env.bound 2)) (a : (innerModel hM env hS).Domain) :
    (innerModel hM env hS).IsOrdinal a ↔ M.IsOrdinal a.val :=
  class_ordinal_absolute_d hM (constructible_transitive_class_d hM env hS) a

end KP1Y.Constructible
