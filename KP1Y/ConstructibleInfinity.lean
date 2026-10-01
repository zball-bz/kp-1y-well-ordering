import KP1Y.ConstructibleCollection
import KP1Y.ConstructibleOrdinalContent
import KP1Y.ClassInductiveSets

/-! 所有序数已进入构造类，故同一个ω对象进入类并满足类内最小归纳集和无穷公理。 -/
namespace KP1Y.Constructible
open YesMetaZFC YesMetaZFC.SetTheory YesMetaZFC.SetTheory.Definitional
open KP1Y.Classes KP1Y.SetLanguage
universe u

theorem inner_omega_exists_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    (env : Env M 24) (hS : FixedSyntax M (defContext.eval env) (defData.eval env)
      (env.bound 0) (env.bound 1) (env.bound 2)) {ω : M.Domain} (hω : M.IsOmega ω) :
    ∃ w : (innerModel hM env hS).Domain, w.val=ω ∧ (innerModel hM env hS).IsOmega w := by
  have hωL := ordinal_constructible_d hM env hS (KP1Y.Naturals.omega_isOrdinal_d hM hω)
  let w : (innerModel hM env hS).Domain := ⟨ω,hωL⟩
  exact ⟨w,rfl,omega_into_class hM.1 (constructible_transitive_class_d hM env hS) w hω⟩

theorem inner_omega_absolute_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    (env : Env M 24) (hS : FixedSyntax M (defContext.eval env) (defData.eval env)
      (env.bound 0) (env.bound 1) (env.bound 2)) (w : (innerModel hM env hS).Domain) :
    (innerModel hM env hS).IsOmega w ↔ M.IsOmega w.val := by
  constructor
  · intro hw
    obtain ⟨w0,hValue,hw0⟩ := inner_omega_exists_d hM env hS hS.spaces.omega
    have hEq := KP1Y.Naturals.omega_unique (inner_extensional_d hM env hS) hw hw0
    have hVal := (congrArg Subtype.val hEq).trans hValue
    rw [hVal]
    exact hS.spaces.omega
  · exact omega_into_class hM.1 (constructible_transitive_class_d hM env hS) w

theorem inner_infinity_axiom_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    (env : Env M 24) (hS : FixedSyntax M (defContext.eval env) (defData.eval env)
      (env.bound 0) (env.bound 1) (env.bound 2)) (free : FreeVarId → (innerModel hM env hS).Domain) :
    Project.Formula.satisfies ({bound := Fin.elim0,free := free} : Env (innerModel hM env hS) 0) Axioms.infinity.formula := by
  obtain ⟨w,_,hw⟩ := inner_omega_exists_d hM env hS hS.spaces.omega
  exact (Axioms.satisfies_infinity_iff free).mpr ⟨w,hw.1⟩

end KP1Y.Constructible
