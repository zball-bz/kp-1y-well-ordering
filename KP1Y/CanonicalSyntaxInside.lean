import KP1Y.CanonicalSyntaxMembers
import KP1Y.ClassContextSpaces

/-! 将全部规范参数作为实际类对象提升，得到内模型可用的同一FixedSyntax。 -/
namespace KP1Y.Classes
open YesMetaZFC YesMetaZFC.SetTheory YesMetaZFC.SetTheory.Definitional
open KP1Y.Satisfaction KP1Y.SetLanguage
universe u

theorem defContext_values_match {M : SetTheory.Structure.{u}} {P : M.Domain → Prop} {hNe : ∃ x, P x}
    (s : Env (classModel M P hNe) 24) (e : Env M 24) (hBound : ∀ i, (s.bound i).val=e.bound i) :
    (defContext.eval s).map Subtype.val=defContext.eval e := by
  simp only [defContext,Context.eval,Context.map,Definitional.Term.eval,hBound]

theorem defData_values_match {M : SetTheory.Structure.{u}} {P : M.Domain → Prop} {hNe : ∃ x, P x}
    (s : Env (classModel M P hNe) 24) (e : Env M 24) (hBound : ∀ i, (s.bound i).val=e.bound i) :
    (defData.eval s).map Subtype.val=defData.eval e := by
  simp only [defData,RelationalData.eval,RelationalData.map,Definitional.Term.eval,hBound]

theorem fixed_syntax_matched_into_class_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {P : M.Domain → Prop} {hNe : ∃ x, P x} (hP : TransitiveClass M P) (hInner : (classModel M P hNe).Models KP1Y.theory)
    (s : Env (classModel M P hNe) 24) (e : Env M 24) (hBound : ∀ i, (s.bound i).val=e.bound i)
    (hS : FixedSyntax M (defContext.eval e) (defData.eval e) (e.bound 0) (e.bound 1) (e.bound 2)) :
    FixedSyntax (classModel M P hNe) (defContext.eval s) (defData.eval s) (s.bound 0) (s.bound 1) (s.bound 2) := by
  apply fixed_syntax_into_class_d hM hP hInner (defContext.eval s) (defData.eval s) (s.bound 0) (s.bound 1) (s.bound 2)
  simpa only [defContext_values_match s e hBound,defData_values_match s e hBound,hBound] using hS

theorem canonical_syntax_into_class_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {P : M.Domain → Prop} {hNe : ∃ x, P x} (hP : TransitiveClass M P) (hInner : (classModel M P hNe).Models KP1Y.theory)
    (C : Context (classModel M P hNe).Domain) (D : RelationalData (classModel M P hNe).Domain)
    (zero one two : (classModel M P hNe).Domain)
    (h : CanonicalSyntax M (C.map Subtype.val) (D.map Subtype.val) zero.val one.val two.val) :
    CanonicalSyntax (classModel M P hNe) C D zero one two :=
  ⟨fixed_syntax_into_class_d hM hP hInner C D zero one two h.toFixedSyntax,
    Subtype.ext h.carrier_omega,fun x => h.operands_exact x.val,
    (relationSupport_class_absolute hM.1 hP D.interpretation D.symbols D.values).mpr h.relation_support,
    Subtype.ext h.atomic_zero⟩

theorem canonical_syntax_matched_into_class_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {P : M.Domain → Prop} {hNe : ∃ x, P x} (hP : TransitiveClass M P) (hInner : (classModel M P hNe).Models KP1Y.theory)
    (s : Env (classModel M P hNe) 24) (e : Env M 24) (hBound : ∀ i, (s.bound i).val=e.bound i)
    (h : CanonicalSyntax M (defContext.eval e) (defData.eval e) (e.bound 0) (e.bound 1) (e.bound 2)) :
    CanonicalSyntax (classModel M P hNe) (defContext.eval s) (defData.eval s) (s.bound 0) (s.bound 1) (s.bound 2) := by
  apply canonical_syntax_into_class_d hM hP hInner (defContext.eval s) (defData.eval s) (s.bound 0) (s.bound 1) (s.bound 2)
  simpa only [defContext_values_match s e hBound,defData_values_match s e hBound,hBound] using h

end KP1Y.Classes

namespace KP1Y.Constructible
open YesMetaZFC YesMetaZFC.SetTheory
open KP1Y.Classes KP1Y.SetLanguage
universe u

def canonicalInnerEnv {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory) (env : Env M 24)
    (h : CanonicalSyntax M (defContext.eval env) (defData.eval env) (env.bound 0) (env.bound 1) (env.bound 2)) :
    Env (innerModel hM env h.toFixedSyntax) 24 :=
  liftParameters env (canonical_parameters_constructible_d hM env h) ⟨env.bound 0,canonical_parameters_constructible_d hM env h 0⟩

theorem canonicalInnerEnv_values {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory) (env : Env M 24)
    (h : CanonicalSyntax M (defContext.eval env) (defData.eval env) (env.bound 0) (env.bound 1) (env.bound 2)) (i : Fin 24) :
    ((canonicalInnerEnv hM env h).bound i).val=env.bound i := rfl

theorem canonical_inner_fixed_syntax_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory) (env : Env M 24)
    (h : CanonicalSyntax M (defContext.eval env) (defData.eval env) (env.bound 0) (env.bound 1) (env.bound 2)) :
    FixedSyntax (innerModel hM env h.toFixedSyntax) (defContext.eval (canonicalInnerEnv hM env h))
      (defData.eval (canonicalInnerEnv hM env h)) ((canonicalInnerEnv hM env h).bound 0)
      ((canonicalInnerEnv hM env h).bound 1) ((canonicalInnerEnv hM env h).bound 2) :=
  fixed_syntax_matched_into_class_d hM (constructible_transitive_class_d hM env h.toFixedSyntax)
    (inner_models_kp_d hM env h.toFixedSyntax) (canonicalInnerEnv hM env h) env
    (canonicalInnerEnv_values hM env h) h.toFixedSyntax

theorem canonical_inner_syntax_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory) (env : Env M 24)
    (h : CanonicalSyntax M (defContext.eval env) (defData.eval env) (env.bound 0) (env.bound 1) (env.bound 2)) :
    CanonicalSyntax (innerModel hM env h.toFixedSyntax) (defContext.eval (canonicalInnerEnv hM env h))
      (defData.eval (canonicalInnerEnv hM env h)) ((canonicalInnerEnv hM env h).bound 0)
      ((canonicalInnerEnv hM env h).bound 1) ((canonicalInnerEnv hM env h).bound 2) :=
  canonical_syntax_matched_into_class_d hM (constructible_transitive_class_d hM env h.toFixedSyntax)
    (inner_models_kp_d hM env h.toFixedSyntax) (canonicalInnerEnv hM env h) env (canonicalInnerEnv_values hM env h) h

theorem canonical_environment_exists_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {ω : M.Domain} (hω : M.IsOmega ω) : ∃ env : Env M 24, (defContext.eval env).omega=ω ∧
      CanonicalSyntax M (defContext.eval env) (defData.eval env) (env.bound 0) (env.bound 1) (env.bound 2) := by
  obtain ⟨C,D,zero,one,two,hOmega,h⟩ := canonical_syntax_exists_d hM hω
  exact ⟨defEnv C D zero one two,hOmega,h⟩

end KP1Y.Constructible
