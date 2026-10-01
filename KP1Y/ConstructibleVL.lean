import KP1Y.CanonicalSyntaxInside

/-! 规范参数下内外每一层相同，构造类因而在内部满足V=L的实际公式。 -/
namespace KP1Y.Constructible
open YesMetaZFC YesMetaZFC.SetTheory YesMetaZFC.SetTheory.Definitional
open KP1Y.Classes KP1Y.SetLanguage
universe u

theorem level_from_class_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {P : M.Domain → Prop} {hNe : ∃ x, P x} (hP : TransitiveClass M P) (hInner : (classModel M P hNe).Models KP1Y.theory)
    (s : Env (classModel M P hNe) 24) (env : Env M 24) (hBound : ∀ i, (s.bound i).val=env.bound i)
    (α T : (classModel M P hNe).Domain) (hLevel : IsLevel (classModel M P hNe) s α T) : IsLevel M env α.val T.val := by
  obtain ⟨B,hB⟩ := hLevel
  have hInnerCert := (levelCertificateMatrix_iff hInner s α T B).mpr hB
  have hOuterCert := (witness_matrix_transfer_iff hP levelCertificateMatrix s env hBound α T B).mp hInnerCert
  exact ⟨B.val,(levelCertificateMatrix_iff hM env α.val T.val B.val).mp hOuterCert⟩

theorem canonical_level_absolute_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory) (env : Env M 24)
    (h : CanonicalSyntax M (defContext.eval env) (defData.eval env) (env.bound 0) (env.bound 1) (env.bound 2))
    (α T : (innerModel hM env h.toFixedSyntax).Domain) :
    IsLevel (innerModel hM env h.toFixedSyntax) (canonicalInnerEnv hM env h) α T ↔ IsLevel M env α.val T.val := by
  have hInner := inner_models_kp_d hM env h.toFixedSyntax
  have hP := constructible_transitive_class_d hM env h.toFixedSyntax
  constructor
  · exact level_from_class_d hM hP hInner (canonicalInnerEnv hM env h) env (canonicalInnerEnv_values hM env h) α T
  · intro hLevel
    have hα := (inner_ordinal_absolute_d hM env h.toFixedSyntax α).mpr hLevel.ordinal
    obtain ⟨T',hT'⟩ := is_level_exists_d hInner (canonicalInnerEnv hM env h) (canonical_inner_fixed_syntax_d hM env h) hα
    have hUp := level_from_class_d hM hP hInner (canonicalInnerEnv hM env h) env (canonicalInnerEnv_values hM env h) α T' hT'
    have hEq : T=T' := Subtype.ext (is_level_unique_d hM env h.toFixedSyntax hLevel hUp)
    rw [hEq]
    exact hT'

theorem inner_v_equals_l_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory) (env : Env M 24)
    (h : CanonicalSyntax M (defContext.eval env) (defData.eval env) (env.bound 0) (env.bound 1) (env.bound 2)) :
    ∀ x : (innerModel hM env h.toFixedSyntax).Domain,
      InConstructible (innerModel hM env h.toFixedSyntax) (canonicalInnerEnv hM env h) x := by
  intro x
  obtain ⟨α,T,hT,hxT⟩ := x.property
  let α0 : (innerModel hM env h.toFixedSyntax).Domain := ⟨α,ordinal_constructible_d hM env h.toFixedSyntax hT.ordinal⟩
  let T0 : (innerModel hM env h.toFixedSyntax).Domain := ⟨T,hT.constructible_d hM env h.toFixedSyntax⟩
  exact ⟨α0,T0,(canonical_level_absolute_d hM env h α0 T0).mpr hT,hxT⟩

def vEqualsLCore : Project.Formula 1 24 := .forallE constructibleSchema.body

theorem vEqualsLCore_freeClosed : vEqualsLCore.FreeClosed := by
  simpa only [vEqualsLCore,Definitional.Formula.FreeClosed] using constructibleSchema.freeClosed

theorem vEqualsLCore_iff {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory) (env : Env M 24) :
    Project.Formula.satisfies env vEqualsLCore ↔ ∀ x, InConstructible M env x := by
  simp only [vEqualsLCore,Project.Formula.satisfies_forall_iff,constructibleSchema_iff hM]

theorem inner_v_equals_l_formula_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory) (env : Env M 24)
    (h : CanonicalSyntax M (defContext.eval env) (defData.eval env) (env.bound 0) (env.bound 1) (env.bound 2)) :
    Project.Formula.satisfies (canonicalInnerEnv hM env h) vEqualsLCore :=
  (vEqualsLCore_iff (inner_models_kp_d hM env h.toFixedSyntax) (canonicalInnerEnv hM env h)).mpr (inner_v_equals_l_d hM env h)

end KP1Y.Constructible
