import KP1Y.ConstructibleInfinity

/-! 全部实际KPω公理的装配：构造类结构满足完整集合归纳、Δ₀分离/收集及无穷。 -/
namespace KP1Y.Constructible
open YesMetaZFC YesMetaZFC.SetTheory YesMetaZFC.SetTheory.Definitional
open KP1Y.SetLanguage
universe u

private theorem extensionality_axiom {M : SetTheory.Structure.{u}} (he : Extensional M) (free : FreeVarId → M.Domain) :
    Project.Formula.satisfies ({bound := Fin.elim0,free := free} : Env M 0) Axioms.extensionality.formula := by
  simp only [Axioms.extensionality,Project.Sentence.ofFormula,Project.Formula.satisfies_forall_iff,
    Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_iff_iff,Project.Formula.satisfies_mem_iff,
    Project.Formula.satisfies_extensionalEq_iff_eq he,Definitional.Term.eval,Env.push]
  exact he.eq_of_same_members

theorem inner_models_kp_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    (env : Env M 24) (hS : FixedSyntax M (defContext.eval env) (defData.eval env)
      (env.bound 0) (env.bound 1) (env.bound 2)) : (innerModel hM env hS).Models KP1Y.theory := by
  have he := inner_extensional_d hM env hS
  refine ⟨he,?_⟩
  intro sentence hAx free
  cases hAx with
  | extensionality => exact extensionality_axiom he free
  | emptySet => exact (Axioms.satisfies_emptySet_iff free).mpr (inner_empty_d hM env hS)
  | pairing =>
      apply (Axioms.satisfies_pairing_iff free).mpr
      intro x y
      obtain ⟨p,hP⟩ := inner_pair_d hM env hS x y
      refine ⟨p,?_⟩
      intro z
      constructor
      · intro hz
        rcases (hP z).mp hz with hzx | hzy
        · exact Or.inl (hzx ▸ fun _ => Iff.rfl)
        · exact Or.inr (hzy ▸ fun _ => Iff.rfl)
      · rintro (hSame | hSame)
        · exact (hP z).mpr (Or.inl (he.eq_of_same_members z x hSame))
        · exact (hP z).mpr (Or.inr (he.eq_of_same_members z y hSame))
  | union => exact (Axioms.satisfies_union_iff free).mpr (inner_union_d hM env hS)
  | infinity => exact inner_infinity_axiom_d hM env hS free
  | separation φ => exact inner_separation_axiom_d hM env hS φ free
  | collection φ => exact inner_collection_axiom_d hM env hS φ free
  | setInduction φ => exact inner_setInduction_axiom_d hM env hS φ free

theorem inner_ordinals_cover_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    (env : Env M 24) (hS : FixedSyntax M (defContext.eval env) (defData.eval env)
      (env.bound 0) (env.bound 1) (env.bound 2)) {α : M.Domain} (hα : M.IsOrdinal α) :
    ∃ a : (innerModel hM env hS).Domain, a.val=α ∧ (innerModel hM env hS).IsOrdinal a := by
  let a : (innerModel hM env hS).Domain := ⟨α,ordinal_constructible_d hM env hS hα⟩
  exact ⟨a,rfl,(inner_ordinal_absolute_d hM env hS a).mpr hα⟩

end KP1Y.Constructible
