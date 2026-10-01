import KP1Y.ClassBoundedTruth
import KP1Y.Product

/-! 传递类内外的序数绝对性；向外方向使用原KP模型的基础性，不误移内部良基性。 -/
namespace KP1Y.Classes
open YesMetaZFC YesMetaZFC.SetTheory YesMetaZFC.SetTheory.Definitional
open KP1Y.Bounded KP1Y.Kuratowski
universe u

theorem ordinal_formula_of_ordinal {M : SetTheory.Structure.{u}} (he : Extensional M) {n : Nat}
    (env : Env M n) (t : Project.Term n) (h : M.IsOrdinal (t.eval env)) :
    Project.Formula.satisfies env (ordinalFormula t) := by
  simp only [ordinalFormula,Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_isTransitive_iff,
    Project.Formula.satisfies_forallMem_iff,Project.Formula.satisfies_disj_iff,
    Project.Formula.satisfies_extensionalEq_iff_eq he,Project.Formula.satisfies_mem_iff,Definitional.Term.eval_weaken]
  refine ⟨h.transitive,fun x hx => (h.mem hx).transitive,?_⟩
  intro x hx y hy
  rcases h.wellOrder.linear.compare x hx y hy with hSame | hxy | hyx
  · exact Or.inl (he.eq_of_same_members x y hSame)
  · exact Or.inr (Or.inl hxy)
  · exact Or.inr (Or.inr hyx)

theorem ordinal_into_class {M : SetTheory.Structure.{u}} {P : M.Domain → Prop} {hNe : ∃ x, P x}
    (hP : TransitiveClass M P) (a : (classModel M P hNe).Domain) (ha : M.IsOrdinal a.val) :
    (classModel M P hNe).IsOrdinal a := by
  refine ⟨fun x hx y hy => ha.transitive x.val hx y.val hy,⟨?_,?_⟩⟩
  · refine ⟨fun x hx => ha.wellOrder.linear.irrefl x.val hx,
      fun x hx y hy z hz hxy hyz => ha.wellOrder.linear.trans x.val hx y.val hy z.val hz hxy hyz,?_⟩
    intro x hx y hy
    rcases ha.wellOrder.linear.compare x.val hx y.val hy with hSame | hxy | hyx
    · exact Or.inl ((same_members_absolute hP x y).mpr hSame)
    · exact Or.inr (Or.inl hxy)
    · exact Or.inr (Or.inr hyx)
  · intro S hSub hNonempty
    have hSubM := (subset_absolute hP S a).mp hSub
    have hNonemptyM : ∃ x, M.mem x S.val := by
      obtain ⟨x,hx⟩ := hNonempty
      exact ⟨x.val,hx⟩
    obtain ⟨x,hx,hLeast⟩ := ha.wellOrder.least S.val hSubM hNonemptyM
    let a0 : (classModel M P hNe).Domain := ⟨x,hP S.val S.property x hx⟩
    refine ⟨a0,hx,?_⟩
    intro y hy
    rcases hLeast y.val hy with hSame | hxy
    · exact Or.inl ((same_members_absolute hP a0 y).mpr hSame)
    · exact Or.inr hxy

theorem ordinal_out_of_class_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {P : M.Domain → Prop} {hNe : ∃ x, P x} (hP : TransitiveClass M P)
    (a : (classModel M P hNe).Domain) (ha : (classModel M P hNe).IsOrdinal a) : M.IsOrdinal a.val := by
  have hFormula := ordinal_formula_of_ordinal (class_extensional hM.1 hP) (oneEnv a) (.bound 0) ha
  have hExternal := (delta0_class_absolute hP (ordinalFormula_delta0 (.bound 0)) (oneEnv a)).mp hFormula
  exact (ordinalFormula_iff hM (forgetEnv (oneEnv a)) (.bound 0)).mp hExternal

theorem class_ordinal_absolute_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {P : M.Domain → Prop} {hNe : ∃ x, P x} (hP : TransitiveClass M P) (a : (classModel M P hNe).Domain) :
    (classModel M P hNe).IsOrdinal a ↔ M.IsOrdinal a.val :=
  ⟨ordinal_out_of_class_d hM hP a,ordinal_into_class hP a⟩

end KP1Y.Classes
