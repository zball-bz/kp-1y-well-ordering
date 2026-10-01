import KP1Y.ClassBoundedTruth
import KP1Y.Product
import KP1Y.NaturalNumbers

/-! 传递类中空对象、后继与归纳集绝对；若ω属于类，则原ω也是类内的最小归纳集。 -/
namespace KP1Y.Classes
open YesMetaZFC YesMetaZFC.SetTheory YesMetaZFC.SetTheory.Definitional
open KP1Y.Kuratowski KP1Y.Bounded
universe u

theorem empty_class_absolute {M : SetTheory.Structure.{u}} {P : M.Domain → Prop} {hNe : ∃ x, P x}
    (hP : TransitiveClass M P) (a : (classModel M P hNe).Domain) :
    (∀ x, ¬(classModel M P hNe).mem x a) ↔ (∀ x, ¬M.mem x a.val) := by
  constructor
  · intro h x hx
    exact h ⟨x,hP a.val a.property x hx⟩ hx
  · intro h x hx
    exact h x.val hx

theorem successor_class_absolute {M : SetTheory.Structure.{u}} (he : Extensional M)
    {P : M.Domain → Prop} {hNe : ∃ x, P x} (hP : TransitiveClass M P)
    (a b : (classModel M P hNe).Domain) :
    (classModel M P hNe).SuccessorOf a b ↔ M.SuccessorOf a.val b.val := by
  let e := (oneEnv b).push a
  exact (successorFormula_iff (class_extensional he hP) e (.bound 0) (.bound 1)).symm.trans
    ((delta0_class_absolute hP (successorFormula_delta0 (.bound 0) (.bound 1)) e).trans
      (successorFormula_iff he (forgetEnv e) (.bound 0) (.bound 1)))

theorem inductive_class_absolute {M : SetTheory.Structure.{u}} (he : Extensional M)
    {P : M.Domain → Prop} {hNe : ∃ x, P x} (hP : TransitiveClass M P) (I : (classModel M P hNe).Domain) :
    (classModel M P hNe).IsInductive I ↔ M.IsInductive I.val := by
  constructor
  · rintro ⟨⟨z,hEmpty,hzI⟩,hNext⟩
    refine ⟨⟨z.val,(empty_class_absolute hP z).mp hEmpty,hzI⟩,?_⟩
    intro x hx
    let x0 : (classModel M P hNe).Domain := ⟨x,hP I.val I.property x hx⟩
    obtain ⟨y,hs,hyI⟩ := hNext x0 hx
    exact ⟨y.val,(successor_class_absolute he hP y x0).mp hs,hyI⟩
  · rintro ⟨⟨z,hEmpty,hzI⟩,hNext⟩
    let z0 : (classModel M P hNe).Domain := ⟨z,hP I.val I.property z hzI⟩
    refine ⟨⟨z0,(empty_class_absolute hP z0).mpr hEmpty,hzI⟩,?_⟩
    intro x hx
    obtain ⟨y,hs,hyI⟩ := hNext x.val hx
    let y0 : (classModel M P hNe).Domain := ⟨y,hP I.val I.property y hyI⟩
    exact ⟨y0,(successor_class_absolute he hP y0 x).mpr hs,hyI⟩

theorem omega_into_class {M : SetTheory.Structure.{u}} (he : Extensional M)
    {P : M.Domain → Prop} {hNe : ∃ x, P x} (hP : TransitiveClass M P) (ω : (classModel M P hNe).Domain)
    (hω : M.IsOmega ω.val) : (classModel M P hNe).IsOmega ω := by
  refine ⟨(inductive_class_absolute he hP ω).mpr hω.1,?_⟩
  intro I hI
  exact (subset_absolute hP ω I).mpr (hω.2 I.val ((inductive_class_absolute he hP I).mp hI))

end KP1Y.Classes
