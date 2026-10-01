import KP1Y.BoundedSets

/-! 任意非空传递类的隶属结构及其与原模型的环境、原子语义对应。 -/
namespace KP1Y.Classes
open YesMetaZFC YesMetaZFC.SetTheory YesMetaZFC.SetTheory.Definitional
universe u

def TransitiveClass (M : SetTheory.Structure.{u}) (P : M.Domain → Prop) : Prop :=
  ∀ x, P x → ∀ y, M.mem y x → P y

def classModel (M : SetTheory.Structure.{u}) (P : M.Domain → Prop) (hNe : ∃ x, P x) : SetTheory.Structure.{u} where
  Domain := {x : M.Domain // P x}
  nonempty := by
    obtain ⟨x,hx⟩ := hNe
    exact ⟨⟨x,hx⟩⟩
  mem x y := M.mem x.val y.val

def forgetEnv {M : SetTheory.Structure.{u}} {P : M.Domain → Prop} {hNe : ∃ x, P x} {n : Nat}
    (env : Env (classModel M P hNe) n) : Env M n := ⟨fun i => (env.bound i).val,fun i => (env.free i).val⟩

theorem forgetEnv_push {M : SetTheory.Structure.{u}} {P : M.Domain → Prop} {hNe : ∃ x, P x} {n : Nat}
    (env : Env (classModel M P hNe) n) (x : (classModel M P hNe).Domain) :
    forgetEnv (env.push x) = (forgetEnv env).push x.val := by
  rw [Env.mk.injEq]
  constructor
  · funext i
    refine Fin.cases ?_ (fun _ => ?_) i <;> rfl
  · rfl

theorem term_value_forget {M : SetTheory.Structure.{u}} {P : M.Domain → Prop} {hNe : ∃ x, P x} {n : Nat}
    (env : Env (classModel M P hNe) n) (t : Project.Term n) : (t.eval env).val = t.eval (forgetEnv env) := by
  cases t <;> rfl

theorem same_members_absolute {M : SetTheory.Structure.{u}} {P : M.Domain → Prop} {hNe : ∃ x, P x}
    (hP : TransitiveClass M P) (x y : (classModel M P hNe).Domain) :
    (classModel M P hNe).SameMembers x y ↔ M.SameMembers x.val y.val := by
  constructor
  · intro h z
    constructor
    · intro hz
      exact (h ⟨z,hP x.val x.property z hz⟩).mp hz
    · intro hz
      exact (h ⟨z,hP y.val y.property z hz⟩).mpr hz
  · intro h z
    exact h z.val

theorem subset_absolute {M : SetTheory.Structure.{u}} {P : M.Domain → Prop} {hNe : ∃ x, P x}
    (hP : TransitiveClass M P) (x y : (classModel M P hNe).Domain) :
    (classModel M P hNe).MemberSubset x y ↔ M.MemberSubset x.val y.val := by
  constructor
  · intro h z hz
    exact h ⟨z,hP x.val x.property z hz⟩ hz
  · intro h z hz
    exact h z.val hz

theorem class_extensional {M : SetTheory.Structure.{u}} (he : Extensional M)
    {P : M.Domain → Prop} {hNe : ∃ x, P x} (hP : TransitiveClass M P) : Extensional (classModel M P hNe) := by
  refine ⟨?_⟩
  intro x y hSame
  apply Subtype.ext
  exact he.eq_of_same_members x.val y.val ((same_members_absolute hP x y).mp hSame)

end KP1Y.Classes
