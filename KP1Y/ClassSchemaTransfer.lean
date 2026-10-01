import KP1Y.ClassBoundedTruth
import KP1Y.ClosedEnvironments
import KP1Y.SigmaOneCollection

/-! 对象模式在传递类内外的参数匹配与Σ₁单值运算闭包；输出由内证书向上绝对后识别。 -/
namespace KP1Y.Classes
open YesMetaZFC YesMetaZFC.SetTheory YesMetaZFC.SetTheory.Definitional
universe u

def liftParameters {M : SetTheory.Structure.{u}} {P : M.Domain → Prop} {hNe : ∃ x, P x} {n : Nat}
    (e : Env M n) (hParams : ∀ i, P (e.bound i)) (default : (classModel M P hNe).Domain) : Env (classModel M P hNe) n :=
  ⟨fun i => ⟨e.bound i,hParams i⟩,fun _ => default⟩

theorem delta0_matched_iff {M : SetTheory.Structure.{u}} {P : M.Domain → Prop} {hNe : ∃ x, P x}
    (hP : TransitiveClass M P) {n : Nat} (φ : Project.Formula 1 n) (hδ : φ.IsDelta0) (hClosed : φ.FreeClosed)
    (s : Env (classModel M P hNe) n) (e : Env M n) (hBound : ∀ i, (s.bound i).val=e.bound i) :
    Project.Formula.satisfies s φ ↔ Project.Formula.satisfies e φ :=
  (delta0_class_absolute hP hδ s).trans (KP1Y.formula_bound_congr φ hClosed (forgetEnv s) e hBound)

theorem unary_matrix_transfer_iff {M : SetTheory.Structure.{u}} {P : M.Domain → Prop} {hNe : ∃ x, P x}
    (hP : TransitiveClass M P) {n : Nat} (φ : Project.Delta0UnarySchema n)
    (s : Env (classModel M P hNe) n) (e : Env M n) (hBound : ∀ i, (s.bound i).val=e.bound i)
    (y : (classModel M P hNe).Domain) :
    Project.Formula.satisfies (s.push y) φ.body ↔ Project.Formula.satisfies (e.push y.val) φ.body := by
  apply delta0_matched_iff hP φ.body φ.delta0 φ.freeClosed
  intro i
  refine Fin.cases ?_ (fun i => ?_) i
  · rfl
  · exact hBound i

theorem witness_matrix_transfer_iff {M : SetTheory.Structure.{u}} {P : M.Domain → Prop} {hNe : ∃ x, P x}
    (hP : TransitiveClass M P) {n : Nat} (φ : KP1Y.WitnessMatrix n)
    (s : Env (classModel M P hNe) n) (e : Env M n) (hBound : ∀ i, (s.bound i).val=e.bound i)
    (x y z : (classModel M P hNe).Domain) :
    Project.Formula.satisfies (((s.push x).push y).push z) φ.body ↔
      Project.Formula.satisfies (((e.push x.val).push y.val).push z.val) φ.body := by
  apply delta0_matched_iff hP φ.body φ.delta0 φ.freeClosed
  intro i
  refine Fin.cases ?_ (fun i => ?_) i
  · rfl
  · refine Fin.cases ?_ (fun i => ?_) i
    · rfl
    · refine Fin.cases ?_ (fun i => ?_) i
      · rfl
      · exact hBound i

theorem binary_matrix_transfer_iff {M : SetTheory.Structure.{u}} {P : M.Domain → Prop} {hNe : ∃ x, P x}
    (hP : TransitiveClass M P) {n : Nat} (φ : Project.Delta0BinarySchema n)
    (s : Env (classModel M P hNe) n) (e : Env M n) (hBound : ∀ i, (s.bound i).val=e.bound i)
    (x y : (classModel M P hNe).Domain) :
    Project.Formula.satisfies ((s.push x).push y) φ.body ↔ Project.Formula.satisfies ((e.push x.val).push y.val) φ.body := by
  apply delta0_matched_iff hP φ.body φ.delta0 φ.freeClosed
  intro i
  refine Fin.cases ?_ (fun i => ?_) i
  · rfl
  · refine Fin.cases ?_ (fun i => ?_) i
    · rfl
    · exact hBound i

theorem delta0_operation_closed {M : SetTheory.Structure.{u}} {P : M.Domain → Prop} {hNe : ∃ x, P x}
    (hP : TransitiveClass M P) {n : Nat} (φ : Project.Delta0UnarySchema n)
    (s : Env (classModel M P hNe) n) (e : Env M n) (hBound : ∀ i, (s.bound i).val=e.bound i)
    {y : M.Domain} (hValue : Project.Formula.satisfies (e.push y) φ.body)
    (hExists : ∃ z, Project.Formula.satisfies (s.push z) φ.body)
    (hUnique : ∀ y z, Project.Formula.satisfies (e.push y) φ.body → Project.Formula.satisfies (e.push z) φ.body → y=z) : P y := by
  obtain ⟨z,hz⟩ := hExists
  have hUp := (unary_matrix_transfer_iff hP φ s e hBound z).mp hz
  have hyz := hUnique y z.val hValue hUp
  rw [hyz]
  exact z.property

theorem sigma_one_operation_closed {M : SetTheory.Structure.{u}} {P : M.Domain → Prop} {hNe : ∃ x, P x}
    (hP : TransitiveClass M P) {n : Nat} (φ : KP1Y.WitnessMatrix n)
    (s : Env (classModel M P hNe) n) (e : Env M n) (hBound : ∀ i, (s.bound i).val=e.bound i)
    (x : (classModel M P hNe).Domain) {y z : M.Domain}
    (hValue : Project.Formula.satisfies (((e.push x.val).push y).push z) φ.body)
    (hExists : ∃ y z, Project.Formula.satisfies (((s.push x).push y).push z) φ.body)
    (hUnique : ∀ y y' z z', Project.Formula.satisfies (((e.push x.val).push y).push z) φ.body →
      Project.Formula.satisfies (((e.push x.val).push y').push z') φ.body → y=y') : P y := by
  obtain ⟨y',z',hInner⟩ := hExists
  have hUp := (witness_matrix_transfer_iff hP φ s e hBound x y' z').mp hInner
  have hEq := hUnique y y'.val z z'.val hValue hUp
  rw [hEq]
  exact y'.property

end KP1Y.Classes
