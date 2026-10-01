import KP1Y.OrdinalAdditionKP

/-! 乘法以后继x↦x+α连续迭代；完整证书包含空初值和迭代值证书。 -/
namespace KP1Y.Arithmetic
open YesMetaZFC YesMetaZFC.SetTheory YesMetaZFC.SetTheory.Definitional
open KP1Y.Kuratowski KP1Y.Bounded
universe u

private def swapAdditionSlots : Fin 4 → Fin 4 := Fin.cases 0 (Fin.cases 1 (Fin.cases 3 (fun _ => 2)))

def rightAddMatrix : KP1Y.WitnessMatrix 1 where
  body := sumMatrix.body.rename swapAdditionSlots
  freeClosed := by simp [sumMatrix.freeClosed]
  delta0 := KP1Y.delta0_rename sumMatrix.delta0 _

theorem rightAddMatrix_iff {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory) (e : Env M 1) (x y z : M.Domain) :
    KP1Y.OrdinalIteration.Next rightAddMatrix e x y z ↔
      KP1Y.OrdinalIteration.ValueCertificate successorMatrix (oneEnv x) (e.bound 0) y z := by
  rw [KP1Y.OrdinalIteration.Next,rightAddMatrix,Project.Formula.satisfies_rename]
  apply (KP1Y.formula_bound_congr sumMatrix.body sumMatrix.freeClosed _
    ((((oneEnv x).push (e.bound 0)).push y).push z) ?_).trans (sumMatrix_iff hM (oneEnv x) (e.bound 0) y z)
  intro i
  refine Fin.cases ?_ (fun i => ?_) i
  · rfl
  · refine Fin.cases ?_ (fun i => ?_) i
    · rfl
    · refine Fin.cases ?_ (fun i => ?_) i
      · rfl
      · exact Fin.cases rfl (fun i => Fin.elim0 i) i

theorem right_add_total_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory) (e : Env M 1)
    (hα : M.IsOrdinal (e.bound 0)) : KP1Y.OrdinalIteration.Total rightAddMatrix e := by
  intro x
  obtain ⟨y,hy⟩ := sum_exists_d hM x hα
  obtain ⟨z,hz⟩ := hy
  exact ⟨y,z,(rightAddMatrix_iff hM e x y z).mpr hz⟩

theorem right_add_functional_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory) (e : Env M 1) :
    KP1Y.OrdinalIteration.Functional rightAddMatrix e := by
  intro x y y' z z' h h'
  exact sum_unique_d hM ⟨z,(rightAddMatrix_iff hM e x y z).mp h⟩ ⟨z',(rightAddMatrix_iff hM e x y' z').mp h'⟩

theorem right_add_preserves_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory) (e : Env M 1) :
    KP1Y.OrdinalIteration.PreservesOrdinals rightAddMatrix e := by
  intro x hx y z h
  exact Sum.isOrdinal_d hM hx ⟨z,(rightAddMatrix_iff hM e x y z).mp h⟩

theorem right_add_strict_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory) (e : Env M 1)
    (hα : ∃ a, M.mem a (e.bound 0)) : KP1Y.OrdinalIteration.StrictGrowth rightAddMatrix e := by
  intro x hx y z h
  exact sum_base_mem_d hM hx ⟨z,(rightAddMatrix_iff hM e x y z).mp h⟩ hα

def Product (M : SetTheory.Structure.{u}) (α β γ : M.Domain) : Prop :=
  M.IsOrdinal α ∧ ∃ zero, (∀ x, ¬M.mem x zero) ∧ KP1Y.OrdinalIteration.Value rightAddMatrix ((oneEnv α).push zero) β γ

def ProductCertificate (M : SetTheory.Structure.{u}) (α β γ B : M.Domain) : Prop :=
  M.IsOrdinal α ∧ ∃ zero, M.mem zero B ∧ ∃ C, M.mem C B ∧ (∀ x, ¬M.mem x zero) ∧
    KP1Y.OrdinalIteration.ValueCertificate rightAddMatrix ((oneEnv α).push zero) β γ C

private def productValueSlots : Fin 5 → Fin 6 :=
  Fin.cases 0 (Fin.cases 3 (Fin.cases 4 (Fin.cases 1 (fun _ => 5))))

def productMatrix : KP1Y.WitnessMatrix 1 where
  body := .conj (ordinalFormula (.bound 3))
    (Project.Formula.existsMem (.bound 0) (Project.Formula.existsMem (.bound 1)
      (.conj (emptyFormula (.bound 1)) ((KP1Y.OrdinalIteration.valueMatrix rightAddMatrix).body.rename productValueSlots))))
  freeClosed := by
    simp [ordinalFormula,Project.Formula.isTransitive,emptyFormula,Project.Formula.existsMem,Project.Formula.forallMem,
      Definitional.Formula.FreeClosed,(KP1Y.OrdinalIteration.valueMatrix rightAddMatrix).freeClosed]
  delta0 := .conj (ordinalFormula_delta0 _) (.existsMem _ (.existsMem _
    (.conj (emptyFormula_delta0 _) (KP1Y.delta0_rename (KP1Y.OrdinalIteration.valueMatrix rightAddMatrix).delta0 _))))

private theorem productValueSlots_iff {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    (e : Env M 1) (β γ B zero C : M.Domain) :
    Project.Formula.satisfies (((((e.push β).push γ).push B).push zero).push C)
      ((KP1Y.OrdinalIteration.valueMatrix rightAddMatrix).body.rename productValueSlots) ↔
        KP1Y.OrdinalIteration.ValueCertificate rightAddMatrix ((oneEnv (e.bound 0)).push zero) β γ C := by
  rw [Project.Formula.satisfies_rename]
  apply (KP1Y.formula_bound_congr (KP1Y.OrdinalIteration.valueMatrix rightAddMatrix).body
    (KP1Y.OrdinalIteration.valueMatrix rightAddMatrix).freeClosed _
    (((((oneEnv (e.bound 0)).push zero).push β).push γ).push C) ?_).trans
      (KP1Y.OrdinalIteration.valueMatrix_iff hM rightAddMatrix ((oneEnv (e.bound 0)).push zero) β γ C)
  intro i
  refine Fin.cases ?_ (fun i => ?_) i
  · rfl
  · refine Fin.cases ?_ (fun i => ?_) i
    · rfl
    · refine Fin.cases ?_ (fun i => ?_) i
      · rfl
      · refine Fin.cases ?_ (fun i => ?_) i
        · rfl
        · exact Fin.cases rfl (fun i => Fin.elim0 i) i

theorem productMatrix_iff {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory) (e : Env M 1) (β γ B : M.Domain) :
    Project.Formula.satisfies (((e.push β).push γ).push B) productMatrix.body ↔ ProductCertificate M (e.bound 0) β γ B := by
  simp only [productMatrix,Project.Formula.satisfies_conj_iff,ordinalFormula_iff hM,
    Project.Formula.satisfies_existsMem_iff,emptyFormula_iff,productValueSlots_iff hM]
  rfl

theorem product_sigmaOne_iff_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory) (e : Env M 1) (β γ : M.Domain) :
    Product M (e.bound 0) β γ ↔ ∃ B, Project.Formula.satisfies (((e.push β).push γ).push B) productMatrix.body := by
  constructor
  · rintro ⟨hα,zero,hZero,C,hC⟩
    obtain ⟨B,hB⟩ := SetTheory.KP.exists_pair (KP1Y.models_weakKP hM) zero C
    exact ⟨B,(productMatrix_iff hM e β γ B).mpr ⟨hα,zero,(hB zero).mpr (Or.inl rfl),C,(hB C).mpr (Or.inr rfl),hZero,hC⟩⟩
  · rintro ⟨B,hB⟩
    obtain ⟨hα,zero,_,C,_,hZero,hC⟩ := (productMatrix_iff hM e β γ B).mp hB
    exact ⟨hα,zero,hZero,C,hC⟩

end KP1Y.Arithmetic
