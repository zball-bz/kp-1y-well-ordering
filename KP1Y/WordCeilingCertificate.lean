import KP1Y.WordBudgets
import KP1Y.SigmaGraphCertificate

/-! 字词编码总界的统一Σ₁证书。只需保留ω阶段增长迭代，预算图可由此恢复。 -/
namespace KP1Y.WordRank
open YesMetaZFC YesMetaZFC.SetTheory YesMetaZFC.SetTheory.Definitional
open KP1Y.Kuratowski KP1Y.Functions KP1Y.Bounded
universe u

def budgetValueFormula {n : Nat} (κ one i C B : Project.Term n) : Project.Formula 1 n :=
  witnessInstanceFormula (KP1Y.OrdinalIteration.valueMatrix growthMatrix)
    (Fin.cases one (fun _ => κ)) i C B

theorem budgetValueFormula_delta0 {n : Nat} (κ one i C B : Project.Term n) :
    (budgetValueFormula κ one i C B).IsDelta0 := witnessInstanceFormula_delta0 _ _ _ _ _

theorem budgetValueFormula_freeClosed {n : Nat} (κ one i C B : Project.Term n)
    (hκ : κ.freeSupport=[]) (hOne : one.freeSupport=[]) (hi : i.freeSupport=[])
    (hC : C.freeSupport=[]) (hB : B.freeSupport=[]) : (budgetValueFormula κ one i C B).FreeClosed :=
  witnessInstanceFormula_freeClosed _ _ _ _ _ (Fin.cases hOne (fun _ => hκ)) hi hC hB

theorem budgetValueFormula_iff {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory) {n : Nat}
    (e : Env M n) (κ one i C B : Project.Term n) :
    Project.Formula.satisfies e (budgetValueFormula κ one i C B) ↔
      KP1Y.OrdinalIteration.ValueCertificate growthMatrix ((oneEnv (κ.eval e)).push (one.eval e))
        (i.eval e) (C.eval e) (B.eval e) := by
  rw [budgetValueFormula,witnessInstanceFormula,Project.Formula.satisfies_bind]
  apply (KP1Y.formula_bound_congr (KP1Y.OrdinalIteration.valueMatrix growthMatrix).body
    (KP1Y.OrdinalIteration.valueMatrix growthMatrix).freeClosed _
      (((((oneEnv (κ.eval e)).push (one.eval e)).push (i.eval e)).push (C.eval e)).push (B.eval e)) ?_).trans
        (KP1Y.OrdinalIteration.valueMatrix_iff hM growthMatrix ((oneEnv (κ.eval e)).push (one.eval e)) _ _ _)
  intro j
  refine Fin.cases ?_ (fun j => ?_) j
  · rfl
  · refine Fin.cases ?_ (fun j => ?_) j
    · rfl
    · refine Fin.cases ?_ (fun j => ?_) j
      · rfl
      · refine Fin.cases ?_ (fun j => ?_) j
        · rfl
        · exact Fin.cases rfl (fun j => Fin.elim0 j) j

def CeilingCertificate (M : SetTheory.Structure.{u}) (κ ω C B : M.Domain) : Prop :=
  ∃ zero, M.mem zero ω ∧ ∃ one, M.mem one ω ∧ (∀ x, ¬M.mem x zero) ∧ M.SuccessorOf one zero ∧
    KP1Y.OrdinalIteration.ValueCertificate growthMatrix ((oneEnv κ).push one) ω C B

def ceilingCertificateFormula {n : Nat} (κ ω C B : Project.Term n) : Project.Formula 1 n :=
  Project.Formula.existsMem ω (Project.Formula.existsMem ω.weaken
    (.conj (emptyFormula (.bound 1)) (.conj (successorFormula (.bound 0) (.bound 1))
      (budgetValueFormula κ.weaken.weaken (.bound 0) ω.weaken.weaken C.weaken.weaken B.weaken.weaken))))

theorem ceilingCertificateFormula_delta0 {n : Nat} (κ ω C B : Project.Term n) :
    (ceilingCertificateFormula κ ω C B).IsDelta0 :=
  .existsMem _ (.existsMem _ (.conj (emptyFormula_delta0 _) (.conj (successorFormula_delta0 _ _)
    (budgetValueFormula_delta0 _ _ _ _ _))))

theorem ceilingCertificateFormula_freeClosed {n : Nat} (κ ω C B : Project.Term n)
    (hκ : κ.freeSupport=[]) (hω : ω.freeSupport=[]) (hC : C.freeSupport=[]) (hB : B.freeSupport=[]) :
    (ceilingCertificateFormula κ ω C B).FreeClosed := by
  unfold ceilingCertificateFormula
  simp only [Project.Formula.existsMem,Definitional.Formula.FreeClosed]
  refine ⟨?_,?_,?_,?_,?_⟩
  · simp [hω]
  · simp [hω]
  · simp [emptyFormula,Project.Formula.forallMem,Definitional.Formula.FreeClosed]
  · simp [successorFormula,Project.Formula.forallMem,Definitional.Formula.FreeClosed]
  · apply budgetValueFormula_freeClosed <;> simp [hκ,hω,hC,hB]

theorem ceilingCertificateFormula_iff {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory) {n : Nat}
    (e : Env M n) (κ ω C B : Project.Term n) :
    Project.Formula.satisfies e (ceilingCertificateFormula κ ω C B) ↔
      CeilingCertificate M (κ.eval e) (ω.eval e) (C.eval e) (B.eval e) := by
  simp only [ceilingCertificateFormula,Project.Formula.satisfies_existsMem_iff,Project.Formula.satisfies_conj_iff,
    emptyFormula_iff,successorFormula_iff hM.1,budgetValueFormula_iff hM,Term.eval_weaken]
  rfl

theorem ceiling_certificate_exists_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory) {κ ω : M.Domain}
    (hω : M.IsOmega ω) (hκ : M.IsOrdinal κ) : ∃ C B, CeilingCertificate M κ ω C B := by
  obtain ⟨zero,one,C,F,h⟩ := budget_exists_d hM hω hκ
  obtain ⟨B,hB⟩ := h.limit_value
  exact ⟨C,B,zero,h.zero_nat,one,h.one_nat,h.zero_empty,h.one_successor,hB⟩

theorem CeilingCertificate.unique_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {κ ω C C' B B' : M.Domain} (h : CeilingCertificate M κ ω C B) (h' : CeilingCertificate M κ ω C' B') : C=C' := by
  obtain ⟨zero,_,one,_,hZero,hOne,hC⟩ := h
  obtain ⟨zero',_,one',_,hZero',hOne',hC'⟩ := h'
  have hzz' := hM.1.eq_of_same_members zero zero' (fun x => iff_of_false (hZero x) (hZero' x))
  subst zero'
  have hoo' := hM.1.eq_of_same_members one one' (fun x => (hOne x).trans (hOne' x).symm)
  subst one'
  exact KP1Y.OrdinalIteration.value_unique_d hM growthMatrix ((oneEnv κ).push one)
    (growth_functional_d hM _) ⟨B,hC⟩ ⟨B',hC'⟩

theorem CeilingCertificate.budget_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {κ ω C B : M.Domain} (hω : M.IsOmega ω) (hκ : M.IsOrdinal κ) (h : CeilingCertificate M κ ω C B) :
    ∃ zero one F, Budget M κ ω zero one C F := by
  obtain ⟨zero,one,C',F,hBudget⟩ := budget_exists_d hM hω hκ
  have hValue := hBudget.limit_value
  obtain ⟨B',hB'⟩ := hValue
  have hCC' := h.unique_d hM ⟨zero,hBudget.zero_nat,one,hBudget.one_nat,hBudget.zero_empty,hBudget.one_successor,hB'⟩
  subst C'
  exact ⟨zero,one,F,hBudget⟩

end KP1Y.WordRank
