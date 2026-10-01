import KP1Y.OrdinalArithmeticLimits
import KP1Y.BoundedSubstitution

/-! 序数加/乘证书可实例化到任意对象项，保持字面Δ₀和自由环境一致性。 -/
namespace KP1Y.Arithmetic
open YesMetaZFC YesMetaZFC.SetTheory YesMetaZFC.SetTheory.Definitional
open KP1Y.Kuratowski
universe u

def sumCertificateFormula {n : Nat} (α β γ B : Project.Term n) : Project.Formula 1 n :=
  sumMatrix.body.bind (Fin.cases B (Fin.cases γ (Fin.cases β (fun _ => α))))

def productCertificateFormula {n : Nat} (α β γ B : Project.Term n) : Project.Formula 1 n :=
  productMatrix.body.bind (Fin.cases B (Fin.cases γ (Fin.cases β (fun _ => α))))

theorem sumCertificateFormula_delta0 {n : Nat} (α β γ B : Project.Term n) : (sumCertificateFormula α β γ B).IsDelta0 :=
  KP1Y.delta0_bind sumMatrix.delta0 _

theorem productCertificateFormula_delta0 {n : Nat} (α β γ B : Project.Term n) : (productCertificateFormula α β γ B).IsDelta0 :=
  KP1Y.delta0_bind productMatrix.delta0 _

theorem sumCertificateFormula_freeClosed {n : Nat} (α β γ B : Project.Term n)
    (hα : α.freeSupport=[]) (hβ : β.freeSupport=[]) (hγ : γ.freeSupport=[]) (hB : B.freeSupport=[]) :
    (sumCertificateFormula α β γ B).FreeClosed := by
  apply (Definitional.Formula.freeClosed_bind_iff_of_closed _ ?_ sumMatrix.body).mpr sumMatrix.freeClosed
  exact Fin.cases hB (Fin.cases hγ (Fin.cases hβ (fun _ => hα)))

theorem productCertificateFormula_freeClosed {n : Nat} (α β γ B : Project.Term n)
    (hα : α.freeSupport=[]) (hβ : β.freeSupport=[]) (hγ : γ.freeSupport=[]) (hB : B.freeSupport=[]) :
    (productCertificateFormula α β γ B).FreeClosed := by
  apply (Definitional.Formula.freeClosed_bind_iff_of_closed _ ?_ productMatrix.body).mpr productMatrix.freeClosed
  exact Fin.cases hB (Fin.cases hγ (Fin.cases hβ (fun _ => hα)))

theorem sumCertificateFormula_iff {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory) {n : Nat}
    (e : Env M n) (α β γ B : Project.Term n) :
    Project.Formula.satisfies e (sumCertificateFormula α β γ B) ↔
      KP1Y.OrdinalIteration.ValueCertificate successorMatrix (oneEnv (α.eval e)) (β.eval e) (γ.eval e) (B.eval e) := by
  rw [sumCertificateFormula,Project.Formula.satisfies_bind]
  apply (KP1Y.formula_bound_congr sumMatrix.body sumMatrix.freeClosed _
    ((((oneEnv (α.eval e)).push (β.eval e)).push (γ.eval e)).push (B.eval e)) ?_).trans
      (sumMatrix_iff hM (oneEnv (α.eval e)) (β.eval e) (γ.eval e) (B.eval e))
  intro i
  refine Fin.cases ?_ (fun i => ?_) i
  · rfl
  · refine Fin.cases ?_ (fun i => ?_) i
    · rfl
    · refine Fin.cases ?_ (fun _ => ?_) i <;> rfl

theorem productCertificateFormula_iff {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory) {n : Nat}
    (e : Env M n) (α β γ B : Project.Term n) :
    Project.Formula.satisfies e (productCertificateFormula α β γ B) ↔
      ProductCertificate M (α.eval e) (β.eval e) (γ.eval e) (B.eval e) := by
  rw [productCertificateFormula,Project.Formula.satisfies_bind]
  apply (KP1Y.formula_bound_congr productMatrix.body productMatrix.freeClosed _
    ((((oneEnv (α.eval e)).push (β.eval e)).push (γ.eval e)).push (B.eval e)) ?_).trans
      (productMatrix_iff hM (oneEnv (α.eval e)) (β.eval e) (γ.eval e) (B.eval e))
  intro i
  refine Fin.cases ?_ (fun i => ?_) i
  · rfl
  · refine Fin.cases ?_ (fun i => ?_) i
    · rfl
    · refine Fin.cases ?_ (fun _ => ?_) i <;> rfl

theorem ProductCertificate.meaning {M : SetTheory.Structure.{u}} {α β γ B : M.Domain}
    (h : ProductCertificate M α β γ B) : Product M α β γ := by
  obtain ⟨hα,zero,_,C,_,hZero,hC⟩ := h
  exact ⟨hα,zero,hZero,C,hC⟩

end KP1Y.Arithmetic
