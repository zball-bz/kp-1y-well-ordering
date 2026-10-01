import KP1Y.SequenceCertificateSyntax
import KP1Y.BoundedSubstitution

/-! 将完整序列空间证书实例化到任意项，同时保留Δ₀与环境语义证明。 -/
namespace KP1Y.Sequences
open YesMetaZFC YesMetaZFC.SetTheory YesMetaZFC.SetTheory.Definitional
universe u

def spaceCertificateFormula {n : Nat} (ω A S B : Project.Term n) : Project.Formula 1 n :=
  spaceCertificateMatrix.body.bind (Fin.cases B (Fin.cases S (Fin.cases A (fun _ => ω))))

theorem spaceCertificateFormula_delta0 {n : Nat} (ω A S B : Project.Term n) :
    (spaceCertificateFormula ω A S B).IsDelta0 := KP1Y.delta0_bind spaceCertificateMatrix.delta0 _

theorem spaceCertificateFormula_freeClosed {n : Nat} (ω A S B : Project.Term n)
    (hω : ω.freeSupport=[]) (hA : A.freeSupport=[]) (hS : S.freeSupport=[]) (hB : B.freeSupport=[]) :
    (spaceCertificateFormula ω A S B).FreeClosed := by
  apply (Definitional.Formula.freeClosed_bind_iff_of_closed _ ?_ spaceCertificateMatrix.body).mpr spaceCertificateMatrix.freeClosed
  intro i
  exact Fin.cases hB (Fin.cases hS (Fin.cases hA (fun _ => hω))) i

theorem spaceCertificateFormula_iff {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory) {n : Nat}
    (env : Env M n) (ω A S B : Project.Term n) :
    Project.Formula.satisfies env (spaceCertificateFormula ω A S B) ↔
      SpaceCertificate M (ω.eval env) (A.eval env) (S.eval env) (B.eval env) := by
  let e : Env M 1 := ⟨fun _ => ω.eval env,env.free⟩
  have hEnv : Definitional.Env.substitute env (Fin.cases B (Fin.cases S (Fin.cases A (fun _ => ω)))) =
      ((e.push (A.eval env)).push (S.eval env)).push (B.eval env) := by
    rw [Env.mk.injEq]
    constructor
    · funext i
      refine Fin.cases ?_ (fun i => ?_) i
      · rfl
      · refine Fin.cases ?_ (fun i => ?_) i
        · rfl
        · refine Fin.cases ?_ (fun _ => ?_) i <;> rfl
    · rfl
  rw [spaceCertificateFormula,Project.Formula.satisfies_bind,hEnv]
  exact spaceCertificateMatrix_iff hM e _ _ _

end KP1Y.Sequences
