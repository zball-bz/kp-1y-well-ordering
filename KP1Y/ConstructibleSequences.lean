import KP1Y.ConstructibleKP
import KP1Y.ClassSchemaTransfer

/-! 同一ω、内KP与Σ₁证书唯一性使完整A^{<ω}进入构造类，覆盖全部内部有限长度。 -/
namespace KP1Y.Constructible
open YesMetaZFC YesMetaZFC.SetTheory YesMetaZFC.SetTheory.Definitional
open KP1Y.Classes KP1Y.Kuratowski KP1Y.Functions KP1Y.Sequences KP1Y.SetLanguage
universe u

theorem sequence_space_constructible_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    (env : Env M 24) (hS : FixedSyntax M (defContext.eval env) (defData.eval env)
      (env.bound 0) (env.bound 1) (env.bound 2)) {ω A S : M.Domain} (hω : M.IsOmega ω)
    (hA : InConstructible M env A) (hSpace : ∀ F, M.mem F S ↔ ∃ n, M.mem n ω ∧ Graph M F n A) :
    InConstructible M env S := by
  let A0 : (innerModel hM env hS).Domain := ⟨A,hA⟩
  obtain ⟨ω0,hωValue,hωInner⟩ := inner_omega_exists_d hM env hS hω
  obtain ⟨B,hB⟩ := (sequence_space_sigmaOne_iff_d hM (oneEnv ω) hω A S).mp hSpace
  apply sigma_one_operation_closed (constructible_transitive_class_d hM env hS) spaceCertificateMatrix
    (oneEnv ω0) (oneEnv ω) (fun _ => hωValue) A0 hB
  · exact sequence_space_matrix_total_d (inner_models_kp_d hM env hS) (oneEnv ω0) hωInner A0
  · intro T T' B B' hT hT'
    exact space_certificate_unique_d hM hω ((spaceCertificateMatrix_iff hM (oneEnv ω) A T B).mp hT)
      ((spaceCertificateMatrix_iff hM (oneEnv ω) A T' B').mp hT')

theorem constructible_sequence_space_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    (env : Env M 24) (hS : FixedSyntax M (defContext.eval env) (defData.eval env)
      (env.bound 0) (env.bound 1) (env.bound 2)) {ω A : M.Domain} (hω : M.IsOmega ω) (hA : InConstructible M env A) :
    ∃ S, InConstructible M env S ∧ ∀ F, M.mem F S ↔ ∃ n, M.mem n ω ∧ Graph M F n A := by
  obtain ⟨S,hSpace⟩ := finite_sequences_exist_d hM hω A
  exact ⟨S,sequence_space_constructible_d hM env hS hω hA hSpace,hSpace⟩

theorem finite_sequence_constructible_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    (env : Env M 24) (hS : FixedSyntax M (defContext.eval env) (defData.eval env)
      (env.bound 0) (env.bound 1) (env.bound 2)) {ω A F n : M.Domain} (hω : M.IsOmega ω)
    (hA : InConstructible M env A) (hn : M.mem n ω) (hF : Graph M F n A) : InConstructible M env F := by
  obtain ⟨S,hSClass,hSpace⟩ := constructible_sequence_space_d hM env hS hω hA
  exact hSClass.mem_closed_d hM env hS ((hSpace F).mpr ⟨n,hn,hF⟩)

end KP1Y.Constructible
