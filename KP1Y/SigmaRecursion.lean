import KP1Y.OrdinalCases
import KP1Y.SigmaHistorySuccessor
import KP1Y.SigmaHistoryLimit

/-! KPω 的一般 Σ₁ 集合值序数递归；存在性由对象集合归纳得到。 -/
namespace KP1Y.SigmaRecursion
open YesMetaZFC YesMetaZFC.SetTheory YesMetaZFC.SetTheory.Definitional
open KP1Y.Kuratowski KP1Y.Functions
universe u

def existsCertificateSchema {n : Nat} (φ : StepMatrix n) : Project.UnarySchema (n+1) where
  body := .imp (Project.Formula.subset (.bound 0) (.bound 1))
    (.existsE (.existsE ((certificateMatrix φ).body.rename boundedCertificateSlots)))
  freeClosed := by
    simp [Definitional.Formula.FreeClosed, (certificateMatrix φ).freeClosed]

private theorem existence_env {M : SetTheory.Structure.{u}} {n : Nat}
    (env : Env M n) (Γ δ H B : M.Domain) :
    ((((env.push Γ).push δ).push H).push B).reindex boundedCertificateSlots =
      ((env.push δ).push H).push B := by
  rw [Env.mk.injEq]
  constructor
  · funext i
    refine Fin.cases ?_ (fun i => ?_) i
    · rfl
    · refine Fin.cases ?_ (fun i => ?_) i
      · rfl
      · refine Fin.cases ?_ (fun i => ?_) i <;> rfl
  · rfl

theorem existsCertificateSchema_iff {M : SetTheory.Structure.{u}} (he : Extensional M)
    {n : Nat} (φ : StepMatrix n) (env : Env M n) (Γ δ : M.Domain) :
    Project.Formula.satisfies ((env.push Γ).push δ) (existsCertificateSchema φ).body ↔
      (M.MemberSubset δ Γ → ∃ H B, Certificate M (φ.denote env) δ H B) := by
  simp only [existsCertificateSchema, Project.Formula.satisfies_imp_iff,
    Project.Formula.satisfies_subset_iff, Project.Formula.satisfies_exists_iff,
    Project.Formula.satisfies_rename, existence_env, certificateMatrix_iff he]
  rfl

theorem sigma_recursion_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {n : Nat} (φ : StepMatrix n) (env : Env M n) {Γ : M.Domain} (hΓ : M.IsOrdinal Γ)
    (hTotal : Total M Γ (φ.denote env)) (hFun : Functional M Γ (φ.denote env)) :
    ∃ H B, Certificate M (φ.denote env) Γ H B := by
  have hAll := KP1Y.ordinal_induction_d hM (existsCertificateSchema φ) (env.push Γ)
    (fun δ hδ ih => (existsCertificateSchema_iff hM.1 φ env Γ δ).mpr (by
      intro hδΓ
      rcases KP1Y.ordinal_cases hM.1 hδ with hEmpty | hSucc | hLimit
      · have hH : ValueHistory M (φ.denote env) δ δ δ δ :=
          ⟨empty_graph hEmpty,empty_graph hEmpty,fun i hi => False.elim (hEmpty i hi)⟩
        obtain ⟨B,hB⟩ := certificate_exists hM hH
        exact ⟨δ,B,hB⟩
      · obtain ⟨ε,hε,hSucc⟩ := hSucc
        have hεδ := hSucc.predecessor_mem
        have hεΓ : M.MemberSubset ε Γ := fun i hi => hδΓ i (hδ.transitive ε hεδ i hi)
        obtain ⟨H,B,hH⟩ := (existsCertificateSchema_iff hM.1 φ env Γ ε).mp (ih ε hεδ) hεΓ
        exact certificate_successor_d hM hε (hδΓ ε hεδ) hSucc hTotal hH
      · apply certificate_limit_d hM φ env hLimit hδΓ hFun
        intro ε hεδ
        exact (existsCertificateSchema_iff hM.1 φ env Γ ε).mp (ih ε hεδ)
          (fun i hi => hδΓ i (hδ.transitive ε hεδ i hi))))
  exact (existsCertificateSchema_iff hM.1 φ env Γ Γ).mp (hAll Γ hΓ) (fun _ h => h)

theorem sigma_recursion_unique_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {n : Nat} (φ : StepMatrix n) (env : Env M n) {Γ : M.Domain} (hΓ : M.IsOrdinal Γ)
    (hTotal : Total M Γ (φ.denote env)) (hFun : Functional M Γ (φ.denote env)) :
    ∃ H B, Certificate M (φ.denote env) Γ H B ∧
      ∀ J C, Certificate M (φ.denote env) Γ J C → J=H := by
  obtain ⟨H,B,hH⟩ := sigma_recursion_d hM φ env hΓ hTotal hFun
  exact ⟨H,B,hH,fun J _ hJ => certificate_unique hM hΓ (fun _ h => h) hFun hJ hH⟩

theorem value_recursion_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {n : Nat} (φ : StepMatrix n) (env : Env M n) {Γ : M.Domain} (hΓ : M.IsOrdinal Γ)
    (hTotal : Total M Γ (φ.denote env)) (hFun : Functional M Γ (φ.denote env)) :
    ∃ H V Q, ValueHistory M (φ.denote env) H Γ V Q := by
  obtain ⟨H,_,V,_,Q,_,hH⟩ := sigma_recursion_d hM φ env hΓ hTotal hFun
  exact ⟨H,V,Q,hH⟩

end KP1Y.SigmaRecursion
