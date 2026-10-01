import KP1Y.SigmaHistoryPrefix

/-! 用共同证书界形成实际历史族、前缀选择图和统一值域界；不使用选择公理。 -/
namespace KP1Y.SigmaRecursion
open YesMetaZFC YesMetaZFC.SetTheory YesMetaZFC.SetTheory.Definitional
open KP1Y.Kuratowski KP1Y.Functions
universe u

def boundedCertificateSlots {n : Nat} : Fin (n+3) → Fin (n+4) :=
  Fin.cases 0 (Fin.cases 1 (Fin.cases 2 (fun i => ⟨i.val+4, by omega⟩)))

def boundedCertificateSchema {n : Nat} (φ : StepMatrix n) : Project.Delta0BinarySchema (n+1) where
  body := .conj (.mem (.bound 0) (.bound 2))
    (Project.Formula.existsMem (.bound 2) ((certificateMatrix φ).body.rename boundedCertificateSlots))
  freeClosed := by
    simp [Project.Formula.existsMem, Definitional.Formula.FreeClosed, (certificateMatrix φ).freeClosed]
  delta0 := .conj (.mem _ _)
    (.existsMem _ (KP1Y.delta0_rename (certificateMatrix φ).delta0 _))

private theorem boundedCertificateSlots_env {M : SetTheory.Structure.{u}} {n : Nat}
    (env : Env M n) (C δ H B : M.Domain) :
    ((((env.push C).push δ).push H).push B).reindex boundedCertificateSlots =
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

theorem boundedCertificateSchema_iff {M : SetTheory.Structure.{u}} (he : Extensional M)
    {n : Nat} (φ : StepMatrix n) (env : Env M n) (C δ H : M.Domain) :
    Project.Formula.satisfies (((env.push C).push δ).push H) (boundedCertificateSchema φ).body ↔
      M.mem H C ∧ ∃ B, M.mem B C ∧ Certificate M (φ.denote env) δ H B := by
  simp only [boundedCertificateSchema, Project.Formula.satisfies_conj_iff,
    Project.Formula.satisfies_mem_iff, Project.Formula.satisfies_existsMem_iff,
    Project.Formula.satisfies_rename, boundedCertificateSlots_env, certificateMatrix_iff he]
  rfl

structure CollectedFamily (M : SetTheory.Structure.{u})
    (step : M.Domain → M.Domain → M.Domain → M.Domain → Prop) (δ C Q D W : M.Domain) : Prop where
  total : ∀ i, M.mem i δ → ∃ H, M.mem H C ∧ ∃ B, M.mem B C ∧ Certificate M step i H B
  graph : Graph M Q δ C
  rows : ∀ i H, MemPair M Q i H ↔
    M.mem i δ ∧ M.mem H C ∧ ∃ B, M.mem B C ∧ Certificate M step i H B
  members : ∀ H, M.mem H D ↔
    ∃ i, M.mem i δ ∧ M.mem H C ∧ ∃ B, M.mem B C ∧ Certificate M step i H B
  candidates : M.MemberSubset C W
  pools : ∀ B, M.mem B C → ∀ V, M.mem V B → M.MemberSubset V W

private theorem common_pool_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    (C : M.Domain) : ∃ W, M.MemberSubset C W ∧
      ∀ B, M.mem B C → ∀ V, M.mem V B → M.MemberSubset V W := by
  have hw := KP1Y.models_weakKP hM
  obtain ⟨C1,h1⟩ := SetTheory.KP.exists_union hw C
  obtain ⟨C2,h2⟩ := SetTheory.KP.exists_union hw C1
  obtain ⟨W,hW⟩ := SetTheory.KP.exists_unionOfTwo hw C C2
  refine ⟨W,fun x hx => (hW x).mpr (Or.inl hx),?_⟩
  intro B hB V hV x hx
  exact (hW x).mpr (Or.inr ((h2 x).mpr ⟨V,(h1 V).mpr ⟨B,hB,hV⟩,hx⟩))

theorem collect_histories_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {n : Nat} (φ : StepMatrix n) (env : Env M n) {Γ δ : M.Domain}
    (hδ : M.IsOrdinal δ) (hδΓ : M.MemberSubset δ Γ) (hFun : Functional M Γ (φ.denote env))
    (ih : ∀ i, M.mem i δ → ∃ H B, Certificate M (φ.denote env) i H B) :
    ∃ C Q D W, CollectedFamily M (φ.denote env) δ C Q D W := by
  obtain ⟨C,hC⟩ := KP1Y.joint_collection_d hM (certificateMatrix φ) env δ
    (fun i hi => by
      obtain ⟨H,B,hHB⟩ := ih i hi
      exact ⟨H,B,(certificateMatrix_iff hM.1 φ env i H B).mpr hHB⟩)
  have hTotal : ∀ i, M.mem i δ →
      ∃ H, M.mem H C ∧ ∃ B, M.mem B C ∧ Certificate M (φ.denote env) i H B := by
    intro i hi
    obtain ⟨H,hH,B,hB,hHB⟩ := hC i hi
    exact ⟨H,hH,B,hB,(certificateMatrix_iff hM.1 φ env i H B).mp hHB⟩
  have hUnique : ∀ i, M.mem i δ → ∀ H J,
      Project.Formula.satisfies (((env.push C).push i).push H) (boundedCertificateSchema φ).body →
      Project.Formula.satisfies (((env.push C).push i).push J) (boundedCertificateSchema φ).body → H=J := by
    intro i hi H J hH hJ
    obtain ⟨_,B,_,hHB⟩ := (boundedCertificateSchema_iff hM.1 φ env C i H).mp hH
    obtain ⟨_,B',_,hJB⟩ := (boundedCertificateSchema_iff hM.1 φ env C i J).mp hJ
    exact certificate_unique hM (hδ.mem hi)
      (fun x hx => hδΓ x (hδ.transitive i hi x hx)) hFun hHB hJB
  obtain ⟨Q,hSupport,hQ⟩ := relation_comprehension_d hM (boundedCertificateSchema φ) (env.push C) δ C
  have hRows : ∀ i H, MemPair M Q i H ↔
      M.mem i δ ∧ M.mem H C ∧ ∃ B, M.mem B C ∧ Certificate M (φ.denote env) i H B := by
    intro i H
    rw [hQ i H, boundedCertificateSchema_iff hM.1]
    exact ⟨fun h => ⟨h.1,h.2.1,h.2.2.2⟩,fun h => ⟨h.1,h.2.1,h.2⟩⟩
  have hGraph : Graph M Q δ C := by
    refine ⟨hSupport,?_,?_⟩
    · intro i hi
      obtain ⟨H,hHC,hHB⟩ := hTotal i hi
      exact ⟨H,hHC,(hRows i H).mpr ⟨hi,hHC,hHB⟩⟩
    · intro i H J hH hJ
      have hcH := (hQ i H).mp hH
      have hcJ := (hQ i J).mp hJ
      exact hUnique i hcH.1 H J hcH.2.2 hcJ.2.2
  obtain ⟨D,hD⟩ := KP1Y.functional_image_d hM (boundedCertificateSchema φ) (env.push C) δ
    (fun i hi => by
      obtain ⟨H,hH⟩ := hTotal i hi
      exact ⟨H,(boundedCertificateSchema_iff hM.1 φ env C i H).mpr hH⟩) hUnique
  obtain ⟨W,hCW,hPools⟩ := common_pool_d hM C
  refine ⟨C,Q,D,W,hTotal,hGraph,hRows,?_,hCW,hPools⟩
  intro H
  simpa only [boundedCertificateSchema_iff hM.1] using hD H

end KP1Y.SigmaRecursion
