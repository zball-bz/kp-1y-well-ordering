import KP1Y.SequenceCertificate

/-! 完整序列空间的统一 Σ₁ 定义：一个集合证书，内部验证全为字面 Δ₀。 -/
namespace KP1Y.Sequences
open YesMetaZFC YesMetaZFC.SetTheory YesMetaZFC.SetTheory.Definitional
open KP1Y.Kuratowski KP1Y.Functions KP1Y.Bounded
universe u

theorem spaceStep_general_iff {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    (env : Env M 1) (i P T w : M.Domain) :
    spaceStep.denote env i P T w ↔ SpaceStep M (env.bound 0) i P T w := by
  simp only [KP1Y.SigmaRecursion.StepMatrix.denote, spaceStep,
    Project.Formula.satisfies_conj_iff, Project.Formula.satisfies_disj_iff,
    Project.Formula.satisfies_existsMem_iff, graphFormula_iff hM.1, emptyFormula_iff,
    pairFormula_iff hM.1, successorFormula_iff hM.1, memPairFormula_iff hM.1, appendSpaceFormula_iff hM]
  rfl

theorem spaceStep_denote_same {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory) (env : Env M 1) :
    spaceStep.denote env = spaceStep.denote (oneEnv (env.bound 0)) := by
  funext i P T w
  exact propext ((spaceStep_general_iff hM env i P T w).trans (spaceStep_iff hM (env.bound 0) i P T w).symm)

def certificateHistorySlots : Fin 5 → Fin 8 :=
  Fin.cases 1 (Fin.cases 2 (Fin.cases 3 (Fin.cases 7 (fun _ => 6))))

def spaceCertificateMatrix : KP1Y.WitnessMatrix 1 where
  body := Project.Formula.existsMem (.bound 0) (Project.Formula.existsMem (.bound 1)
    (Project.Formula.existsMem (.bound 2) (Project.Formula.existsMem (.bound 3)
      (.conj ((KP1Y.SigmaRecursion.historyVerifier spaceStep).rename certificateHistorySlots)
        (.conj (rangeBoundFormula (.bound 0) (.bound 2) (.bound 3) (.bound 7))
          (unionFormula (.bound 5) (.bound 0)))))))
  freeClosed := by
    simp [Project.Formula.existsMem, Definitional.Formula.FreeClosed,
      KP1Y.SigmaRecursion.historyVerifier_freeClosed, rangeBoundFormula, unionFormula,
      memPairFormula, codeFormula, pairFormula, Project.Formula.forallMem]
  delta0 := .existsMem _ (.existsMem _ (.existsMem _ (.existsMem _
    (.conj (KP1Y.delta0_rename (KP1Y.SigmaRecursion.historyVerifier_delta0 spaceStep) _)
      (.conj (rangeBoundFormula_delta0 _ _ _ _) (unionFormula_delta0 _ _))))))

private theorem certificateHistory_iff {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    (env : Env M 1) (A S B H V Q D : M.Domain) :
    Project.Formula.satisfies (((((((env.push A).push S).push B).push H).push V).push Q).push D)
      ((KP1Y.SigmaRecursion.historyVerifier spaceStep).rename certificateHistorySlots) ↔
      KP1Y.SigmaRecursion.ValueHistory M (spaceStep.denote (oneEnv A)) H (env.bound 0) V Q := by
  let aEnv : Env M 1 := ⟨fun _ => A,env.free⟩
  have hEnv : (((((((env.push A).push S).push B).push H).push V).push Q).push D).reindex certificateHistorySlots =
      (((aEnv.push (env.bound 0)).push H).push V).push Q := by
    rw [Env.mk.injEq]
    constructor
    · funext i
      refine Fin.cases ?_ (fun i => ?_) i
      · rfl
      · refine Fin.cases ?_ (fun i => ?_) i
        · rfl
        · refine Fin.cases ?_ (fun i => ?_) i
          · rfl
          · refine Fin.cases ?_ (fun i => ?_) i <;> rfl
    · rfl
  rw [Project.Formula.satisfies_rename,hEnv]
  simpa only [spaceStep_denote_same hM aEnv] using
    (KP1Y.SigmaRecursion.historyVerifier_iff hM.1 spaceStep aEnv (env.bound 0) H V Q)

theorem spaceCertificateMatrix_iff {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    (env : Env M 1) (A S B : M.Domain) :
    Project.Formula.satisfies (((env.push A).push S).push B) spaceCertificateMatrix.body ↔
      SpaceCertificate M (env.bound 0) A S B := by
  simp only [spaceCertificateMatrix, Project.Formula.satisfies_existsMem_iff,
    Project.Formula.satisfies_conj_iff, certificateHistory_iff hM,
    rangeBoundFormula_iff hM.1, unionFormula_iff]
  rfl

theorem sequence_space_sigmaOne_iff_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    (env : Env M 1) (hω : M.IsOmega (env.bound 0)) (A S : M.Domain) :
    (∀ F, M.mem F S ↔ ∃ n, M.mem n (env.bound 0) ∧ Graph M F n A) ↔
      ∃ B, Project.Formula.satisfies (((env.push A).push S).push B) spaceCertificateMatrix.body := by
  constructor
  · intro hSpace
    obtain ⟨T,B,hT⟩ := space_certificate_exists_d hM hω A
    have hST : S=T := hM.1.eq_of_same_members S T (fun F => (hSpace F).trans (space_certificate_exact_d hM hω hT F).symm)
    subst T
    exact ⟨B,(spaceCertificateMatrix_iff hM env A S B).mpr hT⟩
  · rintro ⟨B,hB⟩
    exact space_certificate_exact_d hM hω ((spaceCertificateMatrix_iff hM env A S B).mp hB)

theorem sequence_space_matrix_total_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    (env : Env M 1) (hω : M.IsOmega (env.bound 0)) :
    ∀ A, ∃ S B, Project.Formula.satisfies (((env.push A).push S).push B) spaceCertificateMatrix.body := by
  intro A
  obtain ⟨S,B,hB⟩ := space_certificate_exists_d hM hω A
  exact ⟨S,B,(spaceCertificateMatrix_iff hM env A S B).mpr hB⟩

end KP1Y.Sequences
