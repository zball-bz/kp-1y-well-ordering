import KP1Y.ConstructibleCumulative

/-! 单层Lα的统一Σ₁证书：明确检查α为序数、取到α后继的历史并读取第α项。 -/
namespace KP1Y.Constructible
open YesMetaZFC YesMetaZFC.SetTheory YesMetaZFC.SetTheory.Definitional
open KP1Y.Kuratowski KP1Y.Functions KP1Y.Bounded
universe u

def LevelCertificate (M : SetTheory.Structure.{u}) (env : Env M 24) (α T B : M.Domain) : Prop :=
  M.IsOrdinal α ∧ ∃ δ, M.mem δ B ∧ ∃ H, M.mem H B ∧ ∃ C, M.mem C B ∧
    M.SuccessorOf δ α ∧ KP1Y.SigmaRecursion.Certificate M (levelStepMatrix.denote env) δ H C ∧ MemPair M H α T

private def levelHistorySlots : Fin 27 → Fin 30 :=
  Fin.cases 0 (Fin.cases 1 (Fin.cases 2 (fun i => ⟨i.val+6,by omega⟩)))

def levelCertificateMatrix : KP1Y.WitnessMatrix 24 where
  body := .conj (ordinalFormula (.bound 2))
    (Project.Formula.existsMem (.bound 0) (Project.Formula.existsMem (.bound 1)
      (Project.Formula.existsMem (.bound 2)
        (.conj (successorFormula (.bound 2) (.bound 5))
          (.conj ((KP1Y.SigmaRecursion.certificateMatrix levelStepMatrix).body.rename levelHistorySlots)
            (memPairFormula (.bound 1) (.bound 5) (.bound 4)))))))
  freeClosed := by
    simp [ordinalFormula,Project.Formula.isTransitive,successorFormula,memPairFormula,codeFormula,pairFormula,
      Project.Formula.existsMem,Project.Formula.forallMem,Definitional.Formula.FreeClosed,
      (KP1Y.SigmaRecursion.certificateMatrix levelStepMatrix).freeClosed]
  delta0 := .conj (ordinalFormula_delta0 _) (.existsMem _ (.existsMem _ (.existsMem _
    (.conj (successorFormula_delta0 _ _)
      (.conj (KP1Y.delta0_rename (KP1Y.SigmaRecursion.certificateMatrix levelStepMatrix).delta0 _)
        (memPairFormula_delta0 _ _ _))))))

private theorem levelHistorySlots_env {M : SetTheory.Structure.{u}} (env : Env M 24) (α T B δ H C : M.Domain) :
    ((((((env.push α).push T).push B).push δ).push H).push C).reindex levelHistorySlots =
      ((env.push δ).push H).push C := by
  rw [Env.mk.injEq]
  constructor
  · funext i
    refine Fin.cases ?_ (fun i => ?_) i
    · rfl
    · refine Fin.cases ?_ (fun i => ?_) i
      · rfl
      · refine Fin.cases ?_ (fun _ => ?_) i <;> rfl
  · rfl

theorem levelCertificateMatrix_iff {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    (env : Env M 24) (α T B : M.Domain) :
    Project.Formula.satisfies (((env.push α).push T).push B) levelCertificateMatrix.body ↔ LevelCertificate M env α T B := by
  simp only [levelCertificateMatrix,Project.Formula.satisfies_conj_iff,ordinalFormula_iff hM,
    Project.Formula.satisfies_existsMem_iff,successorFormula_iff hM.1,
    Project.Formula.satisfies_rename,levelHistorySlots_env,
    KP1Y.SigmaRecursion.certificateMatrix_iff hM.1,memPairFormula_iff hM.1]
  rfl

def IsLevel (M : SetTheory.Structure.{u}) (env : Env M 24) (α T : M.Domain) : Prop :=
  ∃ B, LevelCertificate M env α T B

theorem IsLevel.ordinal {M : SetTheory.Structure.{u}} {env : Env M 24} {α T : M.Domain} (h : IsLevel M env α T) : M.IsOrdinal α := by
  obtain ⟨_,hα,_⟩ := h
  exact hα

end KP1Y.Constructible
