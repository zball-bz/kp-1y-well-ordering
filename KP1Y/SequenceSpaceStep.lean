import KP1Y.SequenceAppendSpace
import KP1Y.SigmaRecursion

/-! 有限序列族的具体 Σ₁ 行算子；全定义与单值性均已从 KPω 证明。 -/
namespace KP1Y.Sequences
open YesMetaZFC YesMetaZFC.SetTheory YesMetaZFC.SetTheory.Definitional
open KP1Y.Kuratowski KP1Y.Functions KP1Y.Bounded KP1Y.Naturals
universe u

def SpaceStep (M : SetTheory.Structure.{u}) (A i P T w : M.Domain) : Prop :=
  Graph M P i w ∧
    (((∀ x, ¬M.mem x i) ∧ PairSet M T i i) ∨
      ∃ p, M.mem p i ∧ ∃ B, M.mem B w ∧
        M.SuccessorOf i p ∧ MemPair M P p B ∧ AppendSpace M T B A p)

def spaceStep : KP1Y.SigmaRecursion.StepMatrix 1 where
  body := .conj (graphFormula (.bound 2) (.bound 3) (.bound 0))
    (.disj (.conj (emptyFormula (.bound 3)) (pairFormula (.bound 1) (.bound 3) (.bound 3)))
      (Project.Formula.existsMem (.bound 3) (Project.Formula.existsMem (.bound 1)
        (.conj (successorFormula (.bound 5) (.bound 1))
          (.conj (memPairFormula (.bound 4) (.bound 1) (.bound 0))
            (appendSpaceFormula (.bound 3) (.bound 0) (.bound 6) (.bound 1)))))))
  freeClosed := by
    simp [graphFormula, emptyFormula, successorFormula, memPairFormula,
      appendSpaceFormula, appendFormula, insertFormula, codeFormula, pairFormula,
      Project.Formula.forallMem, Project.Formula.existsMem, Definitional.Formula.FreeClosed]
  delta0 := .conj (graphFormula_delta0 _ _ _)
    (.disj (.conj (emptyFormula_delta0 _) (pairFormula_delta0 _ _ _))
      (.existsMem _ (.existsMem _ (.conj (successorFormula_delta0 _ _)
        (.conj (memPairFormula_delta0 _ _ _) (appendSpaceFormula_delta0 _ _ _ _))))))

theorem spaceStep_iff {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    (A i P T w : M.Domain) :
    spaceStep.denote (oneEnv A) i P T w ↔ SpaceStep M A i P T w := by
  simp only [KP1Y.SigmaRecursion.StepMatrix.denote, spaceStep,
    Project.Formula.satisfies_conj_iff, Project.Formula.satisfies_disj_iff,
    Project.Formula.satisfies_existsMem_iff, graphFormula_iff hM.1,
    emptyFormula_iff, pairFormula_iff hM.1, successorFormula_iff hM.1,
    memPairFormula_iff hM.1, appendSpaceFormula_iff hM]
  rfl

theorem spaceStep_total_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {ω : M.Domain} (hω : M.IsOmega ω) (A : M.Domain) :
    KP1Y.SigmaRecursion.Total M ω (spaceStep.denote (oneEnv A)) := by
  intro i hi P V hP
  rcases natural_cases hM hω hi with hEmpty | ⟨p,_,hs⟩
  · obtain ⟨T,hT⟩ := SetTheory.KP.exists_pair (KP1Y.models_weakKP hM) i i
    exact ⟨T,V,(spaceStep_iff hM A i P T V).mpr ⟨hP,Or.inl ⟨hEmpty,hT⟩⟩⟩
  · obtain ⟨B,hB,hPB⟩ := hP.total p hs.predecessor_mem
    obtain ⟨T,hT⟩ := appendSpace_exists_d hM B A p
    exact ⟨T,V,(spaceStep_iff hM A i P T V).mpr
      ⟨hP,Or.inr ⟨p,hs.predecessor_mem,B,hB,hs,hPB,hT⟩⟩⟩

theorem spaceStep_functional_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {ω : M.Domain} (hω : M.IsOmega ω) (A : M.Domain) :
    KP1Y.SigmaRecursion.Functional M ω (spaceStep.denote (oneEnv A)) := by
  intro i hi P T T' w w' hT hT'
  obtain ⟨hP,hCases⟩ := (spaceStep_iff hM A i P T w).mp hT
  obtain ⟨_,hCases'⟩ := (spaceStep_iff hM A i P T' w').mp hT'
  rcases hCases with ⟨hEmpty,hPair⟩ | ⟨p,hp,B,_,hs,hPB,hSpace⟩
  · rcases hCases' with ⟨_,hPair'⟩ | ⟨p,hp,_,_,_,_,_⟩
    · exact hPair.unique hM.1 hPair'
    · exact False.elim (hEmpty p hp)
  · rcases hCases' with ⟨hEmpty,_⟩ | ⟨p',_,B',_,hs',hPB',hSpace'⟩
    · exact False.elim (hEmpty p hp)
    · have hpp' := Structure.SuccessorOf.predecessor_eq hM.1
        (((omega_isOrdinal_d hM hω).mem hi).mem hp) hs hs'
      subst p'
      have hBB' := hP.unique p B B' hPB hPB'
      subst B'
      exact appendSpace_unique hM.1 hSpace hSpace'

theorem space_history_exists_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {ω : M.Domain} (hω : M.IsOmega ω) (A : M.Domain) :
    ∃ H V Q, KP1Y.SigmaRecursion.ValueHistory M (spaceStep.denote (oneEnv A)) H ω V Q :=
  KP1Y.SigmaRecursion.value_recursion_d hM spaceStep (oneEnv A) (omega_isOrdinal_d hM hω)
    (spaceStep_total_d hM hω A) (spaceStep_functional_d hM hω A)

end KP1Y.Sequences
