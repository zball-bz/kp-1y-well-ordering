import KP1Y.DefSuccessorMatrix

/-! L层级一步递归：空阶段、Def后继、历史值域之并；所有辅助集合界于证书。 -/
namespace KP1Y.Constructible
open YesMetaZFC YesMetaZFC.SetTheory YesMetaZFC.SetTheory.Definitional
open KP1Y.Kuratowski KP1Y.Functions KP1Y.Bounded KP1Y.Sequences KP1Y.SetLanguage
universe u

def Empty (M : SetTheory.Structure.{u}) (i : M.Domain) : Prop := ∀ x, ¬M.mem x i

def NoPredecessor (M : SetTheory.Structure.{u}) (i : M.Domain) : Prop :=
  ∀ p, M.mem p i → ¬M.SuccessorOf i p

def LevelStep (M : SetTheory.Structure.{u}) (env : Env M 24) (i P T w : M.Domain) : Prop :=
  ∃ V, M.mem V w ∧ Graph M P i V ∧
    ((Empty M i ∧ Empty M T) ∨
      (∃ p, M.mem p i ∧ ∃ A, M.mem A V ∧ ∃ B, M.mem B w ∧
        M.SuccessorOf i p ∧ MemPair M P p A ∧
          Project.Formula.satisfies (((env.push A).push T).push B) defSuccessorMatrix.body) ∨
      ((¬Empty M i ∧ NoPredecessor M i) ∧ ∃ D, M.mem D w ∧ RangeBound M D V P i ∧
        ∀ x, M.mem x T ↔ ∃ A, M.mem A D ∧ M.mem x A))

private def successorSlots : Fin 27 → Fin 32 :=
  Fin.cases 0 (Fin.cases 5 (Fin.cases 1 (fun i => ⟨i.val+8,by omega⟩)))

def levelStepMatrix : KP1Y.SigmaRecursion.StepMatrix 24 where
  body := Project.Formula.existsMem (.bound 0)
    (.conj (graphFormula (.bound 3) (.bound 4) (.bound 0))
      (.disj (.conj (emptyFormula (.bound 4)) (emptyFormula (.bound 2)))
        (.disj
          (Project.Formula.existsMem (.bound 4) (Project.Formula.existsMem (.bound 1)
            (Project.Formula.existsMem (.bound 3)
              (.conj (successorFormula (.bound 7) (.bound 2))
                (.conj (memPairFormula (.bound 6) (.bound 2) (.bound 1))
                  (defSuccessorMatrix.body.rename successorSlots))))))
          (.conj (.conj (.neg (emptyFormula (.bound 4)))
              (Project.Formula.forallMem (.bound 4) (.neg (successorFormula (.bound 5) (.bound 0)))))
            (Project.Formula.existsMem (.bound 1)
              (.conj (rangeBoundFormula (.bound 0) (.bound 1) (.bound 4) (.bound 5))
                (unionFormula (.bound 3) (.bound 0))))))))
  freeClosed := by
    simp [graphFormula,emptyFormula,successorFormula,rangeBoundFormula,unionFormula,
      memPairFormula,codeFormula,pairFormula,Project.Formula.existsMem,Project.Formula.forallMem,
      Definitional.Formula.FreeClosed,defSuccessorMatrix.freeClosed]
  delta0 := .existsMem _ (.conj (graphFormula_delta0 _ _ _)
    (.disj (.conj (emptyFormula_delta0 _) (emptyFormula_delta0 _))
      (.disj (.existsMem _ (.existsMem _ (.existsMem _
        (.conj (successorFormula_delta0 _ _) (.conj (memPairFormula_delta0 _ _ _)
          (KP1Y.delta0_rename defSuccessorMatrix.delta0 _))))))
        (.conj (.conj (.neg (emptyFormula_delta0 _)) (.forallMem _ (.neg (successorFormula_delta0 _ _))))
          (.existsMem _ (.conj (rangeBoundFormula_delta0 _ _ _ _) (unionFormula_delta0 _ _)))))))

private theorem successorSlots_env {M : SetTheory.Structure.{u}} (env : Env M 24) (i P T w V p A B : M.Domain) :
    ((((((((env.push i).push P).push T).push w).push V).push p).push A).push B).reindex successorSlots =
      ((env.push A).push T).push B := by
  rw [Env.mk.injEq]
  constructor
  · funext k
    refine Fin.cases ?_ (fun k => ?_) k
    · rfl
    · refine Fin.cases ?_ (fun k => ?_) k
      · rfl
      · refine Fin.cases ?_ (fun _ => ?_) k <;> rfl
  · rfl

theorem levelStepMatrix_iff {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    (env : Env M 24) (i P T w : M.Domain) : levelStepMatrix.denote env i P T w ↔ LevelStep M env i P T w := by
  simp only [KP1Y.SigmaRecursion.StepMatrix.denote,levelStepMatrix,
    Project.Formula.satisfies_existsMem_iff,Project.Formula.satisfies_forallMem_iff,
    Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_disj_iff,Project.Formula.satisfies_neg_iff,
    graphFormula_iff hM.1,emptyFormula_iff,successorFormula_iff hM.1,
    rangeBoundFormula_iff hM.1,unionFormula_iff,memPairFormula_iff hM.1,
    Project.Formula.satisfies_rename,successorSlots_env]
  rfl

end KP1Y.Constructible
