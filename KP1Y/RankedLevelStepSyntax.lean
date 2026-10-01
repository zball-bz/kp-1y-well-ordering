import KP1Y.RankedSuccessorPacket
import KP1Y.RankedUnion
import KP1Y.ConstructibleStepSyntax

/-! 已排名L层级的一步：坏历史返回空排名，合法历史取Def后继或规范并集。 -/
namespace KP1Y.ConstructibleRank
open YesMetaZFC YesMetaZFC.SetTheory YesMetaZFC.SetTheory.Definitional
open KP1Y.Kuratowski KP1Y.Functions KP1Y.Bounded KP1Y.Ranking
universe u

def RankedStep (M : SetTheory.Structure.{u}) (e : Env M 26) (i P Out w : M.Domain) : Prop :=
  ∃ V, M.mem V w ∧ Graph M P i V ∧
    ((¬RankedFamily M P i V) ∧ Packet M Out (e.bound 2) (e.bound 2) (e.bound 2) ∨
      RankedFamily M P i V ∧
        ((∃ j, M.mem j i ∧ ∃ p, M.mem p V ∧ ∃ B, M.mem B w ∧ M.SuccessorOf i j ∧ MemPair M P j p ∧
          Project.Formula.satisfies (((e.push p).push Out).push B) successorPacketMatrix.body) ∨
          KP1Y.Constructible.NoPredecessor M i ∧ ∃ B, M.mem B w ∧
            Project.Formula.satisfies ((((oneEnv i).push P).push Out).push B) rankedUnionMatrix.body))

private def successorSlots : Fin 29 → Fin 34 :=
  Fin.cases 0 (Fin.cases 5 (Fin.cases 1 (fun i => ⟨i.val+8,by omega⟩)))

private def unionSlots : Fin 4 → Fin 32 := Fin.cases 0 (Fin.cases 3 (Fin.cases 4 (fun _ => 5)))

def rankedStepMatrix : KP1Y.SigmaRecursion.StepMatrix 26 where
  body := Project.Formula.existsMem (.bound 0)
    (.conj (graphFormula (.bound 3) (.bound 4) (.bound 0))
      (.disj
        (.conj (.neg (rankedFamilyFormula (.bound 3) (.bound 4) (.bound 0)))
          (packetFormula (.bound 2) (.bound 7) (.bound 7) (.bound 7)))
        (.conj (rankedFamilyFormula (.bound 3) (.bound 4) (.bound 0))
          (.disj
            (Project.Formula.existsMem (.bound 4) (Project.Formula.existsMem (.bound 1) (Project.Formula.existsMem (.bound 3)
              (.conj (successorFormula (.bound 7) (.bound 2)) (.conj (memPairFormula (.bound 6) (.bound 2) (.bound 1))
                (successorPacketMatrix.body.rename successorSlots))))))
            (.conj (Project.Formula.forallMem (.bound 4) (.neg (successorFormula (.bound 5) (.bound 0))))
              (Project.Formula.existsMem (.bound 1) (rankedUnionMatrix.body.rename unionSlots)))))))
  freeClosed := by
    have hFam := rankedFamilyFormula_freeClosed (n := 31) (.bound 3) (.bound 4) (.bound 0) rfl rfl rfl
    have hPacket := packetFormula_freeClosed (n := 31) (.bound 2) (.bound 7) (.bound 7) (.bound 7) rfl rfl rfl rfl
    simp [graphFormula,successorFormula,memPairFormula,codeFormula,pairFormula,
      Project.Formula.existsMem,Project.Formula.forallMem,Definitional.Formula.FreeClosed,hFam,hPacket,
      successorPacketMatrix.freeClosed,rankedUnionMatrix.freeClosed]
  delta0 := .existsMem _ (.conj (graphFormula_delta0 _ _ _)
    (.disj (.conj (.neg (rankedFamilyFormula_delta0 _ _ _)) (packetFormula_delta0 _ _ _ _))
      (.conj (rankedFamilyFormula_delta0 _ _ _)
        (.disj (.existsMem _ (.existsMem _ (.existsMem _ (.conj (successorFormula_delta0 _ _)
          (.conj (memPairFormula_delta0 _ _ _) (KP1Y.delta0_rename successorPacketMatrix.delta0 _))))))
          (.conj (.forallMem _ (.neg (successorFormula_delta0 _ _)))
            (.existsMem _ (KP1Y.delta0_rename rankedUnionMatrix.delta0 _)))))))

private theorem successorSlots_env {M : SetTheory.Structure.{u}} (e : Env M 26) (i P Out w V j p B : M.Domain) :
    ((((((((e.push i).push P).push Out).push w).push V).push j).push p).push B).reindex successorSlots =
      ((e.push p).push Out).push B := by
  rw [Env.mk.injEq]
  constructor
  · funext k
    refine Fin.cases ?_ (fun k => ?_) k
    · rfl
    · refine Fin.cases ?_ (fun k => ?_) k
      · rfl
      · refine Fin.cases ?_ (fun _ => ?_) k <;> rfl
  · rfl

private theorem unionSlots_iff {M : SetTheory.Structure.{u}} (e : Env M 26) (i P Out w V B : M.Domain) :
    Project.Formula.satisfies (((((((e.push i).push P).push Out).push w).push V).push B).reindex unionSlots)
      rankedUnionMatrix.body ↔
        Project.Formula.satisfies ((((oneEnv i).push P).push Out).push B) rankedUnionMatrix.body := by
  apply KP1Y.formula_bound_congr rankedUnionMatrix.body rankedUnionMatrix.freeClosed
  exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun k => Fin.elim0 k))))

theorem rankedStepMatrix_iff {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    (e : Env M 26) (i P Out w : M.Domain) : rankedStepMatrix.denote e i P Out w ↔ RankedStep M e i P Out w := by
  simp only [KP1Y.SigmaRecursion.StepMatrix.denote,rankedStepMatrix,
    Project.Formula.satisfies_existsMem_iff,Project.Formula.satisfies_forallMem_iff,
    Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_disj_iff,Project.Formula.satisfies_neg_iff,
    graphFormula_iff hM.1,rankedFamilyFormula_iff hM,packetFormula_iff hM.1,successorFormula_iff hM.1,memPairFormula_iff hM.1,
    unionSlots_iff,Project.Formula.satisfies_rename,successorSlots_env]
  rfl

end KP1Y.ConstructibleRank
