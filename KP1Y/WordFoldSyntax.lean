import KP1Y.WordBudgets

/-! 内部字词逐项折叠c_{p+1}=κ·c_p+s(p)，坏前缀旧值非序数时显式返回空集。 -/
namespace KP1Y.WordRank
open YesMetaZFC YesMetaZFC.SetTheory YesMetaZFC.SetTheory.Definitional
open KP1Y.Kuratowski KP1Y.Functions KP1Y.Bounded KP1Y.Arithmetic
universe u

def FoldStep (M : SetTheory.Structure.{u}) (s κ i P c W : M.Domain) : Prop :=
  ∃ V, M.mem V W ∧ Graph M P i V ∧
    (((∀ x, ¬M.mem x i) ∧ ∀ x, ¬M.mem x c) ∨
      ∃ p, M.mem p i ∧ ∃ b, M.mem b V ∧ ∃ a, M.mem a κ ∧
        M.SuccessorOf i p ∧ MemPair M P p b ∧ MemPair M s p a ∧
          ((M.IsOrdinal b ∧ ∃ u, M.mem u W ∧ ∃ C, M.mem C W ∧ ∃ D, M.mem D W ∧
            ProductCertificate M κ b u C ∧ KP1Y.OrdinalIteration.ValueCertificate successorMatrix (oneEnv u) a c D) ∨
            (¬M.IsOrdinal b ∧ ∀ x, ¬M.mem x c)))

private def foldPositive : Project.Formula 1 13 :=
  .conj (productCertificateFormula (.bound 12) (.bound 4) (.bound 2) (.bound 1))
    (sumCertificateFormula (.bound 2) (.bound 3) (.bound 8) (.bound 0))

private theorem foldPositive_freeClosed : foldPositive.FreeClosed := by
  simp only [foldPositive,Definitional.Formula.FreeClosed]
  exact ⟨productCertificateFormula_freeClosed _ _ _ _ rfl rfl rfl rfl,
    sumCertificateFormula_freeClosed _ _ _ _ rfl rfl rfl rfl⟩

def foldMatrix : KP1Y.SigmaRecursion.StepMatrix 2 where
  body := Project.Formula.existsMem (.bound 0)
    (.conj (graphFormula (.bound 3) (.bound 4) (.bound 0))
      (.disj (.conj (emptyFormula (.bound 4)) (emptyFormula (.bound 2)))
        (Project.Formula.existsMem (.bound 4) (Project.Formula.existsMem (.bound 1) (Project.Formula.existsMem (.bound 8)
          (.conj (successorFormula (.bound 7) (.bound 2))
            (.conj (memPairFormula (.bound 6) (.bound 2) (.bound 1))
              (.conj (memPairFormula (.bound 8) (.bound 2) (.bound 0))
                (.disj (.conj (ordinalFormula (.bound 1))
                    (Project.Formula.existsMem (.bound 4) (Project.Formula.existsMem (.bound 5)
                      (Project.Formula.existsMem (.bound 6) foldPositive))))
                  (.conj (.neg (ordinalFormula (.bound 1))) (emptyFormula (.bound 5))))))))))))
  freeClosed := by
    simp [graphFormula,ordinalFormula,Project.Formula.isTransitive,successorFormula,emptyFormula,memPairFormula,
      codeFormula,pairFormula,Project.Formula.existsMem,Project.Formula.forallMem,Definitional.Formula.FreeClosed,foldPositive_freeClosed]
  delta0 := .existsMem _ (.conj (graphFormula_delta0 _ _ _)
    (.disj (.conj (emptyFormula_delta0 _) (emptyFormula_delta0 _))
      (.existsMem _ (.existsMem _ (.existsMem _ (.conj (successorFormula_delta0 _ _)
        (.conj (memPairFormula_delta0 _ _ _) (.conj (memPairFormula_delta0 _ _ _)
          (.disj (.conj (ordinalFormula_delta0 _) (.existsMem _ (.existsMem _ (.existsMem _
            (.conj (productCertificateFormula_delta0 _ _ _ _) (sumCertificateFormula_delta0 _ _ _ _))))))
            (.conj (.neg (ordinalFormula_delta0 _)) (emptyFormula_delta0 _)))))))))))

theorem foldMatrix_iff {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory) (e : Env M 2) (i P c W : M.Domain) :
    foldMatrix.denote e i P c W ↔ FoldStep M (e.bound 0) (e.bound 1) i P c W := by
  simp only [KP1Y.SigmaRecursion.StepMatrix.denote,foldMatrix,foldPositive,
    Project.Formula.satisfies_existsMem_iff,Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_disj_iff,
    Project.Formula.satisfies_neg_iff,graphFormula_iff hM.1,ordinalFormula_iff hM,emptyFormula_iff,
    successorFormula_iff hM.1,memPairFormula_iff hM.1,productCertificateFormula_iff hM,sumCertificateFormula_iff hM]
  rfl

end KP1Y.WordRank
