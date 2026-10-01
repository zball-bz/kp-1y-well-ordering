import KP1Y.ClosureExpansionCoverage

/-! 以枚举函数图为集合值的 Σ₁ 递归矩阵；不使用全部函数构成的幂集。 -/
namespace KP1Y.Closure
open YesMetaZFC YesMetaZFC.SetTheory YesMetaZFC.SetTheory.Definitional
open KP1Y.Kuratowski KP1Y.Functions KP1Y.Bounded
universe u

def EnumeratorStep (M : SetTheory.Structure.{u}) (C : Data M.Domain) (base i P E V : M.Domain) : Prop :=
  Graph M E C.omega C.carrier ∧ Graph M P i V ∧
    (((∀ x, ¬M.mem x i) ∧ E=base) ∨
      ∃ j, M.mem j i ∧ ∃ old, M.mem old V ∧ M.SuccessorOf i j ∧ MemPair M P j old ∧
        ((Graph M old C.omega C.carrier ∧ NextEnumerator M C old E) ∨
          (¬Graph M old C.omega C.carrier ∧ E=base)))

private def iterationContext : Data (Project.Term 17) :=
  ⟨.bound 5,.bound 6,.bound 7,.bound 8,.bound 9,.bound 10,.bound 11,.bound 12,.bound 13,.bound 14,.bound 15,.bound 16⟩

def iterationMatrix : KP1Y.SigmaRecursion.StepMatrix 13 where
  body := .conj (graphFormula (.bound 1) (.bound 5) (.bound 6)) (.conj (graphFormula (.bound 2) (.bound 3) (.bound 0))
    (.disj (.conj (emptyFormula (.bound 3)) (Project.Formula.extensionalEq (.bound 1) (.bound 4)))
      (Project.Formula.existsMem (.bound 3) (Project.Formula.existsMem (.bound 1)
        (.conj (successorFormula (.bound 5) (.bound 1)) (.conj (memPairFormula (.bound 4) (.bound 1) (.bound 0))
          (.disj (.conj (graphFormula (.bound 0) (.bound 7) (.bound 8))
              (nextEnumeratorFormula iterationContext.weaken.weaken (.bound 0) (.bound 3)))
            (.conj (.neg (graphFormula (.bound 0) (.bound 7) (.bound 8)))
              (Project.Formula.extensionalEq (.bound 3) (.bound 6))))))))))
  freeClosed := by
    simp [nextEnumeratorFormula, nextPointFormula, operationQueryFormula, decodesFormula,
      Cardinal.wordMapFormula, Assignments.tupleValueFormula, graphFormula, emptyFormula, successorFormula,
      memPairFormula, codeFormula, pairFormula, Data.weaken, Data.map, iterationContext,
      Project.Formula.existsMem, Project.Formula.forallMem, Definitional.Formula.FreeClosed]
  delta0 := .conj (graphFormula_delta0 _ _ _) (.conj (graphFormula_delta0 _ _ _)
    (.disj (.conj (emptyFormula_delta0 _) (.atom _ _ _)) (.existsMem _ (.existsMem _
      (.conj (successorFormula_delta0 _ _) (.conj (memPairFormula_delta0 _ _ _)
        (.disj (.conj (graphFormula_delta0 _ _ _) (nextEnumeratorFormula_delta0 _ _ _))
          (.conj (.neg (graphFormula_delta0 _ _ _)) (.atom _ _ _)))))))))

theorem iterationMatrix_iff {M : SetTheory.Structure.{u}} (he : Extensional M)
    (C : Data M.Domain) (base i P E V : M.Domain) :
    iterationMatrix.denote ((dataEnv C).push base) i P E V ↔ EnumeratorStep M C base i P E V := by
  simp only [KP1Y.SigmaRecursion.StepMatrix.denote, iterationMatrix,
    Project.Formula.satisfies_conj_iff, Project.Formula.satisfies_disj_iff,
    Project.Formula.satisfies_existsMem_iff, Project.Formula.satisfies_neg_iff,
    Project.Formula.satisfies_extensionalEq_iff_eq he, graphFormula_iff he,
    emptyFormula_iff, successorFormula_iff he, memPairFormula_iff he,
    nextEnumeratorFormula_iff he, Data.eval_weaken]
  rfl

theorem iterationMatrix_total_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : Data M.Domain} (hC : Valid M C) {base : M.Domain} (hBase : Graph M base C.omega C.carrier) :
    KP1Y.SigmaRecursion.Total M C.omega (iterationMatrix.denote ((dataEnv C).push base)) := by
  classical
  intro i hi P V hP
  rcases KP1Y.Naturals.natural_cases hM hC.omega hi with hEmpty | ⟨j,_,hSucc⟩
  · exact ⟨base,V,(iterationMatrix_iff hM.1 C base i P base V).mpr ⟨hBase,hP,Or.inl ⟨hEmpty,rfl⟩⟩⟩
  · obtain ⟨old,hOld,hAt⟩ := hP.total j hSucc.predecessor_mem
    by_cases hGood : Graph M old C.omega C.carrier
    · obtain ⟨E,hE⟩ := next_enumerator_exists_d hM hC hGood
      exact ⟨E,V,(iterationMatrix_iff hM.1 C base i P E V).mpr
        ⟨hE.graph,hP,Or.inr ⟨j,hSucc.predecessor_mem,old,hOld,hSucc,hAt,Or.inl ⟨hGood,hE⟩⟩⟩⟩
    · exact ⟨base,V,(iterationMatrix_iff hM.1 C base i P base V).mpr
        ⟨hBase,hP,Or.inr ⟨j,hSucc.predecessor_mem,old,hOld,hSucc,hAt,Or.inr ⟨hGood,rfl⟩⟩⟩⟩

theorem iterationMatrix_functional_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : Data M.Domain} (hC : Valid M C) (base : M.Domain) :
    KP1Y.SigmaRecursion.Functional M C.omega (iterationMatrix.denote ((dataEnv C).push base)) := by
  intro i hi P E F V W hE hF
  obtain ⟨_,hP,hCases⟩ := (iterationMatrix_iff hM.1 C base i P E V).mp hE
  obtain ⟨_,_,hCases'⟩ := (iterationMatrix_iff hM.1 C base i P F W).mp hF
  rcases hCases with ⟨hEmpty,he⟩ | ⟨j,hj,old,_,hSucc,hAt,hCase⟩
  · rcases hCases' with ⟨_,hf⟩ | ⟨j,hj,_⟩
    · exact he.trans hf.symm
    · exact False.elim (hEmpty j hj)
  · rcases hCases' with ⟨hEmpty,_⟩ | ⟨j',_,old',_,hSucc',hAt',hCase'⟩
    · exact False.elim (hEmpty j hj)
    · have hjs := Structure.SuccessorOf.predecessor_eq hM.1
        (((KP1Y.Naturals.omega_isOrdinal_d hM hC.omega).mem hi).mem hj) hSucc hSucc'
      subst j'
      have hOlds := hP.unique j old old' hAt hAt'
      subst old'
      rcases hCase with ⟨hGood,hNext⟩ | ⟨hGood,he⟩ <;> rcases hCase' with ⟨hGood',hNext'⟩ | ⟨hGood',hf⟩
      · exact next_enumerator_unique hM.1 hNext hNext'
      · exact False.elim (hGood' hGood)
      · exact False.elim (hGood hGood')
      · exact he.trans hf.symm

end KP1Y.Closure
