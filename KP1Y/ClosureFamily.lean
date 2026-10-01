import KP1Y.ClosureIterationSyntax

/-! 实际存在的 ω 次枚举器迭代族，所有值均为模型内部的函数图。 -/
namespace KP1Y.Closure
open YesMetaZFC YesMetaZFC.SetTheory
open KP1Y.Kuratowski KP1Y.Functions
universe u

structure EnumeratorFamily (M : SetTheory.Structure.{u}) (C : Data M.Domain) (base R V : M.Domain) : Prop where
  graph : Graph M R C.omega V
  values : ∀ i, M.mem i C.omega → ∀ E, MemPair M R i E → Graph M E C.omega C.carrier
  initial : MemPair M R C.zero base
  step : ∀ i j E F, M.SuccessorOf j i → MemPair M R i E → MemPair M R j F → NextEnumerator M C E F

theorem enumerator_family_exists_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : Data M.Domain} (hC : Valid M C) {base : M.Domain} (hBase : Graph M base C.omega C.carrier) :
    ∃ R V, EnumeratorFamily M C base R V := by
  obtain ⟨R,V,Q,hR⟩ := KP1Y.SigmaRecursion.value_recursion_d hM iterationMatrix ((dataEnv C).push base)
    (KP1Y.Naturals.omega_isOrdinal_d hM hC.omega) (iterationMatrix_total_d hM hC hBase) (iterationMatrix_functional_d hM hC base)
  have hStep : ∀ i, M.mem i C.omega → ∀ E, MemPair M R i E →
      ∃ P W, Prefix M P R i V ∧ EnumeratorStep M C base i P E W := by
    intro i hi E hAt
    obtain ⟨P,hPV,hQi⟩ := hR.prefixes.total i hi
    obtain ⟨hPrefix,W,_,hState⟩ := hR.obeys i hi P hPV E (hR.values.bounds hM.1 hAt).2 hQi hAt
    exact ⟨P,W,hPrefix,(iterationMatrix_iff hM.1 C base i P E W).mp hState⟩
  have hValues : ∀ i, M.mem i C.omega → ∀ E, MemPair M R i E → Graph M E C.omega C.carrier := by
    intro i hi E hAt
    obtain ⟨_,_,_,hState⟩ := hStep i hi E hAt
    exact hState.1
  refine ⟨R,V,hR.values,hValues,?_,?_⟩
  · obtain ⟨E,_,hAt⟩ := hR.values.total C.zero hC.zero_nat
    obtain ⟨_,_,_,hState⟩ := hStep C.zero hC.zero_nat E hAt
    rcases hState.2.2 with ⟨_,he⟩ | ⟨j,hj,_⟩
    · subst E
      exact hAt
    · exact False.elim (hC.zero_empty j hj)
  · intro i j E F hSucc hE hF
    have hi := (hR.values.bounds hM.1 hE).1
    have hj := (hR.values.bounds hM.1 hF).1
    obtain ⟨P,W,hPrefix,hState⟩ := hStep j hj F hF
    rcases hState.2.2 with ⟨hEmpty,_⟩ | ⟨k,_,old,_,hSucc',hAt,hCase⟩
    · exact False.elim (hEmpty i hSucc.predecessor_mem)
    · have hik := Structure.SuccessorOf.predecessor_eq hM.1
        ((KP1Y.Naturals.omega_isOrdinal_d hM hC.omega).mem hi) hSucc hSucc'
      subst k
      have hOldAt := (hPrefix.all_rows hM.1 hR.values i hSucc.predecessor_mem old).mp hAt
      have hOld := hR.values.unique i E old hE hOldAt
      subst old
      rcases hCase with ⟨_,hNext⟩ | ⟨hBad,_⟩
      · exact hNext
      · exact False.elim (hBad (hValues i hi E hE))

end KP1Y.Closure
