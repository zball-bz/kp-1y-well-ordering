import KP1Y.SigmaRecursion
import KP1Y.NaturalNumbers

/-! 任意有界状态集合上的 Δ₀ 函数迭代。非法输入历史使用指定初态，保证对象全定义。 -/
namespace KP1Y.Iteration
open YesMetaZFC YesMetaZFC.SetTheory YesMetaZFC.SetTheory.Definitional
open KP1Y.Kuratowski KP1Y.Functions KP1Y.Bounded
universe u

def nextDenote {M : SetTheory.Structure.{u}} {n : Nat} (φ : Project.Delta0BinarySchema n) (env : Env M n)
    (x y : M.Domain) : Prop := Project.Formula.satisfies ((env.push x).push y) φ.body

def StateStep (M : SetTheory.Structure.{u}) (next : M.Domain → M.Domain → Prop)
    (S base i P value w : M.Domain) : Prop :=
  M.mem value S ∧ Graph M P i w ∧
    (((∀ x, ¬M.mem x i) ∧ value=base) ∨
      ∃ j, M.mem j i ∧ ∃ x, M.mem x w ∧ M.SuccessorOf i j ∧ MemPair M P j x ∧
        ((M.mem x S ∧ next x value) ∨ (¬M.mem x S ∧ value=base)))

def iterationNextSlots {n : Nat} : Fin (n+2) → Fin (n+8) :=
  Fin.cases 3 (Fin.cases 0 (fun i => ⟨i.val+8,by omega⟩))

def stateMatrix {n : Nat} (φ : Project.Delta0BinarySchema n) : KP1Y.SigmaRecursion.StepMatrix (n+2) where
  body := .conj (.mem (.bound 1) (.bound 5)) (.conj (graphFormula (.bound 2) (.bound 3) (.bound 0))
    (.disj (.conj (emptyFormula (.bound 3)) (Project.Formula.extensionalEq (.bound 1) (.bound 4)))
      (Project.Formula.existsMem (.bound 3) (Project.Formula.existsMem (.bound 1)
        (.conj (successorFormula (.bound 5) (.bound 1))
          (.conj (memPairFormula (.bound 4) (.bound 1) (.bound 0))
            (.disj (.conj (.mem (.bound 0) (.bound 7)) (φ.body.rename iterationNextSlots))
              (.conj (.neg (.mem (.bound 0) (.bound 7))) (Project.Formula.extensionalEq (.bound 3) (.bound 6))))))))))
  freeClosed := by
    simp [graphFormula, emptyFormula, successorFormula, memPairFormula, codeFormula, pairFormula,
      Project.Formula.forallMem, Project.Formula.existsMem, Definitional.Formula.FreeClosed, φ.freeClosed]
  delta0 := .conj (.mem _ _) (.conj (graphFormula_delta0 _ _ _)
    (.disj (.conj (emptyFormula_delta0 _) (.atom _ _ _)) (.existsMem _ (.existsMem _
      (.conj (successorFormula_delta0 _ _) (.conj (memPairFormula_delta0 _ _ _)
        (.disj (.conj (.mem _ _) (KP1Y.delta0_rename φ.delta0 _)) (.conj (.neg (.mem _ _)) (.atom _ _ _)))))))))

private theorem iterationNextSlots_env {M : SetTheory.Structure.{u}} {n : Nat}
    (env : Env M n) (S base i P value w j x : M.Domain) :
    ((((((((env.push S).push base).push i).push P).push value).push w).push j).push x).reindex iterationNextSlots =
      (env.push x).push value := by
  rw [Env.mk.injEq]
  constructor
  · funext k
    refine Fin.cases ?_ (fun k => ?_) k
    · rfl
    · refine Fin.cases ?_ (fun k => ?_) k <;> rfl
  · rfl

theorem stateMatrix_iff {M : SetTheory.Structure.{u}} (he : Extensional M) {n : Nat}
    (φ : Project.Delta0BinarySchema n) (env : Env M n) (S base i P value w : M.Domain) :
    (stateMatrix φ).denote ((env.push S).push base) i P value w ↔ StateStep M (nextDenote φ env) S base i P value w := by
  simp only [KP1Y.SigmaRecursion.StepMatrix.denote, stateMatrix, Project.Formula.satisfies_conj_iff,
    Project.Formula.satisfies_disj_iff, Project.Formula.satisfies_existsMem_iff,
    Project.Formula.satisfies_mem_iff, Project.Formula.satisfies_neg_iff,
    Project.Formula.satisfies_extensionalEq_iff_eq he, graphFormula_iff he, emptyFormula_iff,
    successorFormula_iff he, memPairFormula_iff he, Project.Formula.satisfies_rename, iterationNextSlots_env]
  rfl

theorem stateMatrix_total {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory) {n : Nat}
    (φ : Project.Delta0BinarySchema n) (env : Env M n) {ω S base : M.Domain} (hω : M.IsOmega ω)
    (hBase : M.mem base S) (hNext : ∀ x, M.mem x S → ∃ y, M.mem y S ∧ nextDenote φ env x y) :
    KP1Y.SigmaRecursion.Total M ω ((stateMatrix φ).denote ((env.push S).push base)) := by
  classical
  intro i hi P V hP
  rcases KP1Y.Naturals.natural_cases hM hω hi with he | ⟨j,_,hSucc⟩
  · exact ⟨base,V,(stateMatrix_iff hM.1 φ env S base i P base V).mpr ⟨hBase,hP,Or.inl ⟨he,rfl⟩⟩⟩
  · obtain ⟨x,hx,hAt⟩ := hP.total j hSucc.predecessor_mem
    by_cases hxS : M.mem x S
    · obtain ⟨y,hy,hNextxy⟩ := hNext x hxS
      exact ⟨y,V,(stateMatrix_iff hM.1 φ env S base i P y V).mpr
        ⟨hy,hP,Or.inr ⟨j,hSucc.predecessor_mem,x,hx,hSucc,hAt,Or.inl ⟨hxS,hNextxy⟩⟩⟩⟩
    · exact ⟨base,V,(stateMatrix_iff hM.1 φ env S base i P base V).mpr
        ⟨hBase,hP,Or.inr ⟨j,hSucc.predecessor_mem,x,hx,hSucc,hAt,Or.inr ⟨hxS,rfl⟩⟩⟩⟩

theorem stateMatrix_functional {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory) {n : Nat}
    (φ : Project.Delta0BinarySchema n) (env : Env M n) {ω S base : M.Domain} (hω : M.IsOmega ω)
    (hNext : ∀ x, M.mem x S → ∀ y, M.mem y S → ∀ z, M.mem z S →
      nextDenote φ env x y → nextDenote φ env x z → y=z) :
    KP1Y.SigmaRecursion.Functional M ω ((stateMatrix φ).denote ((env.push S).push base)) := by
  intro i hi P y z w w' hy hz
  obtain ⟨hyS,hP,hyCases⟩ := (stateMatrix_iff hM.1 φ env S base i P y w).mp hy
  obtain ⟨hzS,_,hzCases⟩ := (stateMatrix_iff hM.1 φ env S base i P z w').mp hz
  rcases hyCases with ⟨he,hyBase⟩ | ⟨j,hj,x,_,hs,hAt,hxCase⟩
  · rcases hzCases with ⟨_,hzBase⟩ | ⟨j,hj,_⟩
    · exact hyBase.trans hzBase.symm
    · exact False.elim (he j hj)
  · rcases hzCases with ⟨he,_⟩ | ⟨j',_,x',_,hs',hAt',hxCase'⟩
    · exact False.elim (he j hj)
    · have hjj' := Structure.SuccessorOf.predecessor_eq hM.1
        (((KP1Y.Naturals.omega_isOrdinal_d hM hω).mem hi).mem hj) hs hs'
      subst j'
      have hxx' := hP.unique j x x' hAt hAt'
      subst x'
      rcases hxCase with ⟨hx,hxy⟩ | ⟨hx,hyBase⟩ <;> rcases hxCase' with ⟨hx',hxz⟩ | ⟨hx',hzBase⟩
      · exact hNext x hx y hyS z hzS hxy hxz
      · exact False.elim (hx' hx)
      · exact False.elim (hx hx')
      · exact hyBase.trans hzBase.symm

end KP1Y.Iteration
