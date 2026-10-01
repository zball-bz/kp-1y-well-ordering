import KP1Y.BoundedRecursion

/-! 有界关系递归的实际纯 ∈ 闭句及 KPω Hilbert 推导。 -/
namespace KP1Y.Recursion
open YesMetaZFC YesMetaZFC.SetTheory YesMetaZFC.SetTheory.Definitional
open KP1Y.Kuratowski
universe u

def localLeftSlots {n : Nat} : Fin (n+3) → Fin (n+6) :=
  Fin.cases 2 (Fin.cases 0 (Fin.cases 3 (fun i => ⟨i.val+6, by omega⟩)))
def localRightSlots {n : Nat} : Fin (n+3) → Fin (n+6) :=
  Fin.cases 1 (Fin.cases 0 (Fin.cases 3 (fun i => ⟨i.val+6, by omega⟩)))

def localityCore {n : Nat} (φ : StepMatrix n) : Project.Formula 1 (n+2) :=
  Project.Formula.forallMem (.bound 1) (.forallE (.forallE
    (.imp
      (Project.Formula.forallMem (.bound 2) (Project.Formula.forallMem (.bound 4)
        (.iff (memPairFormula (.bound 3) (.bound 1) (.bound 0))
          (memPairFormula (.bound 2) (.bound 1) (.bound 0)))))
      (Project.Formula.forallMem (.bound 3)
        (.iff (φ.body.rename localLeftSlots) (φ.body.rename localRightSlots))))))

private theorem localLeft_env {M : SetTheory.Structure.{u}} {n : Nat}
    (env : Env M n) (Γ B t H J a : M.Domain) :
    ((((((env.push Γ).push B).push t).push H).push J).push a).reindex localLeftSlots =
      ((env.push t).push a).push H := by
  rw [Env.mk.injEq]
  constructor
  · funext i
    refine Fin.cases ?_ (fun i => ?_) i
    · rfl
    · refine Fin.cases ?_ (fun i => ?_) i
      · rfl
      · refine Fin.cases ?_ (fun i => ?_) i <;> rfl
  · rfl

private theorem localRight_env {M : SetTheory.Structure.{u}} {n : Nat}
    (env : Env M n) (Γ B t H J a : M.Domain) :
    ((((((env.push Γ).push B).push t).push H).push J).push a).reindex localRightSlots =
      ((env.push t).push a).push J := by
  rw [Env.mk.injEq]
  constructor
  · funext i
    refine Fin.cases ?_ (fun i => ?_) i
    · rfl
    · refine Fin.cases ?_ (fun i => ?_) i
      · rfl
      · refine Fin.cases ?_ (fun i => ?_) i <;> rfl
  · rfl

theorem localityCore_iff {M : SetTheory.Structure.{u}} (he : Extensional M) {n : Nat}
    (φ : StepMatrix n) (env : Env M n) (Γ B : M.Domain) :
    Project.Formula.satisfies ((env.push Γ).push B) (localityCore φ) ↔
      Local M Γ B (φ.denote env) := by
  simp only [localityCore, Project.Formula.satisfies_forallMem_iff,
    Project.Formula.satisfies_forall_iff, Project.Formula.satisfies_imp_iff,
    Project.Formula.satisfies_iff_iff, memPairFormula_iff he,
    Project.Formula.satisfies_rename, localLeft_env, localRight_env]
  rfl

def resultSlots {n : Nat} : Fin (n+3) → Fin (n+3) :=
  Fin.cases 0 (Fin.cases 2 (Fin.cases 1 (fun i => ⟨i.val+3, by omega⟩)))

def resultCore {n : Nat} (φ : StepMatrix n) : Project.Formula 1 (n+2) :=
  .existsE ((historySchema φ).body.rename resultSlots)

private theorem resultSlots_env {M : SetTheory.Structure.{u}} {n : Nat}
    (env : Env M n) (Γ B H : M.Domain) :
    (((env.push Γ).push B).push H).reindex resultSlots = ((env.push B).push Γ).push H := by
  rw [Env.mk.injEq]
  constructor
  · funext i
    refine Fin.cases ?_ (fun i => ?_) i
    · rfl
    · refine Fin.cases ?_ (fun i => ?_) i
      · rfl
      · refine Fin.cases ?_ (fun i => ?_) i <;> rfl
  · rfl

theorem resultCore_iff {M : SetTheory.Structure.{u}} (he : Extensional M) {n : Nat}
    (φ : StepMatrix n) (env : Env M n) (Γ B : M.Domain) :
    Project.Formula.satisfies ((env.push Γ).push B) (resultCore φ) ↔
      ∃ H, History M (φ.denote env) H Γ B := by
  simp only [resultCore, Project.Formula.satisfies_exists_iff,
    Project.Formula.satisfies_rename, resultSlots_env, historySchema_iff he]

def recursionCore {n : Nat} (φ : StepMatrix n) : Project.Formula 1 (n+2) :=
  .imp (.conj (Project.Formula.isOrdinal (.bound 1)) (localityCore φ)) (resultCore φ)

def recursionSentence {n : Nat} (φ : StepMatrix n) : Project.Sentence :=
  Project.Sentence.forallClosure (recursionCore φ) (by
    simp [recursionCore, localityCore, resultCore, memPairFormula, codeFormula, pairFormula,
      Project.Formula.isOrdinal, Project.Formula.isTransitive, Project.Formula.isWellOrderOn,
      Project.Formula.isLinearOrderOn, Project.Formula.isStrictPartialOrderOn,
      Project.Formula.isIrreflexiveOn, Project.Formula.isTransitiveOn, Project.Formula.isLeastOf,
      Project.Formula.lessOrEqual, Project.Formula.forallMem, Project.Formula.existsMem,
      Project.Formula.subset, Project.Formula.extensionalEq, Definitional.Formula.FreeClosed,
      φ.freeClosed, (historySchema φ).freeClosed])

theorem recursionCore_iff {M : SetTheory.Structure.{u}} (he : Extensional M) {n : Nat}
    (φ : StepMatrix n) (env : Env M n) (Γ B : M.Domain) :
    Project.Formula.satisfies ((env.push Γ).push B) (recursionCore φ) ↔
      (M.IsOrdinal Γ ∧ Local M Γ B (φ.denote env) → ∃ H, History M (φ.denote env) H Γ B) := by
  simp only [recursionCore, Project.Formula.satisfies_imp_iff,
    Project.Formula.satisfies_conj_iff, Project.Formula.satisfies_isOrdinal_iff,
    localityCore_iff he, resultCore_iff he]
  rfl

/-- 所有参数均闭合的实际对象推导。其结论不是宿主 `WellFounded.fix`。 -/
theorem bounded_recursion_derivable {n : Nat} (φ : StepMatrix n) :
    KP1Y.Derives (recursionSentence φ) := by
  apply KP1Y.derives_of_all_models
  intro M hM free
  apply (Project.Formula.satisfies_forallClosure_iff free (recursionCore φ)).mpr
  intro v
  let env : Env M n := ⟨fun i => v i.succ.succ,free⟩
  have he : ({bound := v,free := free} : Env M (n+2)) =
      (env.push (v 1)).push (v 0) := by
    rw [Env.mk.injEq]
    constructor
    · funext i
      refine Fin.cases ?_ (fun i => ?_) i
      · rfl
      · refine Fin.cases ?_ (fun i => ?_) i <;> rfl
    · rfl
  rw [he]
  apply (recursionCore_iff hM.1 φ env (v 1) (v 0)).mpr
  intro h
  exact bounded_recursion_d hM φ env h.1 h.2

end KP1Y.Recursion
