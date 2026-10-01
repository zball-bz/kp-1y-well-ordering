import KP1Y.SigmaRecursion

/-! 一般 Σ₁ 递归的纯 ∈ 闭句；全定义和单值性均在对象前件中明写。 -/
namespace KP1Y.SigmaRecursion
open YesMetaZFC YesMetaZFC.SetTheory YesMetaZFC.SetTheory.Definitional
open KP1Y.Kuratowski KP1Y.Functions
universe u

def totalSlots {n : Nat} : Fin (n+4) → Fin (n+6) :=
  Fin.cases 0 (Fin.cases 1 (Fin.cases 3 (Fin.cases 4 (fun i => ⟨i.val+6, by omega⟩))))

def totalCore {n : Nat} (φ : StepMatrix n) : Project.Formula 1 (n+1) :=
  Project.Formula.forallMem (.bound 0) (.forallE (.forallE
    (.imp (graphFormula (.bound 1) (.bound 2) (.bound 0))
      (.existsE (.existsE (φ.body.rename totalSlots))))))

private theorem totalSlots_env {M : SetTheory.Structure.{u}} {n : Nat}
    (env : Env M n) (Γ i P V v w : M.Domain) :
    ((((((env.push Γ).push i).push P).push V).push v).push w).reindex totalSlots =
      (((env.push i).push P).push v).push w := by
  rw [Env.mk.injEq]
  constructor
  · funext j
    refine Fin.cases ?_ (fun j => ?_) j
    · rfl
    · refine Fin.cases ?_ (fun j => ?_) j
      · rfl
      · refine Fin.cases ?_ (fun j => ?_) j
        · rfl
        · refine Fin.cases ?_ (fun j => ?_) j <;> rfl
  · rfl

theorem totalCore_iff {M : SetTheory.Structure.{u}} (he : Extensional M) {n : Nat}
    (φ : StepMatrix n) (env : Env M n) (Γ : M.Domain) :
    Project.Formula.satisfies (env.push Γ) (totalCore φ) ↔ Total M Γ (φ.denote env) := by
  simp only [totalCore, Project.Formula.satisfies_forallMem_iff,
    Project.Formula.satisfies_forall_iff, Project.Formula.satisfies_imp_iff,
    graphFormula_iff he, Project.Formula.satisfies_exists_iff,
    Project.Formula.satisfies_rename, totalSlots_env]
  rfl

def functionalLeftSlots {n : Nat} : Fin (n+4) → Fin (n+7) :=
  Fin.cases 1 (Fin.cases 3 (Fin.cases 4 (Fin.cases 5 (fun i => ⟨i.val+7, by omega⟩))))

def functionalRightSlots {n : Nat} : Fin (n+4) → Fin (n+7) :=
  Fin.cases 0 (Fin.cases 2 (Fin.cases 4 (Fin.cases 5 (fun i => ⟨i.val+7, by omega⟩))))

def functionalCore {n : Nat} (φ : StepMatrix n) : Project.Formula 1 (n+1) :=
  Project.Formula.forallMem (.bound 0) (.forallE (.forallE (.forallE (.forallE (.forallE
    (.imp (.conj (φ.body.rename functionalLeftSlots) (φ.body.rename functionalRightSlots))
      (Project.Formula.extensionalEq (.bound 3) (.bound 2))))))))

private theorem functionalLeft_env {M : SetTheory.Structure.{u}} {n : Nat}
    (env : Env M n) (Γ i P v v' w w' : M.Domain) :
    (((((((env.push Γ).push i).push P).push v).push v').push w).push w').reindex functionalLeftSlots =
      (((env.push i).push P).push v).push w := by
  rw [Env.mk.injEq]
  constructor
  · funext j
    refine Fin.cases ?_ (fun j => ?_) j
    · rfl
    · refine Fin.cases ?_ (fun j => ?_) j
      · rfl
      · refine Fin.cases ?_ (fun j => ?_) j
        · rfl
        · refine Fin.cases ?_ (fun j => ?_) j <;> rfl
  · rfl

private theorem functionalRight_env {M : SetTheory.Structure.{u}} {n : Nat}
    (env : Env M n) (Γ i P v v' w w' : M.Domain) :
    (((((((env.push Γ).push i).push P).push v).push v').push w).push w').reindex functionalRightSlots =
      (((env.push i).push P).push v').push w' := by
  rw [Env.mk.injEq]
  constructor
  · funext j
    refine Fin.cases ?_ (fun j => ?_) j
    · rfl
    · refine Fin.cases ?_ (fun j => ?_) j
      · rfl
      · refine Fin.cases ?_ (fun j => ?_) j
        · rfl
        · refine Fin.cases ?_ (fun j => ?_) j <;> rfl
  · rfl

theorem functionalCore_iff {M : SetTheory.Structure.{u}} (he : Extensional M) {n : Nat}
    (φ : StepMatrix n) (env : Env M n) (Γ : M.Domain) :
    Project.Formula.satisfies (env.push Γ) (functionalCore φ) ↔ Functional M Γ (φ.denote env) := by
  simp only [functionalCore, Project.Formula.satisfies_forallMem_iff,
    Project.Formula.satisfies_forall_iff, Project.Formula.satisfies_imp_iff,
    Project.Formula.satisfies_conj_iff, Project.Formula.satisfies_extensionalEq_iff_eq he,
    Project.Formula.satisfies_rename, functionalLeft_env, functionalRight_env]
  exact ⟨fun h i hi P v v' w w' h1 h2 => h i hi P v v' w w' ⟨h1,h2⟩,
    fun h i hi P v v' w w' hs => h i hi P v v' w w' hs.1 hs.2⟩

def resultCore {n : Nat} (φ : StepMatrix n) : Project.Formula 1 (n+1) :=
  .existsE (.existsE (certificateMatrix φ).body)

theorem resultCore_iff {M : SetTheory.Structure.{u}} (he : Extensional M) {n : Nat}
    (φ : StepMatrix n) (env : Env M n) (Γ : M.Domain) :
    Project.Formula.satisfies (env.push Γ) (resultCore φ) ↔
      ∃ H B, Certificate M (φ.denote env) Γ H B := by
  simp only [resultCore, Project.Formula.satisfies_exists_iff, certificateMatrix_iff he]

def recursionCore {n : Nat} (φ : StepMatrix n) : Project.Formula 1 (n+1) :=
  .imp (.conj (Project.Formula.isOrdinal (.bound 0)) (.conj (totalCore φ) (functionalCore φ)))
    (resultCore φ)

def recursionSentence {n : Nat} (φ : StepMatrix n) : Project.Sentence :=
  Project.Sentence.forallClosure (recursionCore φ) (by
    simp [recursionCore, totalCore, functionalCore, resultCore, graphFormula,
      memPairFormula, codeFormula, pairFormula, Project.Formula.isOrdinal,
      Project.Formula.isTransitive, Project.Formula.isWellOrderOn, Project.Formula.isLinearOrderOn,
      Project.Formula.isStrictPartialOrderOn, Project.Formula.isIrreflexiveOn,
      Project.Formula.isTransitiveOn, Project.Formula.isLeastOf, Project.Formula.lessOrEqual,
      Project.Formula.forallMem, Project.Formula.existsMem, Project.Formula.subset,
      Project.Formula.extensionalEq, Definitional.Formula.FreeClosed,
      φ.freeClosed, (certificateMatrix φ).freeClosed])

theorem recursionCore_iff {M : SetTheory.Structure.{u}} (he : Extensional M) {n : Nat}
    (φ : StepMatrix n) (env : Env M n) (Γ : M.Domain) :
    Project.Formula.satisfies (env.push Γ) (recursionCore φ) ↔
      (M.IsOrdinal Γ ∧ Total M Γ (φ.denote env) ∧ Functional M Γ (φ.denote env) →
        ∃ H B, Certificate M (φ.denote env) Γ H B) := by
  simp only [recursionCore, Project.Formula.satisfies_imp_iff,
    Project.Formula.satisfies_conj_iff, Project.Formula.satisfies_isOrdinal_iff,
    totalCore_iff he, functionalCore_iff he, resultCore_iff he]
  rfl

/-- 从任意 KPω 模型的内部递归，经已证明的完备性产生实际 Hilbert 推导。 -/
theorem sigma_recursion_derivable {n : Nat} (φ : StepMatrix n) :
    KP1Y.Derives (recursionSentence φ) := by
  apply KP1Y.derives_of_all_models
  intro M hM free
  apply (Project.Formula.satisfies_forallClosure_iff free (recursionCore φ)).mpr
  intro v
  let env : Env M n := ⟨fun i => v i.succ,free⟩
  have he : ({bound := v,free := free} : Env M (n+1)) = env.push (v 0) := by
    rw [Env.mk.injEq]
    constructor
    · funext i
      refine Fin.cases ?_ (fun i => ?_) i <;> rfl
    · rfl
  rw [he]
  apply (recursionCore_iff hM.1 φ env (v 0)).mpr
  intro h
  exact sigma_recursion_d hM φ env h.1 h.2.1 h.2.2

end KP1Y.SigmaRecursion
