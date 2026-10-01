import KP1Y.FunctionGraphs
import KP1Y.JointCollection

/-! 集合值 Σ₁ 递归的有界证书：函数、前缀及一步见证都落在一个实际集合中。 -/
namespace KP1Y.SigmaRecursion
open YesMetaZFC YesMetaZFC.SetTheory YesMetaZFC.SetTheory.Definitional
open KP1Y.Kuratowski KP1Y.Functions
universe u

/-- 槽位依次为：一步证书、当前值、严格前缀函数、当前序数，然后是参数。 -/
structure StepMatrix (n : Nat) where
  body : Project.Formula 1 (n+4)
  freeClosed : body.FreeClosed
  delta0 : body.IsDelta0

def StepMatrix.denote {M : SetTheory.Structure.{u}} {n : Nat} (φ : StepMatrix n)
    (env : Env M n) (i P v w : M.Domain) : Prop :=
  Project.Formula.satisfies ((((env.push i).push P).push v).push w) φ.body

def Total (M : SetTheory.Structure.{u}) (Γ : M.Domain)
    (step : M.Domain → M.Domain → M.Domain → M.Domain → Prop) : Prop :=
  ∀ i, M.mem i Γ → ∀ P V, Graph M P i V → ∃ v w, step i P v w

def Functional (M : SetTheory.Structure.{u}) (Γ : M.Domain)
    (step : M.Domain → M.Domain → M.Domain → M.Domain → Prop) : Prop :=
  ∀ i, M.mem i Γ → ∀ P v v' w w', step i P v w → step i P v' w' → v=v'

structure ValueHistory (M : SetTheory.Structure.{u})
    (step : M.Domain → M.Domain → M.Domain → M.Domain → Prop)
    (H δ V Q : M.Domain) : Prop where
  values : Graph M H δ V
  prefixes : Graph M Q δ V
  obeys : ∀ i, M.mem i δ → ∀ P, M.mem P V → ∀ v, M.mem v V →
    MemPair M Q i P → MemPair M H i v →
      Prefix M P H i V ∧ ∃ w, M.mem w V ∧ step i P v w

def historyStepSlots {n : Nat} : Fin (n+4) → Fin (n+8) :=
  Fin.cases 0 (Fin.cases 1 (Fin.cases 2 (Fin.cases 3 (fun i => ⟨i.val+8, by omega⟩))))

def historyVerifier {n : Nat} (φ : StepMatrix n) : Project.Formula 1 (n+4) :=
  .conj (graphFormula (.bound 2) (.bound 3) (.bound 1))
    (.conj (graphFormula (.bound 0) (.bound 3) (.bound 1))
      (Project.Formula.forallMem (.bound 3) (Project.Formula.forallMem (.bound 2)
        (Project.Formula.forallMem (.bound 3)
          (.imp (.conj (memPairFormula (.bound 3) (.bound 2) (.bound 1))
              (memPairFormula (.bound 5) (.bound 2) (.bound 0)))
            (.conj (prefixFormula (.bound 1) (.bound 5) (.bound 2) (.bound 4))
              (Project.Formula.existsMem (.bound 4) (φ.body.rename historyStepSlots))))))))

theorem historyVerifier_delta0 {n : Nat} (φ : StepMatrix n) : (historyVerifier φ).IsDelta0 :=
  .conj (graphFormula_delta0 _ _ _) (.conj (graphFormula_delta0 _ _ _)
    (.forallMem _ (.forallMem _ (.forallMem _
      (.imp (.conj (memPairFormula_delta0 _ _ _) (memPairFormula_delta0 _ _ _))
        (.conj (prefixFormula_delta0 _ _ _ _) (.existsMem _ (KP1Y.delta0_rename φ.delta0 _))))))))

theorem historyVerifier_freeClosed {n : Nat} (φ : StepMatrix n) : (historyVerifier φ).FreeClosed := by
  simp [historyVerifier, graphFormula, prefixFormula, memPairFormula, codeFormula, pairFormula,
    Project.Formula.forallMem, Project.Formula.existsMem, Definitional.Formula.FreeClosed, φ.freeClosed]

private theorem historyStepSlots_env {M : SetTheory.Structure.{u}} {n : Nat}
    (env : Env M n) (δ H V Q i P v w : M.Domain) :
    ((((((((env.push δ).push H).push V).push Q).push i).push P).push v).push w).reindex historyStepSlots =
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

theorem historyVerifier_iff {M : SetTheory.Structure.{u}} (he : Extensional M) {n : Nat}
    (φ : StepMatrix n) (env : Env M n) (δ H V Q : M.Domain) :
    Project.Formula.satisfies ((((env.push δ).push H).push V).push Q) (historyVerifier φ) ↔
      ValueHistory M (φ.denote env) H δ V Q := by
  simp only [historyVerifier, Project.Formula.satisfies_conj_iff, graphFormula_iff he,
    Project.Formula.satisfies_forallMem_iff, Project.Formula.satisfies_imp_iff,
    Project.Formula.satisfies_existsMem_iff, memPairFormula_iff he, prefixFormula_iff he,
    Project.Formula.satisfies_rename, historyStepSlots_env]
  constructor
  · rintro ⟨hH,hQ,hStep⟩
    exact ⟨hH,hQ,fun i hi P hP v hv hQi hHi => hStep i hi P hP v hv ⟨hQi,hHi⟩⟩
  · intro h
    exact ⟨h.values,h.prefixes,fun i hi P hP v hv hs => h.obeys i hi P hP v hv hs.1 hs.2⟩

def Certificate (M : SetTheory.Structure.{u})
    (step : M.Domain → M.Domain → M.Domain → M.Domain → Prop) (δ H B : M.Domain) : Prop :=
  ∃ V, M.mem V B ∧ ∃ Q, M.mem Q B ∧ ValueHistory M step H δ V Q

def certificateSlots {n : Nat} : Fin (n+4) → Fin (n+5) :=
  Fin.cases 0 (Fin.cases 1 (Fin.cases 3 (Fin.cases 4 (fun i => ⟨i.val+5, by omega⟩))))

/-- 外面只需一个无界存在量词；所有辅助字段的检查均为有界量词。 -/
def certificateMatrix {n : Nat} (φ : StepMatrix n) : KP1Y.WitnessMatrix n where
  body := Project.Formula.existsMem (.bound 0) (Project.Formula.existsMem (.bound 1)
    ((historyVerifier φ).rename certificateSlots))
  freeClosed := by
    simp [Project.Formula.existsMem, Definitional.Formula.FreeClosed, historyVerifier_freeClosed]
  delta0 := .existsMem _ (.existsMem _ (KP1Y.delta0_rename (historyVerifier_delta0 φ) _))

private theorem certificateSlots_env {M : SetTheory.Structure.{u}} {n : Nat}
    (env : Env M n) (δ H B V Q : M.Domain) :
    (((((env.push δ).push H).push B).push V).push Q).reindex certificateSlots =
      (((env.push δ).push H).push V).push Q := by
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

theorem certificateMatrix_iff {M : SetTheory.Structure.{u}} (he : Extensional M) {n : Nat}
    (φ : StepMatrix n) (env : Env M n) (δ H B : M.Domain) :
    Project.Formula.satisfies (((env.push δ).push H).push B) (certificateMatrix φ).body ↔
      Certificate M (φ.denote env) δ H B := by
  simp only [certificateMatrix, Project.Formula.satisfies_existsMem_iff,
    Project.Formula.satisfies_rename, certificateSlots_env, historyVerifier_iff he]
  rfl

theorem certificate_exists {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {step : M.Domain → M.Domain → M.Domain → M.Domain → Prop} {δ H V Q : M.Domain}
    (hH : ValueHistory M step H δ V Q) : ∃ B, Certificate M step δ H B := by
  obtain ⟨B,hB⟩ := SetTheory.KP.exists_pair (KP1Y.models_weakKP hM) V Q
  exact ⟨B,V,(hB V).mpr (Or.inl rfl),Q,(hB Q).mpr (Or.inr rfl),hH⟩

end KP1Y.SigmaRecursion
