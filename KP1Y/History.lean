import KP1Y.RelationComprehension
import KP1Y.OrdinalInduction

/-! 关系表的内部递归历史：验证谓词为 Δ₀，唯一性用内部最小反例。 -/
namespace KP1Y.Recursion
open YesMetaZFC YesMetaZFC.SetTheory YesMetaZFC.SetTheory.Definitional
open KP1Y.Kuratowski
universe u

structure StepMatrix (n : Nat) where
  body : Project.Formula 1 (n+3)
  freeClosed : body.FreeClosed
  delta0 : body.IsDelta0

def StepMatrix.denote {M : SetTheory.Structure.{u}} {n : Nat}
    (φ : StepMatrix n) (env : Env M n) (t a H : M.Domain) : Prop :=
  Project.Formula.satisfies (((env.push t).push a).push H) φ.body

def History (M : SetTheory.Structure.{u}) (step : M.Domain → M.Domain → M.Domain → Prop)
    (H δ B : M.Domain) : Prop :=
  (∀ p, M.mem p H → ∃ t, M.mem t δ ∧ ∃ a, M.mem a B ∧ Codes M p t a) ∧
    ∀ t, M.mem t δ → ∀ a, M.mem a B → (MemPair M H t a ↔ step t a H)

/-- 当前行只读取严格更早的行。这是算子的明确条件，须由实际 R 的定义证明。 -/
def Local (M : SetTheory.Structure.{u}) (Γ B : M.Domain)
    (step : M.Domain → M.Domain → M.Domain → Prop) : Prop :=
  ∀ t, M.mem t Γ → ∀ H J,
    (∀ s, M.mem s t → ∀ a, M.mem a B → (MemPair M H s a ↔ MemPair M J s a)) →
    ∀ a, M.mem a B → (step t a H ↔ step t a J)

def historySlots {n : Nat} : Fin (n+3) → Fin (n+5) :=
  Fin.cases 2 (Fin.cases 0 (Fin.cases 1 (fun i => ⟨i.val+5, by omega⟩)))

def historySchema {n : Nat} (φ : StepMatrix n) : Project.Delta0BinarySchema (n+1) where
  body := .conj
    (Project.Formula.forallMem (.bound 0) (Project.Formula.existsMem (.bound 2)
      (Project.Formula.existsMem (.bound 4) (codeFormula (.bound 2) (.bound 1) (.bound 0)))))
    (Project.Formula.forallMem (.bound 1) (Project.Formula.forallMem (.bound 3)
      (.iff (memPairFormula (.bound 2) (.bound 1) (.bound 0)) (φ.body.rename historySlots))))
  freeClosed := by
    simp [Project.Formula.forallMem, Project.Formula.existsMem, codeFormula,
      memPairFormula, pairFormula, Definitional.Formula.FreeClosed, φ.freeClosed]
  delta0 := .conj
    (.forallMem _ (.existsMem _ (.existsMem _ (codeFormula_delta0 _ _ _))))
    (.forallMem _ (.forallMem _ (.iff (memPairFormula_delta0 _ _ _)
      (KP1Y.delta0_rename φ.delta0 historySlots))))

private theorem historySlots_env {M : SetTheory.Structure.{u}} {n : Nat}
    (env : Env M n) (B δ H t a : M.Domain) :
    (((((env.push B).push δ).push H).push t).push a).reindex historySlots =
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

theorem historySchema_iff {M : SetTheory.Structure.{u}} (he : Extensional M) {n : Nat}
    (φ : StepMatrix n) (env : Env M n) (B δ H : M.Domain) :
    Project.Formula.satisfies (((env.push B).push δ).push H) (historySchema φ).body ↔
      History M (φ.denote env) H δ B := by
  simp only [historySchema, Project.Formula.satisfies_conj_iff,
    Project.Formula.satisfies_forallMem_iff, Project.Formula.satisfies_existsMem_iff,
    Project.Formula.satisfies_iff_iff, codeFormula_iff he, memPairFormula_iff he,
    Project.Formula.satisfies_rename, historySlots_env]
  rfl

def badStage : Project.Delta0UnarySchema 3 where
  body := Project.Formula.existsMem (.bound 1) (.neg (.iff
    (memPairFormula (.bound 3) (.bound 1) (.bound 0))
    (memPairFormula (.bound 4) (.bound 1) (.bound 0))))
  freeClosed := by
    simp [Project.Formula.existsMem, memPairFormula, codeFormula, pairFormula,
      Project.Formula.forallMem, Definitional.Formula.FreeClosed]
  delta0 := .existsMem _ (.neg (.iff (memPairFormula_delta0 _ _ _) (memPairFormula_delta0 _ _ _)))

def badEnv {M : SetTheory.Structure.{u}} (B H J : M.Domain) : Env M 3 :=
  ⟨Fin.cases B (Fin.cases H (fun _ => J)), fun _ => B⟩

theorem badStage_iff {M : SetTheory.Structure.{u}} (he : Extensional M)
    (B H J t : M.Domain) :
    Project.Formula.satisfies ((badEnv B H J).push t) badStage.body ↔
      ∃ a, M.mem a B ∧ ¬(MemPair M H t a ↔ MemPair M J t a) := by
  simp only [badStage, Project.Formula.satisfies_existsMem_iff,
    Project.Formula.satisfies_neg_iff, Project.Formula.satisfies_iff_iff, memPairFormula_iff he]
  rfl

/-- 只在模型内部的序数上用最小反例；没有把其成员关系当宿主良基关系。 -/
theorem history_rows_agree {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {Γ B δ H J : M.Domain} {step : M.Domain → M.Domain → M.Domain → Prop}
    (hδ : M.IsOrdinal δ) (hδΓ : M.MemberSubset δ Γ) (hLocal : Local M Γ B step)
    (hH : History M step H δ B) (hJ : History M step J δ B) :
    ∀ t, M.mem t δ → ∀ a, M.mem a B → (MemPair M H t a ↔ MemPair M J t a) := by
  classical
  obtain ⟨D,hD⟩ := SetTheory.KP.separation_exists_d (KP1Y.models_weakKP hM)
    badStage (badEnv B H J) δ
  have hd (t : M.Domain) : M.mem t D ↔ M.mem t δ ∧
      ∃ a, M.mem a B ∧ ¬(MemPair M H t a ↔ MemPair M J t a) :=
    (hD t).trans (and_congr Iff.rfl (badStage_iff hM.1 B H J t))
  intro t ht a ha
  apply Classical.byContradiction
  intro hbad
  have hne : ∃ t, M.mem t D := ⟨t,(hd t).mpr ⟨ht,a,ha,hbad⟩⟩
  obtain ⟨m,hm,hmin⟩ := hδ.wellOrder.least D (fun t ht => ((hd t).mp ht).1) hne
  have hmδ := ((hd m).mp hm).1
  have hprev : ∀ s, M.mem s m → ∀ a, M.mem a B →
      (MemPair M H s a ↔ MemPair M J s a) := by
    intro s hsm a ha
    apply Classical.byContradiction
    intro hsbad
    have hsδ := hδ.transitive m hmδ s hsm
    have hsD := (hd s).mpr ⟨hsδ,a,ha,hsbad⟩
    rcases hmin s hsD with he | hms
    · have heq := hM.1.eq_of_same_members m s he
      cases heq
      exact hδ.wellOrder.linear.irrefl m hmδ hsm
    · exact hδ.wellOrder.linear.irrefl m hmδ
        (hδ.wellOrder.linear.trans m hmδ s hsδ m hmδ hms hsm)
  obtain ⟨b,hb,hneq⟩ := ((hd m).mp hm).2
  exact hneq ((hH.2 m hmδ b hb).trans
    ((hLocal m (hδΓ m hmδ) H J hprev b hb).trans (hJ.2 m hmδ b hb).symm))

theorem history_unique {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {Γ B δ H J : M.Domain} {step : M.Domain → M.Domain → M.Domain → Prop}
    (hδ : M.IsOrdinal δ) (hδΓ : M.MemberSubset δ Γ) (hLocal : Local M Γ B step)
    (hH : History M step H δ B) (hJ : History M step J δ B) : H = J := by
  have hr := history_rows_agree hM hδ hδΓ hLocal hH hJ
  apply hM.1.eq_of_same_members
  intro p
  constructor
  · intro hp
    obtain ⟨t,ht,a,ha,hcode⟩ := hH.1 p hp
    obtain ⟨q,hq,hcode'⟩ := (hr t ht a ha).mp ⟨p,hp,hcode⟩
    exact (codes_unique hM.1 hcode hcode') ▸ hq
  · intro hp
    obtain ⟨t,ht,a,ha,hcode⟩ := hJ.1 p hp
    obtain ⟨q,hq,hcode'⟩ := (hr t ht a ha).mpr ⟨p,hp,hcode⟩
    exact (codes_unique hM.1 hcode hcode') ▸ hq

end KP1Y.Recursion
