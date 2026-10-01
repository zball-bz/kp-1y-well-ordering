import KP1Y.HistoryPrefix

/-! 一步追加一个递归行，使用实际 Δ₀ 关系分离。 -/
namespace KP1Y.Recursion
open YesMetaZFC YesMetaZFC.SetTheory YesMetaZFC.SetTheory.Definitional
open KP1Y.Kuratowski
universe u

def successorSlots {n : Nat} : Fin (n+3) → Fin (n+4) :=
  Fin.cases 3 (Fin.cases 0 (Fin.cases 1 (fun i => ⟨i.val+4, by omega⟩)))

def successorSchema {n : Nat} (φ : StepMatrix n) : Project.Delta0BinarySchema (n+2) where
  body := .disj (memPairFormula (.bound 3) (.bound 1) (.bound 0))
    (.conj (Project.Formula.extensionalEq (.bound 1) (.bound 2))
      (φ.body.rename successorSlots))
  freeClosed := by
    simp [memPairFormula, codeFormula, pairFormula, Project.Formula.existsMem,
      Project.Formula.forallMem, Definitional.Formula.FreeClosed, φ.freeClosed]
  delta0 := .disj (memPairFormula_delta0 _ _ _)
    (.conj (.atom _ _ _) (KP1Y.delta0_rename φ.delta0 successorSlots))

private theorem successorSlots_env {M : SetTheory.Structure.{u}} {n : Nat}
    (env : Env M n) (H δ t a : M.Domain) :
    ((((env.push H).push δ).push t).push a).reindex successorSlots =
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

theorem successorSchema_iff {M : SetTheory.Structure.{u}} (he : Extensional M) {n : Nat}
    (φ : StepMatrix n) (env : Env M n) (H δ t a : M.Domain) :
    Project.Formula.satisfies ((((env.push H).push δ).push t).push a) (successorSchema φ).body ↔
      MemPair M H t a ∨ (t=δ ∧ φ.denote env t a H) := by
  simp only [successorSchema, Project.Formula.satisfies_disj_iff,
    Project.Formula.satisfies_conj_iff, memPairFormula_iff he,
    Project.Formula.satisfies_extensionalEq_iff_eq he,
    Project.Formula.satisfies_rename, successorSlots_env]
  rfl

/-- 已有历史存在时，其后继历史由实际集合操作构造。 -/
theorem history_successor {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {n : Nat} (φ : StepMatrix n) (env : Env M n)
    {Γ B δ γ H : M.Domain} (hδ : M.IsOrdinal δ)
    (hγΓ : M.MemberSubset γ Γ) (hSucc : M.SuccessorOf γ δ)
    (hLocal : Local M Γ B (φ.denote env)) (hH : History M (φ.denote env) H δ B) :
    ∃ J, History M (φ.denote env) J γ B := by
  have hw := KP1Y.models_weakKP hM
  have hSuccEq (t : M.Domain) : M.mem t γ ↔ M.mem t δ ∨ t=δ := by
    rw [hSucc t]
    constructor
    · rintro (h | h)
      · exact Or.inl h
      · exact Or.inr (hM.1.eq_of_same_members t δ h)
    · rintro (h | h)
      · exact Or.inl h
      · cases h
        exact Or.inr (fun _ => Iff.rfl)
  have hδγ : M.MemberSubset δ γ := fun t ht => (hSuccEq t).mpr (Or.inl ht)
  obtain ⟨J,hSupport,hJ⟩ := relation_comprehension_d hM (successorSchema φ)
    ((env.push H).push δ) γ B
  have hrow : ∀ t, M.mem t γ → ∀ a, M.mem a B →
      (MemPair M J t a ↔ MemPair M H t a ∨ (t=δ ∧ φ.denote env t a H)) := by
    intro t ht a ha
    have h := hJ t a
    rw [successorSchema_iff hM.1] at h
    simpa only [ht,ha,true_and] using h
  have hOld : ∀ t, M.mem t δ → ∀ a, M.mem a B → (MemPair M J t a ↔ MemPair M H t a) := by
    intro t ht a ha
    have hne : t ≠ δ := by
      intro he
      cases he
      exact SetTheory.KP.mem_irrefl_d hw δ ht
    simpa only [hne,false_and,or_false] using hrow t (hδγ t ht) a ha
  refine ⟨J,hSupport,?_⟩
  intro t ht a ha
  have hPast : ∀ s, M.mem s t → M.mem s δ := by
    intro s hs
    rcases (hSuccEq t).mp ht with htδ | he
    · exact hδ.transitive t htδ s hs
    · cases he
      exact hs
  have hloc := hLocal t (hγΓ t ht) J H
    (fun s hs b hb => hOld s (hPast s hs) b hb) a ha
  apply Iff.trans ?_ hloc.symm
  rcases (hSuccEq t).mp ht with htδ | he
  · exact (hOld t htδ a ha).trans (hH.2 t htδ a ha)
  · cases he
    have hnone : ¬ MemPair M H δ a := fun hm =>
      SetTheory.KP.mem_irrefl_d hw δ (hH.bounds hM.1 hm).1
    simpa only [hnone,false_or,eq_self,true_and] using hrow δ ht a ha

end KP1Y.Recursion
