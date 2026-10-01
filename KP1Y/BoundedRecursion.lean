import KP1Y.HistoryLimit

/-! KPω 内的有界 Δ₀ 关系递归：用对象集合归纳装配空、后继和极限历史。 -/
namespace KP1Y.Recursion
open YesMetaZFC YesMetaZFC.SetTheory YesMetaZFC.SetTheory.Definitional
open KP1Y.Kuratowski
universe u

/-- 原分类引理的直接证明，避免原生自动化证书进入可信依赖。 -/
private theorem classify_ordinal {ℳ : SetTheory.Structure.{u}} {α : ℳ.Domain} (hExt : Extensional ℳ) (hα : Structure.IsOrdinal ℳ α) : (∀ value, ¬ ℳ.mem value α) ∨
      (∃ predecessor, Structure.IsOrdinal ℳ predecessor ∧
        ℳ.SuccessorOf α predecessor) ∨
      ℳ.IsLimitOrdinal α := by
  classical
  by_cases hEmpty : ∀ value, ¬ ℳ.mem value α
  · exact Or.inl hEmpty
  · have hNonempty : ∃ value, ℳ.mem value α := by
      apply Classical.byContradiction
      intro hNone
      apply hEmpty
      intro value hValue
      exact hNone ⟨value, hValue⟩
    by_cases hGreatest : ∃ candidate,
        ℳ.mem candidate α ∧
          ∀ value, ℳ.mem value α →
            ℳ.mem value candidate ∨ ℳ.SameMembers value candidate
    · rcases hGreatest with
        ⟨predecessor, hPredecessor, hGreatest⟩
      apply Or.inr
      apply Or.inl
      refine ⟨predecessor, hα.mem hPredecessor, ?_⟩
      intro value
      constructor
      · exact hGreatest value
      · intro hValue
        rcases hValue with hValuePredecessor | hSameMembers
        · exact hα.transitive predecessor hPredecessor
            value hValuePredecessor
        · have hEq := hExt.eq_of_same_members value predecessor
            hSameMembers
          simpa [hEq] using hPredecessor
    · apply Or.inr
      apply Or.inr
      refine ⟨hα, hNonempty, ?_⟩
      intro predecessor hPredecessor
      apply Classical.byContradiction
      intro hNoLarger
      apply hGreatest
      refine ⟨predecessor, hPredecessor, ?_⟩
      intro value hValue
      have hCompare :=
        hα.wellOrder.linear.compare value hValue
          predecessor hPredecessor
      rcases hCompare with hSame | hValuePredecessor | hPredecessorValue
      · exact Or.inr hSame
      · exact Or.inl hValuePredecessor
      · exact False.elim <| hNoLarger
          ⟨value, hValue, hPredecessorValue⟩

def existenceSlots {n : Nat} : Fin (n+3) → Fin (n+4) :=
  Fin.cases 0 (Fin.cases 1 (Fin.cases 2 (fun i => ⟨i.val+4, by omega⟩)))

def existsHistorySchema {n : Nat} (φ : StepMatrix n) : Project.UnarySchema (n+2) where
  body := .imp (Project.Formula.subset (.bound 0) (.bound 2))
    (.existsE ((historySchema φ).body.rename existenceSlots))
  freeClosed := by
    simp [Definitional.Formula.FreeClosed, (historySchema φ).freeClosed]

private theorem existenceSlots_env {M : SetTheory.Structure.{u}} {n : Nat}
    (env : Env M n) (Γ B δ H : M.Domain) :
    ((((env.push Γ).push B).push δ).push H).reindex existenceSlots =
      ((env.push B).push δ).push H := by
  rw [Env.mk.injEq]
  constructor
  · funext i
    refine Fin.cases ?_ (fun i => ?_) i
    · rfl
    · refine Fin.cases ?_ (fun i => ?_) i
      · rfl
      · refine Fin.cases ?_ (fun i => ?_) i <;> rfl
  · rfl

theorem existsHistorySchema_iff {M : SetTheory.Structure.{u}} (he : Extensional M)
    {n : Nat} (φ : StepMatrix n) (env : Env M n) (Γ B δ : M.Domain) :
    Project.Formula.satisfies (((env.push Γ).push B).push δ) (existsHistorySchema φ).body ↔
      (M.MemberSubset δ Γ → ∃ H, History M (φ.denote env) H δ B) := by
  simp only [existsHistorySchema, Project.Formula.satisfies_imp_iff,
    Project.Formula.satisfies_subset_iff, Project.Formula.satisfies_exists_iff,
    Project.Formula.satisfies_rename, existenceSlots_env, historySchema_iff he]
  rfl

/-- 这是任意 KPω 模型内部的集合存在性，不是宿主的递归函数。 -/
theorem bounded_recursion_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {n : Nat} (φ : StepMatrix n) (env : Env M n) {Γ B : M.Domain}
    (hΓ : M.IsOrdinal Γ) (hLocal : Local M Γ B (φ.denote env)) :
    ∃ H, History M (φ.denote env) H Γ B := by
  have hAll := KP1Y.ordinal_induction_d hM (existsHistorySchema φ) ((env.push Γ).push B)
    (fun δ hδ ih => (existsHistorySchema_iff hM.1 φ env Γ B δ).mpr (by
      intro hδΓ
      rcases classify_ordinal hM.1 hδ with hEmpty | hSucc | hLimit
      · obtain ⟨H,hH⟩ := SetTheory.KP.exists_empty (KP1Y.models_weakKP hM)
        refine ⟨H,?_,?_⟩
        · intro p hp
          exact False.elim (hH p hp)
        · intro t ht
          exact False.elim (hEmpty t ht)
      · obtain ⟨ε,hε,hSucc⟩ := hSucc
        have hεδ := hSucc.predecessor_mem
        have hεΓ : M.MemberSubset ε Γ := fun t ht => hδΓ t (hδ.transitive ε hεδ t ht)
        obtain ⟨H,hH⟩ := (existsHistorySchema_iff hM.1 φ env Γ B ε).mp (ih ε hεδ) hεΓ
        exact history_successor hM φ env hε hδΓ hSucc hLocal hH
      · apply history_limit hM φ env hLimit hδΓ hLocal
        intro ε hεδ
        exact (existsHistorySchema_iff hM.1 φ env Γ B ε).mp (ih ε hεδ)
          (fun t ht => hδΓ t (hδ.transitive ε hεδ t ht))))
  exact (existsHistorySchema_iff hM.1 φ env Γ B Γ).mp (hAll Γ hΓ) (fun _ h => h)

theorem bounded_recursion_unique_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {n : Nat} (φ : StepMatrix n) (env : Env M n) {Γ B : M.Domain}
    (hΓ : M.IsOrdinal Γ) (hLocal : Local M Γ B (φ.denote env)) :
    ∃ H, History M (φ.denote env) H Γ B ∧
      ∀ J, History M (φ.denote env) J Γ B → J=H := by
  obtain ⟨H,hH⟩ := bounded_recursion_d hM φ env hΓ hLocal
  exact ⟨H,hH,fun J hJ => history_unique hM hΓ (fun _ h => h) hLocal hJ hH⟩

end KP1Y.Recursion
