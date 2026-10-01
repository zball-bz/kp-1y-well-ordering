import KP1Y.OrdinalInduction

/-! 序数的空、后继、极限分类；直接逻辑证明，供对象递归使用。 -/
namespace KP1Y
open YesMetaZFC YesMetaZFC.SetTheory
universe u

theorem ordinal_cases {M : SetTheory.Structure.{u}} (he : Extensional M)
    {δ : M.Domain} (hδ : M.IsOrdinal δ) :
    (∀ x, ¬M.mem x δ) ∨ (∃ ε, M.IsOrdinal ε ∧ M.SuccessorOf δ ε) ∨ M.IsLimitOrdinal δ := by
  classical
  by_cases hEmpty : ∀ x, ¬M.mem x δ
  · exact Or.inl hEmpty
  · have hNonempty : ∃ x, M.mem x δ := by
      apply Classical.byContradiction
      intro hNone
      exact hEmpty (fun x hx => hNone ⟨x,hx⟩)
    by_cases hGreatest : ∃ ε, M.mem ε δ ∧
        ∀ x, M.mem x δ → M.mem x ε ∨ M.SameMembers x ε
    · obtain ⟨ε,hε,hGreatest⟩ := hGreatest
      refine Or.inr (Or.inl ⟨ε,hδ.mem hε,fun x => ⟨hGreatest x,?_⟩⟩)
      rintro (hx | hx)
      · exact hδ.transitive ε hε x hx
      · exact (he.eq_of_same_members x ε hx) ▸ hε
    · refine Or.inr (Or.inr ⟨hδ,hNonempty,?_⟩)
      intro ε hε
      apply Classical.byContradiction
      intro hNone
      apply hGreatest
      refine ⟨ε,hε,?_⟩
      intro x hx
      rcases hδ.wellOrder.linear.compare x hx ε hε with hSame | hLess | hMore
      · exact Or.inr hSame
      · exact Or.inl hLess
      · exact False.elim (hNone ⟨x,hx,hMore⟩)

end KP1Y
