import KP1Y.OrdinalMultiplicationKP
import KP1Y.OrdinalIterationBounds

/-! 加法的右参数下界及加/乘法的独立极限方程。 -/
namespace KP1Y.Arithmetic
open YesMetaZFC YesMetaZFC.SetTheory
open KP1Y.Kuratowski
universe u

theorem sum_right_subset_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory) {α β γ : M.Domain}
    (hα : M.IsOrdinal α) (h : Sum M α β γ) : M.MemberSubset β γ :=
  KP1Y.OrdinalIteration.value_index_bounded_d hM successorMatrix (oneEnv α) hα
    (successor_preserves_ordinals_d hM _) (successor_strict hM.1 _) h

theorem sum_limit_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory) {α β γ : M.Domain}
    (hβ : M.IsLimitOrdinal β) (h : Sum M α β γ) :
    ∀ x, M.mem x γ ↔ ∃ i, M.mem i β ∧ ∃ y, Sum M α i y ∧ M.mem x y :=
  KP1Y.OrdinalIteration.Value.limit_d hM successorMatrix (oneEnv α) (successor_functional hM.1 _) hβ h

theorem product_limit_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory) {α β γ : M.Domain}
    (hβ : M.IsLimitOrdinal β) (h : Product M α β γ) :
    ∀ x, M.mem x γ ↔ ∃ i, M.mem i β ∧ ∃ y, Product M α i y ∧ M.mem x y := by
  obtain ⟨zero,hZero⟩ := SetTheory.KP.exists_empty (KP1Y.models_weakKP hM)
  have hLimit := KP1Y.OrdinalIteration.Value.limit_d hM rightAddMatrix ((oneEnv α).push zero)
    (right_add_functional_d hM _) hβ (h.at_zero hM.1 hZero)
  intro x
  constructor
  · intro hx
    obtain ⟨i,hi,y,hy,hxy⟩ := (hLimit x).mp hx
    exact ⟨i,hi,y,⟨h.left_ordinal,zero,hZero,hy⟩,hxy⟩
  · rintro ⟨i,hi,y,hy,hxy⟩
    exact (hLimit x).mpr ⟨i,hi,y,hy.at_zero hM.1 hZero,hxy⟩

end KP1Y.Arithmetic
