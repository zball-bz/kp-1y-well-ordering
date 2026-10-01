import KP1Y.OrdinalMultiplicationSyntax

/-! KPω中的序数乘法存在唯一、序数性、零/后继方程及正左因子的严格增长。 -/
namespace KP1Y.Arithmetic
open YesMetaZFC YesMetaZFC.SetTheory
open KP1Y.Kuratowski
universe u

theorem Product.left_ordinal {M : SetTheory.Structure.{u}} {α β γ : M.Domain} (h : Product M α β γ) : M.IsOrdinal α := h.1

theorem Product.right_ordinal {M : SetTheory.Structure.{u}} {α β γ : M.Domain} (h : Product M α β γ) : M.IsOrdinal β := by
  obtain ⟨_,_,_,hValue⟩ := h
  exact hValue.ordinal

theorem Product.at_zero {M : SetTheory.Structure.{u}} (he : Extensional M) {α β γ zero : M.Domain}
    (h : Product M α β γ) (hZero : ∀ x, ¬M.mem x zero) :
    KP1Y.OrdinalIteration.Value rightAddMatrix ((oneEnv α).push zero) β γ := by
  obtain ⟨_,z,hz,hValue⟩ := h
  have hz0 := he.eq_of_same_members z zero (fun x => iff_of_false (hz x) (hZero x))
  subst z
  exact hValue

theorem product_exists_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory) {α β : M.Domain}
    (hα : M.IsOrdinal α) (hβ : M.IsOrdinal β) : ∃ γ, Product M α β γ := by
  obtain ⟨zero,hZero⟩ := SetTheory.KP.exists_empty (KP1Y.models_weakKP hM)
  obtain ⟨γ,hγ⟩ := KP1Y.OrdinalIteration.value_exists_d hM rightAddMatrix ((oneEnv α).push zero)
    (right_add_total_d hM _ hα) (right_add_functional_d hM _) hβ
  exact ⟨γ,hα,zero,hZero,hγ⟩

theorem product_unique_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory) {α β γ δ : M.Domain}
    (h : Product M α β γ) (h' : Product M α β δ) : γ=δ := by
  obtain ⟨zero,hZero⟩ := SetTheory.KP.exists_empty (KP1Y.models_weakKP hM)
  exact KP1Y.OrdinalIteration.value_unique_d hM rightAddMatrix ((oneEnv α).push zero)
    (right_add_functional_d hM _) (h.at_zero hM.1 hZero) (h'.at_zero hM.1 hZero)

theorem Product.isOrdinal_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory) {α β γ : M.Domain}
    (h : Product M α β γ) : M.IsOrdinal γ := by
  obtain ⟨_,zero,hZero,hValue⟩ := h
  exact KP1Y.OrdinalIteration.Value.isOrdinal_d hM rightAddMatrix ((oneEnv α).push zero)
    (Structure.IsOrdinal.of_no_members hZero) (right_add_preserves_d hM _) hValue

theorem Product.zero_value_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory) {α β γ : M.Domain}
    (h : Product M α β γ) (hβ : ∀ x, ¬M.mem x β) : ∀ x, ¬M.mem x γ := by
  obtain ⟨_,zero,hZero,hValue⟩ := h
  have hEq := hValue.initial_d hM hβ
  exact hEq ▸ hZero

theorem product_zero_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory) {α zero : M.Domain}
    (hα : M.IsOrdinal α) (hZero : ∀ x, ¬M.mem x zero) : Product M α zero zero := by
  obtain ⟨γ,hγ⟩ := product_exists_d hM hα (Structure.IsOrdinal.of_no_members hZero)
  have hEq := hM.1.eq_of_same_members γ zero (fun x => iff_of_false (hγ.zero_value_d hM hZero x) (hZero x))
  exact hEq ▸ hγ

theorem product_successor_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory) {α β β' γ γ' : M.Domain}
    (hs : M.SuccessorOf β' β) (h : Product M α β γ) (h' : Product M α β' γ') : Sum M γ α γ' := by
  obtain ⟨zero,hZero⟩ := SetTheory.KP.exists_empty (KP1Y.models_weakKP hM)
  obtain ⟨z,hNext⟩ := KP1Y.OrdinalIteration.Value.next_d hM rightAddMatrix ((oneEnv α).push zero)
    (right_add_functional_d hM _) hs (h.at_zero hM.1 hZero) (h'.at_zero hM.1 hZero)
  exact ⟨z,(rightAddMatrix_iff hM _ γ γ' z).mp hNext⟩

theorem product_strict_right_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory) {α β β' γ γ' : M.Domain}
    (hα : ∃ x, M.mem x α) (h : Product M α β γ) (h' : Product M α β' γ') (hββ' : M.mem β β') : M.mem γ γ' := by
  obtain ⟨zero,hZero⟩ := SetTheory.KP.exists_empty (KP1Y.models_weakKP hM)
  exact KP1Y.OrdinalIteration.value_strict_d hM rightAddMatrix ((oneEnv α).push zero)
    (Structure.IsOrdinal.of_no_members hZero) (right_add_functional_d hM _)
    (right_add_preserves_d hM _) (right_add_strict_d hM _ hα) (h.at_zero hM.1 hZero) (h'.at_zero hM.1 hZero) hββ'

theorem product_mono_right_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory) {α β β' γ γ' : M.Domain}
    (hα : ∃ x, M.mem x α) (h : Product M α β γ) (h' : Product M α β' γ') (hββ' : M.MemberSubset β β') : M.MemberSubset γ γ' := by
  obtain ⟨zero,hZero⟩ := SetTheory.KP.exists_empty (KP1Y.models_weakKP hM)
  exact KP1Y.OrdinalIteration.value_mono_d hM rightAddMatrix ((oneEnv α).push zero)
    (Structure.IsOrdinal.of_no_members hZero) (right_add_functional_d hM _)
    (right_add_preserves_d hM _) (right_add_strict_d hM _ hα) (h.at_zero hM.1 hZero) (h'.at_zero hM.1 hZero) hββ'

end KP1Y.Arithmetic
