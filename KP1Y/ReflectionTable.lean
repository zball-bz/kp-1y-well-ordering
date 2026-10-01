import KP1Y.ReflectionRow

/-! KP内实际构造单张R表，证明方程(5)、反射与根弱化；不以这些性质作新公理。 -/
namespace KP1Y.Reflection
open YesMetaZFC YesMetaZFC.SetTheory YesMetaZFC.SetTheory.Definitional
open KP1Y.Kuratowski KP1Y.Functions
universe u

structure Table (M : SetTheory.Structure.{u}) (C : Data M.Domain) (H : M.Domain) : Prop where
  history : KP1Y.Recursion.History M (Row M C) H C.bound C.cap

theorem table_exists_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory) {C : Data M.Domain} (hC : C.Valid M) :
    ∃ H, Table M C H := by
  obtain ⟨H,hH⟩ := reflection_history_exists_d hM (dataEnv C) hC
  refine ⟨H,⟨hH.1,?_⟩⟩
  intro σ hσ a ha
  exact (hH.2 σ hσ a ha).trans (rowMatrix_iff hM.1 (dataEnv C) σ a H)

theorem Table.unique_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory) {C : Data M.Domain} (hC : C.Valid M)
    {H J : M.Domain} (h : Table M C H) (h' : Table M C J) : H=J := by
  have hLocal : KP1Y.Recursion.Local M C.bound C.cap (Row M C) := by
    intro σ hσ A B hAgree a ha
    exact (rowMatrix_iff hM.1 (dataEnv C) σ a A).symm.trans
      ((row_local_d hM (dataEnv C) hC σ hσ A B hAgree a ha).trans (rowMatrix_iff hM.1 (dataEnv C) σ a B))
  exact KP1Y.Recursion.history_unique hM (hC.bound.isOrdinal_d hM) (fun _ h => h) hLocal h.history h'.history

theorem Table.equation_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory) {C : Data M.Domain} (hC : C.Valid M)
    {H : M.Domain} (h : Table M C H) (K θ a b : M.Domain) :
    Query M C.toIndexData H K θ a b ↔ ValidQuery M C.toIndexData K θ a b ∧ Reflect M C H K θ a b := by
  constructor
  · rintro ⟨hValid,σ,hσ,hCursor,hAt⟩
    obtain ⟨b',_,K',_,θ',_,hCursor',_,hFR⟩ := (h.history.2 σ hσ a hValid.2.2.1).mp hAt
    obtain ⟨hbb',hKK',hθθ'⟩ := hC.toValid.cursor_parameters_unique_d hM hCursor hCursor'
    subst b'
    subst K'
    subst θ'
    exact ⟨hValid,hFR⟩
  · rintro ⟨hValid,hFR⟩
    obtain ⟨σ,hσ,hCursor⟩ := hC.toValid.cursor_exists_d hM hValid.2.2.2.1 hValid.1 hValid.2.1
    exact ⟨hValid,σ,hσ,hCursor,(h.history.2 σ hσ a hValid.2.2.1).mpr
      ⟨b,hValid.2.2.2.1,K,hValid.1,θ,hValid.2.1,hCursor,hValid,hFR⟩⟩

theorem valid_query_weaken_root {M : SetTheory.Structure.{u}} {C : IndexData M.Domain} (hCap : M.IsOrdinal C.cap)
    {K ξ θ a b : M.Domain} (hξθ : ξ=θ ∨ M.mem ξ θ) (h : ValidQuery M C K θ a b) : ValidQuery M C K ξ a b := by
  rcases hξθ with he | hξθ
  · subst ξ
    exact h
  · refine ⟨h.1,hCap.transitive θ h.2.1 ξ hξθ,h.2.2.1,h.2.2.2.1,?_,h.2.2.2.2.2⟩
    apply Or.inr
    rcases h.2.2.2.2.1 with he | hθa
    · exact he ▸ hξθ
    · exact (hCap.mem h.2.2.1).transitive θ hθa ξ hξθ

theorem Table.root_weaken_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory) {C : Data M.Domain} (hC : C.Valid M)
    {H K ξ θ a b : M.Domain} (h : Table M C H) (hR : Query M C.toIndexData H K θ a b) (hξθ : ξ=θ ∨ M.mem ξ θ) :
    Query M C.toIndexData H K ξ a b := by
  obtain ⟨hValid,hFR⟩ := (h.equation_d hM hC K θ a b).mp hR
  exact (h.equation_d hM hC K ξ a b).mpr ⟨valid_query_weaken_root hC.cap hξθ hValid,
    reflect_mono_root (hC.cap.mem hValid.2.1) hξθ hFR⟩

theorem Table.reflect_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory) {C : Data M.Domain} (hC : C.Valid M)
    {H K θ a b : M.Domain} (h : Table M C H) (hR : Query M C.toIndexData H K θ a b) : Reflect M C H K θ a b :=
  ((h.equation_d hM hC K θ a b).mp hR).2

theorem reflection_table_for_ordinal_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory) {ω κ : M.Domain}
    (hω : M.IsOmega ω) (hκ : M.IsOrdinal κ) : ∃ (cap : M.Domain) (C : Data M.Domain) (H : M.Domain),
      M.SuccessorOf cap κ ∧ C.omega=ω ∧ C.cap=cap ∧ C.Valid M ∧ Table M C H := by
  obtain ⟨cap,hCap⟩ := SetTheory.KP.exists_successor (KP1Y.models_weakKP hM) κ
  have hCapOrd := SetTheory.KP.successor_isOrdinal (KP1Y.models_weakKP hM) hκ hCap
  obtain ⟨C,hωC,hCapC,hC⟩ := reflection_data_exists_d hM hω hCapOrd
  obtain ⟨H,hH⟩ := table_exists_d hM hC
  exact ⟨cap,C,H,hCap,hωC,hCapC,hC,hH⟩

end KP1Y.Reflection
