import KP1Y.OrdinalRectangleGraph

/-! R表的实际阶段次序：先上端点b，再层号K，再根标签θ。 -/
namespace KP1Y.Reflection
open YesMetaZFC YesMetaZFC.SetTheory
open KP1Y.Arithmetic
universe u

def StageCode (M : SetTheory.Structure.{u}) (cap L b K θ σ : M.Domain) : Prop :=
  ∃ t, RectangleCode M cap K θ t ∧ RectangleCode M L b t σ

theorem stage_code_exists_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory) {cap L b K θ : M.Domain}
    (hCap : M.IsOrdinal cap) (hL : M.IsOrdinal L) (hb : M.IsOrdinal b) (hK : M.IsOrdinal K) (hθ : M.IsOrdinal θ) :
    ∃ σ, StageCode M cap L b K θ σ := by
  obtain ⟨t,ht⟩ := rectangle_exists_d hM hCap hK hθ
  obtain ⟨σ,hσ⟩ := rectangle_exists_d hM hL hb (ht.isOrdinal_d hM)
  exact ⟨σ,t,ht,hσ⟩

theorem stage_code_unique_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory) {cap L b K θ σ τ : M.Domain}
    (h : StageCode M cap L b K θ σ) (h' : StageCode M cap L b K θ τ) : σ=τ := by
  obtain ⟨t,ht,hσ⟩ := h
  obtain ⟨t',ht',hτ⟩ := h'
  have htt' := rectangle_unique_d hM ht ht'
  subst t'
  exact rectangle_unique_d hM hσ hτ

theorem stage_code_bounded_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {ω cap L Γ b K θ σ : M.Domain} (hL : Product M cap ω L) (hΓ : Product M L cap Γ)
    (hb : M.mem b cap) (hK : M.mem K ω) (hθ : M.mem θ cap) (h : StageCode M cap L b K θ σ) : M.mem σ Γ := by
  obtain ⟨t,ht,hσ⟩ := h
  exact rectangle_bounded_d hM hΓ hσ hb (rectangle_bounded_d hM hL ht hK hθ)

theorem stage_code_injective_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {ω cap L b K θ σ b' K' θ' τ : M.Domain} (hL : Product M cap ω L)
    (hK : M.mem K ω) (hK' : M.mem K' ω) (hθ : M.mem θ cap) (hθ' : M.mem θ' cap)
    (h : StageCode M cap L b K θ σ) (h' : StageCode M cap L b' K' θ' τ) (hστ : σ=τ) : b=b' ∧ K=K' ∧ θ=θ' := by
  obtain ⟨t,ht,hσ⟩ := h
  obtain ⟨t',ht',hτ⟩ := h'
  obtain ⟨hbb',htt'⟩ := rectangle_injective_d hM hσ hτ
    (rectangle_bounded_d hM hL ht hK hθ) (rectangle_bounded_d hM hL ht' hK' hθ') hστ
  exact ⟨hbb',rectangle_injective_d hM ht ht' hθ hθ' htt'⟩

theorem stage_code_earlier_endpoint_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {ω cap L b K θ σ b' K' θ' τ : M.Domain} (hL : Product M cap ω L)
    (hK : M.mem K ω) (hθ : M.mem θ cap) (hbb' : M.mem b b')
    (h : StageCode M cap L b K θ σ) (h' : StageCode M cap L b' K' θ' τ) : M.mem σ τ := by
  obtain ⟨t,ht,hσ⟩ := h
  obtain ⟨t',_,hτ⟩ := h'
  exact rectangle_strict_first_d hM hσ hτ hbb' (rectangle_bounded_d hM hL ht hK hθ)

theorem stage_code_earlier_layer_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {cap L b K θ σ K' θ' τ : M.Domain} (hθ : M.mem θ cap) (hKK' : M.mem K K')
    (h : StageCode M cap L b K θ σ) (h' : StageCode M cap L b K' θ' τ) : M.mem σ τ := by
  obtain ⟨t,ht,hσ⟩ := h
  obtain ⟨t',ht',hτ⟩ := h'
  exact rectangle_strict_second_d hM hσ hτ (rectangle_strict_first_d hM ht ht' hKK' hθ)

theorem stage_code_earlier_root_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {cap L b K θ σ θ' τ : M.Domain} (hθθ' : M.mem θ θ')
    (h : StageCode M cap L b K θ σ) (h' : StageCode M cap L b K θ' τ) : M.mem σ τ := by
  obtain ⟨t,ht,hσ⟩ := h
  obtain ⟨t',ht',hτ⟩ := h'
  exact rectangle_strict_second_d hM hσ hτ (rectangle_strict_second_d hM ht ht' hθθ')

end KP1Y.Reflection
