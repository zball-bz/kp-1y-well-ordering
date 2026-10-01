import KP1Y.WordCodeSyntax

/-! 全部内部有限序数字词拥有实际有界单射排名，包括长度为非标准自然数的字词。 -/
namespace KP1Y.WordRank
open YesMetaZFC YesMetaZFC.SetTheory YesMetaZFC.SetTheory.Definitional
open KP1Y.Kuratowski KP1Y.Functions KP1Y.Arithmetic KP1Y.Ranking KP1Y.Naturals
universe u

theorem code_exists_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {κ ω zero one C F s n : M.Domain} (hBudget : Budget M κ ω zero one C F) (hn : M.mem n ω) (hS : Graph M s n κ) :
    ∃ r, Code M ω κ C s r := by
  obtain ⟨c,hc⟩ := fold_exists_d hM hBudget.omega hBudget.stride hn hS
  have hcC := fold_bounded_d hM hBudget hc
  obtain ⟨r,hr⟩ := rectangle_exists_d hM hBudget.ceiling ((omega_isOrdinal_d hM hBudget.omega).mem hn) (hBudget.ceiling.mem hcC)
  exact ⟨r,n,hn,c,hcC,hS,hc,hr⟩

theorem code_unique_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {ω κ C s r r' : M.Domain} (hω : M.IsOmega ω) (h : Code M ω κ C s r) (h' : Code M ω κ C s r') : r=r' := by
  obtain ⟨n,_,c,_,hS,hFold,hCode⟩ := h
  obtain ⟨n',_,c',_,hS',hFold',hCode'⟩ := h'
  have hnn' := KP1Y.Assignments.domain_unique hM.1 hS hS'
  subst n'
  have hcc' := fold_unique_d hM hω hFold hFold'
  subst c'
  exact rectangle_unique_d hM hCode hCode'

theorem code_injective_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {κ ω zero one C F s t r r' : M.Domain} (hBudget : Budget M κ ω zero one C F)
    (h : Code M ω κ C s r) (h' : Code M ω κ C t r') (hrr' : r=r') : s=t := by
  obtain ⟨n,_,c,hc,hS,hFold,hCode⟩ := h
  obtain ⟨n',_,c',hc',hT,hFold',hCode'⟩ := h'
  obtain ⟨hnn',hcc'⟩ := rectangle_injective_d hM hCode hCode' hc hc' hrr'
  subst n'
  exact fold_injective_same_length_d hM hBudget hS hT hFold hFold' hcc'

theorem ordinal_word_rank_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory) {ω κ Words : M.Domain}
    (hω : M.IsOmega ω) (hκ : M.IsOrdinal κ)
    (hWords : ∀ s, M.mem s Words ↔ ∃ n, M.mem n ω ∧ Graph M s n κ) :
    ∃ Γ R, OrdinalRank M R Words Γ := by
  obtain ⟨zero,one,C,F,hBudget⟩ := budget_exists_d hM hω hκ
  obtain ⟨Γ,hΓ⟩ := product_exists_d hM hBudget.ceiling (omega_isOrdinal_d hM hω)
  let e : Env M 3 := ((oneEnv C).push κ).push ω
  obtain ⟨R,hR,hRows⟩ := sigma_function_graph_d hM codeMatrix e Words Γ (by
    intro s hs
    obtain ⟨n,hn,hS⟩ := (hWords s).mp hs
    obtain ⟨r,hr⟩ := code_exists_d hM hBudget hn hS
    exact ⟨r,(code_sigmaOne_iff_d hM e s r).mp hr⟩) (by
    intro s _ r W hW
    obtain ⟨n,hn,c,hc,_,_,hCode⟩ := (code_sigmaOne_iff_d hM e s r).mpr ⟨W,hW⟩
    exact rectangle_bounded_d hM hΓ hCode hn hc) (by
    intro s _ r r' W W' hW hW'
    exact code_unique_d hM hω ((code_sigmaOne_iff_d hM e s r).mpr ⟨W,hW⟩)
      ((code_sigmaOne_iff_d hM e s r').mpr ⟨W',hW'⟩))
  refine ⟨Γ,R,hΓ.isOrdinal_d hM,hR,?_⟩
  intro s t r hsr htr
  obtain ⟨_,_,W,hW⟩ := (hRows s r).mp hsr
  obtain ⟨_,_,W',hW'⟩ := (hRows t r).mp htr
  exact code_injective_d hM hBudget ((code_sigmaOne_iff_d hM e s r).mpr ⟨W,hW⟩)
    ((code_sigmaOne_iff_d hM e t r).mpr ⟨W',hW'⟩) rfl

end KP1Y.WordRank
