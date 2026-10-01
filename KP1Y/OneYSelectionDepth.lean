import KP1Y.OneYSelectionOrder

/-! 共候选链的深度单调与等值父行，补齐原 nearestSmaller 比较的两个出口。 -/
namespace KP1Y.OneYFinite
open YesMetaZFC YesMetaZFC.SetTheory
open KP1Y.Kuratowski KP1Y.Functions KP1Y.Naturals
universe u

theorem Selects.depth_mono_of_common_chain_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {m F V P c d x y dc dd : M.Domain}
    (hS : Selects false M C m F V P)
    (hCommon : ∀ p, Ancestor M C m F p c ↔ Ancestor M C m F p d)
    (hX : MemPair M V c x) (hY : MemPair M V d y) (hXY : x=y ∨ M.mem x y)
    (hDC : Depth M C m P c dc) (hDD : Depth M C m P d dd) : dc=dd ∨ M.mem dc dd := by
  have hω := omega_isOrdinal_d hM hC.omega
  classical
  by_cases hNo : NoParent M m P c
  · have hZero := depth_of_no_parent_d hM hC hS.forest hNo hDC
    subst dc
    exact ordinal_subset_cases_d hM (hω.mem hC.zero_nat) (hω.mem hDD.1)
      (fun z hz => False.elim (hC.zero_empty z hz))
  · have hSome : ∃ p, M.mem p m ∧ MemPair M P c p := by
      apply Classical.byContradiction
      intro hNone
      exact hNo (fun p hp hcp => hNone ⟨p,hp,hcp⟩)
    obtain ⟨p,_,hCP⟩ := hSome
    have hPD := hS.ancestor_mono_of_common_chain_d hM hC hCommon hX hY hXY (ancestor_direct_d hM hC hS.forest hCP)
    obtain ⟨q,hDQ,hTail⟩ := ancestor_parent_cases_d hM hC hS.forest hPD
    obtain ⟨dp,hDP,hPS⟩ := depth_parent_predecessor_d hM hC hS.forest hCP hDC
    obtain ⟨dq,hDQDepth,hQS⟩ := depth_parent_predecessor_d hM hC hS.forest hDQ hDD
    rcases hTail with he | hPQ
    · subst q
      have hD := depth_unique_d hM hC hS.forest hDP hDQDepth
      subst dq
      exact Or.inl (Structure.SuccessorOf.eq hM.1 hPS hQS)
    · have hLt := ancestor_depth_lt_d hM hC hS.forest hPQ hDP hDQDepth
      have hSub : M.MemberSubset dc dq := by
        intro z hz
        rcases (hPS z).mp hz with hzp | he
        · exact (hω.mem hDQDepth.1).transitive dp hLt z hzp
        · exact (hM.1.eq_of_same_members z dp he) ▸ hLt
      rcases ordinal_subset_cases_d hM (hω.mem hDC.1) (hω.mem hDQDepth.1) hSub with he | hcd
      · subst dc
        exact Or.inr hQS.predecessor_mem
      · exact Or.inr ((hQS dc).mpr (Or.inl hcd))

theorem Selects.parent_rows_eq_of_common_chain_value_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} {positive : Bool} {m F V P c d x : M.Domain}
    (hS : Selects positive M C m F V P)
    (hCommon : ∀ p, Ancestor M C m F p c ↔ Ancestor M C m F p d)
    (hX : MemPair M V c x) (hY : MemPair M V d x) : ∀ p, MemPair M P c p ↔ MemPair M P d p := by
  have hCand (p : M.Domain) : ParentCandidate positive M C m F V c p ↔ ParentCandidate positive M C m F V d p := by
    constructor
    · rintro ⟨hA,v,hv,y,hy,hV,hC,hvy,hPos⟩
      have hyx := hS.values.unique c y x hC hX
      subst y
      exact ⟨(hCommon p).mp hA,v,hv,x,hy,hV,hY,hvy,hPos⟩
    · rintro ⟨hA,v,hv,y,hy,hV,hD,hvy,hPos⟩
      have hyx := hS.values.unique d y x hD hY
      subst y
      exact ⟨(hCommon p).mpr hA,v,hv,x,hy,hV,hX,hvy,hPos⟩
  intro p
  rw [hS.parents c p,hS.parents d p]
  constructor
  · rintro ⟨hP,hMax⟩
    refine ⟨(hCand p).mp hP,?_⟩
    intro q _ hQ
    have hQ' := (hCand q).mpr hQ
    exact hMax q hQ'.1.1 hQ'
  · rintro ⟨hP,hMax⟩
    refine ⟨(hCand p).mpr hP,?_⟩
    intro q _ hQ
    have hQ' := (hCand q).mp hQ
    exact hMax q hQ'.1.1 hQ'

end KP1Y.OneYFinite
