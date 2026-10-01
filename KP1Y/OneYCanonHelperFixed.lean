import KP1Y.OneYCanonHelperKey

/-! H3：好部父（或无父）的非root坏部列，其所有副本的目标底值与源底值相同。
副本列与原列在目标山形中逐行父项完全相同（好部父不平移），Top相同，故由目标网格的孪生列比较得到。 -/
namespace KP1Y.OneYFinite.TerminalBase
open YesMetaZFC YesMetaZFC.SetTheory YesMetaZFC.SetTheory.Definitional
open KP1Y.Kuratowski KP1Y.Functions KP1Y.Naturals KP1Y.Bounded KP1Y.Arithmetic
open ReconstructionCanonical Reconstruction MountainReconstruction ReconstructionRecovery
universe u

section
variable {M : SetTheory.Structure.{u}} {C : ExpressionData M.Domain} {T : MatrixArithmetic M.Domain}
  {m V P H level index n OldTop NewTop Bottom : M.Domain} {R : RowStateSpace M.Domain}
  {X Y : CopiedMountain.Data M.Domain} {A : CopyCoordinates.Context M.Domain}

/-- 源任一行的父项都是源第0行（父森林P）中的祖先。 -/
theorem Base.source_row_ancestor_d (hM : M.Models KP1Y.theory) (hC : C.Valid M)
    (h : Base M C T m V P H level index n OldTop NewTop Bottom R X Y A) {r s p : M.Domain}
    (hP : CopiedMountain.ParentAt M X r s p) : Ancestor M C m P p s := by
  obtain ⟨U,F,hAt,hSP⟩ := (h.fromRun.parent_iff hM.1 h.source r s p).mp hP
  have hr := (hP.bounds hM.1 h.source).1
  have hFF := (h.run.at_numeric_d hM hC hAt).forest
  have hLe : C.zero=r ∨ M.mem C.zero r := by
    classical
    by_cases he : r=C.zero
    · exact Or.inl he.symm
    · exact Or.inr ((hC.zero_mem_iff hM hr).mpr he)
  exact h.run.ancestor_lower_d hM hC (h.run.initial_row_at_d hM) hAt hLe (ancestor_direct_d hM hC hFF hSP)

/-- 源第0行父项为好部（或无父）时，各行父项都是好部。 -/
theorem Base.source_row_good_d (hM : M.Models KP1Y.theory) (hC : C.Valid M)
    (h : Base M C T m V P H level index n OldTop NewTop Bottom R X Y A) {r s p : M.Domain}
    (hGood : ∀ q, MemPair M P s q → M.mem q A.root) (hP : CopiedMountain.ParentAt M X r s p) : M.mem p A.root := by
  have hAnc := h.source_row_ancestor_d hM hC hP
  obtain ⟨q,hq,_⟩ := ancestor_parent_cases_d hM hC h.run.base.forest hAnc
  rcases ancestor_le_parent_d hM hC h.run.base.forest hq hAnc with he | hlt
  · exact he ▸ hGood q hq
  · exact ((omega_isOrdinal_d hM hC.omega).mem h.coords.root).transitive q (hGood q hq) p hlt

/-- 好部父非root列的任一副本：目标底值等于源底值。 -/
theorem Base.fixed_value_d (hM : M.Models KP1Y.theory) (hC : C.Valid M) (hT : T.Valid M C)
    (h : Base M C T m V P H level index n OldTop NewTop Bottom R X Y A) {s b c v : M.Domain}
    (hRoot : M.mem A.root s) (hs : M.mem s A.last) (hGood : ∀ q, MemPair M P s q → M.mem q A.root)
    (hMap : CopyCoordinates.ParentCopy M C T A b s c) (hc : M.mem c n) :
    MemPair M Bottom c v ↔ MemPair M V s v := by
  have hw := omega_isOrdinal_d hM hC.omega
  have hNonroot : s≠A.root := fun he => SetTheory.KP.mem_irrefl_d (KP1Y.models_weakKP hM) A.root (he ▸ hRoot)
  have hsn : M.mem s n := h.last_subset_d hM hC hT s hs
  have hcY : M.mem c Y.width := h.width_eq ▸ hc
  have hsY : M.mem s Y.width := h.width_eq ▸ hsn
  have hRows : ∀ r, M.mem r C.omega → ∀ p, CopiedMountain.ParentAt M Y r c p ↔ CopiedMountain.ParentAt M Y r s p := by
    intro r _ p
    rw [h.copies.parents r c p,CopiedMountain.Terminal.parent_parent_copy_nonroot_d hM hC hT h.coords h.source hs hNonroot hMap,
      h.copies.original_parents_d hM hC h.coords hsn hs]
    constructor
    · rintro ⟨_,p',_,hP',hMapP⟩
      have hGoodP := h.source_row_good_d hM hC hGood hP'
      have he := (CopyCoordinates.parent_copy_good_iff hMapP.2.1 hMapP.1 hGoodP).mp hMapP
      exact he ▸ hP'
    · intro hP
      have hGoodP := h.source_row_good_d hM hC hGood hP
      have hpNat := hw.transitive A.root h.coords.root p hGoodP
      exact ⟨hc,p,hpNat,hP,(CopyCoordinates.parent_copy_good_iff hMap.2.1 hpNat hGoodP).mpr rfl⟩
  have hTops : ∀ t, MemPair M NewTop c t ↔ MemPair M NewTop s t := fun t =>
    (h.newTop.parent_copy_iff_d hM hC hT h.coords hs hcY hMap).trans (h.newTop.prefix_iff_d hM hC hT h.coords hsY hs).symm
  exact (h.twin_value_d hM hC hT hcY hsY hRows hTops v).trans (h.prefix_values_d hM hC hT s hs v)

end

/-- H3：原 badAtTerminalBase_upperFixed。 -/
theorem terminal_base_upper_fixed_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {m V P H level index n OldTop NewTop Bottom : M.Domain} {R : RowStateSpace M.Domain}
    (hRun : RowRun M C m R V P H) (hBase : RootedRow M C m V P)
    {X Y : CopiedMountain.Data M.Domain} (hX : X.Valid M C) (hFrom : CopiedMountain.FromRun M C m R V H X)
    (hOldTop : TopValueGraph M C m R H X.heights OldTop)
    {A : CopyCoordinates.Context M.Domain} (hA : A.Valid M C) (hWidth : M.SuccessorOf m A.last)
    (hBad : RowBadAt M C R H level A.last A.root) (hIndex : M.mem index C.omega)
    (hN : CopyCoordinates.Width M C T A index n) (hY : Y.Valid M C)
    (hCopy : CopiedMountain.Terminal.Copies M C T A X level n Y)
    (hTop : CopiedTop M C T A OldTop Y.width NewTop)
    (hRebuild : Rebuilds M C T.addPairs T.plus Y NewTop Bottom)
    {D : CopiedMountain.Lower.Context M.Domain} (hD : D.coordinates=A) :
    CopiedMountain.Lower.UpperFixed M C T D V P n Bottom := by
  have h := Base.mk hRun hBase hX hFrom hOldTop hA hWidth hBad hIndex hN hY hCopy hTop hRebuild
  subst hD
  intro s hRoot hs hGood b c v hMap hc hV
  exact (h.fixed_value_d hM hC hT hRoot hs hGood hMap hc).mpr hV

end KP1Y.OneYFinite.TerminalBase
