import KP1Y.OneYReconstructionSelection
import KP1Y.OneYTerminalCopyHighRoots

/-! 真实Terminal复制的规范重提取：先把实际扩展帧装饰S转成图层阻挡。 -/
namespace KP1Y.OneYFinite.TerminalCanonical
open YesMetaZFC YesMetaZFC.SetTheory YesMetaZFC.SetTheory.Definitional
open KP1Y.Kuratowski KP1Y.Functions KP1Y.Naturals KP1Y.Bounded
open KP1Y.Arithmetic
universe u

private theorem matrix_parent_at_iff {M : SetTheory.Structure.{u}} (he : Extensional M)
    {C : ExpressionData M.Domain} {m height cells values Forests Rows L r F : M.Domain}
    (hRun : MatrixParentRun M C m height cells values Forests Rows L) (hF : MemPair M Rows r F) (c p : M.Domain) :
    MatrixParentAt M Forests Rows r c p ↔ MemPair M F c p := by
  constructor
  · rintro ⟨G,_,hG,hP⟩
    exact hRun.graph.unique r G F hG hF ▸ hP
  · exact fun h => ⟨F,(hRun.graph.bounds he hF).2,hF,h⟩

theorem expanded_frame_blocker_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {m V P H L : M.Domain} {R : RowStateSpace M.Domain} (hRun : RowRun M C m R V P H)
    {Frame : ActiveFrame M.Domain} (hFrame : Frame.Valid M C T m P H R) (hCap : FrameValueCap M V Frame.cap)
    (hFrameRaw : MatrixParentRun M C m Frame.height Frame.cells Frame.values R.forests Frame.rows L)
    {B D : FiniteMatrix M.Domain} (hTrim : TrimmedMatrix M C (Frame.raw m) B) {BF BR BL DF DR DL : M.Domain}
    (hBRun : MatrixParentRun M C B.width B.height B.cells B.values BF BR BL)
    (hDRun : MatrixParentRun M C D.width D.height D.cells D.values DF DR DL)
    {X Y : CopiedMountain.Data M.Domain} (hX : X.Valid M C) (hFrom : CopiedMountain.FromRun M C m R V H X)
    {A : CopyCoordinates.Context M.Domain} (hA : A.Valid M C) {level active index Top r s t c q p Q : M.Domain}
    (hLevel : M.mem level C.omega) (hActive : AddAt M T.addPairs T.plus Frame.frame.height level active)
    (hContext : MatrixExpansionContext M C B BF BR A.last active A.root)
    (hIndex : M.mem index C.omega) (hExpansion : MatrixExpansion M C B T BF BR index D)
    (hY : Y.Valid M C) (hCopy : CopiedMountain.Terminal.Copies M C T A X level D.width Y)
    (hS : DecoratedAboveS M C D DF DR DL Frame.frame.height Top)
    (hSucc : M.SuccessorOf s r) (hNext : M.SuccessorOf t s)
    (hOld : CopiedMountain.ParentAt M Y r c q) (hNew : CopiedMountain.ParentAt M Y s c p)
    (hQ : MemPair M Y.parents s Q) (hNe : p≠q) :
    ∃ z, M.mem z Y.width ∧ (z=q ∨ Ancestor M C Y.width Q z q) ∧ MemPair M Q z p ∧
      ∃ tc, M.mem tc C.omega ∧ ∃ tz, M.mem tz C.omega ∧ MemPair M Top c tc ∧ MemPair M Top z tz ∧
        ForestOrder.KeyLE M C Y c z t tc tz := by
  have hw := omega_isOrdinal_d hM hC.omega
  have hr := (hOld.bounds hM.1 hY).1
  have hs := (hNew.bounds hM.1 hY).1
  have ht := natural_successor_mem_d hM hC hs hNext
  have hOffset := natural_successor_mem_d hM hC hRun.space.width hFrame.frame.height
  obtain ⟨fr,hfr,hFR⟩ := hT.add.add_exists_d hM hC hOffset hr
  obtain ⟨fs,hfs,hFS⟩ := hT.add.add_exists_d hM hC hOffset hs
  obtain ⟨ft,hft,hFT⟩ := hT.add.add_exists_d hM hC hOffset ht
  have hFRS := sum_successor_d hM hSucc ((hT.add.add_iff_sum hM hOffset hr).mp hFR) ((hT.add.add_iff_sum hM hOffset hs).mp hFS)
  have hFST := sum_successor_d hM hNext ((hT.add.add_iff_sum hM hOffset hs).mp hFS) ((hT.add.add_iff_sum hM hOffset ht).mp hFT)
  have hc : M.mem c D.width := hCopy.width ▸ (hNew.bounds hM.1 hY).2.1
  have hRead (j full : M.Domain) (hj : M.mem j C.omega) (hAdd : AddAt M T.addPairs T.plus Frame.frame.height j full)
      (c : M.Domain) (hc : M.mem c D.width) (p : M.Domain) :
      MatrixParentAt M DF DR full c p ↔ CopiedMountain.ParentAt M Y j c p := by
    apply (ActiveFrameTransport.expanded_terminal_parent_iff_d hM hC hT hRun hFrame hCap hFrameRaw hTrim hBRun hDRun
      hX hFrom hA hLevel hActive hContext hIndex hExpansion hj hAdd hc p).trans
    exact ((hCopy.parents j c p).trans ⟨And.right,fun h => ⟨hc,h⟩⟩).symm
  obtain ⟨Fmat,hFM,hFmat,hOldMat⟩ := (hRead r fr hr hFR c hc q).mpr hOld
  obtain ⟨Qmat,hQM,hQmat,hNewMat⟩ := (hRead s fs hs hFS c hc p).mpr hNew
  have hFRBound := (hDRun.graph.bounds hM.1 hFmat).1
  have hFSBound := (hDRun.graph.bounds hM.1 hQmat).1
  have hBaseFS : Frame.frame.height=fs ∨ M.mem Frame.frame.height fs :=
    ordinal_subset_cases_d hM (hw.mem hOffset) (hw.mem hfs)
      (sum_base_subset_d hM (hw.mem hOffset) ((hT.add.add_iff_sum hM hOffset hs).mp hFS))
  have hPrev : PreviousMatrixForest M C D.height DF DR DL fs Fmat := Or.inr ⟨fr,hFRBound,hFRS,hFM,hFmat⟩
  obtain ⟨z,hz,hPath,hZP,tc,htc,tz,htz,hTC,hTZ,hKey⟩ := hS fs hFSBound hBaseFS Fmat hPrev Qmat hQM hQmat ft hft hFST
    c hc q ((hDRun.forests fr Fmat hFmat).bounds hM.1 hOldMat).2 p ((hDRun.forests fs Qmat hQmat).bounds hM.1 hNewMat).2
    hOldMat hNewMat hNe
  have hRows (a : M.Domain) (ha : M.mem a D.width) (b : M.Domain) : MemPair M Qmat a b ↔ MemPair M Q a b := by
    apply ((matrix_parent_at_iff hM.1 hDRun hQmat a b).symm.trans (hRead s fs hs hFS a ha b)).trans
    constructor
    · rintro ⟨Q',_,hQ',hAB⟩
      exact hY.parents.unique s Q' Q hQ' hQ ▸ hAB
    · exact fun h => ⟨Q,(hY.parents.bounds hM.1 hQ).2,hQ,h⟩
  have hQWidth : M.MemberSubset D.width Y.width := hCopy.width.symm ▸ fun _ h => h
  have hPath' : z=q ∨ Ancestor M C Y.width Q z q := hPath.imp id
    ((ancestor_common_prefix_iff_d hM hC (hDRun.forests fs Qmat hQmat) (hY.forest s Q hQ)
      hExpansion.matrix.width (fun _ h => h) hQWidth ((hDRun.forests fr Fmat hFmat).bounds hM.1 hOldMat).2 hRows).mp)
  exact ⟨z,hCopy.width.symm ▸ hz,hPath',(hRows z hz p).mp hZP,tc,htc,tz,htz,hTC,hTZ,
    (ForestOrder.expanded_terminal_key_iff_d hM hC hT hRun hFrame hCap hFrameRaw hTrim hBRun hDRun hX hFrom hA
      hLevel hActive hContext hIndex hExpansion hY hCopy hc hz ht hFT).mpr hKey⟩

private theorem coordinate_eq_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {A B : CopyCoordinates.Context M.Domain}
    (hA : A.Valid M C) (hB : B.Valid M C) (hLast : A.last=B.last) (hRoot : A.root=B.root) : A=B := by
  cases A with
  | mk last root length first =>
    cases B with
    | mk last' root' length' first' =>
      dsimp only at hLast hRoot
      subst last'
      subst root'
      have hl := truncated_difference_unique_d hM hC hA.difference hB.difference
      change length=length' at hl
      have hf := Structure.SuccessorOf.eq hM.1 hA.first hB.first
      change first=first' at hf
      subst length'
      subst first'
      rfl

theorem expanded_top_copied_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain}
    {B D : FiniteMatrix M.Domain} (hB : B.Valid M C.omega) {BF BR BL active index OldTop NewTop : M.Domain}
    (hRun : MatrixParentRun M C B.width B.height B.cells B.values BF BR BL)
    {A : CopyCoordinates.Context M.Domain} (hA : A.Valid M C)
    (hContext : MatrixExpansionContext M C B BF BR A.last active A.root)
    (hTop : ExpandedTop M C B T BF BR index OldTop D NewTop) : CopiedTop M C T A OldTop D.width NewTop := by
  obtain ⟨Raw,_,_,hTrim,hTop⟩ := hTop
  rcases hTop with ⟨hEmpty,_,_⟩ | ⟨last,hLast,hCase⟩
  · exact False.elim (hC.zero_empty A.last (hEmpty ▸ hContext.width_successor.predecessor_mem))
  · have hLastEq := Structure.SuccessorOf.predecessor_eq hM.1 ((omega_isOrdinal_d hM hC.omega).mem hA.last)
      hContext.width_successor hLast
    subst last
    rcases hCase with ⟨hNone,_,_⟩ | ⟨maximal,root,hContext',A',hLast',hRoot',hA',hCopied⟩
    · obtain ⟨F,hF,hRow,hParent⟩ := hContext.parent
      exact False.elim (hNone active hContext.row ⟨F,hF,hRow,A.root,(hRun.forests active F hRow).bounds hM.1 hParent |>.2,hParent⟩)
    · have hm := maximal_parent_row_unique_d hM ((omega_isOrdinal_d hM hC.omega).mem hB.height) hContext.maximality hContext'.maximality
      subst maximal
      have hr := hContext.unique_root hRun hContext'
      have he := coordinate_eq_d hM hC hA' hA hLast' (hRoot'.trans hr.symm)
      subst A'
      exact hTrim.width.symm ▸ hCopied

/-- 真RowBadAt构造帧、展开矩阵与Top图，并提供所有内部行的实际装饰阻挡。 -/
theorem row_bad_blocker_exists_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {m V P H level index n OldTop : M.Domain} {R : RowStateSpace M.Domain}
    (hRun : RowRun M C m R V P H) (hBase : RootedRow M C m V P)
    {X Y : CopiedMountain.Data M.Domain} (hX : X.Valid M C) (hFrom : CopiedMountain.FromRun M C m R V H X)
    (hOldTop : TopValueGraph M C m R H X.heights OldTop)
    {A : CopyCoordinates.Context M.Domain} (hA : A.Valid M C) (hWidth : M.SuccessorOf m A.last)
    (hBad : RowBadAt M C R H level A.last A.root) (hIndex : M.mem index C.omega)
    (hN : CopyCoordinates.Width M C T A index n) (hY : Y.Valid M C)
    (hCopy : CopiedMountain.Terminal.Copies M C T A X level n Y) :
    ∃ NewTop, CopiedTop M C T A OldTop n NewTop ∧
      ∀ r s t c q p Q, M.SuccessorOf s r → M.SuccessorOf t s →
        CopiedMountain.ParentAt M Y r c q → CopiedMountain.ParentAt M Y s c p → MemPair M Y.parents s Q → p≠q →
        ∃ z, M.mem z Y.width ∧ (z=q ∨ Ancestor M C Y.width Q z q) ∧ MemPair M Q z p ∧
          ∃ tc, M.mem tc C.omega ∧ ∃ tz, M.mem tz C.omega ∧ MemPair M NewTop c tc ∧ MemPair M NewTop z tz ∧
            ForestOrder.KeyLE M C Y c z t tc tz := by
  obtain ⟨Frame,B,L,BF,BR,BL,Heights,Top,active,hFrame,hCap,hTrim,_,hFrameRaw,hBRun,hI,hHeights,hTop,hTopGraph,_,hActive,hContext,hS⟩ :=
    NumericOrder.row_bad_active_frame_decorated_exists_d hM hC hT hRun hBase hWidth hBad
  have hHeightEq := hHeights.unique hM.1 hFrom.heights
  subst Heights
  have hTopEq := hTop.unique hM.1 hOldTop
  subst Top
  obtain ⟨D,DF,DR,DL,NewTop,hExpansion,_,hDRun,_,_,hExpandedTop,hDecor⟩ :=
    matrix_expansion_decorated_exists_d hM hC hTrim.matrix hT hBRun hIndex hTopGraph hI hS
  have hWidthD := hExpansion.width_coordinates_d hM hC hTrim.matrix hT hA hBRun hContext hIndex
  have hWidthEq := CopyCoordinates.encode_unique hM.1 hT hWidthD hN
  have hCopy' : CopiedMountain.Terminal.Copies M C T A X level D.width Y := hWidthEq.symm ▸ hCopy
  have hCopiedTop := expanded_top_copied_d hM hC hTrim.matrix hBRun hA hContext hExpandedTop
  refine ⟨NewTop,hWidthEq ▸ hCopiedTop,?_⟩
  intro r s t c q p Q hSucc hNext hOld hNew hQ hNe
  exact expanded_frame_blocker_d hM hC hT hRun hFrame hCap hFrameRaw hTrim hBRun hDRun hX hFrom hA
    (hActive.bounds hM.1 hT.add).2.1 hActive hContext hIndex hExpansion hY hCopy' hDecor hSucc hNext hOld hNew hQ hNe

end KP1Y.OneYFinite.TerminalCanonical
