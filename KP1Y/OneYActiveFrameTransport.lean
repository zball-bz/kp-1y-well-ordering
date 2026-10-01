import KP1Y.OneYActiveFrame
import KP1Y.OneYTerminalCopy

/-! 实际活动帧展开与Terminal复制图的逐父边和深度读取桥。 -/
namespace KP1Y.OneYFinite.ActiveFrameTransport
open YesMetaZFC YesMetaZFC.SetTheory YesMetaZFC.SetTheory.Definitional
open KP1Y.Kuratowski KP1Y.Functions KP1Y.Naturals KP1Y.Bounded KP1Y.Arithmetic
open KP1Y.OneYFinite
universe u

private theorem parent_copy_unique_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {A : CopyCoordinates.Context M.Domain} (hA : A.Valid M C) {copy p x y : M.Domain}
    (hx : CopyCoordinates.ParentCopy M C T A copy p x) (hy : CopyCoordinates.ParentCopy M C T A copy p y) : x=y := by
  obtain ⟨J,hJ,hRows⟩ := CopyCoordinates.parent_copy_graph_exists_d hM hC hT hA hx.2.1
  exact hJ.graph.unique p x y ((hRows p x).mpr hx) ((hRows p y).mpr hy)

private theorem parent_copy_original_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {A : CopyCoordinates.Context M.Domain} (hA : A.Valid M C) {copy source child : M.Domain}
    (hSource : M.mem source A.last) (hMap : CopyCoordinates.ParentCopy M C T A copy source child) (hChild : M.mem child A.last) :
    child=source ∧ (M.mem source A.root ∨ copy=C.zero) := by
  have hw := omega_isOrdinal_d hM hC.omega
  classical
  by_cases hGood : M.mem source A.root
  · exact ⟨(CopyCoordinates.parent_copy_good_iff hMap.2.1 hMap.1 hGood).mp hMap,Or.inl hGood⟩
  · have hAfter : A.root=source ∨ M.mem A.root source := by
      rcases hw.wellOrder.linear.compare A.root hA.root source hMap.1 with he | hlt | hgt
      · exact Or.inl (hM.1.eq_of_same_members A.root source he)
      · exact Or.inr hlt
      · exact False.elim (hGood hgt)
    have hCopyZero : copy=C.zero := by
      apply Classical.byContradiction
      intro hNot
      exact MatrixCopy.parent_copy_different_copy_disjoint_d hM hC hT hA hNot hAfter hSource hMap hChild
        (CopyCoordinates.parent_copy_zero_d hM hC hT hA (hw.transitive A.last hA.last child hChild))
    subst copy
    exact ⟨parent_copy_unique_d hM hC hT hA hMap (CopyCoordinates.parent_copy_zero_d hM hC hT hA hMap.1),Or.inr rfl⟩

/-- Terminal真实分支在非root源列上的ParentCopy方程；不另建复制父定义。 -/
theorem _root_.KP1Y.OneYFinite.CopiedMountain.Terminal.parent_parent_copy_nonroot_d
    {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {A : CopyCoordinates.Context M.Domain} (hA : A.Valid M C) {X : CopiedMountain.Data M.Domain} (hX : X.Valid M C)
    {level r copy source child target : M.Domain} (hSource : M.mem source A.last) (hNonroot : source≠A.root)
    (hMap : CopyCoordinates.ParentCopy M C T A copy source child) :
    CopiedMountain.Terminal.Parent M C T A X level r child target ↔
      ∃ p, M.mem p C.omega ∧ CopiedMountain.ParentAt M X r source p ∧ CopyCoordinates.ParentCopy M C T A copy p target := by
  have hw := omega_isOrdinal_d hM hC.omega
  classical
  by_cases hChild : M.mem child A.last
  · obtain ⟨hEq,hCase⟩ := parent_copy_original_d hM hC hT hA hSource hMap hChild
    subst child
    apply (CopiedMountain.Terminal.parent_original_iff_d hM hC hA hSource).trans
    have hIdentity (p : M.Domain) (hParent : CopiedMountain.ParentAt M X r source p) : CopyCoordinates.ParentCopy M C T A copy p p := by
      have hpNat := hw.transitive X.width hX.width p (hParent.bounds hM.1 hX).2.2.1
      rcases hCase with hGood | hZero
      · have hpGood := (hw.mem hA.root).transitive source hGood p (hParent.bounds hM.1 hX).2.2.2
        exact (CopyCoordinates.parent_copy_good_iff hMap.2.1 hpNat hpGood).mpr rfl
      · exact hZero.symm ▸ CopyCoordinates.parent_copy_zero_d hM hC hT hA hpNat
    constructor
    · intro hParent
      exact ⟨target,hw.transitive X.width hX.width target (hParent.bounds hM.1 hX).2.2.1,hParent,hIdentity target hParent⟩
    · rintro ⟨p,_,hParent,hImage⟩
      have hTarget := parent_copy_unique_d hM hC hT hA hImage (hIdentity p hParent)
      exact hTarget.symm ▸ hParent
  · have hNotGood : ¬M.mem source A.root := by
      intro hGood
      have hEq := (CopyCoordinates.parent_copy_good_iff hMap.2.1 hMap.1 hGood).mp hMap
      exact hChild (hEq.symm ▸ hSource)
    have hAfter : M.mem A.root source := by
      rcases hw.wellOrder.linear.compare A.root hA.root source hMap.1 with he | hlt | hgt
      · exact False.elim (hNonroot (hM.1.eq_of_same_members A.root source he).symm)
      · exact hlt
      · exact False.elim (hNotGood hgt)
    have hEncode := (CopyCoordinates.parent_copy_bad_iff hNotGood).mp hMap
    have hRaw := CopyCoordinates.encoded_decodes_d hM hC hT ⟨hAfter,Or.inr hSource⟩ hEncode
    have hChildNat : M.mem child C.omega := by
      obtain ⟨_,_,_,_,_,hAdd⟩ := hEncode
      exact (hAdd.bounds hM.1 hT.add).2.2
    exact CopiedMountain.Terminal.parent_raw_low_iff_d hM hC hT hA hChildNat hChild hRaw
      (fun hHigh => SetTheory.KP.mem_irrefl_d (KP1Y.models_weakKP hM) A.last (hHigh.1 ▸ hSource))

private theorem seam_encode_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {A : CopyCoordinates.Context M.Domain} (hA : A.Valid M C) {prev next child : M.Domain}
    (hPrev : M.mem prev C.omega) (hs : M.SuccessorOf next prev)
    (hPos : CopyPosition M C.omega T.addPairs T.plus T.mulPairs T.times A.root A.length next C.zero child) :
    CopyCoordinates.Encode M C T A A.last prev child := by
  obtain ⟨off,hOff,hTimes⟩ := hT.mul.mul_exists_d hM hC hPrev (hA.length_nat hM.1)
  rcases (CopyCoordinates.seam_bms_shift_iff_d hM hC hT hA hPrev hs hOff hTimes).mp hPos with ⟨hBad,_⟩ | ⟨_,hAdd⟩
  · exact False.elim (SetTheory.KP.mem_irrefl_d (KP1Y.models_weakKP hM) A.root
      (((omega_isOrdinal_d hM hC.omega).mem hA.root).transitive A.last hBad A.root hA.below))
  · exact ⟨hA.last,hPrev,off,hOff,hTimes,hAdd⟩

/-- 给定同一旧行的实际读取对应，已证明的BM4复制父图逐边等于Terminal的字面分支。 -/
theorem copied_forest_terminal_parent_iff_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {A : CopyCoordinates.Context M.Domain} (hA : A.Valid M C) {X : CopiedMountain.Data M.Domain} (hX : X.Valid M C)
    {m P fullRow active level r count width Q child : M.Domain} (hP : Forest M C.omega m P)
    (hCF : MatrixCopy.CopyForest M C T A P fullRow active count width Q) (hr : M.mem r C.omega) (hLevel : M.mem level C.omega)
    (hCut : M.mem fullRow active ↔ M.mem r level)
    (hRead : ∀ c p, MemPair M P c p ↔ CopiedMountain.ParentAt M X r c p) (hChild : M.mem child width) :
    ∀ target, MemPair M Q child target ↔ CopiedMountain.Terminal.Parent M C T A X level r child target := by
  have hw := omega_isOrdinal_d hM hC.omega
  intro target
  classical
  rcases hCF.column_cases_d hM hC hT hA hChild with hGood | ⟨copy,hCopy,slot,hSlot,source,hSource,hAdd,hPos⟩
  · have hcLast := (hw.mem hA.last).transitive A.root hA.below child hGood
    exact (hCF.good_parent_iff_d hM hC hT hA hGood).trans ((hRead child target).trans
      (CopiedMountain.Terminal.parent_original_iff_d hM hC hA hcLast).symm)
  · have hCopyNat := hw.transitive count hCF.count_nat copy hCopy
    have hSlotNat := hw.transitive A.length (hA.length_nat hM.1) slot hSlot
    have hSourceNat := hw.transitive A.last hA.last source hSource
    have hAfter := ordinal_subset_cases_d hM (hw.mem hA.root) (hw.mem hSourceNat)
      (sum_base_subset_d hM (hw.mem hA.root) ((hT.add.add_iff_sum hM hA.root hSlotNat).mp hAdd))
    have hNotGood : ¬M.mem source A.root := by
      intro hGood
      rcases hAfter with he | hlt
      · exact SetTheory.KP.mem_irrefl_d (KP1Y.models_weakKP hM) A.root (he.symm ▸ hGood)
      · exact SetTheory.KP.mem_irrefl_d (KP1Y.models_weakKP hM) A.root ((hw.mem hA.root).transitive source hGood A.root hlt)
    have hMap := (CopyCoordinates.parent_copy_bad_iff hNotGood).mpr
      ((CopyCoordinates.encode_at_base_iff_d hM hC hT hA.root hSlotNat hCopyNat hAdd).mpr hPos)
    have hMapped (s b : M.Domain) (hBound : ∀ p, MemPair M P s p → M.mem p A.last) :
        (∃ p, M.mem p A.last ∧ MemPair M P s p ∧ CopyCoordinates.ParentCopy M C T A b p target) ↔
          CopiedMountain.Terminal.MappedParent M C T A X b r s target := by
      constructor
      · rintro ⟨p,hp,hParent,hImage⟩
        exact ⟨p,hw.transitive A.last hA.last p hp,(hRead s p).mp hParent,hImage⟩
      · rintro ⟨p,_,hParent,hImage⟩
        have hOld := (hRead s p).mpr hParent
        exact ⟨p,hBound p hOld,hOld,hImage⟩
    by_cases hNonroot : source≠A.root
    · exact (hCF.source_parent_nonroot_d hM hC hT hA hP hCF.count_nat hCopy hSource hNonroot hMap target).trans
        ((hMapped source copy (fun p hp => (hw.mem hA.last).transitive source hSource p (hP.left source p hp))).trans
          (CopiedMountain.Terminal.parent_parent_copy_nonroot_d hM hC hT hA hX hSource hNonroot hMap).symm)
    · have hSourceRoot : source=A.root := Classical.byContradiction hNonroot
      subst source
      have hRootZero := (hT.add.add_iff_sum hM hA.root hC.zero_nat).mpr (sum_zero_d hM A.root hC.zero_empty)
      have hEncode := (CopyCoordinates.parent_copy_bad_iff (SetTheory.KP.mem_irrefl_d (KP1Y.models_weakKP hM) A.root)).mp hMap
      have hRootPos := (CopyCoordinates.encode_at_base_iff_d hM hC hT hA.root hC.zero_nat hCopyNat hRootZero).mp hEncode
      by_cases hCopyZero : copy=C.zero
      · subst copy
        have hChildRoot := parent_copy_unique_d hM hC hT hA hMap (CopyCoordinates.parent_copy_zero_d hM hC hT hA hA.root)
        subst child
        exact (hCF.root_high_parent_iff_d hM hC hT hA hCF.count_nat hCopy (Or.inl rfl) hRootPos target).trans
          ((hRead A.root target).trans (CopiedMountain.Terminal.parent_original_iff_d hM hC hA hA.below).symm)
      · have hNotOld : ¬M.mem child A.last := by
          intro hc
          exact MatrixCopy.parent_copy_different_copy_disjoint_d hM hC hT hA hCopyZero (Or.inl rfl) hA.below hMap hc
            (CopyCoordinates.parent_copy_zero_d hM hC hT hA (hw.transitive A.last hA.last child hc))
        obtain ⟨prev,hPrev,hs⟩ : ∃ prev, M.mem prev C.omega ∧ M.SuccessorOf copy prev := by
          rcases natural_cases hM hC.omega hCopyNat with he | hSucc
          · exact False.elim (hCopyZero (hM.1.eq_of_same_members copy C.zero (fun t => iff_of_false (he t) (hC.zero_empty t))))
          · exact hSucc
        have hSeam := seam_encode_d hM hC hT hA hPrev hs hRootPos
        have hRaw := CopyCoordinates.encoded_decodes_d hM hC hT ⟨hA.below,Or.inl rfl⟩ hSeam
        have hcNat := hw.transitive width hCF.forest.width child hChild
        by_cases hLow : M.mem r level
        · have hNotHigh : ¬CopiedMountain.Terminal.HighSeam M A.last level r A.last := by
            rintro ⟨_,he | hlt⟩
            · exact SetTheory.KP.mem_irrefl_d (KP1Y.models_weakKP hM) r (he ▸ hLow)
            · exact SetTheory.KP.mem_irrefl_d (KP1Y.models_weakKP hM) r ((hw.mem hr).transitive level hlt r hLow)
          exact (hCF.root_low_parent_iff_d hM hC hT hA hCF.count_nat hCopy hPrev hs (hCut.mpr hLow) hRootPos target).trans
            ((hMapped A.last prev (fun p hp => hP.left A.last p hp)).trans
              (CopiedMountain.Terminal.parent_raw_low_iff_d hM hC hT hA hcNat hNotOld hRaw hNotHigh).symm)
        · have hHigh : level=r ∨ M.mem level r := by
            rcases hw.wellOrder.linear.compare level hLevel r hr with he | hlt | hgt
            · exact Or.inl (hM.1.eq_of_same_members level r he)
            · exact Or.inr hlt
            · exact False.elim (hLow hgt)
          exact (hCF.root_high_parent_iff_d hM hC hT hA hCF.count_nat hCopy (Or.inr (fun h => hLow (hCut.mp h))) hRootPos target).trans
            ((hRead A.root target).trans (CopiedMountain.Terminal.parent_raw_high_iff_d hM hC hT hA hcNat hNotOld hRaw hHigh).symm)

private theorem matrix_parent_at_row_iff {M : SetTheory.Structure.{u}} (he : Extensional M)
    {C : ExpressionData M.Domain} {m height Cells Values Forests Rows L r P : M.Domain}
    (hRun : MatrixParentRun M C m height Cells Values Forests Rows L) (hP : MemPair M Rows r P) (c p : M.Domain) :
    MatrixParentAt M Forests Rows r c p ↔ MemPair M P c p := by
  constructor
  · rintro ⟨Q,_,hQ,hParent⟩
    exact hRun.graph.unique r Q P hQ hP ▸ hParent
  · intro hParent
    exact ⟨P,(hRun.graph.bounds he hP).2,hP,hParent⟩

/-- 实际帧的数值父读取与已冻结CopiedMountain.FromRun编码相同，包含列域外。 -/
theorem normalized_source_parent_iff_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {m V P H L : M.Domain} {R : RowStateSpace M.Domain} (hRun : RowRun M C m R V P H)
    {A : ActiveFrame M.Domain} (hA : A.Valid M C T m P H R) (hCap : FrameValueCap M V A.cap)
    (hRaw : MatrixParentRun M C m A.height A.cells A.values R.forests A.rows L)
    {B : FiniteMatrix M.Domain} (hTrim : TrimmedMatrix M C (A.raw m) B) {OtherForests Other OtherL : M.Domain}
    (hOther : MatrixParentRun M C B.width B.height B.cells B.values OtherForests Other OtherL)
    {X : CopiedMountain.Data M.Domain} (hX : X.Valid M C) (hFrom : CopiedMountain.FromRun M C m R V H X)
    {j fullRow : M.Domain} (hj : M.mem j C.omega) (hAdd : AddAt M T.addPairs T.plus A.frame.height j fullRow)
    (c p : M.Domain) : MatrixParentAt M OtherForests Other fullRow c p ↔ CopiedMountain.ParentAt M X j c p := by
  classical
  by_cases hc : M.mem c m
  · obtain ⟨W,Q,hAt⟩ := hRun.at_exists_d hj
    apply (hA.normalized_parent_all_d hM hC hT hRun hCap hRaw hTrim hOther hj hAdd hAt hc).trans
    constructor
    · intro hParent
      exact (hFrom.parent_iff hM.1 hX j c p).mpr ⟨W,Q,hAt,hParent⟩
    · intro hParent
      obtain ⟨W',Q',hAt',hParent'⟩ := (hFrom.parent_iff hM.1 hX j c p).mp hParent
      exact (hRun.at_unique hM.1 hAt' hAt).2 ▸ hParent'
  · apply iff_of_false
    · rintro ⟨Q,_,hAt,hParent⟩
      have hWidth : B.width=m := hTrim.width
      exact hc (hWidth ▸ ((hOther.forests fullRow Q hAt).bounds hM.1 hParent).1)
    · intro hParent
      exact hc (hFrom.width ▸ (hParent.bounds hM.1 hX).2.1)

/-- 已知真实成功Context时，从完整expand反解出它确实执行的raw复制和trim。 -/
theorem _root_.KP1Y.OneYFinite.MatrixExpansion.raw_from_context_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {A B : FiniteMatrix M.Domain} (hA : A.Valid M C.omega)
    {T : MatrixArithmetic M.Domain} (hT : T.Valid M C) {Forests Rows L last maximal root index : M.Domain}
    (hRun : MatrixParentRun M C A.width A.height A.cells A.values Forests Rows L)
    (hContext : MatrixExpansionContext M C A Forests Rows last maximal root) (hIndex : M.mem index C.omega)
    (h : MatrixExpansion M C A T Forests Rows index B) :
    ∃ count len total Raw, RawMatrixExpansion M C A T Forests Rows last maximal root index count len total Raw ∧ TrimmedMatrix M C Raw B := by
  obtain ⟨R,hR,hStep,hTrim⟩ := h
  obtain ⟨count,len,total,Raw,hRaw⟩ := matrix_expand_raw_context_d hM hC hA hT hRun hContext hIndex
  have hRawStep : RawMatrixStep M C A T Forests Rows index Raw :=
    Or.inr ⟨last,hContext.width_successor,Or.inr ⟨maximal,root,count,len,total,hContext,hRaw⟩⟩
  have he := hRawStep.unique_d hM hC hA hRun hRaw.matrix hR hStep
  exact ⟨count,len,total,Raw,hRaw,he.symm ▸ hTrim⟩

private theorem add_index_lt_iff_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {offset i j r s : M.Domain} (hOffset : M.mem offset C.omega) (hi : M.mem i C.omega) (hj : M.mem j C.omega)
    (hR : AddAt M T.addPairs T.plus offset i r) (hS : AddAt M T.addPairs T.plus offset j s) : M.mem r s ↔ M.mem i j := by
  have hw := omega_isOrdinal_d hM hC.omega
  have hRSum := (hT.add.add_iff_sum hM hOffset hi).mp hR
  have hSSum := (hT.add.add_iff_sum hM hOffset hj).mp hS
  constructor
  · intro hrs
    rcases hw.wellOrder.linear.compare i hi j hj with he | hlt | hgt
    · have hij := hM.1.eq_of_same_members i j he
      subst j
      have hEq := hT.add.add_unique hM.1 hR hS
      exact False.elim (SetTheory.KP.mem_irrefl_d (KP1Y.models_weakKP hM) s (hEq ▸ hrs))
    · exact hlt
    · have hsr := sum_strict_right_d hM (hw.mem hOffset) hSSum hRSum hgt
      exact False.elim (SetTheory.KP.mem_irrefl_d (KP1Y.models_weakKP hM) s
        ((hw.mem (hS.bounds hM.1 hT.add).2.2).transitive r hrs s hsr))
  · exact sum_strict_right_d hM (hw.mem hOffset) hRSum hSSum

/-- 完整展开后的实际数值区父关系就是Terminal复制图的字面Parent。
所有矩阵行都可读取；有限Rows域外按已证明的无父性处理。
-/
theorem expanded_terminal_parent_iff_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {m V P H L : M.Domain} {R : RowStateSpace M.Domain} (hRun : RowRun M C m R V P H)
    {Frame : ActiveFrame M.Domain} (hFrame : Frame.Valid M C T m P H R) (hCap : FrameValueCap M V Frame.cap)
    (hFrameRaw : MatrixParentRun M C m Frame.height Frame.cells Frame.values R.forests Frame.rows L)
    {B D : FiniteMatrix M.Domain} (hTrim : TrimmedMatrix M C (Frame.raw m) B) {BF BR BL DF DR DL : M.Domain}
    (hBRun : MatrixParentRun M C B.width B.height B.cells B.values BF BR BL)
    (hDRun : MatrixParentRun M C D.width D.height D.cells D.values DF DR DL)
    {X : CopiedMountain.Data M.Domain} (hX : X.Valid M C) (hFrom : CopiedMountain.FromRun M C m R V H X)
    {A : CopyCoordinates.Context M.Domain} (hA : A.Valid M C) {level active index j fullRow child : M.Domain}
    (hLevel : M.mem level C.omega) (hActive : AddAt M T.addPairs T.plus Frame.frame.height level active)
    (hContext : MatrixExpansionContext M C B BF BR A.last active A.root)
    (hIndex : M.mem index C.omega) (hExpansion : MatrixExpansion M C B T BF BR index D)
    (hj : M.mem j C.omega) (hAdd : AddAt M T.addPairs T.plus Frame.frame.height j fullRow) (hChild : M.mem child D.width) :
    ∀ target, MatrixParentAt M DF DR fullRow child target ↔ CopiedMountain.Terminal.Parent M C T A X level j child target := by
  obtain ⟨count,len,total,Raw,hRaw,hOutTrim⟩ := hExpansion.raw_from_context_d hM hC hTrim.matrix hT hBRun hContext hIndex
  have hLen := truncated_difference_unique_d hM hC hRaw.difference hA.difference
  subst len
  obtain ⟨RF,RR,RL,hRawRun⟩ := matrix_parent_run_exists_d hM hC hRaw.matrix
  have hOriginal (c p : M.Domain) := normalized_source_parent_iff_d hM hC hT hRun hFrame hCap hFrameRaw hTrim hBRun hX hFrom hj hAdd c p
  have hCut := add_index_lt_iff_d hM hC hT (natural_successor_mem_d hM hC hRun.space.width hFrame.frame.height) hj hLevel hAdd hActive
  intro target
  apply (hOutTrim.parent_at_iff_d hM hC hRaw.matrix hRawRun hDRun fullRow child target).trans
  classical
  by_cases hr : M.mem fullRow B.height
  · obtain ⟨OldP,_,hOldP⟩ := hBRun.graph.total fullRow hr
    obtain ⟨NewP,_,hNewP⟩ := hRawRun.graph.total fullRow (hRaw.height.symm ▸ hr)
    have hCF := hRaw.parent_copy_rows_d hM hC hTrim.matrix hT hA hBRun hContext hRawRun hIndex fullRow OldP NewP hOldP hNewP
    have hRead (c p : M.Domain) : MemPair M OldP c p ↔ CopiedMountain.ParentAt M X j c p :=
      (matrix_parent_at_row_iff hM.1 hBRun hOldP c p).symm.trans (hOriginal c p)
    exact (matrix_parent_at_row_iff hM.1 hRawRun hNewP child target).trans
      (copied_forest_terminal_parent_iff_d hM hC hT hA hX (hBRun.forests fullRow OldP hOldP) hCF hj hLevel hCut hRead
        (hOutTrim.width ▸ hChild) target)
  · have hNoSource (c p : M.Domain) : ¬CopiedMountain.ParentAt M X j c p := by
      intro hParent
      obtain ⟨Q,_,hAt,_⟩ := (hOriginal c p).mpr hParent
      exact hr (hBRun.graph.bounds hM.1 hAt).1
    apply iff_of_false
    · rintro ⟨Q,_,hAt,_⟩
      exact hr (hRaw.height ▸ (hRawRun.graph.bounds hM.1 hAt).1)
    · rintro ⟨_,⟨_,hParent⟩ | ⟨_,s,_,b,_,_,hCase⟩⟩
      · exact hNoSource child target hParent
      · rcases hCase with ⟨_,hParent⟩ | ⟨_,p,_,hParent,_⟩
        · exact hNoSource A.root target hParent
        · exact hNoSource s p hParent

/-- 规范化不改列宽；实际BM4复制宽度等于1-Y坐标的last+index*length。 -/
theorem _root_.KP1Y.OneYFinite.MatrixExpansion.width_coordinates_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {B D : FiniteMatrix M.Domain} (hB : B.Valid M C.omega)
    {T : MatrixArithmetic M.Domain} (hT : T.Valid M C) {A : CopyCoordinates.Context M.Domain} (hA : A.Valid M C)
    {Forests Rows L active index : M.Domain} (hRun : MatrixParentRun M C B.width B.height B.cells B.values Forests Rows L)
    (hContext : MatrixExpansionContext M C B Forests Rows A.last active A.root) (hIndex : M.mem index C.omega)
    (hExpansion : MatrixExpansion M C B T Forests Rows index D) : CopyCoordinates.Width M C T A index D.width := by
  obtain ⟨count,len,total,Raw,hRaw,hTrim⟩ := hExpansion.raw_from_context_d hM hC hB hT hRun hContext hIndex
  have hLen := truncated_difference_unique_d hM hC hRaw.difference hA.difference
  subst len
  obtain ⟨width,_,hWidth⟩ := CopyCoordinates.encode_exists_d hM hC hT hA hA.last hIndex
  obtain ⟨count',_,hSucc,total',_,hTimes,hSum⟩ := CopyCoordinates.width_as_bms_d hM hC hT hA hWidth
  have hCount := Structure.SuccessorOf.eq hM.1 hSucc hRaw.copies
  subst count'
  have hTotal := product_unique_d hM hTimes hRaw.product
  subst total'
  have hW := sum_unique_d hM hRaw.width hSum
  exact (hTrim.width.trans hW).symm ▸ hWidth

/-- 完整矩阵展开的独立I出口；高度以上的S没有任何支持行。 -/
theorem _root_.KP1Y.OneYFinite.MatrixExpansion.depth_regular_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {A B : FiniteMatrix M.Domain} (hA : A.Valid M C.omega)
    {T : MatrixArithmetic M.Domain} (hT : T.Valid M C) {Forests Rows L OtherForests Other OtherL index : M.Domain}
    (hRun : MatrixParentRun M C A.width A.height A.cells A.values Forests Rows L)
    (h : MatrixExpansion M C A T Forests Rows index B)
    (hOther : MatrixParentRun M C B.width B.height B.cells B.values OtherForests Other OtherL)
    (hIndex : M.mem index C.omega) (hI : MatrixDepthRegular M C A Forests Rows) : MatrixDepthRegular M C B OtherForests Other := by
  have hVoid : AboveS M C A Forests Rows L A.height := by
    intro r hr hLe
    apply False.elim
    rcases hLe with he | hlt
    · exact SetTheory.KP.mem_irrefl_d (KP1Y.models_weakKP hM) A.height (he.symm ▸ hr)
    · exact SetTheory.KP.mem_irrefl_d (KP1Y.models_weakKP hM) A.height
        (((omega_isOrdinal_d hM hC.omega).mem hA.height).transitive r hr A.height hlt)
  exact (h.relative_structural_d hM hC hA hT hRun hOther hIndex hI hVoid).1

/-- I和实际父读取对应推出矩阵单元恰为目标森林的计算深度，包括有限Rows域外的0。 -/
theorem padded_depth_of_parent_read_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {B : FiniteMatrix M.Domain} (hB : B.Valid M C.omega)
    {Forests Rows L : M.Domain} (hRun : MatrixParentRun M C B.width B.height B.cells B.values Forests Rows L)
    (hI : MatrixDepthRegular M C B Forests Rows) {Y : CopiedMountain.Data M.Domain} (hY : Y.Valid M C)
    (hWidth : Y.width=B.width) {r j Q c d : M.Domain} (hQ : MemPair M Y.parents j Q)
    (hRead : ∀ c p, M.mem c B.width → (MatrixParentAt M Forests Rows r c p ↔ CopiedMountain.ParentAt M Y j c p))
    (hc : M.mem c B.width) : PaddedEntry M C.zero B r c d ↔ Depth M C Y.width Q c d := by
  have hQF := hY.forest j Q hQ
  have hQAt (c p : M.Domain) : CopiedMountain.ParentAt M Y j c p ↔ MemPair M Q c p := by
    constructor
    · rintro ⟨P,_,hP,hParent⟩
      exact hY.parents.unique j P Q hP hQ ▸ hParent
    · intro hParent
      exact ⟨Q,(hY.parents.bounds hM.1 hQ).2,hQ,hParent⟩
  classical
  by_cases hr : M.mem r B.height
  · obtain ⟨P,_,hP⟩ := hRun.graph.total r hr
    have hPF := hRun.forests r P hP
    have hQF' : Forest M C.omega B.width Q := hWidth ▸ hQF
    have hEqual : P=Q := hPF.ext hM.1 hQF' (by
      intro s p
      by_cases hs : M.mem s B.width
      · exact (matrix_parent_at_row_iff hM.1 hRun hP s p).symm.trans ((hRead s p hs).trans (hQAt s p))
      · exact iff_of_false (fun hp => hs (hPF.bounds hM.1 hp).1) (fun hp => hs (hQF'.bounds hM.1 hp).1))
    subst P
    have hEntry : MatrixEntry M B r c d ↔ Depth M C Y.width Q c d := by
      simpa only [hWidth] using matrix_depth_regular_entry_iff_d hM hC hB hRun hI hP c d
    have hPad : PaddedEntry M C.zero B r c d ↔ MatrixEntry M B r c d := by
      simp only [PaddedEntry,hr,hc,not_true_eq_false,false_and,or_false]
    exact hPad.trans hEntry
  · have hNone : NoParent M Y.width Q c := by
      intro p _ hParent
      obtain ⟨P,_,hP,_⟩ := (hRead c p hc).mpr ((hQAt c p).mpr hParent)
      exact hr (hRun.graph.bounds hM.1 hP).1
    obtain ⟨e,hDepth⟩ := depth_exists_d hM hC hQF (hWidth.symm ▸ hc)
    have hZero := depth_of_no_parent_d hM hC hQF hNone hDepth
    have hDepthZero : Depth M C Y.width Q c C.zero := hZero ▸ hDepth
    constructor
    · rintro (hEntry | ⟨_,he⟩)
      · exact False.elim (hr (hEntry.bounds hM.1 hB).1)
      · exact he.symm ▸ hDepthZero
    · intro hDepth
      exact Or.inr ⟨Or.inl hr,depth_of_no_parent_d hM hC hQF hNone hDepth⟩

/-- 完整BM4展开矩阵的数值区读值，等于实际Terminal.Copies行图的计算Depth。 -/
theorem expanded_terminal_depth_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {m V P H L : M.Domain} {R : RowStateSpace M.Domain} (hRun : RowRun M C m R V P H)
    {Frame : ActiveFrame M.Domain} (hFrame : Frame.Valid M C T m P H R) (hCap : FrameValueCap M V Frame.cap)
    (hFrameRaw : MatrixParentRun M C m Frame.height Frame.cells Frame.values R.forests Frame.rows L)
    {B D : FiniteMatrix M.Domain} (hTrim : TrimmedMatrix M C (Frame.raw m) B) {BF BR BL DF DR DL : M.Domain}
    (hBRun : MatrixParentRun M C B.width B.height B.cells B.values BF BR BL)
    (hDRun : MatrixParentRun M C D.width D.height D.cells D.values DF DR DL)
    {X Y : CopiedMountain.Data M.Domain} (hX : X.Valid M C) (hFrom : CopiedMountain.FromRun M C m R V H X)
    {A : CopyCoordinates.Context M.Domain} (hA : A.Valid M C) {level active index j fullRow Q child d : M.Domain}
    (hLevel : M.mem level C.omega) (hActive : AddAt M T.addPairs T.plus Frame.frame.height level active)
    (hContext : MatrixExpansionContext M C B BF BR A.last active A.root)
    (hIndex : M.mem index C.omega) (hExpansion : MatrixExpansion M C B T BF BR index D)
    (hY : Y.Valid M C) (hCopy : CopiedMountain.Terminal.Copies M C T A X level D.width Y)
    (hYRow : MemPair M Y.parents j Q) (hAdd : AddAt M T.addPairs T.plus Frame.frame.height j fullRow) (hChild : M.mem child D.width) :
    PaddedEntry M C.zero D fullRow child d ↔ Depth M C Y.width Q child d := by
  have hBI := hTrim.depth_regular_d hM hC (hFrame.raw_valid hRun.space) hFrameRaw hBRun (hFrame.depth_regular_d hM hC hRun.space)
  have hDI := hExpansion.depth_regular_d hM hC hTrim.matrix hT hBRun hDRun hIndex hBI
  apply padded_depth_of_parent_read_d hM hC hExpansion.matrix hDRun hDI hY hCopy.width hYRow ?_ hChild
  intro c p hc
  have hParents := expanded_terminal_parent_iff_d hM hC hT hRun hFrame hCap hFrameRaw hTrim hBRun hDRun hX hFrom hA hLevel hActive hContext
    hIndex hExpansion (hY.parents.bounds hM.1 hYRow).1 hAdd hc p
  exact hParents.trans ((hCopy.parents j c p).trans ⟨And.right,fun hp => ⟨hc,hp⟩⟩).symm

end KP1Y.OneYFinite.ActiveFrameTransport
