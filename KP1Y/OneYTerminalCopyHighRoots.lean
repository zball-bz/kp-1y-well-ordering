import KP1Y.OneYTerminalCopyRoots
import KP1Y.OneYOrdinaryCopyRoots

/-! 活跃层高行的父森林等于普通复制；与已证低行根运输合并，得到全行根对应。 -/
namespace KP1Y.OneYFinite.CopiedMountain.Terminal
open YesMetaZFC YesMetaZFC.SetTheory YesMetaZFC.SetTheory.Definitional
open KP1Y.Kuratowski KP1Y.Functions KP1Y.Naturals KP1Y.Bounded KP1Y.Arithmetic
open KP1Y.OneYFinite.CopyCoordinates
open KP1Y.OneYFinite.CopiedMountain.Lower (RootAt)
universe u

theorem parent_copied_root_high_iff_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {A : Context M.Domain} (hA : A.Valid M C) {X : Data M.Domain} {level r b c p : M.Domain}
    (hHigh : level=r ∨ M.mem level r) (hMap : ParentCopy M C T A b A.root c) :
    Parent M C T A X level r c p ↔ ParentAt M X r A.root p := by
  obtain ⟨J,hJ,hRows⟩ := parent_copy_graph_exists_d hM hC hT hA hMap.2.1
  rcases natural_cases hM hC.omega hMap.2.1 with hEmpty | ⟨previous,hPrevious,hSucc⟩
  · have hZero := hM.1.eq_of_same_members b C.zero (fun a => ⟨fun h => False.elim (hEmpty a h),fun h => False.elim (hC.zero_empty a h)⟩)
    subst b
    have hEq := hJ.graph.unique A.root c A.root ((hRows A.root c).mpr hMap)
      ((hRows A.root A.root).mpr (parent_copy_zero_d hM hC hT hA hA.root))
    subst c
    exact parent_original_iff_d hM hC hA hA.below
  · obtain ⟨boundary,hBoundary,hWidth⟩ := encode_exists_d hM hC hT hA hA.last hPrevious
    have hNotRoot : ¬M.mem A.root A.root := SetTheory.KP.mem_irrefl_d (KP1Y.models_weakKP hM) A.root
    have hEq := encode_unique hM.1 hT ((parent_copy_bad_iff hNotRoot).mp hMap)
      (width_is_next_cut_d hM hC hT hA hSucc hWidth)
    subst c
    have hCopy := hWidth
    obtain ⟨_,_,off,hOff,_,hAdd⟩ := hCopy
    have hNotOld : ¬M.mem boundary A.last := fun h => SetTheory.KP.mem_irrefl_d (KP1Y.models_weakKP hM) boundary
      (sum_base_subset_d hM ((omega_isOrdinal_d hM hC.omega).mem hA.last)
        ((hT.add.add_iff_sum hM hA.last hOff).mp hAdd) boundary h)
    exact parent_raw_high_iff_d hM hC hT hA hBoundary hNotOld (seam_decodes_d hM hC hT hA hWidth) hHigh

theorem parent_high_eq_ordinary_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {A : Context M.Domain} (hA : A.Valid M C) {X : Data M.Domain} (hX : X.Valid M C)
    {level r c p : M.Domain} (hc : M.mem c C.omega) (hHigh : level=r ∨ M.mem level r) :
    Parent M C T A X level r c p ↔ Ordinary.Parent M C T A X r c p := by
  obtain ⟨s,b,hDec⟩ := OrdinaryCoordinates.decoded_exists_d hM hC hT hA hc
  have hSource := hDec.source_lt_last_d hM hC hT hA
  have hMap := hDec.parent_copy_reconstruct_d hM hC hT hA
  classical
  by_cases hRoot : s=A.root
  · subst s
    rw [parent_copied_root_high_iff_d hM hC hT hA hHigh hMap,
      Ordinary.parent_parent_copy_iff_d hM hC hT hA hX hA.below hMap]
    constructor
    · intro hP
      have hp := (omega_isOrdinal_d hM hC.omega).transitive X.width hX.width p (hP.bounds hM.1 hX).2.2.1
      exact ⟨p,hp,hP,(parent_copy_good_iff hMap.2.1 hp (hP.bounds hM.1 hX).2.2.2).mpr rfl⟩
    · rintro ⟨q,hq,hQ,hMapQ⟩
      have hEq := (parent_copy_good_iff hMapQ.2.1 hq (hQ.bounds hM.1 hX).2.2.2).mp hMapQ
      exact hEq.symm ▸ hQ
  · exact (parent_parent_copy_nonroot_d hM hC hT hA hX hSource hRoot hMap).trans
      (Ordinary.parent_parent_copy_iff_d hM hC hT hA hX hSource hMap).symm

/-- 相同宽度且某一真实父行相同的两个山形，在该行有完全相同的根。 -/
theorem root_at_congr_parents_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} {X Y : Data M.Domain} (hX : X.Valid M C) (hY : Y.Valid M C)
    (hWidth : X.width=Y.width) {r c q : M.Domain}
    (hParents : ∀ a p, ParentAt M X r a p ↔ ParentAt M Y r a p) :
    RootAt M C X r c q ↔ RootAt M C Y r c q := by
  have transfer {D E : Data M.Domain} (hD : D.Valid M C) (hE : E.Valid M C) (hDE : D.width=E.width)
      (hRows : ∀ a p, ParentAt M D r a p ↔ ParentAt M E r a p) (hRoot : RootAt M C D r c q) : RootAt M C E r c q := by
    have hr := (hRoot.bounds hM.1 hD).1
    obtain ⟨F,hF,hRowF,hRF⟩ := hRoot
    obtain ⟨G,hG,hRowG⟩ := hE.parents.total r hr
    have hFG : F=G := (hD.forest r F hRowF).ext hM.1 (hE.forest r G hRowG) (by
      intro a p
      constructor
      · intro hAP
        obtain ⟨G',_,hG',hAP'⟩ := (hRows a p).mp ⟨F,hF,hRowF,hAP⟩
        exact (hE.parents.unique r G' G hG' hRowG) ▸ hAP'
      · intro hAP
        obtain ⟨F',_,hF',hAP'⟩ := (hRows a p).mpr ⟨G,hG,hRowG,hAP⟩
        exact (hD.parents.unique r F' F hF' hRowF) ▸ hAP')
    exact ⟨G,hG,hRowG,hFG ▸ hDE ▸ hRF⟩
  exact ⟨transfer hX hY hWidth hParents,transfer hY hX hWidth.symm (fun a p => (hParents a p).symm)⟩

theorem Copies.high_parents_eq_ordinary_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {A : Context M.Domain} (hA : A.Valid M C) {X Y Z : Data M.Domain} (hX : X.Valid M C)
    {level n r c p : M.Domain} (hCopy : Copies M C T A X level n Y) (hOrd : Ordinary.Copies M C T A X n Z)
    (hn : M.mem n C.omega) (hHigh : level=r ∨ M.mem level r) :
    ParentAt M Y r c p ↔ ParentAt M Z r c p := by
  rw [hCopy.parents,hOrd.parents]
  exact ⟨fun h => ⟨h.1,(parent_high_eq_ordinary_d hM hC hT hA hX
      ((omega_isOrdinal_d hM hC.omega).transitive n hn c h.1) hHigh).mp h.2⟩,
    fun h => ⟨h.1,(parent_high_eq_ordinary_d hM hC hT hA hX
      ((omega_isOrdinal_d hM hC.omega).transitive n hn c h.1) hHigh).mpr h.2⟩⟩

theorem Copies.high_roots_eq_ordinary_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {A : Context M.Domain} (hA : A.Valid M C) {X Y Z : Data M.Domain}
    (hX : X.Valid M C) (hY : Y.Valid M C) (hZ : Z.Valid M C)
    {level n r c q : M.Domain} (hCopy : Copies M C T A X level n Y) (hOrd : Ordinary.Copies M C T A X n Z)
    (hHigh : level=r ∨ M.mem level r) : RootAt M C Y r c q ↔ RootAt M C Z r c q :=
  root_at_congr_parents_d hM hY hZ (hCopy.width.trans hOrd.width.symm)
    (fun _ _ => hCopy.high_parents_eq_ordinary_d hM hC hT hA hX hOrd (hCopy.width ▸ hY.width) hHigh)

theorem Copies.high_root_parent_copy_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {A : Context M.Domain} (hA : A.Valid M C) {X Y : Data M.Domain} (hX : X.Valid M C) (hY : Y.Valid M C)
    {level n r b s c q z : M.Domain} (hLast : M.mem A.last X.width) (hCopy : Copies M C T A X level n Y)
    (hHigh : level=r ∨ M.mem level r) (hSource : M.mem s A.last) (hChild : M.mem c Y.width)
    (hMap : ParentCopy M C T A b s c) (hRoot : RootAt M C X r s q) (hMapRoot : ParentCopy M C T A b q z) :
    RootAt M C Y r c z := by
  obtain ⟨Z,hZ,hOrd⟩ := Ordinary.copy_exists_d hM hC hT hA hX hLast (hCopy.width ▸ hY.width)
  have hChildZ : M.mem c Z.width := hOrd.width.symm ▸ hCopy.width ▸ hChild
  exact (hCopy.high_roots_eq_ordinary_d hM hC hT hA hX hY hZ hOrd hHigh).mpr
    (hOrd.root_parent_copy_d hM hC hT hA hX hZ hSource hChildZ hMap hRoot hMapRoot)

theorem Copies.root_parent_copy_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {A : Context M.Domain} (hA : A.Valid M C) {X Y : Data M.Domain} (hX : X.Valid M C) (hY : Y.Valid M C)
    {m : M.Domain} {R : RowStateSpace M.Domain} {V P H : M.Domain}
    (hRun : RowRun M C m R V P H) (hFrom : FromRun M C m R V H X)
    {level n r b s c q z : M.Domain} (hActive : Active M X A level) (hCopy : Copies M C T A X level n Y)
    (hSource : M.mem s A.last) (hChild : M.mem c Y.width)
    (hMap : ParentCopy M C T A b s c) (hRoot : RootAt M C X r s q) (hMapRoot : ParentCopy M C T A b q z) :
    RootAt M C Y r c z := by
  have hLevel := (hActive.parent.bounds hM.1 hX).1
  rcases (omega_isOrdinal_d hM hC.omega).wellOrder.linear.compare r (hRoot.bounds hM.1 hX).1 level hLevel with he | hLow | hHigh
  · exact hCopy.high_root_parent_copy_d hM hC hT hA hX hY (hActive.parent.bounds hM.1 hX).2.1
      (.inl (hM.1.eq_of_same_members r level he).symm) hSource hChild hMap hRoot hMapRoot
  · exact hCopy.low_root_parent_copy_d hM hC hT hA hX hY hRun hFrom hActive hLow hSource hChild hMap hRoot hMapRoot
  · exact hCopy.high_root_parent_copy_d hM hC hT hA hX hY (hActive.parent.bounds hM.1 hX).2.1
      (.inr hHigh) hSource hChild hMap hRoot hMapRoot

theorem Copies.root_parent_copy_iff_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {A : Context M.Domain} (hA : A.Valid M C) {X Y : Data M.Domain} (hX : X.Valid M C) (hY : Y.Valid M C)
    {m : M.Domain} {R : RowStateSpace M.Domain} {V P H : M.Domain}
    (hRun : RowRun M C m R V P H) (hFrom : FromRun M C m R V H X)
    {level n r b s c z : M.Domain} (hActive : Active M X A level) (hCopy : Copies M C T A X level n Y)
    (hSource : M.mem s A.last) (hChild : M.mem c Y.width) (hMap : ParentCopy M C T A b s c) :
    RootAt M C Y r c z ↔ ∃ q, RootAt M C X r s q ∧ ParentCopy M C T A b q z := by
  constructor
  · intro hRoot
    obtain ⟨height,_,hHeight⟩ := hY.heights.total c hChild
    have hOldHeight := (height_parent_copy_iff_d hM hC hT hA hSource hMap).mp ((hCopy.heights c height).mp hHeight).2
    obtain ⟨q,hQ⟩ := Lower.root_at_exists_d hM hC hX (hRoot.bounds hM.1 hY).1 (hX.heights.bounds hM.1 hOldHeight).1
    have hQNat := (omega_isOrdinal_d hM hC.omega).transitive X.width hX.width q (hQ.bounds hM.1 hX).2.1
    obtain ⟨J,hJ,hRows⟩ := parent_copy_graph_exists_d hM hC hT hA hMap.2.1
    obtain ⟨target,_,hTarget⟩ := hJ.graph.total q hQNat
    have hMapQ := (hRows q target).mp hTarget
    have hNewRoot := hCopy.root_parent_copy_d hM hC hT hA hX hY hRun hFrom hActive hSource hChild hMap hQ hMapQ
    have hEq := hNewRoot.unique_d hM hC hY hRoot
    exact ⟨q,hQ,hEq ▸ hMapQ⟩
  · rintro ⟨q,hQ,hMapQ⟩
    exact hCopy.root_parent_copy_d hM hC hT hA hX hY hRun hFrom hActive hSource hChild hMap hQ hMapQ

/-- 虽然低行seam父路径不同，所有实际行的连通根与普通复制完全相同。 -/
theorem Copies.roots_eq_ordinary_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {A : Context M.Domain} (hA : A.Valid M C) {X Y Z : Data M.Domain}
    (hX : X.Valid M C) (hY : Y.Valid M C) (hZ : Z.Valid M C)
    {m : M.Domain} {R : RowStateSpace M.Domain} {V P H : M.Domain}
    (hRun : RowRun M C m R V P H) (hFrom : FromRun M C m R V H X)
    {level n r c q : M.Domain} (hActive : Active M X A level) (hCopy : Copies M C T A X level n Y)
    (hOrd : Ordinary.Copies M C T A X n Z) (hc : M.mem c n) :
    RootAt M C Y r c q ↔ RootAt M C Z r c q := by
  have hCnat := (omega_isOrdinal_d hM hC.omega).transitive n (hCopy.width ▸ hY.width) c hc
  obtain ⟨s,b,hDec⟩ := OrdinaryCoordinates.decoded_exists_d hM hC hT hA hCnat
  have hSource := hDec.source_lt_last_d hM hC hT hA
  have hMap := hDec.parent_copy_reconstruct_d hM hC hT hA
  exact (hCopy.root_parent_copy_iff_d hM hC hT hA hX hY hRun hFrom hActive hSource (hCopy.width.symm ▸ hc) hMap).trans
    (hOrd.root_parent_copy_iff_d hM hC hT hA hX hZ hSource (hOrd.width.symm ▸ hc) hMap).symm

theorem Copies.nonroot_row_source_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {A : Context M.Domain} (hA : A.Valid M C) {X Y : Data M.Domain} (hX : X.Valid M C) (hY : Y.Valid M C)
    {m : M.Domain} {R : RowStateSpace M.Domain} {V P H : M.Domain}
    (hRun : RowRun M C m R V P H) (hFrom : FromRun M C m R V H X)
    {level n r b s c pNew qNew : M.Domain} (hActive : Active M X A level) (hCopy : Copies M C T A X level n Y)
    (hSource : M.mem s A.last) (hNonroot : s≠A.root) (hMap : ParentCopy M C T A b s c)
    (hParent : ParentAt M Y r c pNew) (hRoot : RootAt M C Y r c qNew) :
    ∃ p q, ParentAt M X r s p ∧ RootAt M C X r s q ∧ ParentCopy M C T A b p pNew ∧ ParentCopy M C T A b q qNew := by
  obtain ⟨p,_,hP,hMapP⟩ := (parent_parent_copy_nonroot_d hM hC hT hA hX hSource hNonroot hMap).mp
    ((hCopy.parents r c pNew).mp hParent).2
  obtain ⟨q,hQ,hMapQ⟩ := (hCopy.root_parent_copy_iff_d hM hC hT hA hX hY hRun hFrom hActive hSource
    (hParent.bounds hM.1 hY).2.1 hMap).mp hRoot
  exact ⟨p,q,hP,hQ,hMapP,hMapQ⟩

theorem Copies.high_row_source_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {A : Context M.Domain} (hA : A.Valid M C) {X Y : Data M.Domain} (hX : X.Valid M C) (hY : Y.Valid M C)
    {level n r c pNew qNew : M.Domain} (hLast : M.mem A.last X.width) (hCopy : Copies M C T A X level n Y)
    (hHigh : level=r ∨ M.mem level r) (hParent : ParentAt M Y r c pNew) (hRoot : RootAt M C Y r c qNew) :
    ∃ s b p q, M.mem s A.last ∧ M.mem b C.omega ∧ ParentAt M X r s p ∧ RootAt M C X r s q ∧
      ParentCopy M C T A b s c ∧ ParentCopy M C T A b p pNew ∧ ParentCopy M C T A b q qNew := by
  obtain ⟨Z,hZ,hOrd⟩ := Ordinary.copy_exists_d hM hC hT hA hX hLast (hCopy.width ▸ hY.width)
  exact hOrd.row_source_d hM hC hT hA hX hZ
    ((hCopy.high_parents_eq_ordinary_d hM hC hT hA hX hOrd (hCopy.width ▸ hY.width) hHigh).mp hParent)
    ((hCopy.high_roots_eq_ordinary_d hM hC hT hA hX hY hZ hOrd hHigh).mp hRoot)

/-- 给定同一源列/block，非root列或高行的实际原子完整来自该源记录。 -/
theorem Copies.row_source_at_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {A : Context M.Domain} (hA : A.Valid M C) {X Y : Data M.Domain} (hX : X.Valid M C) (hY : Y.Valid M C)
    {m : M.Domain} {R : RowStateSpace M.Domain} {V P H : M.Domain}
    (hRun : RowRun M C m R V P H) (hFrom : FromRun M C m R V H X)
    {level n r b s c pNew qNew : M.Domain} (hActive : Active M X A level) (hCopy : Copies M C T A X level n Y)
    (hSource : M.mem s A.last) (hAllowed : s≠A.root ∨ level=r ∨ M.mem level r)
    (hMap : ParentCopy M C T A b s c) (hParent : ParentAt M Y r c pNew) (hRoot : RootAt M C Y r c qNew) :
    ∃ p q, ParentAt M X r s p ∧ RootAt M C X r s q ∧ ParentCopy M C T A b p pNew ∧ ParentCopy M C T A b q qNew := by
  rcases hAllowed with hNonroot | hHigh
  · exact hCopy.nonroot_row_source_d hM hC hT hA hX hY hRun hFrom hActive hSource hNonroot hMap hParent hRoot
  · have hc := (hParent.bounds hM.1 hY).2.1
    have hCNat := (omega_isOrdinal_d hM hC.omega).transitive Y.width hY.width c hc
    have hOrdP := (parent_high_eq_ordinary_d hM hC hT hA hX hCNat hHigh).mp ((hCopy.parents r c pNew).mp hParent).2
    obtain ⟨p,_,hP,hMapP⟩ := (Ordinary.parent_parent_copy_iff_d hM hC hT hA hX hSource hMap).mp hOrdP
    obtain ⟨q,hQ,hMapQ⟩ := (hCopy.root_parent_copy_iff_d hM hC hT hA hX hY hRun hFrom hActive hSource hc hMap).mp hRoot
    exact ⟨p,q,hP,hQ,hMapP,hMapQ⟩

end KP1Y.OneYFinite.CopiedMountain.Terminal
