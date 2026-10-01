import KP1Y.OneYMatrixCopyForest
import KP1Y.OneYMatrixLiftOrder

/-! 实际复制父图与最右较小值选择的识别。
本模块先从真实坐标证明分块隔离与线性初始父图，再处理实际数值行选择。
-/
namespace KP1Y.OneYFinite.MatrixCopy
open YesMetaZFC YesMetaZFC.SetTheory YesMetaZFC.SetTheory.Definitional
open KP1Y.Kuratowski KP1Y.Functions KP1Y.Naturals KP1Y.Bounded
open KP1Y.OneYFinite KP1Y.Arithmetic
universe u

/-- ParentCopy 在坏部的实际 BM4 局部坐标，包含 root 对应 slot=0。 -/
theorem parent_copy_bad_position_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {X : CopyCoordinates.Context M.Domain} (hX : X.Valid M C) {copy source target : M.Domain}
    (hAfter : X.root=source ∨ M.mem X.root source) (hSource : M.mem source X.last)
    (hMap : CopyCoordinates.ParentCopy M C T X copy source target) :
    ∃ slot, M.mem slot X.length ∧ AddAt M T.addPairs T.plus X.root slot source ∧
      CopyPosition M C.omega T.addPairs T.plus T.mulPairs T.times X.root X.length copy slot target := by
  have hw := omega_isOrdinal_d hM hC.omega
  have hNot : ¬M.mem source X.root := by
    intro hs
    rcases hAfter with he | hlt
    · exact SetTheory.KP.mem_irrefl_d (KP1Y.models_weakKP hM) X.root (he.symm ▸ hs)
    · exact SetTheory.KP.mem_irrefl_d (KP1Y.models_weakKP hM) X.root ((hw.mem hX.root).transitive source hs X.root hlt)
  have hEncode := (CopyCoordinates.parent_copy_bad_iff hNot).mp hMap
  rcases hAfter with he | hlt
  · subst source
    have hAdd := (hT.add.add_iff_sum hM hX.root hC.zero_nat).mpr (sum_zero_d hM X.root hC.zero_empty)
    exact ⟨C.zero,hX.length_positive_d hM hC,hAdd,
      (CopyCoordinates.encode_at_base_iff_d hM hC hT hX.root hC.zero_nat hMap.2.1 hAdd).mp hEncode⟩
  · obtain ⟨slot,hSlot,_,hAdd,hPos⟩ := CopyCoordinates.encode_nonseam_bms_d hM hC hT hX hlt hSource hEncode
    exact ⟨slot,hSlot,hAdd,hPos⟩

/-- 一个副本坏部中的列不在另一个副本的完整 ParentCopy 图像中。 -/
theorem parent_copy_different_copy_disjoint_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {X : CopyCoordinates.Context M.Domain} (hX : X.Valid M C) {copy other source target p : M.Domain}
    (hDifferent : copy≠other) (hAfter : X.root=source ∨ M.mem X.root source) (hSource : M.mem source X.last)
    (hMap : CopyCoordinates.ParentCopy M C T X copy source target) (hp : M.mem p X.last) :
    ¬CopyCoordinates.ParentCopy M C T X other p target := by
  intro hOther
  have hw := omega_isOrdinal_d hM hC.omega
  obtain ⟨slot,hSlot,_,hPos⟩ := parent_copy_bad_position_d hM hC hT hX hAfter hSource hMap
  classical
  by_cases hGood : M.mem p X.root
  · have hEq := (CopyCoordinates.parent_copy_good_iff hOther.2.1 hOther.1 hGood).mp hOther
    exact copy_position_not_good_d hM hC hT hX.root (hw.transitive X.length (hX.length_nat hM.1) slot hSlot) hPos (hEq.symm ▸ hGood)
  · have hAfterP : X.root=p ∨ M.mem X.root p := by
      rcases hw.wellOrder.linear.compare X.root hX.root p hOther.1 with he | hlt | hgt
      · exact Or.inl (hM.1.eq_of_same_members X.root p he)
      · exact Or.inr hlt
      · exact False.elim (hGood hgt)
    obtain ⟨slot',hSlot',_,hPos'⟩ := parent_copy_bad_position_d hM hC hT hX hAfterP hp hOther
    exact hDifferent (copy_position_injective_d hM hC hT.add hT.mul hX.root (hX.length_nat hM.1)
      hMap.2.1 hOther.2.1 hSlot hSlot' hPos hPos').1

/-- 实际输出宽度中的每一列，要么为好部，要么有真正的 copy/slot/source 地址。 -/
theorem CopyForest.column_cases_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {X : CopyCoordinates.Context M.Domain} (hX : X.Valid M C) {P row maximal count width Q child : M.Domain}
    (hQ : CopyForest M C T X P row maximal count width Q) (hChild : M.mem child width) :
    M.mem child X.root ∨ ∃ copy, M.mem copy count ∧ ∃ slot, M.mem slot X.length ∧ ∃ source,
      M.mem source X.last ∧ AddAt M T.addPairs T.plus X.root slot source ∧
      CopyPosition M C.omega T.addPairs T.plus T.mulPairs T.times X.root X.length copy slot child := by
  classical
  by_cases hGood : M.mem child X.root
  · exact Or.inl hGood
  · have hw := omega_isOrdinal_d hM hC.omega
    have hAfter : X.root=child ∨ M.mem X.root child := by
      rcases hw.wellOrder.linear.compare X.root hX.root child (hw.transitive width hQ.forest.width child hChild) with he | hlt | hgt
      · exact Or.inl (hM.1.eq_of_same_members X.root child he)
      · exact Or.inr hlt
      · exact False.elim (hGood hgt)
    obtain ⟨total,hTotal,hWidth⟩ := hQ.width_geometry
    obtain ⟨copy,hCopy,slot,hSlot,hPos⟩ := copy_interval_coverage_d hM hC hT.add hT.mul hX.root
      (hX.length_nat hM.1) hQ.count_nat hTotal hWidth hChild hAfter
    have hSlotNat := hw.transitive X.length (hX.length_nat hM.1) slot hSlot
    obtain ⟨source,_,hAdd⟩ := hT.add.add_exists_d hM hC hX.root hSlotNat
    have hSource := sum_strict_right_d hM (hw.mem hX.root) ((hT.add.add_iff_sum hM hX.root hSlotNat).mp hAdd)
      (hX.root_add_length_d hM hC) hSlot
    exact Or.inr ⟨copy,hCopy,slot,hSlot,source,hSource,hAdd,hPos⟩

/-- 另一个副本坏部到当前列的祖先必须经过当前副本根。 -/
theorem CopyForest.ancestor_other_copy_iff_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {X : CopyCoordinates.Context M.Domain} (hX : X.Valid M C) {m P row maximal count width Q copy other a x source child z : M.Domain}
    (hP : Forest M C.omega m P) (hQ : CopyForest M C T X P row maximal count width Q)
    (hLast : M.mem X.last m) (hCopy : M.mem copy count) (hDifferent : other≠copy)
    (hAfter : X.root=a ∨ M.mem X.root a) (ha : M.mem a X.last)
    (hAx : CopyCoordinates.ParentCopy M C T X other a x) (hSource : M.mem source X.last)
    (hMap : CopyCoordinates.ParentCopy M C T X copy source child)
    (hRootMap : CopyCoordinates.ParentCopy M C T X copy X.root z) :
    Ancestor M C width Q x child ↔
      Ancestor M C width Q x z ∧ (source=X.root ∨ Ancestor M C m P X.root source) :=
  hQ.ancestor_outside_copy_iff_d hM hC hT hX hP hLast hCopy hSource hMap hRootMap
    (fun _p hp => parent_copy_different_copy_disjoint_d hM hC hT hX hDifferent hAfter ha hAx hp)

private theorem copied_successor_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {X : CopyCoordinates.Context M.Domain} (hX : X.Valid M C) {copy source p child target : M.Domain}
    (hAfter : M.mem X.root source) (hs : M.SuccessorOf source p)
    (hMap : CopyCoordinates.ParentCopy M C T X copy p target)
    (hEncode : CopyCoordinates.Encode M C T X source copy child) : M.SuccessorOf child target := by
  have hw := omega_isOrdinal_d hM hC.omega
  have hNot : ¬M.mem p X.root := by
    intro hpRoot
    rcases (hs X.root).mp hAfter with hRootP | he
    · exact SetTheory.KP.mem_irrefl_d (KP1Y.models_weakKP hM) X.root ((hw.mem hX.root).transitive p hpRoot X.root hRootP)
    · have hpEq := hM.1.eq_of_same_members X.root p he
      exact SetTheory.KP.mem_irrefl_d (KP1Y.models_weakKP hM) X.root (hpEq.symm ▸ hpRoot)
  obtain ⟨hp,hCopy,off,hOff,hTimes,hAdd⟩ := (CopyCoordinates.parent_copy_bad_iff hNot).mp hMap
  obtain ⟨hSource,_,off',_,hTimes',hAdd'⟩ := hEncode
  have hOffEq := hT.mul.mul_unique hM.1 hTimes hTimes'
  subst off'
  exact natural_sum_left_successor_d hM hC hOff hs ((hT.add.add_iff_sum hM hp hOff).mp hAdd)
    ((hT.add.add_iff_sum hM hSource hOff).mp hAdd')

private theorem seam_encode_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {X : CopyCoordinates.Context M.Domain} (hX : X.Valid M C) {prev next child : M.Domain}
    (hPrev : M.mem prev C.omega) (hs : M.SuccessorOf next prev)
    (hPos : CopyPosition M C.omega T.addPairs T.plus T.mulPairs T.times X.root X.length next C.zero child) :
    CopyCoordinates.Encode M C T X X.last prev child := by
  obtain ⟨off,hOff,hTimes⟩ := hT.mul.mul_exists_d hM hC hPrev (hX.length_nat hM.1)
  rcases (CopyCoordinates.seam_bms_shift_iff_d hM hC hT hX hPrev hs hOff hTimes).mp hPos with ⟨hBad,_⟩ | ⟨_,hAdd⟩
  · exact False.elim (SetTheory.KP.mem_irrefl_d (KP1Y.models_weakKP hM) X.root
      (((omega_isOrdinal_d hM hC.omega).mem hX.root).transitive X.last hBad X.root hX.below))
  · exact ⟨hX.last,hPrev,off,hOff,hTimes,hAdd⟩

/-- 复制线性初始森林（接缝采用低行分支）仍是实际线性初始森林。 -/
theorem CopyForest.linear_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {X : CopyCoordinates.Context M.Domain} (hX : X.Valid M C) {m P row maximal count width Q : M.Domain}
    (hP : LinearForest M C.omega m P) (hQ : CopyForest M C T X P row maximal count width Q)
    (hLast : M.mem X.last m) (hLow : M.mem row maximal) : LinearForest M C.omega width Q := by
  have hw := omega_isOrdinal_d hM hC.omega
  have hLastSub := (hw.mem hP.1.width).transitive X.last hLast
  have hRootM := hLastSub X.root hX.below
  have hEdge (child target : M.Domain) (hAt : MemPair M Q child target) : M.SuccessorOf child target := by
    rcases (hQ.parents child target).mp hAt with ⟨_,hParent⟩ | ⟨copy,hCopy,slot,hSlot,source,_,hSource,hPos,hBranch⟩
    · exact ((hP.2 child target).mp hParent).2
    · have hCopyNat := hw.transitive count hQ.count_nat copy hCopy
      have hSlotNat := hw.transitive X.length (hX.length_nat hM.1) slot hSlot
      rcases hBranch with ⟨hSlot0,p,_,hParent,hMap⟩ | ⟨hSlot0,hCase⟩
      · have hAfter := sum_base_mem_d hM (hw.mem hX.root)
          ((hT.add.add_iff_sum hM hX.root hSlotNat).mp hSource) ⟨C.zero,(hC.zero_mem_iff hM hSlotNat).mpr hSlot0⟩
        have hEncode := (CopyCoordinates.encode_at_base_iff_d hM hC hT hX.root hSlotNat hCopyNat hSource).mpr hPos
        exact copied_successor_d hM hC hT hX hAfter ((hP.2 source p).mp hParent).2 hMap hEncode
      · subst slot
        rcases hCase with ⟨hHigh,hParent⟩ | ⟨_,_,prev,hPrev,hs,p,_,hParent,hMap⟩
        · have hCopyZero : copy=C.zero := hHigh.elim id (fun h => False.elim (h hLow))
          subst copy
          have hAdd := (copy_position_zero_iff_d hM hC hT hX.root (hX.length_nat hM.1)).mp hPos
          have hChildRoot := ((hT.add.add_iff_sum hM hX.root hC.zero_nat).mp hAdd).zero_value_d hM hC.zero_empty
          exact hChildRoot.symm ▸ ((hP.2 X.root target).mp hParent).2
        · exact copied_successor_d hM hC hT hX hX.below ((hP.2 X.last p).mp hParent).2 hMap
            (seam_encode_d hM hC hT hX hPrev hs hPos)
  have hHasParent (child : M.Domain) (hChild : M.mem child width) (hNonzero : child≠C.zero) :
      ∃ target, MemPair M Q child target := by
    have hNat := hw.transitive width hQ.forest.width child hChild
    have hPred (s : M.Domain) (hs : M.mem s C.omega) (hNot : s≠C.zero) : ∃ p, M.mem p C.omega ∧ M.SuccessorOf s p := by
      rcases natural_cases hM hC.omega hs with he | hSucc
      · exact False.elim (hNot (hM.1.eq_of_same_members s C.zero (fun t => ⟨fun ht => False.elim (he t ht),fun ht => False.elim (hC.zero_empty t ht)⟩)))
      · exact hSucc
    rcases hQ.column_cases_d hM hC hT hX hChild with hGood | ⟨copy,hCopy,slot,hSlot,source,hSourceBound,hSource,hPos⟩
    · obtain ⟨p,_,hs⟩ := hPred child hNat hNonzero
      have hChildM := (hw.mem hP.1.width).transitive X.root hRootM child hGood
      exact ⟨p,(hQ.good_parent_iff_d hM hC hT hX hGood).mpr ((hP.2 child p).mpr ⟨hChildM,hs⟩)⟩
    · have hCopyNat := hw.transitive count hQ.count_nat copy hCopy
      have hSlotNat := hw.transitive X.length (hX.length_nat hM.1) slot hSlot
      have hSourceNat := hw.transitive X.last hX.last source hSourceBound
      classical
      by_cases hSlotZero : slot=C.zero
      · subst slot
        by_cases hCopyZero : copy=C.zero
        · subst copy
          have hAdd := (copy_position_zero_iff_d hM hC hT hX.root (hX.length_nat hM.1)).mp hPos
          have hChildRoot := ((hT.add.add_iff_sum hM hX.root hC.zero_nat).mp hAdd).zero_value_d hM hC.zero_empty
          obtain ⟨p,_,hs⟩ := hPred X.root hX.root (fun he => hNonzero (hChildRoot.trans he))
          exact ⟨p,(hQ.root_high_parent_iff_d hM hC hT hX hQ.count_nat hCopy (Or.inl rfl) hPos p).mpr
            ((hP.2 X.root p).mpr ⟨hRootM,hs⟩)⟩
        · obtain ⟨prev,hPrev,hs⟩ := hPred copy hCopyNat hCopyZero
          obtain ⟨p,hp,hLastSucc⟩ := hPred X.last hX.last (fun he => hC.zero_empty X.root (he ▸ hX.below))
          have hParent := (hP.2 X.last p).mpr ⟨hLast,hLastSucc⟩
          obtain ⟨J,hJ,hJRows⟩ := CopyCoordinates.parent_copy_graph_exists_d hM hC hT hX hPrev
          obtain ⟨target,_,hMap⟩ := hJ.graph.total p hp
          exact ⟨target,(hQ.root_low_parent_iff_d hM hC hT hX hQ.count_nat hCopy hPrev hs hLow hPos target).mpr
            ⟨p,hLastSucc.predecessor_mem,hParent,(hJRows p target).mp hMap⟩⟩
      · have hAfter := sum_base_mem_d hM (hw.mem hX.root)
          ((hT.add.add_iff_sum hM hX.root hSlotNat).mp hSource) ⟨C.zero,(hC.zero_mem_iff hM hSlotNat).mpr hSlotZero⟩
        obtain ⟨p,hp,hs⟩ := hPred source hSourceNat (fun he => hC.zero_empty X.root (he ▸ hAfter))
        have hpLast := (hw.mem hX.last).transitive source hSourceBound p hs.predecessor_mem
        have hParent := (hP.2 source p).mpr ⟨hLastSub source hSourceBound,hs⟩
        obtain ⟨J,hJ,hJRows⟩ := CopyCoordinates.parent_copy_graph_exists_d hM hC hT hX hCopyNat
        obtain ⟨target,_,hMap⟩ := hJ.graph.total p hp
        exact ⟨target,(hQ.nonroot_parent_iff_d hM hC hT hX hQ.count_nat hCopy hSlot hSlotZero hSourceBound hSource hPos target).mpr
          ⟨p,hpLast,hParent,(hJRows p target).mp hMap⟩⟩
  refine ⟨hQ.forest,fun child target => ⟨fun h => ⟨(hQ.forest.bounds hM.1 h).1,hEdge child target h⟩,?_⟩⟩
  rintro ⟨hChild,hs⟩
  obtain ⟨p,hParent⟩ := hHasParent child hChild (fun he => hC.zero_empty target (he ▸ hs.predecessor_mem))
  have hTargetNat := hw.transitive width hQ.forest.width target ((hw.mem hQ.forest.width).transitive child hChild target hs.predecessor_mem)
  have hEq := Structure.SuccessorOf.predecessor_eq hM.1 (hw.mem hTargetNat) hs (hEdge child p hParent)
  exact hEq.symm ▸ hParent

theorem not_ascending_good_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {m Forests Rows maximal root source r : M.Domain}
    (hRoot : M.mem root C.omega) (hGood : M.mem source root) :
    ¬Ascending M C m Forests Rows maximal root source r := by
  rintro ⟨_,he | ⟨_,_,_,hAnc⟩⟩
  · exact SetTheory.KP.mem_irrefl_d (KP1Y.models_weakKP hM) root (he ▸ hGood)
  · exact SetTheory.KP.mem_irrefl_d (KP1Y.models_weakKP hM) root
      (((omega_isOrdinal_d hM hC.omega).mem hRoot).transitive source hGood root hAnc.1)

/-- 真正输出矩阵按 ParentCopy 读取即为实际 LiftedEntry；好部也包括在内。 -/
theorem _root_.KP1Y.OneYFinite.RawMatrixExpansion.parent_copy_entry_iff_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {A B : FiniteMatrix M.Domain} (hA : A.Valid M C.omega)
    {T : MatrixArithmetic M.Domain} (hT : T.Valid M C) {X : CopyCoordinates.Context M.Domain} (hX : X.Valid M C)
    {Forests Rows maximal index count total : M.Domain}
    (h : RawMatrixExpansion M C A T Forests Rows X.last maximal X.root index count X.length total B)
    (hLast : M.mem X.last A.width) (hIndex : M.mem index C.omega)
    {copy source child r y : M.Domain} (hCopy : M.mem copy count) (hSource : M.mem source X.last)
    (hMap : CopyCoordinates.ParentCopy M C T X copy source child) :
    MatrixEntry M B r child y ↔ LiftedEntry M C A T Forests Rows X.last maximal X.root copy source r y := by
  classical
  by_cases hGood : M.mem source X.root
  · have hEq := (CopyCoordinates.parent_copy_good_iff hMap.2.1 hMap.1 hGood).mp hMap
    subst child
    exact (h.prefix_entry_iff_d hM hC hA hT hLast hX.below hIndex hSource).trans
      (lifted_entry_unascending_iff hM.1 hA (not_ascending_good_d hM hC hX.root hGood)).symm
  · have hAfter : X.root=source ∨ M.mem X.root source := by
      rcases (omega_isOrdinal_d hM hC.omega).wellOrder.linear.compare X.root hX.root source hMap.1 with he | hlt | hgt
      · exact Or.inl (hM.1.eq_of_same_members X.root source he)
      · exact Or.inr hlt
      · exact False.elim (hGood hgt)
    obtain ⟨slot,hSlot,hAdd,hPos⟩ := parent_copy_bad_position_d hM hC hT hX hAfter hSource hMap
    have hCopyLe : copy=index ∨ M.mem copy index := by
      rcases (h.copies copy).mp hCopy with hlt | he
      · exact Or.inr hlt
      · exact Or.inl (hM.1.eq_of_same_members copy index he)
    exact h.copied_entry_iff_d hM hC hA hT hLast hX.below hIndex hCopyLe hSlot hAdd hPos

theorem _root_.KP1Y.OneYFinite.MatrixParentRun.ascending_at_d {M : SetTheory.Structure.{u}} (he : Extensional M) {C : ExpressionData M.Domain}
    {m height Cells Values Forests Rows L r P root maximal source : M.Domain}
    (h : MatrixParentRun M C m height Cells Values Forests Rows L) (hP : MemPair M Rows r P) :
    Ascending M C m Forests Rows maximal root source r ↔ M.mem r maximal ∧ (source=root ∨ Ancestor M C m P root source) := by
  constructor
  · rintro ⟨hr,he | ⟨Q,_,hQ,hAnc⟩⟩
    · exact ⟨hr,Or.inl he⟩
    · exact ⟨hr,Or.inr (h.graph.unique r Q P hQ hP ▸ hAnc)⟩
  · rintro ⟨hr,he | hAnc⟩
    · exact ⟨hr,Or.inl he⟩
    · exact ⟨hr,Or.inr ⟨P,(h.graph.bounds he hP).2,hP,hAnc⟩⟩

/-- 除 root 自身外，实际父边两端的 ascending 标志一致。 -/
theorem _root_.KP1Y.OneYFinite.MatrixParentRun.ascending_parent_iff_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {m height Cells Values Forests Rows L r P root maximal source p : M.Domain}
    (h : MatrixParentRun M C m height Cells Values Forests Rows L) (hP : MemPair M Rows r P)
    (hParent : MemPair M P source p) (hNonroot : source≠root) :
    Ascending M C m Forests Rows maximal root p r ↔ Ascending M C m Forests Rows maximal root source r := by
  rw [h.ascending_at_d hM.1 hP,h.ascending_at_d hM.1 hP]
  constructor
  · rintro ⟨hr,he | hAnc⟩
    · subst p
      exact ⟨hr,Or.inr (ancestor_direct_d hM hC (h.forests r P hP) hParent)⟩
    · exact ⟨hr,Or.inr (ancestor_step_d hM hC (h.forests r P hP) hAnc hParent)⟩
  · rintro ⟨hr,he | hAnc⟩
    · exact False.elim (hNonroot he)
    · obtain ⟨q,hQ,hBefore⟩ := ancestor_parent_cases_d hM hC (h.forests r P hP) hAnc
      have hEq := (h.forests r P hP).unique source q p hQ hParent
      subst q
      exact ⟨hr,hBefore.imp Eq.symm id⟩

/-- 每个真实非root源父边复制后，确实是新数值行的候选父边。
这里只输入上一行已经构造的 CopyForest；并未假定当前行的 Selects 识别。
-/
theorem copied_nonroot_parent_candidate_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {A B : FiniteMatrix M.Domain} (hA : A.Valid M C.omega)
    {T : MatrixArithmetic M.Domain} (hT : T.Valid M C) {X : CopyCoordinates.Context M.Domain} (hX : X.Valid M C)
    {Forests Rows L maximal index count total r P F previous previousMax QF VB copy source p child target : M.Domain}
    (hRun : MatrixParentRun M C A.width A.height A.cells A.values Forests Rows L)
    (hExp : RawMatrixExpansion M C A T Forests Rows X.last maximal X.root index count X.length total B)
    (hLast : M.mem X.last A.width) (hIndex : M.mem index C.omega)
    (hPrev : PreviousMatrixForest M C A.height Forests Rows L r F) (hP : MemPair M Rows r P)
    (hCF : CopyForest M C T X F previous previousMax count B.width QF)
    (hRootLast : M.mem previous previousMax → Ancestor M C A.width F X.root X.last)
    (hVB : MatrixRowValues M C.omega B.width B.cells B.values r VB)
    (hCopy : M.mem copy count) (hSource : M.mem source X.last) (hNonroot : source≠X.root)
    (hParent : MemPair M P source p)
    (hChild : CopyCoordinates.ParentCopy M C T X copy source child)
    (hTarget : CopyCoordinates.ParentCopy M C T X copy p target) :
    ParentCandidate false M C B.width QF VB child target := by
  have hw := omega_isOrdinal_d hM hC.omega
  have hr := (hRun.graph.bounds hM.1 hP).1
  obtain ⟨V,hV⟩ := hRun.values_exist r hr
  have hSel := hRun.selects_previous_d hPrev hP hV
  have hp := (hw.mem hX.last).transitive source hSource p (hSel.forest.left source p hParent)
  have hAncestor := (hCF.ancestor_copy_iff_d hM hC hT hX hSel.inherited hLast hCopy hRootLast hp hSource hTarget hChild).mpr
    (hSel.parent_ancestor hParent)
  obtain ⟨a,_,b,_,hAEntry,hBEntry,hab,_⟩ := hSel.parent_values hParent
  have hChildBound := hCF.copy_value_bound_d hM hC hT hX hCopy hSource hChild
  have hTargetBound := hCF.copy_value_bound_d hM hC hT hX hCopy hp hTarget
  obtain ⟨x,hx,hXEntry⟩ := hVB.graph.total target hTargetBound
  obtain ⟨y,hy,hYEntry⟩ := hVB.graph.total child hChildBound
  have hrB : M.mem r B.height := hExp.height.symm ▸ hr
  have hLiftX := (hExp.parent_copy_entry_iff_d hM hC hA hT hX hLast hIndex hCopy hp hTarget).mp
    ((matrix_row_view_entry_iff_d hM hExp.matrix hrB hVB target x).mp hXEntry)
  have hLiftY := (hExp.parent_copy_entry_iff_d hM hC hA hT hX hLast hIndex hCopy hSource hChild).mp
    ((matrix_row_view_entry_iff_d hM hExp.matrix hrB hVB child y).mp hYEntry)
  have hxy := lifted_values_lt_of_flags_mono_d hM hC hA hT (U := ⟨Forests,Rows,X.last,maximal,X.root,copy⟩)
    ((matrix_row_view_entry_iff_d hM hA hr hV p a).mp hAEntry)
    ((matrix_row_view_entry_iff_d hM hA hr hV source b).mp hBEntry) hab
    (hRun.ascending_parent_iff_d hM hC hP hParent hNonroot).mp hLiftX hLiftY
  exact ⟨hAncestor,x,hx,y,hy,hXEntry,hYEntry,hxy,True.intro⟩

/-- 与严格版本配套的弱数值比较：只要求较小端的 ascending 蕴含较大端。 -/
theorem lifted_values_le_of_flags_mono_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {A : FiniteMatrix M.Domain} (hA : A.Valid M C.omega)
    {T : MatrixArithmetic M.Domain} (hT : T.Valid M C) {U : MatrixLiftParameters M.Domain} {c d r a b x y : M.Domain}
    (hAEntry : MatrixEntry M A r c a) (hBEntry : MatrixEntry M A r d b) (hab : a=b ∨ M.mem a b)
    (hFlags : Ascending M C A.width U.forests U.rows U.maximal U.root c r →
      Ascending M C A.width U.forests U.rows U.maximal U.root d r)
    (hX : LiftedEntry M C A T U.forests U.rows U.last U.maximal U.root U.copy c r x)
    (hY : LiftedEntry M C A T U.forests U.rows U.last U.maximal U.root U.copy d r y) : x=y ∨ M.mem x y := by
  rcases hab with he | hlt
  · subst b
    classical
    by_cases hc : Ascending M C A.width U.forests U.rows U.maximal U.root c r
    · exact Or.inl (lifted_values_equal_of_flags_equal_d hM hA hT hAEntry hBEntry ⟨hFlags,fun _ => hc⟩ hX hY)
    · by_cases hd : Ascending M C A.width U.forests U.rows U.maximal U.root d r
      · have hXa := hA.entry_unique hM.1 ((lifted_entry_unascending_iff hM.1 hA hc).mp hX) hAEntry
        subst x
        obtain ⟨b,hb,hEntry,hCase⟩ := hY
        have hba := hA.entry_unique hM.1 hEntry hBEntry
        subst b
        rcases hCase with ⟨_,_,_,t,ht,_,_,hPlus⟩ | ⟨hNot,_⟩
        · have hw := omega_isOrdinal_d hM hC.omega
          have hSum := (hT.add.add_iff_sum hM hb ht).mp hPlus
          exact ordinal_subset_cases_d hM (hw.mem hb) (hw.mem (hPlus.bounds hM.1 hT.add).2.2)
            (sum_base_subset_d hM (hw.mem hb) hSum)
        · exact False.elim (hNot hd)
      · exact Or.inl (lifted_values_equal_of_flags_equal_d hM hA hT hAEntry hBEntry (iff_of_false hc hd) hX hY)
  · exact Or.inr (lifted_values_lt_of_flags_mono_d hM hC hA hT hAEntry hBEntry hlt hFlags hX hY)

theorem _root_.KP1Y.OneYFinite.MatrixParentRun.ascending_after_parent_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {m height Cells Values Forests Rows L r P F root maximal source p q : M.Domain}
    (h : MatrixParentRun M C m height Cells Values Forests Rows L)
    (hPrev : PreviousMatrixForest M C height Forests Rows L r F) (hP : MemPair M Rows r P)
    (hParent : MemPair M P source p) (hQ : Ancestor M C m F q source) (hpq : M.mem p q) (hNonroot : source≠root) :
    Ascending M C m Forests Rows maximal root source r → Ascending M C m Forests Rows maximal root q r := by
  intro hAsc
  have hr := (h.graph.bounds hM.1 hP).1
  obtain ⟨V,hV⟩ := h.values_exist r hr
  have hPQ := (h.selects_previous_d hPrev hP hV).ancestor_of_between_d hM hC hParent hQ hpq
  obtain ⟨hLow,he | hRootP⟩ := (h.ascending_at_d hM.1 hP).mp ((h.ascending_parent_iff_d hM hC hP hParent hNonroot).mpr hAsc)
  · subst p
    exact (h.ascending_at_d hM.1 hP).mpr ⟨hLow,Or.inr hPQ⟩
  · exact (h.ascending_at_d hM.1 hP).mpr ⟨hLow,Or.inr (ancestor_trans_d hM hC (h.forests r P hP) hRootP hPQ)⟩

/-- 同副本中，位于源父项之后的旧候选列，其提升值仍不小于子列。 -/
theorem lifted_entry_ge_after_parent_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {A : FiniteMatrix M.Domain} (hA : A.Valid M C.omega)
    {T : MatrixArithmetic M.Domain} (hT : T.Valid M C) {U : MatrixLiftParameters M.Domain}
    {L r P F source p q x y : M.Domain}
    (hRun : MatrixParentRun M C A.width A.height A.cells A.values U.forests U.rows L)
    (hPrev : PreviousMatrixForest M C A.height U.forests U.rows L r F) (hP : MemPair M U.rows r P)
    (hParent : MemPair M P source p) (hQ : Ancestor M C A.width F q source) (hpq : M.mem p q)
    (hNonroot : source≠U.root)
    (hX : LiftedEntry M C A T U.forests U.rows U.last U.maximal U.root U.copy source r x)
    (hY : LiftedEntry M C A T U.forests U.rows U.last U.maximal U.root U.copy q r y) : x=y ∨ M.mem x y := by
  have hr := (hRun.graph.bounds hM.1 hP).1
  obtain ⟨V,hV⟩ := hRun.values_exist r hr
  have hSel := hRun.selects_previous_d hPrev hP hV
  obtain ⟨a,_,hAEntry⟩ := hV.graph.total source (hSel.forest.bounds hM.1 hParent).1
  obtain ⟨b,_,hBEntry⟩ := hV.graph.total q (hQ.bounds hM.1).1
  exact lifted_values_le_of_flags_mono_d hM hC hA hT
    ((matrix_row_view_entry_iff_d hM hA hr hV source a).mp hAEntry)
    ((matrix_row_view_entry_iff_d hM hA hr hV q b).mp hBEntry)
    (hSel.value_ge_after_parent_d hM hC hParent hQ hpq hAEntry hBEntry)
    (hRun.ascending_after_parent_d hM hC hPrev hP hParent hQ hpq hNonroot) hX hY

/-- 新行的同副本候选，其源编号不可能位于原父项之后。 -/
theorem copied_candidate_source_le_parent_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {A B : FiniteMatrix M.Domain} (hA : A.Valid M C.omega)
    {T : MatrixArithmetic M.Domain} (hT : T.Valid M C) {X : CopyCoordinates.Context M.Domain} (hX : X.Valid M C)
    {Forests Rows L maximal index count total r P F previous previousMax QF VB copy source p q child target : M.Domain}
    (hRun : MatrixParentRun M C A.width A.height A.cells A.values Forests Rows L)
    (hExp : RawMatrixExpansion M C A T Forests Rows X.last maximal X.root index count X.length total B)
    (hLast : M.mem X.last A.width) (hIndex : M.mem index C.omega)
    (hPrev : PreviousMatrixForest M C A.height Forests Rows L r F) (hP : MemPair M Rows r P)
    (hCF : CopyForest M C T X F previous previousMax count B.width QF)
    (hRootLast : M.mem previous previousMax → Ancestor M C A.width F X.root X.last)
    (hVB : MatrixRowValues M C.omega B.width B.cells B.values r VB)
    (hCopy : M.mem copy count) (hSource : M.mem source X.last) (hNonroot : source≠X.root)
    (hParent : MemPair M P source p) (hq : M.mem q X.last)
    (hChild : CopyCoordinates.ParentCopy M C T X copy source child)
    (hTarget : CopyCoordinates.ParentCopy M C T X copy q target)
    (hCandidate : ParentCandidate false M C B.width QF VB child target) : q=p ∨ M.mem q p := by
  have hw := omega_isOrdinal_d hM hC.omega
  have hr := (hRun.graph.bounds hM.1 hP).1
  obtain ⟨V,hV⟩ := hRun.values_exist r hr
  have hSel := hRun.selects_previous_d hPrev hP hV
  have hpNat := hw.transitive A.width hA.width p (hSel.forest.bounds hM.1 hParent).2
  have hqNat := hw.transitive X.last hX.last q hq
  rcases hw.wellOrder.linear.compare q hqNat p hpNat with he | hlt | hgt
  · exact Or.inl (hM.1.eq_of_same_members q p he)
  · exact Or.inr hlt
  · have hOldAncestor := (hCF.ancestor_copy_iff_d hM hC hT hX hSel.inherited hLast hCopy hRootLast hq hSource hTarget hChild).mp hCandidate.1
    obtain ⟨x,hx,y,hy,hXEntry,hYEntry,hxy,_⟩ := hCandidate.2
    have hrB : M.mem r B.height := hExp.height.symm ▸ hr
    have hLiftX := (hExp.parent_copy_entry_iff_d hM hC hA hT hX hLast hIndex hCopy hq hTarget).mp
      ((matrix_row_view_entry_iff_d hM hExp.matrix hrB hVB target x).mp hXEntry)
    have hLiftY := (hExp.parent_copy_entry_iff_d hM hC hA hT hX hLast hIndex hCopy hSource hChild).mp
      ((matrix_row_view_entry_iff_d hM hExp.matrix hrB hVB child y).mp hYEntry)
    have hYX := lifted_entry_ge_after_parent_d hM hC hA hT (U := ⟨Forests,Rows,X.last,maximal,X.root,copy⟩)
      hRun hPrev hP hParent hOldAncestor hgt hNonroot hLiftY hLiftX
    rcases hYX with he | hyx
    · exact False.elim (SetTheory.KP.mem_irrefl_d (KP1Y.models_weakKP hM) x (he ▸ hxy))
    · exact False.elim (hw.wellOrder.linear.irrefl x hx (hw.wellOrder.linear.trans x hx y hy x hx hxy hyx))

/-- 非root源列有坏部父项时，复制父项确实满足完整的最右候选条件。 -/
theorem copied_nonroot_bad_parent_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {A B : FiniteMatrix M.Domain} (hA : A.Valid M C.omega)
    {T : MatrixArithmetic M.Domain} (hT : T.Valid M C) {X : CopyCoordinates.Context M.Domain} (hX : X.Valid M C)
    {Forests Rows L maximal index count total r P F previous previousMax QF VB copy source p child target : M.Domain}
    (hRun : MatrixParentRun M C A.width A.height A.cells A.values Forests Rows L)
    (hExp : RawMatrixExpansion M C A T Forests Rows X.last maximal X.root index count X.length total B)
    (hLast : M.mem X.last A.width) (hIndex : M.mem index C.omega)
    (hPrev : PreviousMatrixForest M C A.height Forests Rows L r F) (hP : MemPair M Rows r P)
    (hCF : CopyForest M C T X F previous previousMax count B.width QF)
    (hRootLast : M.mem previous previousMax → Ancestor M C A.width F X.root X.last)
    (hVB : MatrixRowValues M C.omega B.width B.cells B.values r VB)
    (hCopy : M.mem copy count) (hSource : M.mem source X.last) (hNonroot : source≠X.root)
    (hParent : MemPair M P source p) (hBadParent : X.root=p ∨ M.mem X.root p)
    (hChild : CopyCoordinates.ParentCopy M C T X copy source child)
    (hTarget : CopyCoordinates.ParentCopy M C T X copy p target) :
    RestrictedParent false M C B.width QF VB child target := by
  have hCandidate := copied_nonroot_parent_candidate_d hM hC hA hT hX hRun hExp hLast hIndex hPrev hP hCF hRootLast
    hVB hCopy hSource hNonroot hParent hChild hTarget
  refine ⟨hCandidate,?_⟩
  intro t _ hNewCandidate
  have hw := omega_isOrdinal_d hM hC.omega
  have hr := (hRun.graph.bounds hM.1 hP).1
  obtain ⟨V,hV⟩ := hRun.values_exist r hr
  have hSel := hRun.selects_previous_d hPrev hP hV
  have hp := (hw.mem hX.last).transitive source hSource p (hSel.forest.left source p hParent)
  obtain ⟨J,hJ,hJRows⟩ := hCF.copy_embedding_d hM hC hT hX hCopy
  obtain ⟨z,_,hJRoot⟩ := hJ.graph.total X.root hX.below
  have hRootMap := ((hJRows X.root z).mp hJRoot).2
  have hJTarget := (hJRows p target).mpr ⟨hp,hTarget⟩
  have hRootBefore : z=target ∨ M.mem z target := by
    rcases hBadParent with he | hlt
    · subst p
      exact Or.inl (hJ.graph.unique X.root z target hJRoot hJTarget)
    · exact Or.inr (hJ.strict X.root hX.below p hp hlt z target hJRoot hJTarget)
  rcases hCF.ancestor_origin_or_root_d hM hC hT hX hSel.inherited hLast hCopy hSource hChild hRootMap hNewCandidate.1 with
      ⟨q,hq,hMapQ,_⟩ | ⟨hToRoot,_⟩
  · have hBound := copied_candidate_source_le_parent_d hM hC hA hT hX hRun hExp hLast hIndex hPrev hP hCF hRootLast
      hVB hCopy hSource hNonroot hParent hq hChild hMapQ hNewCandidate
    have hJQ := (hJRows q t).mpr ⟨hq,hMapQ⟩
    rcases hBound with he | hlt
    · subst q
      exact Or.inl (hJ.graph.unique p t target hJQ hJTarget)
    · exact Or.inr (hJ.strict q hq p hp hlt t target hJQ hJTarget)
  · have hToRootLe : t=z ∨ M.mem t z := hToRoot.imp id (fun h => h.1)
    rcases hToRootLe with he | hlt <;> rcases hRootBefore with he' | hlt'
    · exact Or.inl (he.trans he')
    · exact Or.inr (he.symm ▸ hlt')
    · exact Or.inr (he' ▸ hlt)
    · have hTargetNat := hw.transitive B.width hExp.matrix.width target (hCandidate.1.bounds hM.1).1
      exact Or.inr ((hw.mem hTargetNat).transitive z hlt' t hlt)

/-- 上述完整候选证明由实际 Selects 的字面行定义消费，给真实新父边。 -/
theorem copied_nonroot_bad_parent_selected_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {A B : FiniteMatrix M.Domain} (hA : A.Valid M C.omega)
    {T : MatrixArithmetic M.Domain} (hT : T.Valid M C) {X : CopyCoordinates.Context M.Domain} (hX : X.Valid M C)
    {Forests Rows L maximal index count total r P F previous previousMax QF VB Q copy source p child target : M.Domain}
    (hRun : MatrixParentRun M C A.width A.height A.cells A.values Forests Rows L)
    (hExp : RawMatrixExpansion M C A T Forests Rows X.last maximal X.root index count X.length total B)
    (hLast : M.mem X.last A.width) (hIndex : M.mem index C.omega)
    (hPrev : PreviousMatrixForest M C A.height Forests Rows L r F) (hP : MemPair M Rows r P)
    (hCF : CopyForest M C T X F previous previousMax count B.width QF)
    (hRootLast : M.mem previous previousMax → Ancestor M C A.width F X.root X.last)
    (hVB : MatrixRowValues M C.omega B.width B.cells B.values r VB)
    (hSel : Selects false M C B.width QF VB Q)
    (hCopy : M.mem copy count) (hSource : M.mem source X.last) (hNonroot : source≠X.root)
    (hParent : MemPair M P source p) (hBadParent : X.root=p ∨ M.mem X.root p)
    (hChild : CopyCoordinates.ParentCopy M C T X copy source child)
    (hTarget : CopyCoordinates.ParentCopy M C T X copy p target) : MemPair M Q child target :=
  (hSel.parents child target).mpr (copied_nonroot_bad_parent_d hM hC hA hT hX hRun hExp hLast hIndex hPrev hP hCF hRootLast
    hVB hCopy hSource hNonroot hParent hBadParent hChild hTarget)

theorem CopyForest.high_root_ancestors_good_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {X : CopyCoordinates.Context M.Domain} (hX : X.Valid M C) {m P row maximal count width Q copy z x : M.Domain}
    (hP : Forest M C.omega m P) (hQ : CopyForest M C T X P row maximal count width Q)
    (hCopy : M.mem copy count) (hHigh : ¬M.mem row maximal)
    (hRoot : CopyCoordinates.ParentCopy M C T X copy X.root z) (hAnc : Ancestor M C width Q x z) : M.mem x X.root := by
  have hw := omega_isOrdinal_d hM hC.omega
  obtain ⟨t,hParent,hBefore⟩ := ancestor_parent_cases_d hM hC hQ.forest hAnc
  obtain ⟨p,hp,hOld,hMap⟩ := (hQ.source_parent_high_d hM hC hT hX hP hQ.count_nat hCopy hX.below hHigh hRoot t).mp hParent
  have hpRoot := hP.left X.root p hOld
  have hTarget := (CopyCoordinates.parent_copy_good_iff hMap.2.1 hMap.1 hpRoot).mp hMap
  subst t
  rcases hBefore with he | hBefore
  · exact he.symm ▸ hpRoot
  · exact (hw.mem hX.root).transitive p hpRoot x hBefore.1

/-- 高行中任意祖先都有同副本源，而不仅限于事先给出源的祖先。 -/
theorem CopyForest.ancestor_high_origin_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {X : CopyCoordinates.Context M.Domain} (hX : X.Valid M C) {m P row maximal count width Q copy source child x : M.Domain}
    (hP : Forest M C.omega m P) (hQ : CopyForest M C T X P row maximal count width Q)
    (hLast : M.mem X.last m) (hCopy : M.mem copy count) (hHigh : ¬M.mem row maximal) (hSource : M.mem source X.last)
    (hMap : CopyCoordinates.ParentCopy M C T X copy source child) (hAnc : Ancestor M C width Q x child) :
    ∃ a, M.mem a X.last ∧ CopyCoordinates.ParentCopy M C T X copy a x ∧ Ancestor M C m P a source := by
  obtain ⟨J,hJ,hJRows⟩ := hQ.copy_embedding_d hM hC hT hX hCopy
  obtain ⟨z,_,hRoot⟩ := hJ.graph.total X.root hX.below
  have hRootMap := ((hJRows X.root z).mp hRoot).2
  rcases hQ.ancestor_origin_or_root_d hM hC hT hX hP hLast hCopy hSource hMap hRootMap hAnc with hOrigin | ⟨hToRoot,_⟩
  · exact hOrigin
  · rcases hToRoot with he | hToRoot
    · subst x
      exact ⟨X.root,hX.below,hRootMap,(hQ.ancestor_high_iff_d hM hC hT hX hP hLast hCopy hHigh hX.below hSource hRootMap hMap).mp hAnc⟩
    · have hw := omega_isOrdinal_d hM hC.omega
      have hGood := hQ.high_root_ancestors_good_d hM hC hT hX hP hCopy hHigh hRootMap hToRoot
      have hx := (hw.mem hX.last).transitive X.root hX.below x hGood
      have hImage : CopyCoordinates.ParentCopy M C T X copy x x :=
        (CopyCoordinates.parent_copy_good_iff (hw.transitive count hQ.count_nat copy hCopy) (hw.transitive X.last hX.last x hx) hGood).mpr rfl
      exact ⟨x,hx,hImage,(hQ.ancestor_high_iff_d hM hC hT hX hP hLast hCopy hHigh hx hSource hImage hMap).mp hAnc⟩

/-- 当前行不提升、前行副本不跨接缝时，候选关系由实际矩阵读值完全对应。 -/
theorem high_candidate_iff_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {A B : FiniteMatrix M.Domain} (hA : A.Valid M C.omega)
    {T : MatrixArithmetic M.Domain} (hT : T.Valid M C) {X : CopyCoordinates.Context M.Domain} (hX : X.Valid M C)
    {Forests Rows maximal index count total r F previous previousMax QF V VB copy source p child target : M.Domain}
    (hExp : RawMatrixExpansion M C A T Forests Rows X.last maximal X.root index count X.length total B)
    (hLast : M.mem X.last A.width) (hIndex : M.mem index C.omega) (hr : M.mem r A.height)
    (hF : Forest M C.omega A.width F) (hCF : CopyForest M C T X F previous previousMax count B.width QF)
    (hPreviousHigh : ¬M.mem previous previousMax) (hHigh : ¬M.mem r maximal)
    (hV : MatrixRowValues M C.omega A.width A.cells A.values r V)
    (hVB : MatrixRowValues M C.omega B.width B.cells B.values r VB)
    (hCopy : M.mem copy count) (hSource : M.mem source X.last) (hp : M.mem p X.last)
    (hChild : CopyCoordinates.ParentCopy M C T X copy source child)
    (hTarget : CopyCoordinates.ParentCopy M C T X copy p target) :
    ParentCandidate false M C B.width QF VB child target ↔ ParentCandidate false M C A.width F V source p := by
  have hrB : M.mem r B.height := hExp.height.symm ▸ hr
  have hAnc := hCF.ancestor_high_iff_d hM hC hT hX hF hLast hCopy hPreviousHigh hp hSource hTarget hChild
  have hEntry (s t : M.Domain) (hs : M.mem s X.last) (hMap : CopyCoordinates.ParentCopy M C T X copy s t) (y : M.Domain) :
      MemPair M VB t y ↔ MemPair M V s y := by
    apply (matrix_row_view_entry_iff_d hM hExp.matrix hrB hVB t y).trans
    apply (hExp.parent_copy_entry_iff_d hM hC hA hT hX hLast hIndex hCopy hs hMap).trans
    apply (lifted_entry_unascending_iff hM.1 hA (fun h => hHigh h.1)).trans
    exact (matrix_row_view_entry_iff_d hM hA hr hV s y).symm
  constructor
  · rintro ⟨hA,x,hx,y,hy,hX,hY,hxy,hPos⟩
    exact ⟨hAnc.mp hA,x,hx,y,hy,(hEntry p target hp hTarget x).mp hX,(hEntry source child hSource hChild y).mp hY,hxy,hPos⟩
  · rintro ⟨hA,x,hx,y,hy,hX,hY,hxy,hPos⟩
    exact ⟨hAnc.mpr hA,x,hx,y,hy,(hEntry p target hp hTarget x).mpr hX,(hEntry source child hSource hChild y).mpr hY,hxy,hPos⟩

/-- 高行的源父项在复制后满足真实最右选择，包括root源列。 -/
theorem high_restricted_parent_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {A B : FiniteMatrix M.Domain} (hA : A.Valid M C.omega)
    {T : MatrixArithmetic M.Domain} (hT : T.Valid M C) {X : CopyCoordinates.Context M.Domain} (hX : X.Valid M C)
    {Forests Rows maximal index count total r F P previous previousMax QF V VB copy source p child target : M.Domain}
    (hExp : RawMatrixExpansion M C A T Forests Rows X.last maximal X.root index count X.length total B)
    (hLast : M.mem X.last A.width) (hIndex : M.mem index C.omega) (hr : M.mem r A.height)
    (hSel : Selects false M C A.width F V P) (hCF : CopyForest M C T X F previous previousMax count B.width QF)
    (hPreviousHigh : ¬M.mem previous previousMax) (hHigh : ¬M.mem r maximal)
    (hV : MatrixRowValues M C.omega A.width A.cells A.values r V)
    (hVB : MatrixRowValues M C.omega B.width B.cells B.values r VB)
    (hCopy : M.mem copy count) (hSource : M.mem source X.last) (hParent : MemPair M P source p)
    (hChild : CopyCoordinates.ParentCopy M C T X copy source child)
    (hTarget : CopyCoordinates.ParentCopy M C T X copy p target) :
    RestrictedParent false M C B.width QF VB child target := by
  have hw := omega_isOrdinal_d hM hC.omega
  have hp := (hw.mem hX.last).transitive source hSource p (hSel.forest.left source p hParent)
  have hOld := (hSel.parents source p).mp hParent
  refine ⟨(high_candidate_iff_d hM hC hA hT hX hExp hLast hIndex hr hSel.inherited hCF hPreviousHigh hHigh
    hV hVB hCopy hSource hp hChild hTarget).mpr hOld.1,?_⟩
  intro t _ hCandidate
  obtain ⟨q,hq,hMapQ,hAncestor⟩ := hCF.ancestor_high_origin_d hM hC hT hX hSel.inherited hLast hCopy hPreviousHigh hSource hChild hCandidate.1
  have hOldCandidate := (high_candidate_iff_d hM hC hA hT hX hExp hLast hIndex hr hSel.inherited hCF hPreviousHigh hHigh
    hV hVB hCopy hSource hq hChild hMapQ).mp hCandidate
  have hLe := hOld.2 q hAncestor.1 hOldCandidate
  obtain ⟨J,hJ,hRows⟩ := hCF.copy_embedding_d hM hC hT hX hCopy
  have hJQ := (hRows q t).mpr ⟨hq,hMapQ⟩
  have hJP := (hRows p target).mpr ⟨hp,hTarget⟩
  rcases hLe with he | hlt
  · subst q
    exact Or.inl (hJ.graph.unique p t target hJQ hJP)
  · exact Or.inr (hJ.strict q hq p hp hlt t target hJQ hJP)

/-- 高行的实际新父图逐行精确对应源父图；含无父情形，未给目标父等式作为假设。 -/
theorem high_selected_parent_iff_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {A B : FiniteMatrix M.Domain} (hA : A.Valid M C.omega)
    {T : MatrixArithmetic M.Domain} (hT : T.Valid M C) {X : CopyCoordinates.Context M.Domain} (hX : X.Valid M C)
    {Forests Rows maximal index count total r F P previous previousMax QF V VB Q copy source child : M.Domain}
    (hExp : RawMatrixExpansion M C A T Forests Rows X.last maximal X.root index count X.length total B)
    (hLast : M.mem X.last A.width) (hIndex : M.mem index C.omega) (hr : M.mem r A.height)
    (hSel : Selects false M C A.width F V P) (hCF : CopyForest M C T X F previous previousMax count B.width QF)
    (hPreviousHigh : ¬M.mem previous previousMax) (hHigh : ¬M.mem r maximal)
    (hV : MatrixRowValues M C.omega A.width A.cells A.values r V)
    (hVB : MatrixRowValues M C.omega B.width B.cells B.values r VB)
    (hNew : Selects false M C B.width QF VB Q)
    (hCopy : M.mem copy count) (hSource : M.mem source X.last)
    (hChild : CopyCoordinates.ParentCopy M C T X copy source child) :
    ∀ target, MemPair M Q child target ↔ ∃ p, M.mem p X.last ∧ MemPair M P source p ∧ CopyCoordinates.ParentCopy M C T X copy p target := by
  intro target
  constructor
  · intro hParent
    have hCandidate := ((hNew.parents child target).mp hParent).1
    obtain ⟨q,hq,hMapQ,_⟩ := hCF.ancestor_high_origin_d hM hC hT hX hSel.inherited hLast hCopy hPreviousHigh hSource hChild hCandidate.1
    have hOldCandidate := (high_candidate_iff_d hM hC hA hT hX hExp hLast hIndex hr hSel.inherited hCF hPreviousHigh hHigh
      hV hVB hCopy hSource hq hChild hMapQ).mp hCandidate
    obtain ⟨p,hChosen⟩ := restricted_parent_exists_d hM false hC hSel.inherited ⟨q,hOldCandidate⟩
    have hOldParent := (hSel.parents source p).mpr hChosen
    have hp := ((omega_isOrdinal_d hM hC.omega).mem hX.last).transitive source hSource p (hSel.forest.left source p hOldParent)
    obtain ⟨J,hJ,hRows⟩ := hCF.copy_embedding_d hM hC hT hX hCopy
    obtain ⟨t,_,hMap⟩ := hJ.graph.total p hp
    have hCopyP := ((hRows p t).mp hMap).2
    have hNewParent := (hNew.parents child t).mpr (high_restricted_parent_d hM hC hA hT hX hExp hLast hIndex hr hSel hCF hPreviousHigh hHigh
      hV hVB hCopy hSource hOldParent hChild hCopyP)
    have hEq := hNew.forest.unique child t target hNewParent hParent
    exact ⟨p,hp,hOldParent,hEq ▸ hCopyP⟩
  · rintro ⟨p,_,hParent,hMap⟩
    exact (hNew.parents child target).mpr (high_restricted_parent_d hM hC hA hT hX hExp hLast hIndex hr hSel hCF hPreviousHigh hHigh
      hV hVB hCopy hSource hParent hChild hMap)

end KP1Y.OneYFinite.MatrixCopy
