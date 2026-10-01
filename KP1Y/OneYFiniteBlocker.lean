import KP1Y.OneYMatrixStructuralDefs
import KP1Y.OneYMatrixExpansionFacts
import KP1Y.OneYMatrixCopyRun
import KP1Y.OneYMatrixGhostColumn
import KP1Y.OneYMatrixDepthExpansion

/-! 任意内部有限矩阵的列后缀次序、逐行阻挡条件及其前缀保持。
帧行不被要求满足 S；相对条件只约束给定边界以上的实际行。
-/
namespace KP1Y.OneYFinite
open YesMetaZFC YesMetaZFC.SetTheory YesMetaZFC.SetTheory.Definitional
open KP1Y.Kuratowski KP1Y.Functions KP1Y.Naturals KP1Y.Bounded
universe u

/-- 阻挡条件在实际列前缀下保持。父链和数值对应均为可由前缀构造证明的明确输入。 -/
theorem row_blocker_prefix_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {A B : FiniteMatrix M.Domain}
    (hB : B.Valid M C.omega) (hHeight : B.height=A.height) (hSub : M.MemberSubset B.width A.width)
    {Prev Cur Prev' Cur' start : M.Domain} (hCur : Forest M C.omega A.width Cur)
    (hPrevRows : RowsAgreeOn M Prev Prev' B.width) (hCurRows : RowsAgreeOn M Cur Cur' B.width)
    (hEntries : ∀ r c d, M.mem c B.width → (MatrixEntry M B r c d ↔ MatrixEntry M A r c d))
    (hS : RowBlocker M C A Prev Cur start) : RowBlocker M C B Prev' Cur' start := by
  intro c hc q hq p hp hPrevAt hCurAt hNe
  have hPrevOld := (hPrevRows c hc q).mpr hPrevAt
  have hCurOld := (hCurRows c hc p).mpr hCurAt
  obtain ⟨z,_,hPath,hZp,hLe⟩ := hS c (hSub c hc) q (hSub q hq) p (hSub p hp) hPrevOld hCurOld hNe
  have hz : M.mem z B.width := by
    rcases hPath with he | hAnc
    · exact he ▸ hq
    · exact ((omega_isOrdinal_d hM hC.omega).mem hB.width).transitive q hq z hAnc.1
  refine ⟨z,hz,?_,(hCurRows z hz p).mp hZp,?_⟩
  · exact hPath.imp id ((ancestor_prefix_iff_d hM hC hCur hB.width hSub hq hCurRows).mp)
  · apply (column_le_from_congr
      (fun r d => (padded_entry_prefix_iff hHeight hSub hEntries hc).symm)
      (fun r d => (padded_entry_prefix_iff hHeight hSub hEntries hz).symm)).mp hLe

/-- 实际构造矩阵前缀和两张父图前缀，得到新行的 S；没有把新 S 假定为输入。 -/
theorem row_blocker_prefix_exists_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {A : FiniteMatrix M.Domain} (hA : A.Valid M C.omega)
    {Prev Cur n start : M.Domain} (hPrev : Forest M C.omega A.width Prev) (hCur : Forest M C.omega A.width Cur)
    (hn : M.mem n C.omega) (hSub : M.MemberSubset n A.width) (hS : RowBlocker M C A Prev Cur start) :
    ∃ B Prev' Cur', B.Valid M C.omega ∧ B.height=A.height ∧ B.width=n ∧
      Forest M C.omega n Prev' ∧ Forest M C.omega n Cur' ∧ RowBlocker M C B Prev' Cur' start := by
  obtain ⟨B,hB,hHeight,hWidth,hEntries⟩ := hA.prefix_exists_d hM hn hSub
  obtain ⟨Prev',hPrev',hPrevRows⟩ := hPrev.restrict_d hM hC.omega hn
  obtain ⟨Cur',hCur',hCurRows⟩ := hCur.restrict_d hM hC.omega hn
  have hSub' : M.MemberSubset B.width A.width := hWidth ▸ hSub
  have hPrevRows' : RowsAgreeOn M Prev Prev' B.width := hWidth ▸ hPrevRows
  have hCurRows' : RowsAgreeOn M Cur Cur' B.width := hWidth ▸ hCurRows
  have hEntries' : ∀ r c d, M.mem c B.width → (MatrixEntry M B r c d ↔ MatrixEntry M A r c d) :=
    fun r c d hc => hEntries r c d (hWidth ▸ hc)
  exact ⟨B,Prev',Cur',hB,hHeight,hWidth,hPrev',hCur',
    row_blocker_prefix_d hM hC hB hHeight hSub' hCur hPrevRows' hCurRows' hEntries' hS⟩

/-- 某源列在该后缀上没有 ascending 格时，其真实复制列后缀完全相同。 -/
theorem RawMatrixExpansion.copied_suffix_unchanged_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {A B : FiniteMatrix M.Domain} (hA : A.Valid M C.omega)
    {T : MatrixArithmetic M.Domain} (hT : T.Valid M C) {Forests Rows last maximal root index count L total : M.Domain}
    (h : RawMatrixExpansion M C A T Forests Rows last maximal root index count L total B)
    (hLast : M.mem last A.width) (hRootLast : M.mem root last) (hIndex : M.mem index C.omega)
    {copy slot source c start : M.Domain} (hCopy : copy=index ∨ M.mem copy index) (hSlot : M.mem slot L)
    (hSource : AddAt M T.addPairs T.plus root slot source)
    (hPos : CopyPosition M C.omega T.addPairs T.plus T.mulPairs T.times root L copy slot c)
    (hNoAsc : ∀ r, M.mem r C.omega → start=r ∨ M.mem start r → ¬Ascending M C A.width Forests Rows maximal root source r) :
    ColumnEqFrom M C.omega C.zero B A c source start := by
  have hw := omega_isOrdinal_d hM hC.omega
  have hL := truncated_difference_natural hM.1 h.difference
  have hCountNat := natural_successor_mem_d hM hC hIndex h.copies
  have hCopyCount : M.mem copy count := by
    rcases hCopy with he | hci
    · exact he ▸ h.copies.predecessor_mem
    · exact (h.copies copy).mpr (Or.inl hci)
  have hCWidth := copy_position_bounded_d hM hC hT.add hT.mul h.difference.2.1 hL hCountNat h.product h.width hCopyCount hSlot hPos
  have hSourceLast := KP1Y.Arithmetic.sum_strict_right_d hM (hw.mem h.difference.2.1)
    ((hT.add.add_iff_sum hM h.difference.2.1 (hw.transitive L hL slot hSlot)).mp hSource)
    (truncated_difference_add_inverse_d hM hC h.difference (Or.inr hRootLast)) hSlot
  have hSourceWidth := (hw.mem hA.width).transitive last hLast source hSourceLast
  intro r hr hs x _ y _ hX hY
  have hEntries := fun z => h.copied_unascending_iff_d hM hC hA hT hLast hRootLast hIndex hCopy hSlot hSource hPos (y := z) (hNoAsc r hr hs)
  have hPads : PaddedEntry M C.zero B r c x ↔ PaddedEntry M C.zero A r source x := by
    simp only [PaddedEntry,h.height,hCWidth,hSourceWidth,not_true_eq_false,or_false,hEntries]
  exact hA.padded_unique hM.1 (hPads.mp hX) hY

theorem RawMatrixExpansion.copied_suffix_high_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {A B : FiniteMatrix M.Domain} (hA : A.Valid M C.omega)
    {T : MatrixArithmetic M.Domain} (hT : T.Valid M C) {Forests Rows last maximal root index count L total : M.Domain}
    (h : RawMatrixExpansion M C A T Forests Rows last maximal root index count L total B)
    (hLast : M.mem last A.width) (hRootLast : M.mem root last) (hIndex : M.mem index C.omega)
    {copy slot source c start : M.Domain} (hCopy : copy=index ∨ M.mem copy index) (hSlot : M.mem slot L)
    (hSource : AddAt M T.addPairs T.plus root slot source)
    (hPos : CopyPosition M C.omega T.addPairs T.plus T.mulPairs T.times root L copy slot c)
    (hStart : maximal=start ∨ M.mem maximal start) : ColumnEqFrom M C.omega C.zero B A c source start := by
  apply h.copied_suffix_unchanged_d hM hC hA hT hLast hRootLast hIndex hCopy hSlot hSource hPos
  intro r hr hStartR hAsc
  have hOrdR := (omega_isOrdinal_d hM hC.omega).mem hr
  have hMaxR : maximal=r ∨ M.mem maximal r := by
    rcases hStartR with he | hsr
    · exact he ▸ hStart
    · rcases hStart with he | hms
      · exact Or.inr (he ▸ hsr)
      · exact Or.inr (hOrdR.transitive start hsr maximal hms)
  rcases hMaxR with he | hmr
  · exact SetTheory.KP.mem_irrefl_d (KP1Y.models_weakKP hM) r (he ▸ hAsc.1)
  · exact SetTheory.KP.mem_irrefl_d (KP1Y.models_weakKP hM) r (hOrdR.transitive maximal hmr r hAsc.1)

theorem RawMatrixExpansion.copied_suffix_parent_good_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {A B : FiniteMatrix M.Domain} (hA : A.Valid M C.omega)
    {T : MatrixArithmetic M.Domain} (hT : T.Valid M C) {Forests Rows Linear last maximal root index count L total : M.Domain}
    (hRun : MatrixParentRun M C A.width A.height A.cells A.values Forests Rows Linear)
    (h : RawMatrixExpansion M C A T Forests Rows last maximal root index count L total B)
    (hLast : M.mem last A.width) (hRootLast : M.mem root last) (hIndex : M.mem index C.omega)
    {copy slot source c start row P p : M.Domain} (hCopy : copy=index ∨ M.mem copy index) (hSlot : M.mem slot L)
    (hSource : AddAt M T.addPairs T.plus root slot source)
    (hPos : CopyPosition M C.omega T.addPairs T.plus T.mulPairs T.times root L copy slot c)
    (hRow : MemPair M Rows row P) (hParent : MemPair M P source p) (hGood : M.mem p root) (hNonroot : source≠root)
    (hStart : M.SuccessorOf start row) : ColumnEqFrom M C.omega C.zero B A c source start := by
  apply h.copied_suffix_unchanged_d hM hC hA hT hLast hRootLast hIndex hCopy hSlot hSource hPos
  intro r hr hStartR
  have hRowR : M.mem row r := by
    rcases hStartR with he | hsr
    · exact he ▸ hStart.predecessor_mem
    · exact ((omega_isOrdinal_d hM hC.omega).mem hr).transitive start hsr row hStart.predecessor_mem
  exact hRun.not_ascending_above_good_parent_d hM hC hRow hParent hGood hNonroot hRowR

theorem aboveS_prefix_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {A B : FiniteMatrix M.Domain} (hB : B.Valid M C.omega)
    {Forests Rows L OtherForests Other OtherL base : M.Domain}
    (hRun : MatrixParentRun M C A.width A.height A.cells A.values Forests Rows L)
    (hOther : MatrixParentRun M C B.width B.height B.cells B.values OtherForests Other OtherL)
    (hHeight : B.height=A.height) (hSub : M.MemberSubset B.width A.width)
    (hParents : ∀ r P Q, MemPair M Rows r P → MemPair M Other r Q → RowsAgreeOn M P Q B.width)
    (hEntries : ∀ r c d, M.mem c B.width → (MatrixEntry M B r c d ↔ MatrixEntry M A r c d))
    (hS : AboveS M C A Forests Rows L base) : AboveS M C B OtherForests Other OtherL base := by
  intro r hr hBase P' hPrev Q' _ hQ' start hStart hs
  have hrA : M.mem r A.height := hHeight ▸ hr
  obtain ⟨Q,hQMem,hQ⟩ := hRun.graph.total r hrA
  have hCurRows := hParents r Q Q' hQ hQ'
  rcases hPrev with ⟨hr0,hP'⟩ | ⟨j,hj,hSucc,hP'Mem,hJ⟩
  · subst P'
    have hLinear : RowsAgreeOn M L OtherL B.width := by
      intro c hc p
      rw [hRun.linear.2 c p,hOther.linear.2 c p]
      simp only [hSub c hc,hc,true_and]
    exact row_blocker_prefix_d hM hC hB hHeight hSub (hRun.forests r Q hQ) hLinear hCurRows hEntries
      (hS r hrA hBase L (Or.inl ⟨hr0,rfl⟩) Q hQMem hQ start hStart hs)
  · have hjA : M.mem j A.height := hHeight ▸ hj
    obtain ⟨P,hPMem,hJP⟩ := hRun.graph.total j hjA
    exact row_blocker_prefix_d hM hC hB hHeight hSub (hRun.forests r Q hQ)
      (hParents j P P' hJP hJ) hCurRows hEntries
      (hS r hrA hBase P (Or.inr ⟨j,hjA,hSucc,hPMem,hJP⟩) Q hQMem hQ start hStart hs)

theorem depth_regular_prefix_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {A B : FiniteMatrix M.Domain} (hB : B.Valid M C.omega)
    {Forests Rows L OtherForests Other : M.Domain}
    (hRun : MatrixParentRun M C A.width A.height A.cells A.values Forests Rows L)
    (hHeight : B.height=A.height) (hSub : M.MemberSubset B.width A.width)
    (hParents : ∀ r P Q, MemPair M Rows r P → MemPair M Other r Q → RowsAgreeOn M P Q B.width)
    (hEntries : ∀ r c d, M.mem c B.width → (MatrixEntry M B r c d ↔ MatrixEntry M A r c d))
    (hI : MatrixDepthRegular M C A Forests Rows) : MatrixDepthRegular M C B OtherForests Other := by
  intro r hr Q' _ hQ' c hc d hd hEntry
  have hrA : M.mem r A.height := hHeight ▸ hr
  obtain ⟨Q,hQMem,hQ⟩ := hRun.graph.total r hrA
  have hRows := hParents r Q Q' hQ hQ'
  have hOld := hI r hrA Q hQMem hQ c (hSub c hc) d hd ((hEntries r c d hc).mp hEntry)
  refine ⟨?_,?_⟩
  · intro hNo
    exact hOld.1 ((no_parent_prefix_iff_d hM hC (hRun.forests r Q hQ) hB.width hc hRows).mpr hNo)
  · intro p hp hParent e he hEntryP
    exact hOld.2 p (hSub p hp) ((hRows c hc p).mpr hParent) e he ((hEntries r p e hp).mp hEntryP)

/-- 真正构造前缀矩阵及其父运行，再证明 I 与给定边界以上 S 同时保持。 -/
theorem relative_structural_prefix_exists_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {A : FiniteMatrix M.Domain} (hA : A.Valid M C.omega)
    {Forests Rows L base n : M.Domain}
    (hRun : MatrixParentRun M C A.width A.height A.cells A.values Forests Rows L)
    (hI : MatrixDepthRegular M C A Forests Rows) (hS : AboveS M C A Forests Rows L base)
    (hn : M.mem n C.omega) (hSub : M.MemberSubset n A.width) :
    ∃ B OtherForests Other OtherL, B.Valid M C.omega ∧ B.height=A.height ∧ B.width=n ∧
      MatrixParentRun M C B.width B.height B.cells B.values OtherForests Other OtherL ∧
      MatrixDepthRegular M C B OtherForests Other ∧ AboveS M C B OtherForests Other OtherL base := by
  obtain ⟨B,OtherForests,Other,OtherL,hB,hHeight,hWidth,hOther,hEntries,hParents⟩ := matrix_prefix_run_exists_d hM hC hA hRun hn hSub
  have hSub' : M.MemberSubset B.width A.width := hWidth ▸ hSub
  have hParents' : ∀ r P Q, MemPair M Rows r P → MemPair M Other r Q → RowsAgreeOn M P Q B.width := by
    intro r P Q hP hQ
    exact hWidth ▸ hParents r P Q hP hQ
  have hEntries' : ∀ r c d, M.mem c B.width → (MatrixEntry M B r c d ↔ MatrixEntry M A r c d) :=
    fun r c d hc => hEntries r c d (hWidth ▸ hc)
  exact ⟨B,OtherForests,Other,OtherL,hB,hHeight,hWidth,hOther,
    depth_regular_prefix_d hM hC hB hRun hHeight hSub' hParents' hEntries' hI,
    aboveS_prefix_d hM hC hB hRun hOther hHeight hSub' hParents' hEntries' hS⟩


def MatrixBlockerAt (M : SetTheory.Structure.{u}) (C : ExpressionData M.Domain) (A : FiniteMatrix M.Domain)
    (previous current start c : M.Domain) : Prop :=
  ∀ q, M.mem q A.width → ∀ p, M.mem p A.width → MemPair M previous c q → MemPair M current c p → p≠q →
    ∃ z, M.mem z A.width ∧ (z=q ∨ Ancestor M C A.width current z q) ∧ MemPair M current z p ∧
      ColumnLeFrom M C.omega C.zero A A c z start

/-- ParentCopy视图上的不加量后缀，包含好部源列。 -/
theorem RawMatrixExpansion.parent_copy_suffix_unchanged_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {A B : FiniteMatrix M.Domain} (hA : A.Valid M C.omega)
    {T : MatrixArithmetic M.Domain} (hT : T.Valid M C) {X : CopyCoordinates.Context M.Domain} (hX : X.Valid M C)
    {Forests Rows maximal index count total copy source child start : M.Domain}
    (hExp : RawMatrixExpansion M C A T Forests Rows X.last maximal X.root index count X.length total B)
    (hLast : M.mem X.last A.width) (hIndex : M.mem index C.omega) (hCopy : M.mem copy count)
    (hSource : M.mem source X.last) (hChild : M.mem child B.width)
    (hMap : CopyCoordinates.ParentCopy M C T X copy source child)
    (hNoAsc : ∀ r, M.mem r C.omega → start=r ∨ M.mem start r → ¬Ascending M C A.width Forests Rows maximal X.root source r) :
    ColumnEqFrom M C.omega C.zero B A child source start := by
  have hSourceWidth := ((omega_isOrdinal_d hM hC.omega).mem hA.width).transitive X.last hLast source hSource
  intro r hr hStart x _ y _ hXEntry hYEntry
  have hEntries (z : M.Domain) := (hExp.parent_copy_entry_iff_d hM hC hA hT hX hLast hIndex hCopy hSource hMap (r := r) (y := z)).trans
    (lifted_entry_unascending_iff hM.1 hA (hNoAsc r hr hStart))
  have hPads : PaddedEntry M C.zero B r child x ↔ PaddedEntry M C.zero A r source x := by
    simp only [PaddedEntry,hExp.height,hChild,hSourceWidth,not_true_eq_false,or_false,hEntries]
  exact hA.padded_unique hM.1 (hPads.mp hXEntry) hYEntry

theorem RawMatrixExpansion.parent_copy_suffix_good_parent_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {A B : FiniteMatrix M.Domain} (hA : A.Valid M C.omega)
    {T : MatrixArithmetic M.Domain} (hT : T.Valid M C) {X : CopyCoordinates.Context M.Domain} (hX : X.Valid M C)
    {Forests Rows L maximal index count total copy source child r P p start : M.Domain}
    (hRun : MatrixParentRun M C A.width A.height A.cells A.values Forests Rows L)
    (hExp : RawMatrixExpansion M C A T Forests Rows X.last maximal X.root index count X.length total B)
    (hLast : M.mem X.last A.width) (hIndex : M.mem index C.omega) (hCopy : M.mem copy count)
    (hSource : M.mem source X.last) (hChild : M.mem child B.width) (hNonroot : source≠X.root)
    (hMap : CopyCoordinates.ParentCopy M C T X copy source child)
    (hP : MemPair M Rows r P) (hParent : MemPair M P source p) (hGood : M.mem p X.root) (hs : M.SuccessorOf start r) :
    ColumnEqFrom M C.omega C.zero B A child source start := by
  apply hExp.parent_copy_suffix_unchanged_d hM hC hA hT hX hLast hIndex hCopy hSource hChild hMap
  intro s hsn hStart
  have hrs : M.mem r s := by
    rcases hStart with he | hlt
    · exact he ▸ hs.predecessor_mem
    · exact ((omega_isOrdinal_d hM hC.omega).mem hsn).transitive start hlt r hs.predecessor_mem
  exact hRun.not_ascending_above_good_parent_d hM hC hP hParent hGood hNonroot hrs

/-- 坏部父项的S见证随同副本运输；后缀次序由实际共同父项提升保序得到。 -/
theorem blocker_at_copy_bad_parent_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {A B : FiniteMatrix M.Domain} (hA : A.Valid M C.omega)
    {T : MatrixArithmetic M.Domain} (hT : T.Valid M C) {X : CopyCoordinates.Context M.Domain} (hX : X.Valid M C)
    {Forests Rows L maximal index count total r F P previous previousMax QF Q copy source child oldP start : M.Domain}
    (hRun : MatrixParentRun M C A.width A.height A.cells A.values Forests Rows L)
    (hExp : RawMatrixExpansion M C A T Forests Rows X.last maximal X.root index count X.length total B)
    (hLast : M.mem X.last A.width) (hIndex : M.mem index C.omega) (hP : MemPair M Rows r P)
    (hF : Forest M C.omega A.width F)
    (hCF : MatrixCopy.CopyForest M C T X F previous previousMax count B.width QF)
    (hCQ : MatrixCopy.CopyForest M C T X P r maximal count B.width Q)
    (hOldS : RowBlocker M C A F P start) (hs : M.SuccessorOf start r)
    (hCopy : M.mem copy count) (hSource : M.mem source X.last)
    (hOldParent : MemPair M P source oldP) (hBad : X.root=oldP ∨ M.mem X.root oldP)
    (hMap : CopyCoordinates.ParentCopy M C T X copy source child) : MatrixBlockerAt M C B QF Q start child := by
  have hw := omega_isOrdinal_d hM hC.omega
  have hPF := hRun.forests r P hP
  have hSourceWidth := (hw.mem hA.width).transitive X.last hLast source hSource
  have hRootWidth := (hw.mem hA.width).transitive X.last hLast X.root hX.below
  have hSourceRoot : M.mem X.root source := by
    rcases hBad with he | hlt
    · exact he.symm ▸ hPF.left source oldP hOldParent
    · exact (hw.mem (hw.transitive A.width hA.width source hSourceWidth)).transitive oldP (hPF.left source oldP hOldParent) X.root hlt
  have hNonroot : source≠X.root := fun he => SetTheory.KP.mem_irrefl_d (KP1Y.models_weakKP hM) X.root (he ▸ hSourceRoot)
  intro q _ p _ hNewPrev hNewCur hDistinct
  obtain ⟨oldQ,hOldQLast,hOldPrev,hMapQ⟩ := (hCF.source_parent_nonroot_d hM hC hT hX hF hCF.count_nat hCopy hSource hNonroot hMap q).mp hNewPrev
  obtain ⟨p',_,hOldP',hMapP⟩ := (hCQ.source_parent_nonroot_d hM hC hT hX hPF hCQ.count_nat hCopy hSource hNonroot hMap p).mp hNewCur
  have hParentsEq := hPF.unique source p' oldP hOldP' hOldParent
  subst p'
  obtain ⟨J,hJ,hJRows⟩ := hCQ.copy_embedding_d hM hC hT hX hCopy
  have hOldPLast := (hw.mem hX.last).transitive source hSource oldP (hPF.left source oldP hOldParent)
  have hJP := (hJRows oldP p).mpr ⟨hOldPLast,hMapP⟩
  have hJQ := (hJRows oldQ q).mpr ⟨hOldQLast,hMapQ⟩
  have hOldDistinct : oldP≠oldQ := by
    intro he
    subst oldQ
    exact hDistinct (hJ.graph.unique oldP p q hJP hJQ)
  obtain ⟨z,hzWidth,hPath,hZParent,hLe⟩ := hOldS source hSourceWidth oldQ (hF.bounds hM.1 hOldPrev).2 oldP
    (hPF.bounds hM.1 hOldParent).2 hOldPrev hOldParent hOldDistinct
  have hzSource : M.mem z source := by
    rcases hPath with he | hAnc
    · exact he.symm ▸ hF.left source oldQ hOldPrev
    · exact (hw.mem (hw.transitive A.width hA.width source hSourceWidth)).transitive oldQ (hF.left source oldQ hOldPrev) z hAnc.1
  have hzLast := (hw.mem hX.last).transitive source hSource z hzSource
  have hRootZ : M.mem X.root z := by
    rcases hBad with he | hlt
    · exact he.symm ▸ hPF.left z oldP hZParent
    · exact (hw.mem (hw.transitive A.width hA.width z hzWidth)).transitive oldP (hPF.left z oldP hZParent) X.root hlt
  have hzNonroot : z≠X.root := fun he => SetTheory.KP.mem_irrefl_d (KP1Y.models_weakKP hM) X.root (he ▸ hRootZ)
  obtain ⟨w,hwWidth,hJW⟩ := hJ.graph.total z hzLast
  have hMapZ := ((hJRows z w).mp hJW).2
  refine ⟨w,hwWidth,?_,?_,?_⟩
  · rcases hPath with he | hAnc
    · subst z
      exact Or.inl (hJ.graph.unique oldQ w q hJW hJQ)
    · exact Or.inr ((hCQ.ancestor_bad_iff_d hM hC hT hX hPF hLast hCopy (Or.inr hRootZ) hzLast hOldQLast hMapZ hMapQ).mpr hAnc)
  · exact (hCQ.source_parent_nonroot_d hM hC hT hX hPF hCQ.count_nat hCopy hzLast hzNonroot hMapZ p).mpr
      ⟨oldP,hOldPLast,hZParent,hMapP⟩
  · have hSame : ParentRowsEqual M P source z := by
      intro t
      constructor
      · intro ht
        have he := hPF.unique source t oldP ht hOldParent
        exact he.symm ▸ hZParent
      · intro ht
        have he := hPF.unique z t oldP ht hZParent
        exact he.symm ▸ hOldParent
    have hLift := lifted_suffix_le_of_common_parent_d hM hC hA hT (U := ⟨Forests,Rows,X.last,maximal,X.root,copy⟩) hRun
      hSourceWidth hzWidth hSourceRoot hRootZ hLast hRootWidth hMap.2.1 hP hs hSame hLe
    exact lifted_suffix_le_realized_d hM.1 hExp.matrix hExp.matrix hExp.height hExp.height
      (hCQ.copy_value_bound_d hM hC hT hX hCopy hSource hMap) hwWidth
      (fun s v => hExp.parent_copy_entry_iff_d hM hC hA hT hX hLast hIndex hCopy hSource hMap)
      (fun s v => hExp.parent_copy_entry_iff_d hM hC hA hT hX hLast hIndex hCopy hzLast hMapZ) hLift

theorem RawMatrixExpansion.prefix_suffix_eq_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {A B : FiniteMatrix M.Domain} (hA : A.Valid M C.omega)
    {T : MatrixArithmetic M.Domain} (hT : T.Valid M C) {Forests Rows last maximal root index count len total c start : M.Domain}
    (hExp : RawMatrixExpansion M C A T Forests Rows last maximal root index count len total B)
    (hLast : M.mem last A.width) (hRootLast : M.mem root last) (hIndex : M.mem index C.omega) (hc : M.mem c last) :
    ColumnEqFrom M C.omega C.zero B A c c start := by
  have hw := omega_isOrdinal_d hM hC.omega
  have hcA := (hw.mem hA.width).transitive last hLast c hc
  have hcB := hExp.prefix_width_d hM hC hIndex hRootLast c hc
  intro r _ _ x _ y _ hX hY
  have hEntries (d : M.Domain) := hExp.prefix_entry_iff_d hM hC hA hT hLast hRootLast hIndex hc (r := r) (y := d)
  have hPads : PaddedEntry M C.zero B r c x ↔ PaddedEntry M C.zero A r c x := by
    simp only [PaddedEntry,hExp.height,hcA,hcB,not_true_eq_false,or_false,hEntries]
  exact hA.padded_unique hM.1 (hPads.mp hX) hY

private def firstRootEnv {M : SetTheory.Structure.{u}} (C : ExpressionData M.Domain) (T : MatrixArithmetic M.Domain)
    (X : CopyCoordinates.Context M.Domain) (count width Q : M.Domain) : Env M 18 :=
  (((((((((((((((((oneEnv C.omega).push C.zero).push C.one).push C.sequences).push C.expressions).push T.addPairs).push T.plus).push T.mulPairs).push T.times).push T.diffPairs).push T.difference).push X.last).push X.root).push X.length).push X.first).push count).push width).push Q

private def firstRootSchema : Project.UnarySchema 18 where
  body := .forallE (.imp (.conj (.mem (.bound 1) (.bound 4))
    (CopyCoordinates.parentCopyFormula ⟨.bound 19,.bound 18,.bound 17,.bound 16,.bound 15⟩
      ⟨.bound 14,.bound 13,.bound 12,.bound 11,.bound 10,.bound 9⟩ ⟨.bound 8,.bound 7,.bound 6,.bound 5⟩ (.bound 1) (.bound 7) (.bound 0)))
    (.disj (Project.Formula.extensionalEq (.bound 7) (.bound 0))
      (ancestorFormula ⟨.bound 19,.bound 18,.bound 17,.bound 16,.bound 15⟩ (.bound 3) (.bound 2) (.bound 7) (.bound 0))))
  freeClosed := by
    have hC : (⟨.bound 19,.bound 18,.bound 17,.bound 16,.bound 15⟩ : ExpressionData (Project.Term 20)).Closed := ⟨rfl,rfl,rfl,rfl,rfl⟩
    have hT : CopyCoordinates.ArithmeticClosed (⟨.bound 14,.bound 13,.bound 12,.bound 11,.bound 10,.bound 9⟩ : MatrixArithmetic (Project.Term 20)) := ⟨rfl,rfl,rfl,rfl,rfl,rfl⟩
    have hX : (⟨.bound 8,.bound 7,.bound 6,.bound 5⟩ : CopyCoordinates.Context (Project.Term 20)).Closed := ⟨rfl,rfl,rfl,rfl⟩
    have hMap := CopyCoordinates.parentCopyFormula_freeClosed hC hT hX (.bound 1) (.bound 7) (.bound 0) rfl rfl rfl
    have hAnc := ancestorFormula_freeClosed hC (.bound 3) (.bound 2) (.bound 7) (.bound 0) rfl rfl rfl rfl
    simp [Definitional.Formula.FreeClosed,hMap,hAnc]

private theorem firstRootSchema_iff {M : SetTheory.Structure.{u}} (he : Extensional M)
    (C : ExpressionData M.Domain) (T : MatrixArithmetic M.Domain) (X : CopyCoordinates.Context M.Domain)
    (count width Q copy : M.Domain) :
    Project.Formula.satisfies ((firstRootEnv C T X count width Q).push copy) firstRootSchema.body ↔
      ∀ child, M.mem copy count → CopyCoordinates.ParentCopy M C T X copy X.root child →
        X.root=child ∨ Ancestor M C width Q X.root child := by
  simp only [firstRootSchema,Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_imp_iff,
    Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_mem_iff,CopyCoordinates.parentCopyFormula_iff he,
    Project.Formula.satisfies_disj_iff,Project.Formula.satisfies_extensionalEq_iff_eq he,ancestorFormula_iff he,and_imp]
  rfl

/-- 首副本root是每个低行块根的非严格祖先；内部copy归纳提供任意多块的实际路径。 -/
theorem MatrixCopy.CopyForest.first_root_reaches_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {X : CopyCoordinates.Context M.Domain} (hX : X.Valid M C) {m P r maximal count width Q copy child : M.Domain}
    (hP : Forest M C.omega m P) (hCF : MatrixCopy.CopyForest M C T X P r maximal count width Q)
    (hLast : M.mem X.last m) (hLow : M.mem r maximal) (hRootLast : Ancestor M C m P X.root X.last)
    (hCopy : M.mem copy count) (hMap : CopyCoordinates.ParentCopy M C T X copy X.root child) :
    X.root=child ∨ Ancestor M C width Q X.root child := by
  have hw := omega_isOrdinal_d hM hC.omega
  have hAll := natural_induction_d hM firstRootSchema (firstRootEnv C T X count width Q) hC.omega
    (fun zero hEmpty => (firstRootSchema_iff hM.1 C T X count width Q zero).mpr (by
      have hz := hM.1.eq_of_same_members zero C.zero (fun t => iff_of_false (hEmpty t) (hC.zero_empty t))
      subst zero
      intro child hCopy hMap
      obtain ⟨J,hJ,hRows⟩ := hCF.copy_embedding_d hM hC hT hX hCopy
      exact Or.inl (hJ.graph.unique X.root X.root child
        ((hRows X.root X.root).mpr ⟨hX.below,CopyCoordinates.parent_copy_zero_d hM hC hT hX hX.root⟩)
        ((hRows X.root child).mpr ⟨hX.below,hMap⟩))))
    (fun prev hPrev ih next hs => (firstRootSchema_iff hM.1 C T X count width Q next).mpr (by
      intro child hNext hMap
      have hPrevCount := (hw.mem hCF.count_nat).transitive next hNext prev hs.predecessor_mem
      obtain ⟨J,hJ,hRows⟩ := hCF.copy_embedding_d hM hC hT hX hPrevCount
      obtain ⟨z,_,hRootAt⟩ := hJ.graph.total X.root hX.below
      have hRootMap := ((hRows X.root z).mp hRootAt).2
      have hReach := (firstRootSchema_iff hM.1 C T X count width Q prev).mp ih z hPrevCount hRootMap
      have hRootZero := (hT.add.add_iff_sum hM hX.root hC.zero_nat).mpr (KP1Y.Arithmetic.sum_zero_d hM X.root hC.zero_empty)
      have hEncode := (CopyCoordinates.parent_copy_bad_iff (SetTheory.KP.mem_irrefl_d (KP1Y.models_weakKP hM) X.root)).mp hMap
      have hPos := (CopyCoordinates.encode_at_base_iff_d hM hC hT hX.root hC.zero_nat hMap.2.1 hRootZero).mp hEncode
      have hNextAnc := (hCF.ancestor_previous_root_iff_d hM hC hT hX hP hLast hNext hPrev hs hLow (Or.inl rfl) hX.below hRootMap hPos).mpr hRootLast
      exact Or.inr (hReach.elim (fun he => he.symm ▸ hNextAnc) (fun hAnc => ancestor_trans_d hM hC hCF.forest hAnc hNextAnc))))
  exact (firstRootSchema_iff hM.1 C T X count width Q copy).mp (hAll copy hMap.2.1) child hCopy hMap

theorem MatrixCopy.CopyForest.zero_root_path_copy_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {X : CopyCoordinates.Context M.Domain} (hX : X.Valid M C) {m P r maximal count width Q copy source child : M.Domain}
    (hP : Forest M C.omega m P) (hCF : MatrixCopy.CopyForest M C T X P r maximal count width Q)
    (hLast : M.mem X.last m) (hLow : M.mem r maximal) (hRootLast : Ancestor M C m P X.root X.last)
    (hCopy : M.mem copy count) (hSource : M.mem source X.last)
    (hMap : CopyCoordinates.ParentCopy M C T X copy source child) (hPath : X.root=source ∨ Ancestor M C m P X.root source) :
    X.root=child ∨ Ancestor M C width Q X.root child := by
  rcases hPath with he | hPath
  · subst source
    exact hCF.first_root_reaches_d hM hC hT hX hP hLast hLow hRootLast hCopy hMap
  · obtain ⟨J,hJ,hRows⟩ := hCF.copy_embedding_d hM hC hT hX hCopy
    obtain ⟨z,_,hRootAt⟩ := hJ.graph.total X.root hX.below
    have hRootMap := ((hRows X.root z).mp hRootAt).2
    have hReach := hCF.first_root_reaches_d hM hC hT hX hP hLast hLow hRootLast hCopy hRootMap
    have hNextAnc := (hCF.ancestor_bad_iff_d hM hC hT hX hP hLast hCopy (Or.inl rfl) hX.below hSource hRootMap hMap).mpr hPath
    exact Or.inr (hReach.elim (fun he => he.symm ▸ hNextAnc) (fun hAnc => ancestor_trans_d hM hC hCF.forest hAnc hNextAnc))

private theorem column_eq_from_symm {M : SetTheory.Structure.{u}} {w z : M.Domain} {A B : FiniteMatrix M.Domain}
    {c d start : M.Domain} (h : ColumnEqFrom M w z A B c d start) : ColumnEqFrom M w z B A d c start :=
  fun r hr hs x hx y hy hX hY => (h r hr hs y hy x hx hY hX).symm

/-- 好部父项的S见证：若旧见证恰为root，使用首副本root；其余同副本运输。 -/
theorem blocker_at_copy_good_parent_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {A B : FiniteMatrix M.Domain} (hA : A.Valid M C.omega)
    {T : MatrixArithmetic M.Domain} (hT : T.Valid M C) {X : CopyCoordinates.Context M.Domain} (hX : X.Valid M C)
    {Forests Rows L maximal index count total r F P previous previousMax QF Q copy source child oldP start : M.Domain}
    (hRun : MatrixParentRun M C A.width A.height A.cells A.values Forests Rows L)
    (hExp : RawMatrixExpansion M C A T Forests Rows X.last maximal X.root index count X.length total B)
    (hLast : M.mem X.last A.width) (hIndex : M.mem index C.omega) (hP : MemPair M Rows r P)
    (hF : Forest M C.omega A.width F)
    (hCF : MatrixCopy.CopyForest M C T X F previous previousMax count B.width QF)
    (hCQ : MatrixCopy.CopyForest M C T X P r maximal count B.width Q)
    (hOldS : RowBlocker M C A F P start) (hs : M.SuccessorOf start r) (hLow : M.mem r maximal)
    (hRootLast : Ancestor M C A.width P X.root X.last)
    (hCopy : M.mem copy count) (hSource : M.mem source X.last) (hNonroot : source≠X.root)
    (hOldParent : MemPair M P source oldP) (hGood : M.mem oldP X.root)
    (hMap : CopyCoordinates.ParentCopy M C T X copy source child) : MatrixBlockerAt M C B QF Q start child := by
  have hw := omega_isOrdinal_d hM hC.omega
  have hPF := hRun.forests r P hP
  have hSourceWidth := (hw.mem hA.width).transitive X.last hLast source hSource
  intro q _ p _ hNewPrev hNewCur hDistinct
  obtain ⟨oldQ,hOldQLast,hOldPrev,hMapQ⟩ := (hCF.source_parent_nonroot_d hM hC hT hX hF hCF.count_nat hCopy hSource hNonroot hMap q).mp hNewPrev
  obtain ⟨p',_,hOldP',hMapP⟩ := (hCQ.source_parent_nonroot_d hM hC hT hX hPF hCQ.count_nat hCopy hSource hNonroot hMap p).mp hNewCur
  have hParentsEq := hPF.unique source p' oldP hOldP' hOldParent
  subst p'
  have hTargetOld := (CopyCoordinates.parent_copy_good_iff hMapP.2.1 hMapP.1 hGood).mp hMapP
  subst p
  obtain ⟨J,hJ,hJRows⟩ := hCQ.copy_embedding_d hM hC hT hX hCopy
  have hOldPLast := (hw.mem hX.last).transitive source hSource oldP (hPF.left source oldP hOldParent)
  have hJP := (hJRows oldP oldP).mpr ⟨hOldPLast,hMapP⟩
  have hJQ := (hJRows oldQ q).mpr ⟨hOldQLast,hMapQ⟩
  have hOldDistinct : oldP≠oldQ := by
    intro he
    subst oldQ
    exact hDistinct (hJ.graph.unique oldP oldP q hJP hJQ)
  obtain ⟨z,_,hPath,hZParent,hLe⟩ := hOldS source hSourceWidth oldQ (hF.bounds hM.1 hOldPrev).2 oldP
    (hPF.bounds hM.1 hOldParent).2 hOldPrev hOldParent hOldDistinct
  have hzSource : M.mem z source := by
    rcases hPath with he | hAnc
    · exact he.symm ▸ hF.left source oldQ hOldPrev
    · exact (hw.mem (hw.transitive A.width hA.width source hSourceWidth)).transitive oldQ (hF.left source oldQ hOldPrev) z hAnc.1
  have hzLast := (hw.mem hX.last).transitive source hSource z hzSource
  have hLeft := hExp.parent_copy_suffix_good_parent_d hM hC hA hT hX hRun hLast hIndex hCopy hSource
    (hCQ.copy_value_bound_d hM hC hT hX hCopy hSource hMap) hNonroot hMap hP hOldParent hGood hs
  have hCompare (w : M.Domain) (hRight : ColumnEqFrom M C.omega C.zero B A w z start) : ColumnLeFrom M C.omega C.zero B B child w start :=
    column_le_from_trans_d hM hC hExp.matrix hA hExp.matrix
      (column_le_from_trans_d hM hC hExp.matrix hA hA (Or.inl hLeft) hLe) (Or.inl (column_eq_from_symm hRight))
  classical
  by_cases hzRoot : z=X.root
  · subst z
    have hZeroCount : M.mem C.zero count := (hC.zero_mem_iff hM hCQ.count_nat).mpr
      (fun he => hC.zero_empty index (he ▸ hExp.copies.predecessor_mem))
    have hPrefix := hCQ.parent_prefix_d hM hC hT hX hPF hCQ.count_nat hZeroCount
    exact ⟨X.root,hExp.prefix_width_d hM hC hIndex hX.below X.root hX.below,
      hCQ.zero_root_path_copy_d hM hC hT hX hPF hLast hLow hRootLast hCopy hOldQLast hMapQ hPath,
      (hPrefix X.root hX.below oldP).mp hZParent,
      hCompare X.root (hExp.prefix_suffix_eq_d hM hC hA hT hLast hX.below hIndex hX.below)⟩
  · obtain ⟨w,hwWidth,hJW⟩ := hJ.graph.total z hzLast
    have hMapZ := ((hJRows z w).mp hJW).2
    refine ⟨w,hwWidth,?_,?_,?_⟩
    · rcases hPath with he | hAnc
      · subst z
        exact Or.inl (hJ.graph.unique oldQ w q hJW hJQ)
      · exact Or.inr ((hCQ.ancestor_copy_iff_d hM hC hT hX hPF hLast hCopy (fun _ => hRootLast) hzLast hOldQLast hMapZ hMapQ).mpr hAnc)
    · exact (hCQ.source_parent_nonroot_d hM hC hT hX hPF hCQ.count_nat hCopy hzLast hzRoot hMapZ oldP).mpr
        ⟨oldP,hOldPLast,hZParent,hMapP⟩
    · exact hCompare w (hExp.parent_copy_suffix_good_parent_d hM hC hA hT hX hRun hLast hIndex hCopy hzLast hwWidth hzRoot
        hMapZ hP hZParent hGood hs)

theorem RawMatrixExpansion.parent_copy_suffix_high_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {A B : FiniteMatrix M.Domain} (hA : A.Valid M C.omega)
    {T : MatrixArithmetic M.Domain} (hT : T.Valid M C) {X : CopyCoordinates.Context M.Domain} (hX : X.Valid M C)
    {Forests Rows maximal index count total copy source child start : M.Domain}
    (hExp : RawMatrixExpansion M C A T Forests Rows X.last maximal X.root index count X.length total B)
    (hLast : M.mem X.last A.width) (hIndex : M.mem index C.omega) (hCopy : M.mem copy count)
    (hSource : M.mem source X.last) (hChild : M.mem child B.width)
    (hMap : CopyCoordinates.ParentCopy M C T X copy source child) (hStart : maximal=start ∨ M.mem maximal start) :
    ColumnEqFrom M C.omega C.zero B A child source start := by
  apply hExp.parent_copy_suffix_unchanged_d hM hC hA hT hX hLast hIndex hCopy hSource hChild hMap
  intro r hr hStartR hAsc
  have hOrdR := (omega_isOrdinal_d hM hC.omega).mem hr
  have hMaxR : maximal=r ∨ M.mem maximal r := by
    rcases hStartR with he | hsr
    · exact he ▸ hStart
    · rcases hStart with he | hms
      · exact Or.inr (he ▸ hsr)
      · exact Or.inr (hOrdR.transitive start hsr maximal hms)
  rcases hMaxR with he | hmr
  · exact SetTheory.KP.mem_irrefl_d (KP1Y.models_weakKP hM) r (he ▸ hAsc.1)
  · exact SetTheory.KP.mem_irrefl_d (KP1Y.models_weakKP hM) r (hOrdR.transitive maximal hmr r hAsc.1)

/-- 保留前缀中的单列S；输出其余列可含任意多个真实副本。 -/
theorem blocker_at_expanded_prefix_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {A B : FiniteMatrix M.Domain} (hA : A.Valid M C.omega)
    {T : MatrixArithmetic M.Domain} (hT : T.Valid M C) {Forests Rows last maximal root index count len total F P QF Q child start : M.Domain}
    (hExp : RawMatrixExpansion M C A T Forests Rows last maximal root index count len total B)
    (hLast : M.mem last A.width) (hRootLast : M.mem root last) (hIndex : M.mem index C.omega)
    (hF : Forest M C.omega A.width F) (hP : Forest M C.omega A.width P) (hQ : Forest M C.omega B.width Q)
    (hPrevRows : RowsAgreeOn M F QF last) (hCurRows : RowsAgreeOn M P Q last)
    (hOldS : RowBlocker M C A F P start) (hChild : M.mem child last) : MatrixBlockerAt M C B QF Q start child := by
  have hw := omega_isOrdinal_d hM hC.omega
  have hSubA := (hw.mem hA.width).transitive last hLast
  have hSubB := hExp.prefix_width_d hM hC hIndex hRootLast
  intro q _ p _ hPrev hCur hDistinct
  have hOldPrev := (hPrevRows child hChild q).mpr hPrev
  have hOldCur := (hCurRows child hChild p).mpr hCur
  obtain ⟨z,_,hPath,hZParent,hLe⟩ := hOldS child (hSubA child hChild) q (hF.bounds hM.1 hOldPrev).2 p
    (hP.bounds hM.1 hOldCur).2 hOldPrev hOldCur hDistinct
  have hqLast := (hw.mem (hw.transitive A.width hA.width last hLast)).transitive child hChild q (hF.left child q hOldPrev)
  have hzLast : M.mem z last := by
    rcases hPath with he | hAnc
    · exact he.symm ▸ hqLast
    · exact (hw.mem (hw.transitive A.width hA.width last hLast)).transitive q hqLast z hAnc.1
  refine ⟨z,hSubB z hzLast,?_,(hCurRows z hzLast p).mp hZParent,?_⟩
  · exact hPath.imp id ((ancestor_common_prefix_iff_d hM hC hP hQ (hw.transitive A.width hA.width last hLast) hSubA hSubB hqLast hCurRows).mp)
  · exact column_le_from_trans_d hM hC hExp.matrix hA hExp.matrix
      (column_le_from_trans_d hM hC hExp.matrix hA hA (Or.inl (hExp.prefix_suffix_eq_d hM hC hA hT hLast hRootLast hIndex hChild)) hLe)
      (Or.inl (column_eq_from_symm (hExp.prefix_suffix_eq_d hM hC hA hT hLast hRootLast hIndex hzLast)))

/-- 当前高行且上一父项按同副本运输时，整个S见证直接运输。 -/
theorem blocker_at_copy_high_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {A B : FiniteMatrix M.Domain} (hA : A.Valid M C.omega)
    {T : MatrixArithmetic M.Domain} (hT : T.Valid M C) {X : CopyCoordinates.Context M.Domain} (hX : X.Valid M C)
    {Forests Rows L maximal index count total r F P QF Q copy source child start : M.Domain}
    (hRun : MatrixParentRun M C A.width A.height A.cells A.values Forests Rows L)
    (hExp : RawMatrixExpansion M C A T Forests Rows X.last maximal X.root index count X.length total B)
    (hLast : M.mem X.last A.width) (hIndex : M.mem index C.omega) (hP : MemPair M Rows r P) (hF : Forest M C.omega A.width F)
    (hCQ : MatrixCopy.CopyForest M C T X P r maximal count B.width Q)
    (hOldS : RowBlocker M C A F P start) (hHigh : ¬M.mem r maximal) (hStart : maximal=start ∨ M.mem maximal start)
    (hCopy : M.mem copy count) (hSource : M.mem source X.last)
    (hMap : CopyCoordinates.ParentCopy M C T X copy source child)
    (hPrevRows : ∀ q, MemPair M QF child q ↔ ∃ oldQ, M.mem oldQ X.last ∧ MemPair M F source oldQ ∧ CopyCoordinates.ParentCopy M C T X copy oldQ q) :
    MatrixBlockerAt M C B QF Q start child := by
  have hw := omega_isOrdinal_d hM hC.omega
  have hPF := hRun.forests r P hP
  have hSourceWidth := (hw.mem hA.width).transitive X.last hLast source hSource
  intro q _ p _ hPrev hCur hDistinct
  obtain ⟨oldQ,hOldQLast,hOldPrev,hMapQ⟩ := (hPrevRows q).mp hPrev
  obtain ⟨oldP,hOldPLast,hOldParent,hMapP⟩ := (hCQ.source_parent_high_d hM hC hT hX hPF hCQ.count_nat hCopy hSource hHigh hMap p).mp hCur
  obtain ⟨J,hJ,hRows⟩ := hCQ.copy_embedding_d hM hC hT hX hCopy
  have hJP := (hRows oldP p).mpr ⟨hOldPLast,hMapP⟩
  have hJQ := (hRows oldQ q).mpr ⟨hOldQLast,hMapQ⟩
  have hOldDistinct : oldP≠oldQ := by
    intro he
    subst oldQ
    exact hDistinct (hJ.graph.unique oldP p q hJP hJQ)
  obtain ⟨z,_,hPath,hZParent,hLe⟩ := hOldS source hSourceWidth oldQ (hF.bounds hM.1 hOldPrev).2 oldP
    (hPF.bounds hM.1 hOldParent).2 hOldPrev hOldParent hOldDistinct
  have hzSource : M.mem z source := by
    rcases hPath with he | hAnc
    · exact he.symm ▸ hF.left source oldQ hOldPrev
    · exact (hw.mem (hw.transitive A.width hA.width source hSourceWidth)).transitive oldQ (hF.left source oldQ hOldPrev) z hAnc.1
  have hzLast := (hw.mem hX.last).transitive source hSource z hzSource
  obtain ⟨w,hwWidth,hJW⟩ := hJ.graph.total z hzLast
  have hMapZ := ((hRows z w).mp hJW).2
  refine ⟨w,hwWidth,?_,?_,?_⟩
  · rcases hPath with he | hAnc
    · subst z
      exact Or.inl (hJ.graph.unique oldQ w q hJW hJQ)
    · exact Or.inr ((hCQ.ancestor_high_iff_d hM hC hT hX hPF hLast hCopy hHigh hzLast hOldQLast hMapZ hMapQ).mpr hAnc)
  · exact (hCQ.source_parent_high_d hM hC hT hX hPF hCQ.count_nat hCopy hzLast hHigh hMapZ p).mpr
      ⟨oldP,hOldPLast,hZParent,hMapP⟩
  · have hLeft := hExp.parent_copy_suffix_high_d hM hC hA hT hX hLast hIndex hCopy hSource
      (hCQ.copy_value_bound_d hM hC hT hX hCopy hSource hMap) hMap hStart
    have hRight := hExp.parent_copy_suffix_high_d hM hC hA hT hX hLast hIndex hCopy hzLast hwWidth hMapZ hStart
    exact column_le_from_trans_d hM hC hExp.matrix hA hExp.matrix
      (column_le_from_trans_d hM hC hExp.matrix hA hA (Or.inl hLeft) hLe) (Or.inl (column_eq_from_symm hRight))

/-- 临界行新root的S见证是前块root；旧last的S给出所需祖先关系。 -/
theorem blocker_at_critical_root_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {A B : FiniteMatrix M.Domain} (hA : A.Valid M C.omega)
    {T : MatrixArithmetic M.Domain} (hT : T.Valid M C) {X : CopyCoordinates.Context M.Domain} (hX : X.Valid M C)
    {Forests Rows L maximal index count total F P previous previousMax QF Q prev next child start : M.Domain}
    (hRun : MatrixParentRun M C A.width A.height A.cells A.values Forests Rows L)
    (hContext : MatrixExpansionContext M C A Forests Rows X.last maximal X.root)
    (hExp : RawMatrixExpansion M C A T Forests Rows X.last maximal X.root index count X.length total B)
    (hIndex : M.mem index C.omega) (hP : MemPair M Rows maximal P) (hF : Forest M C.omega A.width F)
    (hCF : MatrixCopy.CopyForest M C T X F previous previousMax count B.width QF)
    (hCQ : MatrixCopy.CopyForest M C T X P maximal maximal count B.width Q)
    (hPreviousLow : M.mem previous previousMax) (hOldS : RowBlocker M C A F P start)
    (hStart : M.SuccessorOf start maximal) (hPrev : M.mem prev C.omega) (hs : M.SuccessorOf next prev)
    (hNext : M.mem next count) (hRootMap : CopyCoordinates.ParentCopy M C T X next X.root child) :
    MatrixBlockerAt M C B QF Q start child := by
  have hw := omega_isOrdinal_d hM hC.omega
  have hLast := hContext.width_successor.predecessor_mem
  have hPF := hRun.forests maximal P hP
  have hHigh : ¬M.mem maximal maximal := SetTheory.KP.mem_irrefl_d (KP1Y.models_weakKP hM) maximal
  obtain ⟨P',_,hP',hLastParent⟩ := hContext.parent
  have hPEq := hRun.graph.unique maximal P' P hP' hP
  subst P'
  have hPrevCount := (hw.mem hCQ.count_nat).transitive next hNext prev hs.predecessor_mem
  have hRootZero := (hT.add.add_iff_sum hM hX.root hC.zero_nat).mpr (KP1Y.Arithmetic.sum_zero_d hM X.root hC.zero_empty)
  have hEncode := (CopyCoordinates.parent_copy_bad_iff (SetTheory.KP.mem_irrefl_d (KP1Y.models_weakKP hM) X.root)).mp hRootMap
  have hRootPos := (CopyCoordinates.encode_at_base_iff_d hM hC hT hX.root hC.zero_nat hRootMap.2.1 hRootZero).mp hEncode
  intro q _ p _ hPrevAt hCurAt _
  obtain ⟨oldQ,hOldQLast,hOldQ,hMapQ⟩ := (hCF.root_low_parent_iff_d hM hC hT hX hCF.count_nat hNext hPrev hs hPreviousLow hRootPos q).mp hPrevAt
  have hRootP := (hCQ.root_high_parent_iff_d hM hC hT hX hCQ.count_nat hNext (Or.inr hHigh) hRootPos p).mp hCurAt
  have hRootPath : X.root=oldQ ∨ Ancestor M C A.width P X.root oldQ := by
    classical
    by_cases he : X.root=oldQ
    · exact Or.inl he
    · obtain ⟨z,_,hPath,hZParent,_⟩ := hOldS X.last hLast oldQ (hF.bounds hM.1 hOldQ).2 X.root
        (hPF.bounds hM.1 hLastParent).2 hOldQ hLastParent he
      have hRootZ := ancestor_direct_d hM hC hPF hZParent
      rcases hPath with he | hPath
      · exact Or.inr (he ▸ hRootZ)
      · exact Or.inr (ancestor_trans_d hM hC hPF hRootZ hPath)
  obtain ⟨J,hJ,hRows⟩ := hCQ.copy_embedding_d hM hC hT hX hPrevCount
  obtain ⟨w,hwWidth,hJRoot⟩ := hJ.graph.total X.root hX.below
  have hPrevRootMap := ((hRows X.root w).mp hJRoot).2
  have hJQ := (hRows oldQ q).mpr ⟨hOldQLast,hMapQ⟩
  refine ⟨w,hwWidth,?_,?_,?_⟩
  · rcases hRootPath with he | hPath
    · subst oldQ
      exact Or.inl (hJ.graph.unique X.root w q hJRoot hJQ)
    · exact Or.inr ((hCQ.ancestor_high_iff_d hM hC hT hX hPF hLast hPrevCount hHigh hX.below hOldQLast hPrevRootMap hMapQ).mpr hPath)
  · have hPrevEncode := (CopyCoordinates.parent_copy_bad_iff (SetTheory.KP.mem_irrefl_d (KP1Y.models_weakKP hM) X.root)).mp hPrevRootMap
    have hPrevPos := (CopyCoordinates.encode_at_base_iff_d hM hC hT hX.root hC.zero_nat hPrev hRootZero).mp hPrevEncode
    exact (hCQ.root_high_parent_iff_d hM hC hT hX hCQ.count_nat hPrevCount (Or.inr hHigh) hPrevPos p).mpr hRootP
  · have hLeft := hExp.parent_copy_suffix_high_d hM hC hA hT hX hLast hIndex hNext hX.below
      (hCQ.copy_value_bound_d hM hC hT hX hNext hX.below hRootMap) hRootMap (Or.inr hStart.predecessor_mem)
    have hRight := hExp.parent_copy_suffix_high_d hM hC hA hT hX hLast hIndex hPrevCount hX.below hwWidth hPrevRootMap (Or.inr hStart.predecessor_mem)
    exact Or.inl (column_eq_from_trans_d hM hC hA hLeft (column_eq_from_symm hRight))

/-- 低行新root：运输旧last的S见证，并以实际ghost列完成严格seam后缀比较。 -/
theorem blocker_at_low_root_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {A B : FiniteMatrix M.Domain} (hA : A.Valid M C.omega)
    {T : MatrixArithmetic M.Domain} (hT : T.Valid M C) {X : CopyCoordinates.Context M.Domain} (hX : X.Valid M C)
    {Forests Rows L maximal index count total r F P previous previousMax QF Q prev next child start : M.Domain}
    (hRun : MatrixParentRun M C A.width A.height A.cells A.values Forests Rows L)
    (hContext : MatrixExpansionContext M C A Forests Rows X.last maximal X.root)
    (hExp : RawMatrixExpansion M C A T Forests Rows X.last maximal X.root index count X.length total B)
    (hIndex : M.mem index C.omega) (hP : MemPair M Rows r P) (hF : Forest M C.omega A.width F)
    (hCF : MatrixCopy.CopyForest M C T X F previous previousMax count B.width QF)
    (hCQ : MatrixCopy.CopyForest M C T X P r maximal count B.width Q)
    (hPreviousLow : M.mem previous previousMax) (hLow : M.mem r maximal) (hOldS : RowBlocker M C A F P start)
    (hStart : M.SuccessorOf start r) (hPrev : M.mem prev C.omega) (hs : M.SuccessorOf next prev)
    (hNext : M.mem next count) (hRootMap : CopyCoordinates.ParentCopy M C T X next X.root child) :
    MatrixBlockerAt M C B QF Q start child := by
  have hw := omega_isOrdinal_d hM hC.omega
  have hLast := hContext.width_successor.predecessor_mem
  have hRootWidth := (hw.mem hA.width).transitive X.last hLast X.root hX.below
  have hPF := hRun.forests r P hP
  have hRootLast : Ancestor M C A.width P X.root X.last := by
    obtain ⟨_,he | ⟨P',_,hP',hAnc⟩⟩ := hContext.last_ascending_below_d hM hC hRun hLow
    · exact False.elim (SetTheory.KP.mem_irrefl_d (KP1Y.models_weakKP hM) X.root (he ▸ hX.below))
    · exact hRun.graph.unique r P' P hP' hP ▸ hAnc
  have hPrevCount := (hw.mem hCQ.count_nat).transitive next hNext prev hs.predecessor_mem
  have hRootZero := (hT.add.add_iff_sum hM hX.root hC.zero_nat).mpr (KP1Y.Arithmetic.sum_zero_d hM X.root hC.zero_empty)
  have hEncode := (CopyCoordinates.parent_copy_bad_iff (SetTheory.KP.mem_irrefl_d (KP1Y.models_weakKP hM) X.root)).mp hRootMap
  have hRootPos := (CopyCoordinates.encode_at_base_iff_d hM hC hT hX.root hC.zero_nat hRootMap.2.1 hRootZero).mp hEncode
  intro q _ p _ hPrevAt hCurAt hDistinct
  obtain ⟨oldQ,hOldQLast,hOldPrev,hMapQ⟩ := (hCF.root_low_parent_iff_d hM hC hT hX hCF.count_nat hNext hPrev hs hPreviousLow hRootPos q).mp hPrevAt
  obtain ⟨oldP,hOldPLast,hOldParent,hMapP⟩ := (hCQ.root_low_parent_iff_d hM hC hT hX hCQ.count_nat hNext hPrev hs hLow hRootPos p).mp hCurAt
  obtain ⟨J,hJ,hRows⟩ := hCQ.copy_embedding_d hM hC hT hX hPrevCount
  have hJP := (hRows oldP p).mpr ⟨hOldPLast,hMapP⟩
  have hJQ := (hRows oldQ q).mpr ⟨hOldQLast,hMapQ⟩
  have hOldDistinct : oldP≠oldQ := by
    intro he
    subst oldQ
    exact hDistinct (hJ.graph.unique oldP p q hJP hJQ)
  obtain ⟨z,hzWidth,hPath,hZParent,hLe⟩ := hOldS X.last hLast oldQ (hF.bounds hM.1 hOldPrev).2 oldP
    (hPF.bounds hM.1 hOldParent).2 hOldPrev hOldParent hOldDistinct
  have hzLast : M.mem z X.last := by
    rcases hPath with he | hAnc
    · exact he.symm ▸ hOldQLast
    · exact (hw.mem hX.last).transitive oldQ hOldQLast z hAnc.1
  have hBad := ancestor_le_parent_d hM hC hPF hOldParent hRootLast
  have hRootZ : M.mem X.root z := by
    rcases hBad with he | hlt
    · exact he.symm ▸ hPF.left z oldP hZParent
    · exact (hw.mem (hw.transitive A.width hA.width z hzWidth)).transitive oldP (hPF.left z oldP hZParent) X.root hlt
  have hzNonroot : z≠X.root := fun he => SetTheory.KP.mem_irrefl_d (KP1Y.models_weakKP hM) X.root (he ▸ hRootZ)
  obtain ⟨w,hwWidth,hJW⟩ := hJ.graph.total z hzLast
  have hMapZ := ((hRows z w).mp hJW).2
  refine ⟨w,hwWidth,?_,?_,?_⟩
  · rcases hPath with he | hAnc
    · subst z
      exact Or.inl (hJ.graph.unique oldQ w q hJW hJQ)
    · exact Or.inr ((hCQ.ancestor_bad_iff_d hM hC hT hX hPF hLast hPrevCount (Or.inr hRootZ) hzLast hOldQLast hMapZ hMapQ).mpr hAnc)
  · exact (hCQ.source_parent_nonroot_d hM hC hT hX hPF hCQ.count_nat hPrevCount hzLast hzNonroot hMapZ p).mpr
      ⟨oldP,hOldPLast,hZParent,hMapP⟩
  · have hSame : ParentRowsEqual M P X.last z := by
      intro t
      constructor
      · intro ht
        exact (hPF.unique X.last t oldP ht hOldParent).symm ▸ hZParent
      · intro ht
        exact (hPF.unique z t oldP ht hZParent).symm ▸ hOldParent
    let U : MatrixLiftParameters M.Domain := ⟨Forests,Rows,X.last,maximal,X.root,prev⟩
    have hLift := lifted_suffix_le_of_common_parent_d hM hC hA hT (U := U) hRun hLast hzWidth hX.below hRootZ
      hLast hRootWidth hPrev hP hStart hSame hLe
    obtain ⟨G,hG⟩ := ghost_column_exists_d hM hC hA hT (U := U) hLast hRootWidth hPrev
    have hNextBound : next=index ∨ M.mem next index := by
      rcases (hExp.copies next).mp hNext with hlt | he
      · exact Or.inr hlt
      · exact Or.inl (hM.1.eq_of_same_members next index he)
    have hLeft := newroot_suffix_lt_ghost_d hM hC hA hT hRun hContext hExp hIndex hPrev hs hNextBound hRootPos hG hLow hStart
    have hRight := lifted_suffix_le_realized_d hM.1 hG.matrix hExp.matrix hG.height hExp.height
      (hG.column_bound hC) hwWidth hG.entries (fun s v => hExp.parent_copy_entry_iff_d hM hC hA hT hX hLast hIndex hPrevCount hzLast hMapZ) hLift
    exact column_le_from_trans_d hM hC hExp.matrix hG.matrix hExp.matrix (Or.inr hLeft) hRight

/-- 所有列分支合并为整行S；上一行的高低标志仅作明确的内部数值边界。 -/
theorem row_blocker_expand_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {A B : FiniteMatrix M.Domain} (hA : A.Valid M C.omega)
    {T : MatrixArithmetic M.Domain} (hT : T.Valid M C) {X : CopyCoordinates.Context M.Domain} (hX : X.Valid M C)
    {Forests Rows L maximal index count total r F P previous previousMax QF Q start : M.Domain}
    (hRun : MatrixParentRun M C A.width A.height A.cells A.values Forests Rows L)
    (hContext : MatrixExpansionContext M C A Forests Rows X.last maximal X.root)
    (hExp : RawMatrixExpansion M C A T Forests Rows X.last maximal X.root index count X.length total B)
    (hIndex : M.mem index C.omega) (hP : MemPair M Rows r P) (hF : Forest M C.omega A.width F)
    (hCF : MatrixCopy.CopyForest M C T X F previous previousMax count B.width QF)
    (hCQ : MatrixCopy.CopyForest M C T X P r maximal count B.width Q)
    (hPreviousAbove : M.mem maximal r → ¬M.mem previous previousMax)
    (hPreviousBelow : r=maximal ∨ M.mem r maximal → M.mem previous previousMax)
    (hOldS : RowBlocker M C A F P start) (hStart : M.SuccessorOf start r) : RowBlocker M C B QF Q start := by
  have hw := omega_isOrdinal_d hM hC.omega
  have hLast := hContext.width_successor.predecessor_mem
  have hPF := hRun.forests r P hP
  have hrNat := hw.transitive A.height hA.height r (hRun.graph.bounds hM.1 hP).1
  have hMaxNat := hw.transitive A.height hA.height maximal hContext.row
  have hStartNat := natural_successor_mem_d hM hC hrNat hStart
  have hStartAbove (hHigh : ¬M.mem r maximal) : maximal=start ∨ M.mem maximal start := by
    apply Or.inr
    rcases hw.wellOrder.linear.compare r hrNat maximal hMaxNat with he | hlt | hgt
    · exact hM.1.eq_of_same_members r maximal he ▸ hStart.predecessor_mem
    · exact False.elim (hHigh hlt)
    · exact (hw.mem hStartNat).transitive r hStart.predecessor_mem maximal hgt
  have hRootLastBelow (hLow : M.mem r maximal) : Ancestor M C A.width P X.root X.last := by
    obtain ⟨_,he | ⟨P',_,hP',hAnc⟩⟩ := hContext.last_ascending_below_d hM hC hRun hLow
    · exact False.elim (SetTheory.KP.mem_irrefl_d (KP1Y.models_weakKP hM) X.root (he ▸ hX.below))
    · exact hRun.graph.unique r P' P hP' hP ▸ hAnc
  have hZeroCount : M.mem C.zero count := (hC.zero_mem_iff hM hCQ.count_nat).mpr
    (fun he => hC.zero_empty index (he ▸ hExp.copies.predecessor_mem))
  have hPrevPrefix := hCF.parent_prefix_d hM hC hT hX hF hCF.count_nat hZeroCount
  have hCurPrefix := hCQ.parent_prefix_d hM hC hT hX hPF hCQ.count_nat hZeroCount
  intro child hChild
  change MatrixBlockerAt M C B QF Q start child
  classical
  by_cases hPrefix : M.mem child X.last
  · exact blocker_at_expanded_prefix_d hM hC hA hT hExp hLast hX.below hIndex hF hPF hCQ.forest hPrevPrefix hCurPrefix hOldS hPrefix
  · rcases hCQ.column_cases_d hM hC hT hX hChild with hGood | ⟨copy,hCopy,slot,hSlot,source,hSource,hAdd,hPos⟩
    · exact False.elim (hPrefix ((hw.mem hX.last).transitive X.root hX.below child hGood))
    · have hCopyNat := hw.transitive count hCQ.count_nat copy hCopy
      have hSlotNat := hw.transitive X.length (hX.length_nat hM.1) slot hSlot
      have hSourceNat := hw.transitive X.last hX.last source hSource
      have hAfter := ordinal_subset_cases_d hM (hw.mem hX.root) (hw.mem hSourceNat)
        (KP1Y.Arithmetic.sum_base_subset_d hM (hw.mem hX.root) ((hT.add.add_iff_sum hM hX.root hSlotNat).mp hAdd))
      have hNotGood : ¬M.mem source X.root := by
        intro hGood
        rcases hAfter with he | hlt
        · exact SetTheory.KP.mem_irrefl_d (KP1Y.models_weakKP hM) X.root (he.symm ▸ hGood)
        · exact SetTheory.KP.mem_irrefl_d (KP1Y.models_weakKP hM) X.root ((hw.mem hX.root).transitive source hGood X.root hlt)
      have hMap := (CopyCoordinates.parent_copy_bad_iff hNotGood).mpr
        ((CopyCoordinates.encode_at_base_iff_d hM hC hT hX.root hSlotNat hCopyNat hAdd).mpr hPos)
      by_cases hNonroot : source≠X.root
      · by_cases hLow : M.mem r maximal
        · intro q hq p hp hPrevAt hCurAt hDistinct
          obtain ⟨oldP,_,hOldParent,_⟩ := (hCQ.source_parent_nonroot_d hM hC hT hX hPF hCQ.count_nat hCopy hSource hNonroot hMap p).mp hCurAt
          by_cases hGood : M.mem oldP X.root
          · exact blocker_at_copy_good_parent_d hM hC hA hT hX hRun hExp hLast hIndex hP hF hCF hCQ hOldS hStart hLow (hRootLastBelow hLow)
              hCopy hSource hNonroot hOldParent hGood hMap q hq p hp hPrevAt hCurAt hDistinct
          · have hpNat := hw.transitive A.width hA.width oldP (hPF.bounds hM.1 hOldParent).2
            have hBad : X.root=oldP ∨ M.mem X.root oldP := by
              rcases hw.wellOrder.linear.compare X.root hX.root oldP hpNat with he | hlt | hgt
              · exact Or.inl (hM.1.eq_of_same_members X.root oldP he)
              · exact Or.inr hlt
              · exact False.elim (hGood hgt)
            exact blocker_at_copy_bad_parent_d hM hC hA hT hX hRun hExp hLast hIndex hP hF hCF hCQ hOldS hStart
              hCopy hSource hOldParent hBad hMap q hq p hp hPrevAt hCurAt hDistinct
        · exact blocker_at_copy_high_d hM hC hA hT hX hRun hExp hLast hIndex hP hF hCQ hOldS hLow (hStartAbove hLow)
            hCopy hSource hMap (hCF.source_parent_nonroot_d hM hC hT hX hF hCF.count_nat hCopy hSource hNonroot hMap)
      · have hSourceRoot : source=X.root := Classical.byContradiction hNonroot
        subst source
        have hCopyNonzero : copy≠C.zero := by
          intro he
          subst copy
          obtain ⟨J,hJ,hRows⟩ := hCQ.copy_embedding_d hM hC hT hX hCopy
          have hEq := hJ.graph.unique X.root child X.root ((hRows X.root child).mpr ⟨hX.below,hMap⟩)
            ((hRows X.root X.root).mpr ⟨hX.below,CopyCoordinates.parent_copy_zero_d hM hC hT hX hX.root⟩)
          exact hPrefix (hEq.symm ▸ hX.below)
        obtain ⟨prev,hPrev,hs⟩ : ∃ prev, M.mem prev C.omega ∧ M.SuccessorOf copy prev := by
          rcases natural_cases hM hC.omega hCopyNat with he | hSucc
          · exact False.elim (hCopyNonzero (hM.1.eq_of_same_members copy C.zero (fun t => iff_of_false (he t) (hC.zero_empty t))))
          · exact hSucc
        by_cases hLow : M.mem r maximal
        · exact blocker_at_low_root_d hM hC hA hT hX hRun hContext hExp hIndex hP hF hCF hCQ (hPreviousBelow (Or.inr hLow))
            hLow hOldS hStart hPrev hs hCopy hMap
        · by_cases he : r=maximal
          · subst r
            exact blocker_at_critical_root_d hM hC hA hT hX hRun hContext hExp hIndex hP hF hCF hCQ
              (hPreviousBelow (Or.inl rfl)) hOldS hStart hPrev hs hCopy hMap
          · have hAbove : M.mem maximal r := by
              rcases hw.wellOrder.linear.compare r hrNat maximal hMaxNat with he' | hlt | hgt
              · exact False.elim (he (hM.1.eq_of_same_members r maximal he'))
              · exact False.elim (hLow hlt)
              · exact hgt
            exact blocker_at_copy_high_d hM hC hA hT hX hRun hExp hLast hIndex hP hF hCQ hOldS hLow (hStartAbove hLow)
              hCopy hX.below hMap (hCF.source_parent_high_d hM hC hT hX hF hCF.count_nat hCopy hX.below (hPreviousAbove hAbove) hMap)

/-- 实际raw展开保持给定内部边界以上的S，逐行构造来自实际旧/新父运行。 -/
theorem RawMatrixExpansion.aboveS_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {A B : FiniteMatrix M.Domain} (hA : A.Valid M C.omega)
    {T : MatrixArithmetic M.Domain} (hT : T.Valid M C) {X : CopyCoordinates.Context M.Domain} (hX : X.Valid M C)
    {Forests Rows L OtherForests Other OtherL maximal index count total base : M.Domain}
    (hRun : MatrixParentRun M C A.width A.height A.cells A.values Forests Rows L)
    (hContext : MatrixExpansionContext M C A Forests Rows X.last maximal X.root)
    (hExp : RawMatrixExpansion M C A T Forests Rows X.last maximal X.root index count X.length total B)
    (hOther : MatrixParentRun M C B.width B.height B.cells B.values OtherForests Other OtherL)
    (hIndex : M.mem index C.omega) (hS : AboveS M C A Forests Rows L base) : AboveS M C B OtherForests Other OtherL base := by
  have hw := omega_isOrdinal_d hM hC.omega
  have hLast := hContext.width_successor.predecessor_mem
  have hCountNat := natural_successor_mem_d hM hC hIndex hExp.copies
  have hMaxNat := hw.transitive A.height hA.height maximal hContext.row
  intro r hrB hBase QF hPrevious Q _ hQ start hStartNat hStart
  have hr : M.mem r A.height := hExp.height ▸ hrB
  obtain ⟨P,hPMem,hP⟩ := hRun.graph.total r hr
  have hCQ := hExp.parent_copy_rows_d hM hC hA hT hX hRun hContext hOther hIndex r P Q hP hQ
  rcases hPrevious with ⟨hrZero,hQF⟩ | ⟨j,hj,hs,_,hJQF⟩
  · subst r
    subst QF
    obtain ⟨F,hCF⟩ := MatrixCopy.copy_forest_exists_d hM hC hT hX hRun.linear.1 hCountNat hExp.product hExp.width
      (row := C.zero) (maximal := C.one)
    have hLinear := hCF.linear_d hM hC hT hX hRun.linear hLast hC.one_succ.predecessor_mem
    have hEq := linear_forest_unique hM.1 hLinear hOther.linear
    subst F
    exact row_blocker_expand_d hM hC hA hT hX hRun hContext hExp hIndex hP hRun.linear.1 hCF hCQ
      (fun h => False.elim (hC.zero_empty maximal h)) (fun _ => hC.one_succ.predecessor_mem)
      (hS C.zero hr hBase L (Or.inl ⟨rfl,rfl⟩) P hPMem hP start hStartNat hStart) hStart
  · have hjA : M.mem j A.height := hExp.height ▸ hj
    obtain ⟨F,hFMem,hJF⟩ := hRun.graph.total j hjA
    have hCF := hExp.parent_copy_rows_d hM hC hA hT hX hRun hContext hOther hIndex j F QF hJF hJQF
    have hAbove : M.mem maximal r → ¬M.mem j maximal := by
      intro hMR hJM
      rcases (hs maximal).mp hMR with hMJ | he
      · exact SetTheory.KP.mem_irrefl_d (KP1Y.models_weakKP hM) maximal ((hw.mem hMaxNat).transitive j hJM maximal hMJ)
      · have heq := hM.1.eq_of_same_members maximal j he
        exact SetTheory.KP.mem_irrefl_d (KP1Y.models_weakKP hM) maximal (heq.symm ▸ hJM)
    have hBelow : r=maximal ∨ M.mem r maximal → M.mem j maximal := by
      rintro (he | hRM)
      · exact he ▸ hs.predecessor_mem
      · exact (hw.mem hMaxNat).transitive r hRM j hs.predecessor_mem
    exact row_blocker_expand_d hM hC hA hT hX hRun hContext hExp hIndex hP (hRun.forests j F hJF) hCF hCQ hAbove hBelow
      (hS r hr hBase F (Or.inr ⟨j,hjA,hs,hFMem,hJF⟩) P hPMem hP start hStartNat hStart) hStart

/-- 从非退化context真正构造展开矩阵及父运行，同时保持I与相同边界以上的S。 -/
theorem relative_structural_expand_raw_exists_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {A : FiniteMatrix M.Domain} (hA : A.Valid M C.omega)
    {T : MatrixArithmetic M.Domain} (hT : T.Valid M C) {Forests Rows L last maximal root index base : M.Domain}
    (hRun : MatrixParentRun M C A.width A.height A.cells A.values Forests Rows L)
    (hContext : MatrixExpansionContext M C A Forests Rows last maximal root)
    (hIndex : M.mem index C.omega) (hI : MatrixDepthRegular M C A Forests Rows) (hS : AboveS M C A Forests Rows L base) :
    ∃ count len total B first OtherForests Other OtherL,
      let X : CopyCoordinates.Context M.Domain := ⟨last,root,len,first⟩
      X.Valid M C ∧ RawMatrixExpansion M C A T Forests Rows last maximal root index count len total B ∧
      MatrixParentRun M C B.width B.height B.cells B.values OtherForests Other OtherL ∧
      MatrixDepthRegular M C B OtherForests Other ∧ AboveS M C B OtherForests Other OtherL base := by
  obtain ⟨count,len,total,B,first,OtherForests,Other,OtherL,hX,hExp,hOther,_⟩ :=
    MatrixCopy.matrix_expand_raw_with_parent_copy_d hM hC hA hT hRun hContext hIndex
  exact ⟨count,len,total,B,first,OtherForests,Other,OtherL,hX,hExp,hOther,
    hExp.depth_regular_d hM hC hA hT hX hRun hContext hOther hIndex hI,
    hExp.aboveS_d hM hC hA hT hX hRun hContext hOther hIndex hS⟩

end KP1Y.OneYFinite
