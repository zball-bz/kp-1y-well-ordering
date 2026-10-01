import KP1Y.OneYMatrixCopyRun
import KP1Y.OneYMatrixStructuralDefs

/-! 实际raw展开的深度正规性(I)保持；父行复制已由真实算法证明。 -/
namespace KP1Y.OneYFinite
open YesMetaZFC YesMetaZFC.SetTheory YesMetaZFC.SetTheory.Definitional
open KP1Y.Kuratowski KP1Y.Functions KP1Y.Naturals KP1Y.Bounded
open KP1Y.Arithmetic
universe u

private def RegularAt (M : SetTheory.Structure.{u}) (C : ExpressionData M.Domain)
    (A : FiniteMatrix M.Domain) (P r c : M.Domain) : Prop :=
  ∀ d, M.mem d C.omega → MatrixEntry M A r c d →
    (NoParent M A.width P c → d=C.zero) ∧ ∀ p, M.mem p A.width → MemPair M P c p →
      ∀ e, M.mem e C.omega → MatrixEntry M A r p e → M.SuccessorOf d e

/-- 父子同时加上同一个实际复制增量，保持自然数后继关系。 -/
theorem lifted_values_successor_of_flags_equal_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {A : FiniteMatrix M.Domain} (hA : A.Valid M C.omega)
    {T : MatrixArithmetic M.Domain} (hT : T.Valid M C) {U : MatrixLiftParameters M.Domain} {c p r a b x y : M.Domain}
    (hAEntry : MatrixEntry M A r c a) (hBEntry : MatrixEntry M A r p b) (hs : M.SuccessorOf a b)
    (hFlags : Ascending M C A.width U.forests U.rows U.maximal U.root c r ↔
      Ascending M C A.width U.forests U.rows U.maximal U.root p r)
    (hX : LiftedEntry M C A T U.forests U.rows U.last U.maximal U.root U.copy c r x)
    (hY : LiftedEntry M C A T U.forests U.rows U.last U.maximal U.root U.copy p r y) : M.SuccessorOf x y := by
  obtain ⟨a',ha,hA',hX⟩ := hX
  obtain ⟨b',hb,hB',hY⟩ := hY
  have hAA := hA.entry_unique hM.1 hA' hAEntry
  have hBB := hA.entry_unique hM.1 hB' hBEntry
  subst a'
  subst b'
  rcases hX with ⟨hFlag,d,_,t,ht,hD,hTimes,hPlus⟩ | ⟨hNot,hx⟩ <;>
    rcases hY with ⟨hFlag',d',_,t',_,hD',hTimes',hPlus'⟩ | ⟨hNot',hy⟩
  · have hDD := row_increment_unique_d hM hA hT.diff hD hD'
    subst d'
    have hTT := hT.mul.mul_unique hM.1 hTimes hTimes'
    subst t'
    exact natural_sum_left_successor_d hM hC ht hs ((hT.add.add_iff_sum hM hb ht).mp hPlus')
      ((hT.add.add_iff_sum hM ha ht).mp hPlus)
  · exact False.elim (hNot' (hFlags.mp hFlag))
  · exact False.elim (hNot (hFlags.mpr hFlag'))
  · exact hx.symm ▸ hy.symm ▸ hs

private theorem regular_fixed_column_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {A B : FiniteMatrix M.Domain} (hA : A.Valid M C.omega)
    {T : MatrixArithmetic M.Domain} (hT : T.Valid M C) {X : CopyCoordinates.Context M.Domain} (hX : X.Valid M C)
    {Forests Rows maximal index count total r P Q source child : M.Domain}
    (hExp : RawMatrixExpansion M C A T Forests Rows X.last maximal X.root index count X.length total B)
    (hLast : M.mem X.last A.width) (hIndex : M.mem index C.omega)
    (hP : Forest M C.omega A.width P) (hQ : Forest M C.omega B.width Q) (hSource : M.mem source X.last)
    (hOld : RegularAt M C A P r source)
    (hEntries : ∀ d, MatrixEntry M B r child d ↔ MatrixEntry M A r source d)
    (hParents : ∀ p, MemPair M Q child p ↔ MemPair M P source p) : RegularAt M C B Q r child := by
  intro d hd hEntry
  have hRegular := hOld d hd ((hEntries d).mp hEntry)
  refine ⟨?_,?_⟩
  · intro hNone
    apply hRegular.1
    intro p _ hParent
    have hNew := (hParents p).mpr hParent
    exact hNone p (hQ.bounds hM.1 hNew).2 hNew
  · intro p _ hParent e he hEntryP
    have hOldParent := (hParents p).mp hParent
    have hpLast := ((omega_isOrdinal_d hM hC.omega).mem hX.last).transitive source hSource p (hP.left source p hOldParent)
    exact hRegular.2 p (hP.bounds hM.1 hOldParent).2 hOldParent e he
      ((hExp.prefix_entry_iff_d hM hC hA hT hLast hX.below hIndex hpLast).mp hEntryP)

private theorem regular_lifted_nonroot_column_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {A B : FiniteMatrix M.Domain} (hA : A.Valid M C.omega)
    {T : MatrixArithmetic M.Domain} (hT : T.Valid M C) {X : CopyCoordinates.Context M.Domain} (hX : X.Valid M C)
    {Forests Rows L maximal index count total r P Q copy source child : M.Domain}
    (hRun : MatrixParentRun M C A.width A.height A.cells A.values Forests Rows L)
    (hExp : RawMatrixExpansion M C A T Forests Rows X.last maximal X.root index count X.length total B)
    (hLast : M.mem X.last A.width) (hIndex : M.mem index C.omega) (hP : MemPair M Rows r P)
    (hQ : Forest M C.omega B.width Q) (_hSource : M.mem source A.width) (hNonroot : source≠X.root)
    (hCopy : M.mem copy count) (hOld : RegularAt M C A P r source)
    (hParentBound : ∀ p, MemPair M P source p → M.mem p X.last)
    (hEntries : ∀ d, MatrixEntry M B r child d ↔ LiftedEntry M C A T Forests Rows X.last maximal X.root copy source r d)
    (hParents : ∀ t, MemPair M Q child t ↔ ∃ p, M.mem p X.last ∧ MemPair M P source p ∧ CopyCoordinates.ParentCopy M C T X copy p t) :
    RegularAt M C B Q r child := by
  have hw := omega_isOrdinal_d hM hC.omega
  have hr := (hRun.graph.bounds hM.1 hP).1
  have hPF := hRun.forests r P hP
  have hCountNat := natural_successor_mem_d hM hC hIndex hExp.copies
  have hCopyNat := hw.transitive count hCountNat copy hCopy
  intro d hd hEntry
  have hLift := (hEntries d).mp hEntry
  have hLiftData := hLift
  obtain ⟨a,ha,hAEntry,_⟩ := hLiftData
  have hRegular := hOld a ha hAEntry
  refine ⟨?_,?_⟩
  · intro hNone
    have hOldNone : NoParent M A.width P source := by
      intro p hp hParent
      obtain ⟨J,hJ,hRows⟩ := CopyCoordinates.parent_copy_graph_exists_d hM hC hT hX hCopyNat
      obtain ⟨t,_,hMap⟩ := hJ.graph.total p (hw.transitive A.width hA.width p hp)
      have hNew := (hParents t).mpr ⟨p,hParentBound p hParent,hParent,(hRows p t).mp hMap⟩
      exact hNone t (hQ.bounds hM.1 hNew).2 hNew
    have hNot : ¬Ascending M C A.width Forests Rows maximal X.root source r := by
      intro hAsc
      obtain ⟨_,he | hAnc⟩ := (hRun.ascending_at_d hM.1 hP).mp hAsc
      · exact hNonroot he
      · obtain ⟨p,hParent,_⟩ := ancestor_parent_cases_d hM hC hPF hAnc
        exact hOldNone p (hPF.bounds hM.1 hParent).2 hParent
    exact (hA.entry_unique hM.1 ((lifted_entry_unascending_iff hM.1 hA hNot).mp hLift) hAEntry).trans (hRegular.1 hOldNone)
  · intro t _ hParent e _ hEntryP
    obtain ⟨p,hp,hOldParent,hMap⟩ := (hParents t).mp hParent
    have hpWidth := (hPF.bounds hM.1 hOldParent).2
    obtain ⟨b,hb,hBEntry⟩ := hA.entry_total_d hM hr hpWidth
    have hSucc := hRegular.2 p hpWidth hOldParent b hb hBEntry
    have hLiftP := (hExp.parent_copy_entry_iff_d hM hC hA hT hX hLast hIndex hCopy hp hMap).mp hEntryP
    exact lifted_values_successor_of_flags_equal_d hM hC hA hT (U := ⟨Forests,Rows,X.last,maximal,X.root,copy⟩)
      hAEntry hBEntry hSucc (hRun.ascending_parent_iff_d hM hC hP hOldParent hNonroot).symm hLift hLiftP

/-- 实际raw展开保持完整I；任意真实输出父运行均可消费，无父复制假设残留。 -/
theorem RawMatrixExpansion.depth_regular_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {A B : FiniteMatrix M.Domain} (hA : A.Valid M C.omega)
    {T : MatrixArithmetic M.Domain} (hT : T.Valid M C) {X : CopyCoordinates.Context M.Domain} (hX : X.Valid M C)
    {Forests Rows L OtherForests Other OtherL maximal index count total : M.Domain}
    (hRun : MatrixParentRun M C A.width A.height A.cells A.values Forests Rows L)
    (hContext : MatrixExpansionContext M C A Forests Rows X.last maximal X.root)
    (hExp : RawMatrixExpansion M C A T Forests Rows X.last maximal X.root index count X.length total B)
    (hOther : MatrixParentRun M C B.width B.height B.cells B.values OtherForests Other OtherL)
    (hIndex : M.mem index C.omega) (hI : MatrixDepthRegular M C A Forests Rows) : MatrixDepthRegular M C B OtherForests Other := by
  have hw := omega_isOrdinal_d hM hC.omega
  have hLast := hContext.width_successor.predecessor_mem
  have hSourceSub := (hw.mem hA.width).transitive X.last hLast
  have hRootWidth := hSourceSub X.root hX.below
  intro r hr Q _ hQ child hChild
  have hrA : M.mem r A.height := hExp.height ▸ hr
  obtain ⟨P,hPMem,hP⟩ := hRun.graph.total r hrA
  have hCF := hExp.parent_copy_rows_d hM hC hA hT hX hRun hContext hOther hIndex r P Q hP hQ
  have hPF := hRun.forests r P hP
  have hPrefix := hExp.parent_prefix_d hM hC hA hT hRun hOther hLast hX.below hIndex r P Q hP hQ
  have hOld (s : M.Domain) (hs : M.mem s A.width) : RegularAt M C A P r s := hI r hrA P hPMem hP s hs
  have hRegular : RegularAt M C B Q r child := by
    rcases hCF.column_cases_d hM hC hT hX hChild with hGood | ⟨copy,hCopy,slot,hSlot,source,hSource,hAdd,hPos⟩
    · have hChildLast := (hw.mem hX.last).transitive X.root hX.below child hGood
      exact regular_fixed_column_d hM hC hA hT hX hExp hLast hIndex hPF hCF.forest hChildLast (hOld child (hSourceSub child hChildLast))
        (fun d => hExp.prefix_entry_iff_d hM hC hA hT hLast hX.below hIndex hChildLast)
        (fun p => (hPrefix child hChildLast p).symm)
    · have hCopyNat := hw.transitive count hCF.count_nat copy hCopy
      have hSlotNat := hw.transitive X.length (hX.length_nat hM.1) slot hSlot
      have hSourceNat := hw.transitive X.last hX.last source hSource
      have hAfter := ordinal_subset_cases_d hM (hw.mem hX.root) (hw.mem hSourceNat)
        (sum_base_subset_d hM (hw.mem hX.root) ((hT.add.add_iff_sum hM hX.root hSlotNat).mp hAdd))
      have hNotGood : ¬M.mem source X.root := by
        intro hGood
        rcases hAfter with he | hlt
        · exact SetTheory.KP.mem_irrefl_d (KP1Y.models_weakKP hM) X.root (he.symm ▸ hGood)
        · exact SetTheory.KP.mem_irrefl_d (KP1Y.models_weakKP hM) X.root ((hw.mem hX.root).transitive source hGood X.root hlt)
      have hMap := (CopyCoordinates.parent_copy_bad_iff hNotGood).mpr
        ((CopyCoordinates.encode_at_base_iff_d hM hC hT hX.root hSlotNat hCopyNat hAdd).mpr hPos)
      classical
      by_cases hNonroot : source≠X.root
      · exact regular_lifted_nonroot_column_d hM hC hA hT hX hRun hExp hLast hIndex hP hCF.forest
          (hSourceSub source hSource) hNonroot hCopy (hOld source (hSourceSub source hSource))
          (fun p hParent => (hw.mem hX.last).transitive source hSource p (hPF.left source p hParent))
          (fun d => hExp.parent_copy_entry_iff_d hM hC hA hT hX hLast hIndex hCopy hSource hMap)
          (hCF.source_parent_nonroot_d hM hC hT hX hPF hCF.count_nat hCopy hSource hNonroot hMap)
      · have hEq : source=X.root := Classical.byContradiction hNonroot
        subst source
        have hRootZero := (hT.add.add_iff_sum hM hX.root hC.zero_nat).mpr (sum_zero_d hM X.root hC.zero_empty)
        have hEncode := (CopyCoordinates.parent_copy_bad_iff (SetTheory.KP.mem_irrefl_d (KP1Y.models_weakKP hM) X.root)).mp hMap
        have hRootPos := (CopyCoordinates.encode_at_base_iff_d hM hC hT hX.root hC.zero_nat hCopyNat hRootZero).mp hEncode
        by_cases hFixed : copy=C.zero ∨ ¬M.mem r maximal
        · apply regular_fixed_column_d hM hC hA hT hX hExp hLast hIndex hPF hCF.forest hX.below (hOld X.root hRootWidth)
          · intro d
            apply (hExp.parent_copy_entry_iff_d hM hC hA hT hX hLast hIndex hCopy hX.below hMap).trans
            rcases hFixed with he | hHigh
            · subst copy
              exact lifted_entry_zero_iff_d hM hC hA hT hLast hRootWidth
            · exact lifted_entry_unascending_iff hM.1 hA (fun h => hHigh h.1)
          · exact hCF.root_high_parent_iff_d hM hC hT hX hCF.count_nat hCopy hFixed hRootPos
        · have hLow : M.mem r maximal := Classical.byContradiction (fun h => hFixed (Or.inr h))
          have hCopyNonzero : copy≠C.zero := fun h => hFixed (Or.inl h)
          obtain ⟨prev,hPrev,hs⟩ : ∃ prev, M.mem prev C.omega ∧ M.SuccessorOf copy prev := by
            rcases natural_cases hM hC.omega hCopyNat with he | hSucc
            · exact False.elim (hCopyNonzero (hM.1.eq_of_same_members copy C.zero (fun t => iff_of_false (he t) (hC.zero_empty t))))
            · exact hSucc
          have hPrevCount := (hw.mem hCF.count_nat).transitive copy hCopy prev hs.predecessor_mem
          have hLastNonroot : X.last≠X.root := fun he => SetTheory.KP.mem_irrefl_d (KP1Y.models_weakKP hM) X.root (he ▸ hX.below)
          exact regular_lifted_nonroot_column_d hM hC hA hT hX hRun hExp hLast hIndex hP hCF.forest hLast hLastNonroot hPrevCount
            (hOld X.last hLast) (fun p hParent => hPF.left X.last p hParent)
            (fun d => hExp.seam_entry_iff_d hM hC hA hT hX hRun hContext hIndex hLow hPrev hs hCopy hMap)
            (hCF.root_low_parent_iff_d hM hC hT hX hCF.count_nat hCopy hPrev hs hLow hRootPos)
  exact hRegular

end KP1Y.OneYFinite
