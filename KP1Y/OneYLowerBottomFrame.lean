import KP1Y.OneYLowerBottomColumn
import KP1Y.OneYFrameCopy

/-! Lower底行恢复的三件工具：继承候选帧 FrameCopy 的祖先运输（原 `FrameCopy.ancestor_copy`）、
源底行（从帧F选出）的实际阻挡及其第1行起点KeyLE、以及目标重建中由KeyLE读出的数值弱序。 -/
namespace KP1Y.OneYFinite.LowerBlock
open YesMetaZFC YesMetaZFC.SetTheory YesMetaZFC.SetTheory.Definitional
open KP1Y.Kuratowski KP1Y.Functions KP1Y.Naturals KP1Y.Bounded KP1Y.Arithmetic
open KP1Y.OneYFinite KP1Y.OneYFinite.CopyCoordinates KP1Y.OneYFinite.CopiedMountain
open KP1Y.OneYFinite.CopiedMountain.Lower KP1Y.OneYFinite.LowerCanon
open KP1Y.OneYFinite.MountainReconstruction KP1Y.OneYFinite.ReconstructionCanonical
universe u

/-- 帧复制的祖先运输：源列 s∈(root,last]，其帧祖先 a<last；仅接缝列 s=last 需 root≤a。 -/
theorem frame_copy_ancestor_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {A : CopyCoordinates.Context M.Domain} (hA : A.Valid M C) {m F N n F' : M.Domain}
    (hF : Forest M C.omega m F) (hFC : FrameCopy.Copies M C T A F N n F')
    (hLast : M.mem A.last m) (hRootLast : Ancestor M C m F A.root A.last)
    {s a b c x : M.Domain} (hSource : Source M A s) (hEnc : Encode M C T A s b c) (hc : M.mem c n)
    (haLast : M.mem a A.last) (hAfterA : s=A.last → (A.root=a ∨ M.mem A.root a))
    (hMapA : ParentCopy M C T A b a x) (hAnc : Ancestor M C m F a s) : Ancestor M C n F' x c := by
  obtain ⟨count,_,hQ⟩ := hFC
  obtain ⟨total,hTotal,hWidth⟩ := hQ.width_geometry
  rcases hSource.2 with he | hBefore
  · subst s
    obtain ⟨next,hNext,hSucc,hPos⟩ := encode_seam_bms_d hM hC hT hA hEnc
    have hNextCount := (copy_position_lt_width_iff_d hM hC hT hA.root (hA.length_nat hM.1) hQ.count_nat hNext
      hTotal hWidth (hA.length_positive_d hM hC) hPos).mp hc
    exact (hQ.ancestor_previous_root_iff_d hM hC hT hA hF hLast hNextCount hEnc.2.1 hSucc
      hC.one_succ.predecessor_mem (hAfterA rfl) haLast hMapA hPos).mpr hAnc
  · obtain ⟨slot,hSlot,_,_,hPos⟩ := encode_nonseam_bms_d hM hC hT hA hSource.1 hBefore hEnc
    have hBlockCount := (copy_position_lt_width_iff_d hM hC hT hA.root (hA.length_nat hM.1) hQ.count_nat hEnc.2.1
      hTotal hWidth hSlot hPos).mp hc
    have hNotGood : ¬M.mem s A.root := fun h =>
      nat_irrefl hM A.root (((omega_isOrdinal_d hM hC.omega).mem hA.root).transitive s h A.root hSource.1)
    exact (hQ.ancestor_copy_iff_d hM hC hT hA hF hLast hBlockCount (fun _ => hRootLast) haLast hBefore hMapA
      ((parent_copy_bad_iff hNotGood).mpr hEnc)).mpr hAnc

/-- 源底行（由继承帧F选择）的实际阻挡，及第1行起点（C.one）的图层KeyLE。 -/
theorem source_bottom_blocker_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {m W Q J : M.Domain} {R : RowStateSpace M.Domain}
    (hRun : RowRun M C m R W Q J) (hPositive : ∀ c a, MemPair M W c a → M.mem C.zero a)
    {X : Data M.Domain} (hX : X.Valid M C) (hFrom : FromRun M C m R W J X)
    {Top : M.Domain} (hTop : TopValueGraph M C m R J X.heights Top)
    {F s q p : M.Domain} (hSel : Selects true M C m F W Q) (hOld : MemPair M F s q) (hNew : MemPair M Q s p) (hNe : p≠q) :
    ∃ z, M.mem z X.width ∧ (z=q ∨ Ancestor M C X.width Q z q) ∧ MemPair M Q z p ∧
      ∃ tc, M.mem tc C.omega ∧ ∃ tz, M.mem tz C.omega ∧ MemPair M Top s tc ∧ MemPair M Top z tz ∧
        ForestOrder.KeyLE M C X s z C.one tc tz := by
  obtain ⟨_,Wf,_,_,hRows,hFill⟩ := hSel.filled_selection_exists_d hM hC
    (fun c hc => False.elim (nat_irrefl hM C.zero (hPositive c C.zero hc)))
  obtain ⟨z,hzm,hPath,hZParent,hCompare⟩ := hFill.blocker_d hM hC hOld hNew hNe
  have hRow0 := hRun.base
  have hAt0 := hRun.initial_row_at_d hM
  obtain ⟨W1,Q1,hAt1⟩ := hRun.at_exists_d hC.one_nat
  have hStep := hRun.at_next hM.1 hC.one_succ hAt0 hAt1
  have hRow1 := hRun.at_numeric_d hM hC hAt1
  have hsm : M.mem s m := (hRow0.forest.bounds hM.1 hNew).1
  obtain ⟨a,ha,hAValue⟩ := hRow0.values.total s hsm
  obtain ⟨b,hb,hBValue⟩ := hRow0.values.total z hzm
  have hFilledOf (c v : M.Domain) (hv : M.mem v C.omega) (hV : MemPair M W c v) : MemPair M Wf c v :=
    (hRows c v).mpr ⟨v,hv,hV,Or.inr ⟨fun he => nat_irrefl hM C.zero (he ▸ hPositive c v hV),rfl⟩⟩
  have hAB := hCompare a b (hFilledOf s a ha hAValue) (hFilledOf z b hb hBValue)
  obtain ⟨x,_,hXV⟩ := hRow1.values.total s hsm
  obtain ⟨y,_,hYV⟩ := hRow1.values.total z hzm
  have hLe := NumericOrder.difference_mono_common_parent_d hM hC hRow0 hStep.difference hNew hZParent
    hAValue hBValue hAB hXV hYV
  have hSame : ParentRowsEqual M Q s z := by
    intro e
    constructor
    · intro hParent
      exact (hRow0.forest.unique s e p hParent hNew).symm ▸ hZParent
    · intro hParent
      exact (hRow0.forest.unique z e p hParent hZParent).symm ▸ hNew
  have hCommon : NumericOrder.CommonAncestors M C m Q s z :=
    fun e _ => ancestor_iff_of_parent_rows_eq_d hM hC hRow0.forest hSame e
  obtain ⟨tc,htc,hTC⟩ := hTop.graph.total s hsm
  obtain ⟨tz,htz,hTZ⟩ := hTop.graph.total z hzm
  have hKey := NumericOrder.key_le_of_common_values_d hM hC hRun hPositive hFrom.heights hTop hTC hTZ hAt1
    hStep.selection (NumericOrder.row_next_zeros_at_roots_d hM hC hRow0 hStep) hCommon hXV hYV
    ((hRow0.difference_positive_iff_d hM hC hStep.difference hXV).mpr ⟨p,hNew⟩)
    ((hRow0.difference_positive_iff_d hM hC hStep.difference hYV).mpr ⟨p,hZParent⟩) hLe
  refine ⟨z,hFrom.width.symm ▸ hzm,hPath.imp id (fun h => hFrom.width.symm ▸ h),hZParent,tc,htc,tz,htz,hTC,hTZ,?_⟩
  exact (ForestOrder.from_run_key_iff_d hM hC hRun hX hFrom s z C.one tc tz).mpr hKey

/-- 目标重建：s行共同父的两列，若自 succ s 起 KeyLE，则 s 行实际重建值弱序（只用不低于base的行选择）。 -/
theorem key_value_le_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {Pairs Plus : M.Domain} (hPlus : AdditionTable M C Pairs Plus)
    {X : Data M.Domain} (hX : X.Valid M C) {Top B Parents H base : M.Domain}
    (hTop : Graph M Top X.width C.omega) (hPositive : ∀ c top, MemPair M Top c top → M.mem C.zero top)
    (hB : SequenceBound M C X.width X.heights B) (hParents : Prefix M Parents X.parents B X.forests)
    (hH : Reconstruction.Reconstructs M (grid C X Top Pairs Plus B Parents) H)
    (hCanon : ∀ r s V W F Q, M.mem r C.omega → (base=r ∨ M.mem base r) → M.SuccessorOf s r →
      RowValues M (grid C X Top Pairs Plus B Parents) H r V → RowValues M (grid C X Top Pairs Plus B Parents) H s W →
      MemPair M X.parents r F → MemPair M X.parents s Q → Selects true M C X.width F W Q)
    {s t W Q c z p tc tz : M.Domain} (hs : M.mem s C.omega) (hBase : base=s ∨ M.mem base s) (hNext : M.SuccessorOf t s)
    (hW : RowValues M (grid C X Top Pairs Plus B Parents) H s W) (hQ : MemPair M X.parents s Q)
    (hCP : MemPair M Q c p) (hZP : MemPair M Q z p) (hTC : MemPair M Top c tc) (hTZ : MemPair M Top z tz)
    (hKey : ForestOrder.KeyLE M C X c z t tc tz) : ∀ x y, MemPair M W c x → MemPair M W z y → x=y ∨ M.mem x y := by
  intro x y hWX hWY
  have hD := grid_valid_d hM hC hX hTop hPlus hB hParents
  have hNumeric := hW.numeric_d hM hC hPlus hX hTop hPositive hB hParents hH hQ
  have ht := natural_successor_mem_d hM hC hs hNext
  obtain ⟨Z,hZ⟩ := row_values_exists_d hM hD hH ht
  obtain ⟨x',hx',hZX⟩ := hZ.graph.total c (hNumeric.forest.bounds hM.1 hCP).1
  obtain ⟨y',hy',hZY⟩ := hZ.graph.total z (hNumeric.forest.bounds hM.1 hZP).1
  have hDiffNext := hW.difference_d hM hC hPlus hX hTop hB hParents hH hZ hQ hNext
  have hXPos := (hNumeric.difference_positive_iff_d hM hC hDiffNext hZX).mpr ⟨p,hCP⟩
  have hYPos := (hNumeric.difference_positive_iff_d hM hC hDiffNext hZY).mpr ⟨p,hZP⟩
  have hSame : ParentRowsEqual M Q c z := by
    intro a
    constructor
    · intro h
      exact (hNumeric.forest.unique c a p h hCP).symm ▸ hZP
    · intro h
      exact (hNumeric.forest.unique z a p h hZP).symm ▸ hCP
  have hCompare := (ReconstructionOrder.key_iff_value_le_d hM hC hPlus hX hTop hPositive hB hParents hH hCanon
    hs hBase hNext ⟨Q,(hX.parents.bounds hM.1 hQ).2,hQ,hSame⟩
    ((hZ.rows c x').mp hZX) ((hZ.rows z y').mp hZY) hXPos hYPos hTC hTZ).mp hKey
  obtain ⟨parentValue,hPV,hParentValue⟩ := hW.graph.total p (hNumeric.forest.bounds hM.1 hCP).2
  have hParentC : CopiedMountain.ParentAt M X s c p := ⟨Q,(hX.parents.bounds hM.1 hQ).2,hQ,hCP⟩
  have hParentZ : CopiedMountain.ParentAt M X s z p := ⟨Q,(hX.parents.bounds hM.1 hQ).2,hQ,hZP⟩
  have hSumC := ((hW.rows c x).mp hWX).parent_sum_d hM hD hH ((grid_parent_iff_d hM hC hX hB hParents).mpr hParentC) hNext
    ((hZ.rows c x').mp hZX) ((hW.rows p parentValue).mp hParentValue)
  have hSumZ := ((hW.rows z y).mp hWY).parent_sum_d hM hD hH ((grid_parent_iff_d hM hC hX hB hParents).mpr hParentZ) hNext
    ((hZ.rows z y').mp hZY) ((hW.rows p parentValue).mp hParentValue)
  rcases hCompare with he | hlt
  · subst y'
    exact Or.inl (hPlus.add_unique hM.1 hSumC hSumZ)
  · exact Or.inr (natural_sum_strict_left_d hM hC hx' hy' hPV
      ((hPlus.add_iff_sum hM hx' hPV).mp hSumC) ((hPlus.add_iff_sum hM hy' hPV).mp hSumZ) hlt)

end KP1Y.OneYFinite.LowerBlock
