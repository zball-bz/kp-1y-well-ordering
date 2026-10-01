import KP1Y.OneYReconstructionRecovery

/-! Lower阻挡的源端：真实源RowRun逐行产生装饰阻挡（图层KeyLE），不假设任何目标规范性。 -/
namespace KP1Y.OneYFinite.LowerBlock
open YesMetaZFC YesMetaZFC.SetTheory YesMetaZFC.SetTheory.Definitional
open KP1Y.Kuratowski KP1Y.Functions KP1Y.Naturals KP1Y.Bounded
open KP1Y.OneYFinite
universe u

/-- 源行r→s=succ r 的实际阻挡，比较起点 t=succ s；Top为源实际Top图。 -/
theorem source_row_blocker_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {m V P H : M.Domain} {R : RowStateSpace M.Domain}
    (hRun : RowRun M C m R V P H) (hPositive : ∀ c a, MemPair M V c a → M.mem C.zero a)
    {X : CopiedMountain.Data M.Domain} (hX : X.Valid M C) (hFrom : CopiedMountain.FromRun M C m R V H X)
    {Top : M.Domain} (hTop : TopValueGraph M C m R H X.heights Top)
    {r s t F Q c q p : M.Domain} (hSucc : M.SuccessorOf s r) (hNext : M.SuccessorOf t s)
    (hF : MemPair M X.parents r F) (hQ : MemPair M X.parents s Q)
    (hOld : MemPair M F c q) (hNew : MemPair M Q c p) (hNe : p≠q) :
    ∃ z, M.mem z X.width ∧ (z=q ∨ Ancestor M C X.width Q z q) ∧ MemPair M Q z p ∧
      ∃ tc, M.mem tc C.omega ∧ ∃ tz, M.mem tz C.omega ∧ MemPair M Top c tc ∧ MemPair M Top z tz ∧
        ForestOrder.KeyLE M C X c z t tc tz := by
  obtain ⟨U,hAtR⟩ := (hFrom.parents r F).mp hF
  obtain ⟨W,hAtS⟩ := (hFrom.parents s Q).mp hQ
  have hRowR := hRun.at_numeric_d hM hC hAtR
  have hRowS := hRun.at_numeric_d hM hC hAtS
  have hStep := hRun.at_next hM.1 hSucc hAtR hAtS
  obtain ⟨z,hzm,hPath,hZParent,hCompare⟩ := NumericOrder.row_next_blocker_d hM hC hRowR hStep hOld hNew hNe
  have hs : M.mem s C.omega := (hX.parents.bounds hM.1 hQ).1
  have ht := natural_successor_mem_d hM hC hs hNext
  obtain ⟨WN,QN,hAtT⟩ := hRun.at_exists_d ht
  have hRowT := hRun.at_numeric_d hM hC hAtT
  have hStepT := hRun.at_next hM.1 hNext hAtS hAtT
  have hcm : M.mem c m := (hRowS.forest.bounds hM.1 hNew).1
  obtain ⟨a,_,hAValue⟩ := hRowS.values.total c hcm
  obtain ⟨b,_,hBValue⟩ := hRowS.values.total z hzm
  obtain ⟨x,_,hXV⟩ := hRowT.values.total c hcm
  obtain ⟨y,_,hYV⟩ := hRowT.values.total z hzm
  have hLe := NumericOrder.difference_mono_common_parent_d hM hC hRowS hStepT.difference hNew hZParent
    hAValue hBValue (hCompare a b hAValue hBValue) hXV hYV
  have hSame : ParentRowsEqual M Q c z := by
    intro e
    constructor
    · intro hParent
      exact (hRowS.forest.unique c e p hParent hNew).symm ▸ hZParent
    · intro hParent
      exact (hRowS.forest.unique z e p hParent hZParent).symm ▸ hNew
  have hCommon : NumericOrder.CommonAncestors M C m Q c z :=
    fun e _ => ancestor_iff_of_parent_rows_eq_d hM hC hRowS.forest hSame e
  obtain ⟨tc,htc,hTC⟩ := hTop.graph.total c hcm
  obtain ⟨tz,htz,hTZ⟩ := hTop.graph.total z hzm
  have hKey := NumericOrder.key_le_of_common_values_d hM hC hRun hPositive hFrom.heights hTop hTC hTZ hAtT
    hStepT.selection (NumericOrder.row_next_zeros_at_roots_d hM hC hRowS hStepT) hCommon hXV hYV
    ((hRowS.difference_positive_iff_d hM hC hStepT.difference hXV).mpr ⟨p,hNew⟩)
    ((hRowS.difference_positive_iff_d hM hC hStepT.difference hYV).mpr ⟨p,hZParent⟩) hLe
  refine ⟨z,hFrom.width.symm ▸ hzm,hPath.imp id (fun h => hFrom.width.symm ▸ h),hZParent,tc,htc,tz,htz,hTC,hTZ,?_⟩
  exact (ForestOrder.from_run_key_iff_d hM hC hRun hX hFrom c z t tc tz).mpr hKey

/-- 源山形自身满足 `DecoratedBlockers`。 -/
theorem source_decorated_blockers_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {m V P H : M.Domain} {R : RowStateSpace M.Domain}
    (hRun : RowRun M C m R V P H) (hPositive : ∀ c a, MemPair M V c a → M.mem C.zero a)
    {X : CopiedMountain.Data M.Domain} (hX : X.Valid M C) (hFrom : CopiedMountain.FromRun M C m R V H X)
    {Top : M.Domain} (hTop : TopValueGraph M C m R H X.heights Top) :
    ReconstructionRecovery.DecoratedBlockers M C X Top := by
  intro r s t F Q c q p hSucc hNext hF hQ hOld hNew hNe
  exact source_row_blocker_d hM hC hRun hPositive hX hFrom hTop hSucc hNext hF hQ hOld hNew hNe

end KP1Y.OneYFinite.LowerBlock
