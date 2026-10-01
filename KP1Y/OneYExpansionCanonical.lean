import KP1Y.OneYReconstructionRecovery
import KP1Y.OneYTerminalTopBound
import KP1Y.OneYTerminalCopyNesting

/-! 实际展开规范性汇合。当前先闭合Terminal内部数值行恢复；
整个提取塔及底行外部候选森林的识别仍须后续独立接口。 -/
namespace KP1Y.OneYFinite.ExpansionCanonical
open YesMetaZFC YesMetaZFC.SetTheory YesMetaZFC.SetTheory.Definitional
open KP1Y.Kuratowski KP1Y.Functions KP1Y.Naturals KP1Y.Bounded
open ReconstructionCanonical Reconstruction MountainReconstruction ReconstructionRecovery
universe u

/-- 从真正RowBadAt解除Terminal内部各行的所有选择/结构归纳条件。 -/
theorem terminal_rebuild_rows_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
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
    (hRebuild : Rebuilds M C T.addPairs T.plus Y NewTop Bottom) :
    ∃ R' : RowStateSpace M.Domain, ∃ P' Run, RowRun M C Y.width R' Bottom P' Run ∧
      CopiedMountain.FromRun M C Y.width R' Bottom Run Y ∧ TopValueGraph M C Y.width R' Run Y.heights NewTop ∧
      (∀ c v, MemPair M Bottom c v → M.mem C.zero v) := by
  have hActive : CopiedMountain.Terminal.Active M X A level := by
    have hBad' := hBad
    obtain ⟨W,_,Q,_,hAt,hParent,_⟩ := hBad'
    have hP : CopiedMountain.ParentAt M X level A.last A.root := (hFrom.parent_iff hM.1 hX level A.last A.root).mpr ⟨W,Q,hAt,hParent⟩
    obtain ⟨height,_,hHeight⟩ := hX.heights.total A.last (hP.bounds hM.1 hX).2.1
    exact ⟨hP,height,hHeight,(row_bad_height_top_d hM hC hRun hBase hFrom.heights hOldTop hBad hHeight).1⟩
  have hNested := hCopy.nested_d hM hC hT hA hX hY hRun hFrom hActive
  have hTopBound := TerminalTopBound.terminal_pseudo_top_bound_d hM hC hT hA hX hY hRun hFrom hBase.positive hOldTop hActive hCopy hTop
  obtain ⟨Top',hTop',hBlocker⟩ := TerminalCanonical.row_bad_blocker_exists_d hM hC hT hRun hBase hX hFrom hOldTop hA hWidth hBad hIndex hN hY hCopy
  have he := (hCopy.width.symm ▸ hTop').unique hM.1 hTop
  subst Top'
  have hBlockers : DecoratedBlockers M C Y NewTop := by
    intro r s t F Q c q p hSucc hNext hF hQ hOld hNew hNe
    exact hBlocker r s t c q p Q hSucc hNext ⟨F,(hY.parents.bounds hM.1 hF).2,hF,hOld⟩
      ⟨Q,(hY.parents.bounds hM.1 hQ).2,hQ,hNew⟩ hQ hNe
  have hPositive : ∀ c v, MemPair M NewTop c v → M.mem C.zero v := by
    intro c v hAt
    obtain ⟨_,source,_,_,_,_,hOld⟩ := (hTop.rows c v).mp hAt
    obtain ⟨a,_,hVA⟩ := hRun.base.values.total source (hOldTop.graph.bounds hM.1 hOld).1
    exact hOldTop.positive_d hM hC hRun hFrom.heights hVA (hBase.positive source a hVA) hOld
  exact structural_rebuild_run_exists_d hM hC hT.add hY hTop.graph hPositive hRebuild hNested hTopBound hBlockers

end KP1Y.OneYFinite.ExpansionCanonical
