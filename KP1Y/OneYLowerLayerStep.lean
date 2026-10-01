import KP1Y.OneYTowerCanonInterface
import KP1Y.OneYReconstructionRecovery
import KP1Y.OneYLowerCopyNesting

/-! Lower单层(k<K)出口的汇合骨架。各部分（装饰阻挡、伪父Top界、提取、底行、非root、向下传递）
以精确对象命题列出；`rows` 字段在此由 `structural_rebuild_run_exists_d` 实际证明。
本文件不把任何部分当作已证明：最终 `lower_layer_step_d` 需各部分的实际定理实例化。 -/
namespace KP1Y.OneYFinite.LowerLayer
open YesMetaZFC YesMetaZFC.SetTheory YesMetaZFC.SetTheory.Definitional
open KP1Y.Kuratowski KP1Y.Functions KP1Y.Naturals KP1Y.Bounded
open KP1Y.OneYFinite.CopiedMountain KP1Y.OneYFinite.TowerCanon
universe u

/-- LANE-B2 出口：实际Lower复制在四项上层输入下的装饰阻挡。 -/
def BlockersPart (M : SetTheory.Structure.{u}) (C : ExpressionData M.Domain) (T : MatrixArithmetic M.Domain)
    (A : CopyCoordinates.Context M.Domain) (m : M.Domain) (L : LayerStateSpace M.Domain) (H K k N n : M.Domain) : Prop :=
  ∀ {W Q J oldTop Qnext newTop Pnext : M.Domain} {D : Lower.Context M.Domain} {Y : Data M.Domain},
    LowerLayerData M C T A m L H K k n W Q J oldTop Qnext D Y →
    Graph M newTop n C.omega → (∀ c v, MemPair M newTop c v → M.mem C.zero v) →
    LowerInputs M C T D m N n oldTop Qnext newTop Pnext →
    ReconstructionRecovery.DecoratedBlockers M C Y newTop

/-- 伪父Top界（原 badAtLowerCopiedBase_lowerTopBound），由 `LowerInputs.select` 导出。 -/
def BoundPart (M : SetTheory.Structure.{u}) (C : ExpressionData M.Domain) (T : MatrixArithmetic M.Domain)
    (A : CopyCoordinates.Context M.Domain) (m : M.Domain) (L : LayerStateSpace M.Domain) (H K k N n : M.Domain) : Prop :=
  ∀ {W Q J oldTop Qnext newTop Pnext : M.Domain} {D : Lower.Context M.Domain} {Y : Data M.Domain},
    LowerLayerData M C T A m L H K k n W Q J oldTop Qnext D Y →
    Graph M newTop n C.omega → (∀ c v, MemPair M newTop c v → M.mem C.zero v) →
    LowerInputs M C T D m N n oldTop Qnext newTop Pnext →
    ReconstructionSelection.PseudoTopBound M C Y newTop

/-- `bottom` 字段，另加本层伪父Top界。 -/
def BottomPart (M : SetTheory.Structure.{u}) (C : ExpressionData M.Domain) (T : MatrixArithmetic M.Domain)
    (A : CopyCoordinates.Context M.Domain) (m : M.Domain) (L : LayerStateSpace M.Domain) (H K k N n : M.Domain) : Prop :=
  ∀ {W Q J oldTop Qnext newTop Pnext Bottom F F' P0 : M.Domain} {D : Lower.Context M.Domain} {Y : Data M.Domain},
    LowerLayerData M C T A m L H K k n W Q J oldTop Qnext D Y →
    Graph M newTop n C.omega → (∀ c v, MemPair M newTop c v → M.mem C.zero v) →
    LowerInputs M C T D m N n oldTop Qnext newTop Pnext →
    ReconstructionSelection.PseudoTopBound M C Y newTop →
    MountainReconstruction.Rebuilds M C T.addPairs T.plus Y newTop Bottom →
    Selects true M C m F W Q → FrameCopy.Copies M C T A F N n F' → MemPair M Y.parents C.zero P0 →
    Selects true M C n F' Bottom P0

/-- `down` 字段，另加k层伪父Top界。 -/
def DownPart (M : SetTheory.Structure.{u}) (C : ExpressionData M.Domain) (T : MatrixArithmetic M.Domain)
    (A : CopyCoordinates.Context M.Domain) (m : M.Domain) (L : LayerStateSpace M.Domain) (H K k N n : M.Domain) : Prop :=
  ∀ {j W Q J oldTop Qnext newTop Pnext Bottom W' Q' J' oldTop' Qnext' : M.Domain}
      {D D' : Lower.Context M.Domain} {Y Y' : Data M.Domain}, M.SuccessorOf k j →
    LowerLayerData M C T A m L H K j n W' Q' J' oldTop' Qnext' D' Y' →
    LowerLayerData M C T A m L H K k n W Q J oldTop Qnext D Y →
    Graph M newTop n C.omega → (∀ c v, MemPair M newTop c v → M.mem C.zero v) →
    LowerInputs M C T D m N n oldTop Qnext newTop Pnext →
    ReconstructionSelection.PseudoTopBound M C Y newTop →
    MountainReconstruction.Rebuilds M C T.addPairs T.plus Y newTop Bottom →
    Lower.UpperFixed M C T D' oldTop' Qnext' n Bottom ∧
      ∀ Pseudo, GraphPseudoForest M C D'.mountain Pseudo → Lower.UpperOrder M C T D' Pseudo oldTop' Bottom

/-- `rows` 字段：实际重建底行的完整内部ω运行恰好恢复Lower复制图，Top恰为newTop。 -/
theorem lower_layer_rows_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {A : CopyCoordinates.Context M.Domain} {m : M.Domain} {L : LayerStateSpace M.Domain} {H K k N n : M.Domain}
    (hBlk : BlockersPart M C T A m L H K k N n) (hBnd : BoundPart M C T A m L H K k N n)
    {W Q J oldTop Qnext newTop Pnext Bottom : M.Domain} {D : Lower.Context M.Domain} {Y : Data M.Domain}
    (hData : LowerLayerData M C T A m L H K k n W Q J oldTop Qnext D Y)
    (hNew : Graph M newTop n C.omega) (hPos : ∀ c v, MemPair M newTop c v → M.mem C.zero v)
    (hInputs : LowerInputs M C T D m N n oldTop Qnext newTop Pnext)
    (hRebuild : MountainReconstruction.Rebuilds M C T.addPairs T.plus Y newTop Bottom) :
    ∃ R : RowStateSpace M.Domain, ∃ P Run, RowRun M C n R Bottom P Run ∧ FromRun M C n R Bottom Run Y ∧
      TopValueGraph M C n R Run Y.heights newTop := by
  have hWidth := hData.copies.width
  have hNested := hData.copies.nested_d hM hC hT hData.context hData.target hData.run hData.from_run
  obtain ⟨R,P,Run,hRun,hFrom,hTop,_⟩ := ReconstructionRecovery.structural_rebuild_run_exists_d hM hC hT.add hData.target
    (hWidth.symm ▸ hNew) hPos hRebuild hNested (hBnd hData hNew hPos hInputs) (hBlk hData hNew hPos hInputs)
  exact ⟨R,P,Run,hWidth ▸ hRun,hWidth ▸ hFrom,hWidth ▸ hTop⟩

/-- 由各部分的实际定理汇合完整单层结论（只做组装，不加入新的事实）。 -/
theorem lower_layer_step_of_parts_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {A : CopyCoordinates.Context M.Domain} {m : M.Domain} {L : LayerStateSpace M.Domain} {H K k N n : M.Domain}
    (hBlk : BlockersPart M C T A m L H K k N n) (hBnd : BoundPart M C T A m L H K k N n)
    (hExtract : ∀ {W Q J oldTop Qnext newTop Pnext G : M.Domain} {D : Lower.Context M.Domain} {Y : Data M.Domain},
      LowerLayerData M C T A m L H K k n W Q J oldTop Qnext D Y →
      Graph M newTop n C.omega → (∀ c v, MemPair M newTop c v → M.mem C.zero v) →
      LowerInputs M C T D m N n oldTop Qnext newTop Pnext → GraphPseudoForest M C Y G →
      ∃ F F', Selects true M C m F oldTop Qnext ∧ FrameCopy.Copies M C T A F N n F' ∧
        ∀ Q', Selects true M C n G newTop Q' ↔ Selects true M C n F' newTop Q')
    (hBottom : BottomPart M C T A m L H K k N n)
    (hNonroot : ∀ {W Q J oldTop Qnext P0 s b c p : M.Domain} {D : Lower.Context M.Domain} {Y : Data M.Domain},
      LowerLayerData M C T A m L H K k n W Q J oldTop Qnext D Y → MemPair M Y.parents C.zero P0 →
      M.mem A.root s → M.mem s A.last → CopyCoordinates.ParentCopy M C T A b s c → M.mem c n →
      (MemPair M P0 c p ↔ ∃ q, MemPair M Q s q ∧ CopyCoordinates.ParentCopy M C T A b q p))
    (hDown : DownPart M C T A m L H K k N n) :
    LowerLayerStep M C T A m L H K k N n where
  rows := fun hData hNew hPos hInputs hRebuild =>
    lower_layer_rows_d hM hC hT hBlk hBnd hData hNew hPos hInputs hRebuild
  extract := hExtract
  bottom := fun hData hNew hPos hInputs hRebuild hSel hFrame hP0 =>
    hBottom hData hNew hPos hInputs (hBnd hData hNew hPos hInputs) hRebuild hSel hFrame hP0
  nonroot := hNonroot
  down := fun hSucc hData' hData hNew hPos hInputs hRebuild =>
    hDown hSucc hData' hData hNew hPos hInputs (hBnd hData hNew hPos hInputs) hRebuild

end KP1Y.OneYFinite.LowerLayer
