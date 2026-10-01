import KP1Y.OneYCopyTower
import KP1Y.OneYFrameCopy
import KP1Y.OneYGraphPseudo
import KP1Y.OneYLowerValueTransport

/-! Y05b 规范重提取的逐层接口。Lower层(k<K)的单层结论由 LANE-B 独立证明；
本文件只给出精确对象命题，不含任何证明义务的替代。字段一一对应原
`LowerTowerInputs`/`LowerTowerRebuild` 所消费的 lower 单层引理。 -/
namespace KP1Y.OneYFinite.TowerCanon
open YesMetaZFC YesMetaZFC.SetTheory YesMetaZFC.SetTheory.Definitional
open KP1Y.Kuratowski KP1Y.Functions KP1Y.Naturals KP1Y.Bounded
open KP1Y.OneYFinite.CopiedMountain
universe u

/-- 上一层(k+1)底行的实际出口：在任意选出源k+1层父图的继承候选帧F中，
其FrameCopy选出目标底父图Pnext（原 `restrictedParent_bottom_numeric` /
`badAtTerminal_restrictedParent_external`）；以及非root副本行0父项按ParentCopy复制。 -/
def UpperSelect (M : SetTheory.Structure.{u}) (C : ExpressionData M.Domain) (T : MatrixArithmetic M.Domain)
    (A : CopyCoordinates.Context M.Domain) (m N n Vnext Qnext newTop Pnext : M.Domain) : Prop :=
  (∀ F F', Selects true M C m F Vnext Qnext → FrameCopy.Copies M C T A F N n F' →
    Selects true M C n F' newTop Pnext) ∧
  (∀ s b c, M.mem A.root s → M.mem s A.last → CopyCoordinates.ParentCopy M C T A b s c → M.mem c n →
    ∀ p, MemPair M Pnext c p ↔ ∃ q, MemPair M Qnext s q ∧ CopyCoordinates.ParentCopy M C T A b q p)

/-- 原 `LowerTowerInputs` 的四项输入。`oldTop` 为源k层实际Top（=源k+1层底值），
`Qnext` 为源k+1层父图，`newTop` 为塔重建在k+1处的实际行，`Pnext` 为目标k+1层底父图。
第四项 bound 以产生它的上层选择出口 `UpperSelect` 给出（原 bound 由此经
`pseudoTopBound_of_upper_selections` 导出，属于 lower 单层工作）。 -/
structure LowerInputs (M : SetTheory.Structure.{u}) (C : ExpressionData M.Domain) (T : MatrixArithmetic M.Domain)
    (D : Lower.Context M.Domain) (m N n oldTop Qnext newTop Pnext : M.Domain) : Prop where
  prefixTop : RowsAgreeOn M newTop oldTop D.coordinates.last
  fixed : Lower.UpperFixed M C T D oldTop Qnext n newTop
  order : ∀ Pseudo, GraphPseudoForest M C D.mountain Pseudo → Lower.UpperOrder M C T D Pseudo oldTop newTop
  select : UpperSelect M C T D.coordinates m N n oldTop Qnext newTop Pnext

/-- 实际源k层及其Lower复制的全部真实对象。`oldTop,Qnext` 是源k层实际提取。 -/
structure LowerLayerData (M : SetTheory.Structure.{u}) (C : ExpressionData M.Domain) (T : MatrixArithmetic M.Domain)
    (A : CopyCoordinates.Context M.Domain) (m : M.Domain) (L : LayerStateSpace M.Domain)
    (H K k n W Q J oldTop Qnext : M.Domain) (D : Lower.Context M.Domain) (Y : Data M.Domain) : Prop where
  lower : M.mem k K
  layer : RowAt M L.states H k W Q
  run : RowRun M C m L.rows W Q J
  from_run : FromRun M C m L.rows W J D.mountain
  extraction : Extraction M C m W Q oldTop Qnext
  coordinates : D.coordinates=A
  context : D.Valid M C
  target : Y.Valid M C
  copies : Lower.Copies M C T D n Y

/-- 一个 lower 层 k<K 的完整单层结论（LANE-B 目标）。
* rows      ↔ 原 `copiedBase_mountain`（同时给出实际Top=newTop）；
* extract   ↔ 原 `copiedBase_rawExtract`：目标伪父森林与某个选出源k+1层父图的帧之FrameCopy选择一致；
* bottom    ↔ 原 `restrictedParent_bottom_numeric`；
* nonroot   ↔ 原 `parent_zero_parentCopy`（非root副本行0父项）；
* down      ↔ 原 `badAtLowerCopiedBase_upperFixed/_upperOrder`（bound见 `LowerInputs`说明）。
`prefixTop`（原 `value_original_prefix_eq`）与 rootsOne 由已有通用定理导出，不列入。 -/
structure LowerLayerStep (M : SetTheory.Structure.{u}) (C : ExpressionData M.Domain) (T : MatrixArithmetic M.Domain)
    (A : CopyCoordinates.Context M.Domain) (m : M.Domain) (L : LayerStateSpace M.Domain) (H K k N n : M.Domain) : Prop where
  rows : ∀ {W Q J oldTop Qnext newTop Pnext Bottom : M.Domain} {D : Lower.Context M.Domain} {Y : Data M.Domain},
    LowerLayerData M C T A m L H K k n W Q J oldTop Qnext D Y →
    Graph M newTop n C.omega → (∀ c v, MemPair M newTop c v → M.mem C.zero v) →
    LowerInputs M C T D m N n oldTop Qnext newTop Pnext →
    MountainReconstruction.Rebuilds M C T.addPairs T.plus Y newTop Bottom →
    ∃ R : RowStateSpace M.Domain, ∃ P Run, RowRun M C n R Bottom P Run ∧ FromRun M C n R Bottom Run Y ∧
      TopValueGraph M C n R Run Y.heights newTop
  extract : ∀ {W Q J oldTop Qnext newTop Pnext G : M.Domain} {D : Lower.Context M.Domain} {Y : Data M.Domain},
    LowerLayerData M C T A m L H K k n W Q J oldTop Qnext D Y →
    Graph M newTop n C.omega → (∀ c v, MemPair M newTop c v → M.mem C.zero v) →
    LowerInputs M C T D m N n oldTop Qnext newTop Pnext → GraphPseudoForest M C Y G →
    ∃ F F', Selects true M C m F oldTop Qnext ∧ FrameCopy.Copies M C T A F N n F' ∧
      ∀ Q', Selects true M C n G newTop Q' ↔ Selects true M C n F' newTop Q'
  bottom : ∀ {W Q J oldTop Qnext newTop Pnext Bottom F F' P0 : M.Domain} {D : Lower.Context M.Domain} {Y : Data M.Domain},
    LowerLayerData M C T A m L H K k n W Q J oldTop Qnext D Y →
    Graph M newTop n C.omega → (∀ c v, MemPair M newTop c v → M.mem C.zero v) →
    LowerInputs M C T D m N n oldTop Qnext newTop Pnext →
    MountainReconstruction.Rebuilds M C T.addPairs T.plus Y newTop Bottom →
    Selects true M C m F W Q → FrameCopy.Copies M C T A F N n F' → MemPair M Y.parents C.zero P0 →
    Selects true M C n F' Bottom P0
  nonroot : ∀ {W Q J oldTop Qnext P0 s b c p : M.Domain} {D : Lower.Context M.Domain} {Y : Data M.Domain},
    LowerLayerData M C T A m L H K k n W Q J oldTop Qnext D Y → MemPair M Y.parents C.zero P0 →
    M.mem A.root s → M.mem s A.last → CopyCoordinates.ParentCopy M C T A b s c → M.mem c n →
    (MemPair M P0 c p ↔ ∃ q, MemPair M Q s q ∧ CopyCoordinates.ParentCopy M C T A b q p)
  down : ∀ {j W Q J oldTop Qnext newTop Pnext Bottom W' Q' J' oldTop' Qnext' : M.Domain}
      {D D' : Lower.Context M.Domain} {Y Y' : Data M.Domain}, M.SuccessorOf k j →
    LowerLayerData M C T A m L H K j n W' Q' J' oldTop' Qnext' D' Y' →
    LowerLayerData M C T A m L H K k n W Q J oldTop Qnext D Y →
    Graph M newTop n C.omega → (∀ c v, MemPair M newTop c v → M.mem C.zero v) →
    LowerInputs M C T D m N n oldTop Qnext newTop Pnext →
    MountainReconstruction.Rebuilds M C T.addPairs T.plus Y newTop Bottom →
    Lower.UpperFixed M C T D' oldTop' Qnext' n Bottom ∧
      ∀ Pseudo, GraphPseudoForest M C D'.mountain Pseudo → Lower.UpperOrder M C T D' Pseudo oldTop' Bottom

end KP1Y.OneYFinite.TowerCanon
