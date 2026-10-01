import KP1Y.OneYTowerCanonExits
import KP1Y.OneYCanonHelperUpperOrder

/-! 把 H1–H4 打包为 LANE-C 汇合所需的 `TowerCanon.TerminalExits`；每个字段直接由对应定理给出。 -/
namespace KP1Y.OneYFinite.TerminalBase
open YesMetaZFC YesMetaZFC.SetTheory YesMetaZFC.SetTheory.Definitional
universe u

theorem terminal_exits_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory) : TowerCanon.TerminalExits M where
  select := fun ⟨hC,hT,hRun,hBase,hX,hFrom,hOldTop,hA,hWidth,hBad,hIndex,hN,hY,hCopy,hTop,hRebuild⟩ hF hF' hP0 =>
    terminal_base_select_d hM hC hT hRun hBase hX hFrom hOldTop hA hWidth hBad hIndex hN hY hCopy hTop hRebuild hF hF' hP0
  nonroot := fun ⟨hC,hT,hRun,hBase,hX,hFrom,hOldTop,hA,hWidth,hBad,hIndex,hN,hY,hCopy,hTop,hRebuild⟩ hP0 hs hsx hMap hc =>
    terminal_base_nonroot_d hM hC hT hRun hBase hX hFrom hOldTop hA hWidth hBad hIndex hN hY hCopy hTop hRebuild
      hP0 hs hsx hMap hc
  fixed := fun ⟨hC,hT,hRun,hBase,hX,hFrom,hOldTop,hA,hWidth,hBad,hIndex,hN,hY,hCopy,hTop,hRebuild⟩ hD =>
    terminal_base_upper_fixed_d hM hC hT hRun hBase hX hFrom hOldTop hA hWidth hBad hIndex hN hY hCopy hTop hRebuild hD
  order := fun ⟨hC,hT,hRun,hBase,hX,hFrom,hOldTop,hA,hWidth,hBad,hIndex,hN,hY,hCopy,hTop,hRebuild⟩ hD hF =>
    terminal_base_upper_order_d hM hC hT hRun hBase hX hFrom hOldTop hA hWidth hBad hIndex hN hY hCopy hTop hRebuild hD hF

end KP1Y.OneYFinite.TerminalBase
