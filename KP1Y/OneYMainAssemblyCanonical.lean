import KP1Y.OneYMainAssembly
import KP1Y.OneYCanonicalExpansion

/-! 协调者汇合（第二段）：Y05b 的全塔规范性（LANE-C `canonical_copy_bound_last_d`）接到 Y06 接口
`CopyDescent.CanonicalCopyBoundIn`，从而接到闭句。剩余前提只有 Terminal 底行四出口
`TowerCanon.TerminalExits`（LANE-D）与逐层 Lower 规范性 `CanonicalExpansion.LowerStepsIn`（LANE-B/B2/F）。 -/
namespace KP1Y.OneYTheorem
open YesMetaZFC YesMetaZFC.SetTheory YesMetaZFC.SetTheory.Definitional
open KP1Y.OneYFinite
universe u

/-- LANE-C 的出口与 Y06 接口逐字同形。 -/
theorem canonical_copy_bound_in_of_steps {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    (hExits : TowerCanon.TerminalExits M) (hLower : CanonicalExpansion.LowerStepsIn M) :
    CopyDescent.CanonicalCopyBoundIn M :=
  CanonicalExpansion.canonical_copy_bound_last_d hM hExits hLower

theorem canonical_copy_bound_of_steps
    (hExits : ∀ M : SetTheory.Structure.{u}, M.Models KP1Y.theory → TowerCanon.TerminalExits M)
    (hLower : ∀ M : SetTheory.Structure.{u}, M.Models KP1Y.theory → CanonicalExpansion.LowerStepsIn M) :
    CopyDescent.CanonicalCopyBound.{u} :=
  fun M hM => canonical_copy_bound_in_of_steps hM (hExits M hM) (hLower M hM)

/-- 闭句的 Hilbert 推导：仅余 Terminal 底行四出口与逐层 Lower 规范性。 -/
theorem main_derivable_of_steps
    (hExits : ∀ M : SetTheory.Structure.{0}, M.Models KP1Y.theory → TowerCanon.TerminalExits M)
    (hLower : ∀ M : SetTheory.Structure.{0}, M.Models KP1Y.theory → CanonicalExpansion.LowerStepsIn M) :
    KP1Y.Derives mainSentence :=
  main_derivable_of_canonical_bound (canonical_copy_bound_of_steps hExits hLower)

end KP1Y.OneYTheorem
