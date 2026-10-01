import KP1Y.OneYCopyTower
import KP1Y.OneYOrdinaryCopyNesting
import KP1Y.OneYTerminalCopyNesting
import KP1Y.OneYLowerCopyNesting

/-! 真实坏根生成的三分支复制塔逐层满足实际父森林嵌套。 -/
namespace KP1Y.OneYFinite.CopyTower
open YesMetaZFC YesMetaZFC.SetTheory YesMetaZFC.SetTheory.Definitional
open KP1Y.Kuratowski KP1Y.Functions KP1Y.Naturals KP1Y.Bounded
open KP1Y.OneYFinite.CopiedMountain
universe u

theorem Branch.nested_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {m : M.Domain} {L : LayerStateSpace M.Domain} {V P H K level k W Q J n : M.Domain}
    (hLayers : LayerRun M C m L V P H) {A : CopyCoordinates.Context M.Domain} (hA : A.Valid M C)
    (hBad : BadAt M C m L H K level A.last A.root) (hLayer : RowAt M L.states H k W Q)
    (hRun : RowRun M C m L.rows W Q J) {X Y : Data M.Domain} (hX : X.Valid M C) (hY : Y.Valid M C)
    (hFrom : FromRun M C m L.rows W J X) (h : Branch M C T A X K level k n Y) : Nested M C Y := by
  rcases h with ⟨_,D,_,hDX,hD,hCopy⟩ | ⟨hk,hCopy⟩ | ⟨_,hCopy⟩
  · exact hCopy.nested_d hM hC hT hD hY hRun (hDX.symm ▸ hFrom)
  · subst k
    exact hCopy.nested_d hM hC hT hA hX hY hRun hFrom
      (Terminal.active_from_bad_d hM hC hLayers hBad hLayer hRun hX hFrom)
  · exact hCopy.nested_d hM hC hT hA hX hY hRun hFrom

theorem Tower.nested_at_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {m : M.Domain} {L : LayerStateSpace M.Domain} {V P H K level B n Forests CodeSpace G k code heights parents : M.Domain}
    (hLayers : LayerRun M C m L V P H) {A : CopyCoordinates.Context M.Domain} (hA : A.Valid M C)
    (hBad : BadAt M C m L H K level A.last A.root) (h : Tower M C T A m L H K level B n Forests CodeSpace G)
    (hAt : MemPair M G k code) (hCode : Codes M code heights parents) : Nested M C ⟨n,heights,Forests,parents⟩ := by
  obtain ⟨hY,source,sH,sP,hSource,hSC,hBranch⟩ := (((h.rows k code).mp hAt).2).read hM.1 hCode
  obtain ⟨W,Q,J,hLayer,hRun,hX,hFrom⟩ := hSource.read hM.1 hSC
  exact hBranch.nested_d hM hC hT hLayers hA hBad hLayer hRun hX hY hFrom

end KP1Y.OneYFinite.CopyTower
