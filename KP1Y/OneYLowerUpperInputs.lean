import KP1Y.OneYLowerValueTransport
import KP1Y.OneYExpansionPrefix

/-! 真实相邻层输入读取；本层newTop是塔重建图在succ k处的实际序列。 -/
namespace KP1Y.OneYFinite.CopiedMountain.Lower
open YesMetaZFC YesMetaZFC.SetTheory YesMetaZFC.SetTheory.Definitional
open KP1Y.Kuratowski KP1Y.Functions KP1Y.Naturals KP1Y.Bounded
universe u

/-- 明确从实际塔的相邻两项读取重建关系，不使用额外宿主层函数。 -/
theorem tower_step_rebuild_d {M : SetTheory.Structure.{u}} (he : Extensional M)
    {C : ExpressionData M.Domain} {Pairs Plus width Forests CodeSpace G B N Top H k next Bottom NewTop code heights parents : M.Domain}
    (hG : Graph M G B CodeSpace) (hRun : TowerReconstruction.Run M C Pairs Plus width Forests CodeSpace G B N Top H)
    (hk : M.mem k B) (hNext : M.SuccessorOf next k) (hLower : MemPair M H k Bottom) (hUpper : MemPair M H next NewTop)
    (hAt : MemPair M G k code) (hCode : Codes M code heights parents) :
    MountainReconstruction.Rebuilds M C Pairs Plus ⟨width,heights,Forests,parents⟩ NewTop Bottom := by
  obtain ⟨code',_,hAt',heights',parents',hCode',hBuild⟩ := hRun.transition k hk next hNext NewTop Bottom hUpper hLower
  have hCC := hG.unique k code' code hAt' hAt
  subst code'
  obtain ⟨hh,hp⟩ := codes_injective he hCode' hCode
  subst heights'
  subst parents'
  exact hBuild

theorem tower_upper_top_graph {M : SetTheory.Structure.{u}} {C : ExpressionData M.Domain}
    {Pairs Plus width Forests CodeSpace G B N Top H next NewTop : M.Domain}
    (hRun : TowerReconstruction.Run M C Pairs Plus width Forests CodeSpace G B N Top H)
    (hUpper : MemPair M H next NewTop) : Graph M NewTop width C.omega := hRun.values next NewTop hUpper

/-- 源低层oldTop恰是源相邻提取层的底值图。 -/
theorem adjacent_source_top_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {m : M.Domain} {L : LayerStateSpace M.Domain}
    {V P H k next W Q OldTop UpperP J : M.Domain}
    (hLayers : LayerRun M C m L V P H) (hNext : M.SuccessorOf next k)
    (hLower : RowAt M L.states H k W Q) (hUpper : RowAt M L.states H next OldTop UpperP)
    (hRows : RowRun M C m L.rows W Q J) {X : Data M.Domain} (hFrom : FromRun M C m L.rows W J X) :
    TopValueGraph M C m L.rows J X.heights OldTop :=
  Expansion.extraction_top_for_source_d hM hC hRows hFrom (hLayers.at_next hM.1 hNext hLower hUpper)

end KP1Y.OneYFinite.CopiedMountain.Lower
