import KP1Y.OneYTowerCanonAssembly
import KP1Y.OneYTowerCanonInduction
import KP1Y.OneYLowerUpperInputs

/-! 实际展开所用的完整塔数据包，以及逐层读取源运行/塔码的基本事实。
全部字段都是实际展开 `Expansion.Successful` 中的真实对象。 -/
namespace KP1Y.OneYFinite.TowerCanon
open YesMetaZFC YesMetaZFC.SetTheory YesMetaZFC.SetTheory.Definitional
open KP1Y.Kuratowski KP1Y.Functions KP1Y.Naturals KP1Y.Bounded
open KP1Y.OneYFinite.CopiedMountain
universe u

/-- 源层运行、坏根、horizon=max(严格界的前驱)、实际复制塔、倒序重建运行与全1顶部。 -/
structure Setting (M : SetTheory.Structure.{u}) (C : ExpressionData M.Domain) (T : MatrixArithmetic M.Domain)
    (A : CopyCoordinates.Context M.Domain) (m : M.Domain) (L : LayerStateSpace M.Domain)
    (V P H K level B strict N n Forests CodeSpace G Nr Top Hr : M.Domain) : Prop where
  layers : LayerRun M C m L V P H
  coordinates : A.Valid M C
  last : M.SuccessorOf m A.last
  bad : BadAt M C m L H K level A.last A.root
  index : M.mem N C.omega
  width : CopyCoordinates.Width M C T A N n
  bound : SequenceBound M C m V strict
  horizon : M.SuccessorOf strict B
  tower : CopyTower.Tower M C T A m L H K level B n Forests CodeSpace G
  run : TowerReconstruction.Run M C T.addPairs T.plus n Forests CodeSpace G B Nr Top Hr
  top : TowerReconstruction.AllOne M C n Top

variable {M : SetTheory.Structure.{u}} {C : ExpressionData M.Domain} {T : MatrixArithmetic M.Domain}
  {A : CopyCoordinates.Context M.Domain} {m : M.Domain} {L : LayerStateSpace M.Domain}
  {V P H K level B strict N n Forests CodeSpace G Nr Top Hr : M.Domain}

theorem Setting.indices_d (hM : M.Models KP1Y.theory) (hC : C.Valid M)
    (h : Setting M C T A m L V P H K level B strict N n Forests CodeSpace G Nr Top Hr) :
    M.mem K C.omega ∧ M.mem level C.omega ∧ M.mem A.last m ∧ M.mem A.root m :=
  CopyTower.bad_indices_d hM hC h.layers h.bad

theorem Setting.valid_codes (h : Setting M C T A m L V P H K level B strict N n Forests CodeSpace G Nr Top Hr) :
    ∀ k code, MemPair M G k code → CodeValid M C n Forests code :=
  fun _ _ hAt => h.tower.code_valid hAt

/-- 活动层严格低于horizon：K<B。 -/
theorem Setting.active_lt_d (hM : M.Models KP1Y.theory) (hC : C.Valid M)
    (h : Setting M C T A m L V P H K level B strict N n Forests CodeSpace G Nr Top Hr) : M.mem K B := by
  have hw := omega_isOrdinal_d hM hC.omega
  have hK := (h.indices_d hM hC).1
  obtain ⟨a,_,hLayerValue,hAbove⟩ := h.bad.layer_value_d hM hC
  obtain ⟨initial,_,hInitial⟩ := h.layers.base.row.values.total A.last (h.indices_d hM hC).2.2.1
  have hKInitial := h.layers.above_one_layer_lt_initial_d hM hC hK hLayerValue hInitial hAbove
  have hInitialStrict := h.bound.value_lt hM.1 h.layers.base.row.values hInitial
  rcases (h.horizon initial).mp hInitialStrict with hlt | he
  · exact (hw.mem h.tower.bound).transitive initial hlt K hKInitial
  · exact (hM.1.eq_of_same_members initial B he) ▸ hKInitial

/-- horizon以上(含)的源层全为1。 -/
theorem Setting.source_one_d (hM : M.Models KP1Y.theory) (hC : C.Valid M)
    (h : Setting M C T A m L V P H K level B strict N n Forests CodeSpace G Nr Top Hr)
    {k c v : M.Domain} (hk : M.mem k C.omega) (hBk : B=k ∨ M.mem B k) (hValue : LayerValue M L H k c v) : v=C.one :=
  h.layers.all_one_from_bound_predecessor_d hM hC h.bound h.horizon hk hBk hValue

/-- 塔第k层的完整实际读数：目标码、源码、源层行运行及三分支。 -/
theorem Setting.layer_read_d (hM : M.Models KP1Y.theory)
    (h : Setting M C T A m L V P H K level B strict N n Forests CodeSpace G Nr Top Hr) {k : M.Domain} (hk : M.mem k B) :
    ∃ code heights parents sHeights sParents W Q J, MemPair M G k code ∧ Codes M code heights parents ∧
      (⟨n,heights,Forests,parents⟩ : Data M.Domain).Valid M C ∧
      RowAt M L.states H k W Q ∧ RowRun M C m L.rows W Q J ∧
      (⟨m,sHeights,L.rows.forests,sParents⟩ : Data M.Domain).Valid M C ∧
      FromRun M C m L.rows W J ⟨m,sHeights,L.rows.forests,sParents⟩ ∧
      CopyTower.Branch M C T A ⟨m,sHeights,L.rows.forests,sParents⟩ K level k n ⟨n,heights,Forests,parents⟩ := by
  obtain ⟨code,heights,parents,_,hAt,hCode,hY,source,sH,sP,hSource,hSC,hBranch⟩ := h.tower.mountain_at_d hk
  obtain ⟨W,Q,J,hLayer,hRun,hX,hFrom⟩ := hSource.read hM.1 hSC
  exact ⟨code,heights,parents,sH,sP,W,Q,J,hAt,hCode,hY,hLayer,hRun,hX,hFrom,hBranch⟩

/-- 源第k层的实际提取恰为第k+1层。 -/
theorem Setting.source_next_d (hM : M.Models KP1Y.theory) (hC : C.Valid M)
    (h : Setting M C T A m L V P H K level B strict N n Forests CodeSpace G Nr Top Hr)
    {k k' W Q : M.Domain} (hk : M.mem k C.omega) (hs : M.SuccessorOf k' k) (hLayer : RowAt M L.states H k W Q) :
    ∃ W' Q', RowAt M L.states H k' W' Q' ∧ Extraction M C m W Q W' Q' := by
  obtain ⟨W',Q',hLayer'⟩ := h.layers.at_exists_d (natural_successor_mem_d hM hC hk hs)
  exact ⟨W',Q',hLayer',h.layers.at_next hM.1 hs hLayer hLayer'⟩

/-- 源行运行的实际Top等于源下一层的底值。 -/
theorem Setting.source_top_d (hM : M.Models KP1Y.theory) (hC : C.Valid M)
    (h : Setting M C T A m L V P H K level B strict N n Forests CodeSpace G Nr Top Hr)
    {k W Q J sHeights sParents k' W' Q' : M.Domain}
    (hLayer : RowAt M L.states H k W Q) (hRun : RowRun M C m L.rows W Q J)
    (hFrom : FromRun M C m L.rows W J ⟨m,sHeights,L.rows.forests,sParents⟩)
    (hs : M.SuccessorOf k' k) (hLayer' : RowAt M L.states H k' W' Q') :
    TopValueGraph M C m L.rows J sHeights W' :=
  CopiedMountain.Lower.adjacent_source_top_d hM hC h.layers hs hLayer hLayer' hRun hFrom

end KP1Y.OneYFinite.TowerCanon
