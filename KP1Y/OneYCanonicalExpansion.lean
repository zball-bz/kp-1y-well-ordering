import KP1Y.OneYTowerCanonLower
import KP1Y.OneYCopyDescent

/-! Y05b 最终出口：实际坏根分支的展开输出 t 的规范根图 A(t)（用 t 自身预算计算）
宽度等于 Width(N)，且每条边都是同一实际复制塔在 Width(N) 处枚举的复制图之边。
horizon 以上的层由塔高处全1顶部与层值反单调排除。 -/
namespace KP1Y.OneYFinite.CanonicalExpansion
open YesMetaZFC YesMetaZFC.SetTheory YesMetaZFC.SetTheory.Definitional
open KP1Y.Kuratowski KP1Y.Functions KP1Y.Naturals KP1Y.Bounded
open KP1Y.OneYFinite.TowerCanon KP1Y.OneYFinite.ExpressionDiagram
universe u

/-- 唯一的 lower 单层临时前提（LANE-B 目标）：任意实际成功展开的每个 lower 层。 -/
def LowerStepsIn (M : SetTheory.Structure.{u}) : Prop :=
  ∀ (E : ExpressionData M.Domain) (T : MatrixArithmetic M.Domain), E.Valid M → T.Valid M E →
    ∀ s m last N t (W : Expansion.SuccessData M.Domain), Expansion.Successful M E T s m last N t W →
    ∀ k, M.mem k W.K → LowerLayerStep M E T W.coordinates m W.space W.layers W.K k N W.width

/-- `CopyDescent.CanonicalCopyBoundIn` 加上原末列前提 `m=last+1`（调用处 `expand_last_representation_lower_d`
已有 `hSucc`）。 -/
def CanonicalCopyBoundLastIn (M : SetTheory.Structure.{u}) : Prop :=
  ∀ (E : ExpressionData M.Domain) (T : MatrixArithmetic M.Domain) (D : Reflection.Data M.Domain),
    E.Valid M → T.Valid M E → D.Valid M → D.omega=E.omega →
    ∀ s m last N t (W : Expansion.SuccessData M.Domain), Expansion.Successful M E T s m last N t W →
    M.SuccessorOf m last →
    ∀ Old, CopyDiagram.Enumerated M E T D ⟨W.horizon,W.width,W.forests,W.codes,W.tower⟩ Old →
    ∀ n B, ExpressionGraph M E T D t n B → ∀ k q p c, Reflection.EdgeAt M D B k q p c → Reflection.EdgeAt M D Old k q p c

/-- 实际成功展开给出完整塔数据包；t 是塔倒序重建在 0 处的行。 -/
theorem setting_of_successful_d {M : SetTheory.Structure.{u}} {E : ExpressionData M.Domain}
    {T : MatrixArithmetic M.Domain} {s m last N t : M.Domain} {W : Expansion.SuccessData M.Domain}
    (hS : Expansion.Successful M E T s m last N t W) (hSucc : M.SuccessorOf m last) :
    ∃ strict Nr Hr, Setting M E T W.coordinates m W.space s W.initial W.layers W.K W.level W.horizon strict N W.width
      W.forests W.codes W.tower Nr W.top Hr ∧ MemPair M Hr E.zero t := by
  obtain ⟨strict,_,hBound,hHorizon⟩ := hS.horizon
  obtain ⟨Nr,Hr,hRun,hAt⟩ := hS.reconstruction
  have hBad : BadAt M E m W.space W.layers W.K W.level W.coordinates.last W.coordinates.root := by
    rw [hS.last,hS.root]
    exact hS.bad
  exact ⟨strict,Nr,Hr,⟨hS.run,hS.coordinates,hS.last.symm ▸ hSucc,hBad,hS.width.2.1,hS.width,hBound,hHorizon,
    hS.tower,hRun,hS.top⟩,hAt⟩

/-- t 的每个实际根图原子都是复制塔(horizon=W.horizon,宽 Width(N))的原子。 -/
theorem expansion_atom_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory) (hExits : TerminalExits M)
    {E : ExpressionData M.Domain} (hE : E.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M E)
    {s m last N t : M.Domain} {W : Expansion.SuccessData M.Domain}
    (hS : Expansion.Successful M E T s m last N t W) (hSucc : M.SuccessorOf m last)
    (hLower : ∀ k, M.mem k W.K → LowerLayerStep M E T W.coordinates m W.space W.layers W.K k N W.width)
    {F0 P0 H' : M.Domain} {L' : LayerStateSpace M.Domain}
    (hLinear : LinearForest M E.omega W.width F0) (hP0 : Selects true M E W.width F0 t P0)
    (hLayers : LayerRun M E W.width L' t P0 H') {k q p c : M.Domain} (hAtom : ActualAtom M E W.width L' H' k q p c) :
    CopyDiagram.Atom M E ⟨W.horizon,W.width,W.forests,W.codes,W.tower⟩ k q p c := by
  obtain ⟨strict,Nr,Hr,h,hT0⟩ := setting_of_successful_d hS hSucc
  obtain ⟨Sources,Gs,hGs⟩ := CopyTower.source_graph_exists_d hM hE h.layers h.tower.bound
  obtain ⟨hCanon,hSelect⟩ := h.tower_canon_d hM hE hT hExits hLower
  have hBase := h.base_select_d hM hE hT hExits hLower hGs hS.linear hS.selected
  exact tower_atom_d hM hE h.tower.bound ⟨W.K,h.active_lt_d hM hE⟩ h.tower.graph h.tower.forests h.valid_codes
    h.run h.top hT0 hLinear hP0 hLayers hCanon hSelect hBase hAtom

/-- **Y05b 最终规范重提取定理**（Terminal 出口 H1–H4 与 lower 单层为显式前提）：
宽度 n=Width(N)，且 A(t) 的每条边都是同一实际塔在 Width(N) 处复制图的边。 -/
theorem canonical_expansion_diagram_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory) (hExits : TerminalExits M)
    {E : ExpressionData M.Domain} (hE : E.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M E)
    {D : Reflection.Data M.Domain} (hD : D.Valid M) (hOmega : D.omega=E.omega)
    {s m last N t : M.Domain} {W : Expansion.SuccessData M.Domain}
    (hS : Expansion.Successful M E T s m last N t W) (hSucc : M.SuccessorOf m last)
    (hLower : ∀ k, M.mem k W.K → LowerLayerStep M E T W.coordinates m W.space W.layers W.K k N W.width)
    {Old n B : M.Domain} (hOld : CopyDiagram.Enumerated M E T D ⟨W.horizon,W.width,W.forests,W.codes,W.tower⟩ Old)
    (hGraph : ExpressionGraph M E T D t n B) :
    n=W.width ∧ ∀ k q p c, Reflection.EdgeAt M D B k q p c → Reflection.EdgeAt M D Old k q p c := by
  obtain ⟨hLegal,F0,P0,L',H',hLinear,hP0,hLayers,hEnum⟩ := hGraph
  have hnW := legal_length_unique hM.1 hLegal (hS.legal_d hM hE hT)
  subst n
  refine ⟨rfl,?_⟩
  intro k q p c hEdge
  have hAtom := (hEnum.edges_iff_d hM hE hT hD hOmega hLayers).mp hEdge
  have hCopyAtom := expansion_atom_d hM hExits hE hT hS hSucc hLower hLinear hP0 hLayers hAtom
  exact (hOld.edges_iff_d hM hE hT hD hOmega (CopyDiagram.tower_input_valid hS.tower)).mpr hCopyAtom

/-- 协调者指定出口（带原末列前提的形式）。唯一临时前提：`LowerStepsIn`；Terminal 出口 H1–H4 由助手模块提供。 -/
theorem canonical_copy_bound_last_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    (hExits : TerminalExits M) (hLower : LowerStepsIn M) : CanonicalCopyBoundLastIn M := by
  intro E T D hE hT hD hOmega s m last N t W hS hSucc Old hOld n B hGraph k q p c hEdge
  exact (canonical_expansion_diagram_d hM hExits hE hT hD hOmega hS hSucc (hLower E T hE hT s m last N t W hS)
    hOld hGraph).2 k q p c hEdge

end KP1Y.OneYFinite.CanonicalExpansion
