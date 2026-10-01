import KP1Y.OneYCopySeamsSplice
import KP1Y.OneYExpansionPrefix

/-! 复制块归纳的实际不变量：当前标签表示复制图、源事实与端点模板保留、控制边成立；
以及初始块0由原表示的真实限制给出。 -/
namespace KP1Y.OneYFinite.CopySeams
open YesMetaZFC YesMetaZFC.SetTheory YesMetaZFC.SetTheory.Definitional
open KP1Y.Kuratowski KP1Y.Functions KP1Y.Naturals KP1Y.Bounded KP1Y.Reflection
open KP1Y.OneYFinite.CopyCoordinates KP1Y.OneYFinite.CopyInvariant KP1Y.OneYFinite.CopyGeometry
open KP1Y.OneYFinite.CopiedMountain
universe u

/-- 一次实际坏根复制所固定的全部真实数据；没有标签、反射或下降字段。 -/
structure Scene (M : SetTheory.Structure.{u}) (C : ExpressionData M.Domain) (T : MatrixArithmetic M.Domain)
    (D : Reflection.Data M.Domain) (Tab : M.Domain) (A : Context M.Domain) (m : M.Domain) (L : LayerStateSpace M.Domain)
    (V P H Original K level B qControl : M.Domain) : Prop where
  expression : C.Valid M
  arithmetic : T.Valid M C
  reflection : D.Valid M
  omega : D.omega=C.omega
  table : Table M D Tab
  context : A.Valid M C
  layers : LayerRun M C m L V P H
  original : ExpressionDiagram.Enumerated M C T D m L V H Original
  bad : BadAt M C m L H K level A.last A.root
  horizon : M.mem B C.omega
  control : CopyNeeds.Control M C m L H K level A.last qControl

/-- 当前标签g在复制图（以统一大图在width以下的限制给出）上的边真值。 -/
def EdgesHold (M : SetTheory.Structure.{u}) (C : ExpressionData M.Domain) (D : Reflection.Data M.Domain)
    (Tab Big width g : M.Domain) : Prop :=
  ∀ k, M.mem k C.omega → ∀ q, M.mem q C.omega → ∀ p, M.mem p C.omega → ∀ c, M.mem c width →
    EdgeAt M D Big k q p c → EdgeTruth M D Tab g k q p c

/-- 原图层号<B、子列<last的源事实，经第b份ParentCopy平移后在g下成立。 -/
def FactsHold (M : SetTheory.Structure.{u}) (C : ExpressionData M.Domain) (T : MatrixArithmetic M.Domain)
    (D : Reflection.Data M.Domain) (A : Context M.Domain) (Tab Original B b g : M.Domain) : Prop :=
  ∀ k, M.mem k B → ∀ qo, M.mem qo C.omega → ∀ po, M.mem po C.omega → ∀ co, M.mem co A.last →
    EdgeAt M D Original k qo po co → ∀ q, M.mem q C.omega → ∀ p, M.mem p C.omega → ∀ c, M.mem c C.omega →
      ParentCopy M C T A b qo q → ParentCopy M C T A b po p → ParentCopy M C T A b co c → EdgeTruth M D Tab g k q p c

/-- 原末列层号<B的模板经第b份ParentCopy平移后以虚拟端点beta成立。 -/
def TemplatesHold (M : SetTheory.Structure.{u}) (C : ExpressionData M.Domain) (T : MatrixArithmetic M.Domain)
    (D : Reflection.Data M.Domain) (A : Context M.Domain) (Tab Original B b g beta : M.Domain) : Prop :=
  ∀ k, M.mem k B → ∀ qo, M.mem qo C.omega → ∀ po, M.mem po C.omega → EdgeAt M D Original k qo po A.last →
    ∀ q, M.mem q C.omega → ∀ p, M.mem p C.omega → ParentCopy M C T A b qo q → ParentCopy M C T A b po p →
      NeedTruth M D Tab g beta k q p

/-- 控制边：R_K(g(ParentCopy_b(qControl)),g(cut_b),beta)。 -/
def ControlHolds (M : SetTheory.Structure.{u}) (C : ExpressionData M.Domain) (T : MatrixArithmetic M.Domain)
    (D : Reflection.Data M.Domain) (A : Context M.Domain) (Tab K qControl b g beta : M.Domain) : Prop :=
  ∀ cut, M.mem cut C.omega → ∀ control, M.mem control C.omega → Encode M C T A A.root b cut →
    ParentCopy M C T A b qControl control → ∀ θ, M.mem θ D.cap → ∀ a, M.mem a D.cap →
      MemPair M g control θ → MemPair M g cut a → Query M D.toIndexData Tab K θ a beta

structure StageAt (M : SetTheory.Structure.{u}) (C : ExpressionData M.Domain) (T : MatrixArithmetic M.Domain)
    (D : Reflection.Data M.Domain) (A : Context M.Domain) (Tab Original Big B K qControl beta b width g : M.Domain) : Prop where
  size : Width M C T A b width
  labeling : Labeling M D width g
  below : Below M D width g beta
  edges : EdgesHold M C D Tab Big width g
  facts : FactsHold M C T D A Tab Original B b g
  templates : TemplatesHold M C T D A Tab Original B b g beta
  control : ControlHolds M C T D A Tab K qControl b g beta

/-- 第b块存在满足全部不变量的实际标签；这是对象归纳所用的可定义谓词。 -/
def Stage (M : SetTheory.Structure.{u}) (C : ExpressionData M.Domain) (T : MatrixArithmetic M.Domain)
    (D : Reflection.Data M.Domain) (A : Context M.Domain) (Tab Original Big B K qControl beta b : M.Domain) : Prop :=
  ∃ width, M.mem width C.omega ∧ ∃ g, M.mem g D.labels ∧ StageAt M C T D A Tab Original Big B K qControl beta b width g

theorem EdgeTruth.along {M : SetTheory.Structure.{u}} {D : Reflection.Data M.Domain} {Tab f g k q p c q' p' c' : M.Domain}
    (hq : ∀ x, MemPair M g q' x ↔ MemPair M f q x) (hp : ∀ x, MemPair M g p' x ↔ MemPair M f p x)
    (hc : ∀ x, MemPair M g c' x ↔ MemPair M f c x) (h : EdgeTruth M D Tab f k q p c) : EdgeTruth M D Tab g k q' p' c' :=
  fun η hη a ha b hb h1 h2 h3 => h η hη a ha b hb ((hq η).mp h1) ((hp a).mp h2) ((hc b).mp h3)

theorem NeedTruth.along {M : SetTheory.Structure.{u}} {D : Reflection.Data M.Domain} {Tab f g beta k q p q' p' : M.Domain}
    (hq : ∀ x, MemPair M g q' x ↔ MemPair M f q x) (hp : ∀ x, MemPair M g p' x ↔ MemPair M f p x)
    (h : NeedTruth M D Tab f beta k q p) : NeedTruth M D Tab g beta k q' p' :=
  fun η hη a ha h1 h2 => h η hη a ha ((hq η).mp h1) ((hp a).mp h2)

theorem parent_copy_unique_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {A : Context M.Domain} (hA : A.Valid M C) {b p x y : M.Domain}
    (hx : ParentCopy M C T A b p x) (hy : ParentCopy M C T A b p y) : x=y := by
  obtain ⟨J,hJ,hRows⟩ := parent_copy_graph_exists_d hM hC hT hA hx.2.1
  exact hJ.graph.unique p x y ((hRows p x).mpr hx) ((hRows p y).mpr hy)

theorem parent_copy_exists_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {A : Context M.Domain} (hA : A.Valid M C) {b p : M.Domain} (hb : M.mem b C.omega) (hp : M.mem p C.omega) :
    ∃ x, M.mem x C.omega ∧ ParentCopy M C T A b p x := by
  obtain ⟨J,hJ,hRows⟩ := parent_copy_graph_exists_d hM hC hT hA hb
  obtain ⟨x,hx,hAt⟩ := hJ.graph.total p hp
  exact ⟨x,hx,(hRows p x).mp hAt⟩

theorem parent_copy_zero_eq_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {A : Context M.Domain} (hA : A.Valid M C) {p x : M.Domain} (h : ParentCopy M C T A C.zero p x) : x=p :=
  parent_copy_unique_d hM hC hT hA h (parent_copy_zero_d hM hC hT hA h.1)

theorem Scene.last_mem_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} {T : MatrixArithmetic M.Domain} {D : Reflection.Data M.Domain} {Tab : M.Domain}
    {A : Context M.Domain} {m : M.Domain} {L : LayerStateSpace M.Domain} {V P H Original K level B qControl : M.Domain}
    (hS : Scene M C T D Tab A m L V P H Original K level B qControl) : M.mem A.last m := by
  obtain ⟨W,_,Q,_,_,J,hRun,U,_,F,_,hRow,hParent,_⟩ := hS.bad
  exact ((hRun.at_numeric_d hM hS.expression hRow).forest.bounds hM.1 hParent).1

theorem Scene.K_nat_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} {T : MatrixArithmetic M.Domain} {D : Reflection.Data M.Domain} {Tab : M.Domain}
    {A : Context M.Domain} {m : M.Domain} {L : LayerStateSpace M.Domain} {V P H Original K level B qControl : M.Domain}
    (hS : Scene M C T D Tab A m L V P H Original K level B qControl) : M.mem K C.omega :=
  (CopyTower.bad_indices_d hM hS.expression hS.layers hS.bad).1

/-- 同一坏根两座宽度包含的实际复制图：较窄者恰为较宽者在其宽度以下的限制。 -/
theorem copy_diagram_restriction_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} {T : MatrixArithmetic M.Domain} {D : Reflection.Data M.Domain} {Tab : M.Domain}
    {A : Context M.Domain} {m : M.Domain} {L : LayerStateSpace M.Domain} {V P H Original K level B qControl : M.Domain}
    (hS : Scene M C T D Tab A m L V P H Original K level B qControl)
    {n n' Forests Forests' Codes Codes' G G' E E' : M.Domain}
    (hTower : CopyTower.Tower M C T A m L H K level B n Forests Codes G)
    (hTower' : CopyTower.Tower M C T A m L H K level B n' Forests' Codes' G') (hSub : M.MemberSubset n n')
    (hE : CopyDiagram.Enumerated M C T D ⟨B,n,Forests,Codes,G⟩ E)
    (hE' : CopyDiagram.Enumerated M C T D ⟨B,n',Forests',Codes',G'⟩ E') :
    ExpressionDiagram.DiagramRestriction M D n' E' n E := by
  have hC := hS.expression
  have hI := CopyDiagram.tower_input_valid hTower
  have hI' := CopyDiagram.tower_input_valid hTower'
  have hPrefix := CopyNeeds.tower_family_prefix_d hM hC hS.layers (hS.K_nat_d hM) hTower hTower' hTower.width
    (fun _ h => h) hSub
  refine ⟨hSub,fun k q p c => ?_⟩
  rw [hE.edges_iff_d hM hC hS.arithmetic hS.reflection hS.omega hI,hE'.edges_iff_d hM hC hS.arithmetic hS.reflection hS.omega hI']
  constructor
  · intro hAtom
    have hc : M.mem c n := by
      obtain ⟨_,r,_,hRow⟩ := hAtom
      exact (hRow.bounds_d hM hC hI).2.2.1
    exact ⟨hc,(atom_prefix_iff_d hM hC hI hI' rfl hPrefix hc).mp hAtom⟩
  · rintro ⟨hc,hAtom⟩
    exact (atom_prefix_iff_d hM hC hI hI' rfl hPrefix hc).mpr hAtom

/-- 任意复制塔在原末列以前的原子都是原规范图的真实原子。 -/
theorem tower_old_atom_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} {T : MatrixArithmetic M.Domain} {D : Reflection.Data M.Domain} {Tab : M.Domain}
    {A : Context M.Domain} {m : M.Domain} {L : LayerStateSpace M.Domain} {V P H Original K level B qControl : M.Domain}
    (hS : Scene M C T D Tab A m L V P H Original K level B qControl) {n Forests Codes G k r q p c : M.Domain}
    (hTower : CopyTower.Tower M C T A m L H K level B n Forests Codes G) (hLastN : M.MemberSubset A.last n)
    (hAtom : CopyDiagram.RowAtom M C ⟨B,n,Forests,Codes,G⟩ k r q p c) (hc : M.mem c A.last) :
    ExpressionDiagram.ActualAtom M C m L H k q p c := by
  have hC := hS.expression
  have he := hM.1
  have hw := omega_isOrdinal_d hM hC.omega
  obtain ⟨X,Y,W,Q,J,hX,hY,hLayer,hRun,hFrom,hBranch,hParent,hRoot⟩ := tower_row_atom_read_d hM hC hTower hAtom
  have hRows (a : M.Domain) (ha : M.mem a A.last) := Expansion.branch_original_rows_d hM hC hS.arithmetic hS.context hX
    hBranch (hLastN a ha) ha
  have hParentX := ((hRows c hc).2 r p).mp hParent
  have hr := (hParent.bounds he hY).1
  obtain ⟨FY,hFY,hRowY⟩ := hY.parents.total r hr
  obtain ⟨FX,hFX,hRowX⟩ := hX.parents.total r hr
  have hAgree : RowsAgreeOn M FY FX A.last := by
    intro a ha p'
    constructor
    · intro hAt
      obtain ⟨F,_,hRowF,hAtF⟩ := ((hRows a ha).2 r p').mp ⟨FY,hFY,hRowY,hAt⟩
      exact (hX.parents.unique r F FX hRowF hRowX) ▸ hAtF
    · intro hAt
      obtain ⟨F,_,hRowF,hAtF⟩ := ((hRows a ha).2 r p').mpr ⟨FX,hFX,hRowX,hAt⟩
      exact (hY.parents.unique r F FY hRowF hRowY) ▸ hAtF
  have hXW := hFrom.width
  have hYW := hBranch.width
  have hLastM : M.MemberSubset A.last X.width :=
    (hw.mem hX.width).transitive A.last (hXW.symm ▸ hS.last_mem_d hM)
  have hLastY : M.MemberSubset A.last Y.width := hYW.symm ▸ hLastN
  have hRootX : Lower.RootAt M C X r c q := by
    obtain ⟨F,hF,hRowF,hRootF⟩ := hRoot
    have hFF := hY.parents.unique r F FY hRowF hRowY
    subst F
    have h1 := (root_prefix_iff_d hM hC (hY.forest r FY hRowY) hS.context.last hLastY hc hAgree).mp hRootF
    have h2 := (root_prefix_iff_d hM hC (hX.forest r FX hRowX) hS.context.last hLastM hc (fun _ _ _ => Iff.rfl)).mpr h1
    exact ⟨FX,hFX,hRowX,h2⟩
  exact CopyNeeds.source_atom_d he hLayer hRun hX hFrom hParentX hRootX

/-- 控制根、坏根父与末列构成原规范图中的一条真实边。 -/
theorem control_atom_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} {T : MatrixArithmetic M.Domain} {D : Reflection.Data M.Domain} {Tab : M.Domain}
    {A : Context M.Domain} {m : M.Domain} {L : LayerStateSpace M.Domain} {V P H Original K level B qControl : M.Domain}
    (hS : Scene M C T D Tab A m L V P H Original K level B qControl) :
    EdgeAt M D Original K qControl A.root A.last := by
  obtain ⟨source,heights,parents,hSource,hCode,hRootAt⟩ := hS.control
  obtain ⟨W,Q,J,hLayer,hRun,hX,hFrom⟩ := hSource.read hM.1 hCode
  have hActive := Terminal.active_from_bad_d hM hS.expression hS.layers hS.bad hLayer hRun hX hFrom
  exact (hS.original.edges_iff_d hM hS.expression hS.arithmetic hS.reflection hS.omega hS.layers).mpr
    (CopyNeeds.source_atom_d hM.1 hLayer hRun hX hFrom hActive.parent hRootAt)

/-- 初始块：原表示限制到last以前给出第0块的全部不变量，虚拟端点为原末标签beta。 -/
theorem stage_zero_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} {T : MatrixArithmetic M.Domain} {D : Reflection.Data M.Domain} {Tab : M.Domain}
    {A : Context M.Domain} {m : M.Domain} {L : LayerStateSpace M.Domain} {V P H Original K level B qControl : M.Domain}
    (hS : Scene M C T D Tab A m L V P H Original K level B qControl)
    {N BigWidth BigForests BigCodes BigG Big f beta : M.Domain} (hBigWidth : Width M C T A N BigWidth)
    (hBigTower : CopyTower.Tower M C T A m L H K level B BigWidth BigForests BigCodes BigG)
    (hBig : CopyDiagram.Enumerated M C T D ⟨B,BigWidth,BigForests,BigCodes,BigG⟩ Big)
    (hRep : Representation M D Tab m Original f) (hLast : MemPair M f A.last beta) :
    Stage M C T D A Tab Original Big B K qControl beta C.zero := by
  have hC := hS.expression
  have hT := hS.arithmetic
  have hD := hS.reflection
  have hA := hS.context
  have he := hM.1
  have hw := omega_isOrdinal_d hM hC.omega
  have hLastM := hS.last_mem_d hM
  have hm : M.mem m C.omega := hS.omega ▸ hRep.labeling.length
  have hLastSub : M.MemberSubset A.last m := (hw.mem hm).transitive A.last hLastM
  have hLastOrd := hw.mem hA.last
  have hBetaCap := (hRep.labeling.graph.bounds he hLast).2
  obtain ⟨g,hg,hgRows⟩ := restrict_graph_d hM hRep.labeling.graph hLastSub
  have hgf : ∀ i, M.mem i A.last → ∀ x, MemPair M g i x ↔ MemPair M f i x :=
    fun i hi x => (hgRows i x).trans ⟨And.right,fun h => ⟨hi,h⟩⟩
  have hLab : Labeling M D A.last g := by
    refine ⟨hS.omega.symm ▸ hA.last,hg,?_,?_⟩
    · intro i hi x hx hix
      exact hRep.labeling.above i (hLastSub i hi) x hx ((hgf i hi x).mp hix)
    · intro i hi j hj hij x hx y hy hix hjy
      exact hRep.labeling.increasing i (hLastSub i hi) j (hLastSub j hj) hij x hx y hy ((hgf i hi x).mp hix) ((hgf j hj y).mp hjy)
  -- 原边列位于last以前时的读值
  have hCols : ∀ k q p c, EdgeAt M D Original k q p c → M.mem c A.last → M.mem q A.last ∧ M.mem p A.last := by
    intro k q p c hEdge hc
    obtain ⟨_,_,_,hqp,hpc⟩ := hS.original.diagram_d hM hC hT hD hS.omega hS.layers |>.edge_columns_d hM hD hEdge
    have hpl := hLastOrd.transitive c hc p hpc
    exact ⟨hqp.elim (fun h => h ▸ hpl) (hLastOrd.transitive p hpl q),hpl⟩
  have hLastCols : ∀ k q p, EdgeAt M D Original k q p A.last → M.mem q A.last ∧ M.mem p A.last := by
    intro k q p hEdge
    obtain ⟨_,hpm,_,hqp,hpc⟩ := hS.original.diagram_d hM hC hT hD hS.omega hS.layers |>.edge_columns_d hM hD hEdge
    exact ⟨hqp.elim (fun h => h ▸ hpc) (hLastOrd.transitive p hpc q),hpc⟩
  have hOrigTruth : ∀ k q p c, EdgeAt M D Original k q p c → EdgeTruth M D Tab f k q p c := by
    intro k q p c hEdge
    obtain ⟨hk,hq,hp,hc⟩ := hEdge.bounds he hD
    exact hRep.edges k hk q hq p hp c hc hEdge
  refine ⟨A.last,hA.last,g,hLab.sequence hD,⟨encode_zero_d hM hC hT hA hA.last,hLab,?_,?_,?_,?_,?_⟩⟩
  · intro i hi x hx hix
    exact hRep.labeling.increasing i (hLastSub i hi) A.last hLastM hi x hx beta hBetaCap ((hgf i hi x).mp hix) hLast
  · intro k _ q _ p _ c hc hEdge
    have hBigI := CopyDiagram.tower_input_valid hBigTower
    obtain ⟨_,r,_,hRow⟩ := (hBig.edges_iff_d hM hC hT hD hS.omega hBigI).mp hEdge
    have hOrig := (hS.original.edges_iff_d hM hC hT hD hS.omega hS.layers).mpr
      (tower_old_atom_d hM hS hBigTower (Expansion.width_keeps_prefix_d hM hC hT hBigWidth) hRow hc)
    obtain ⟨hql,hpl⟩ := hCols k q p c hOrig hc
    exact EdgeTruth.along (hgf q hql) (hgf p hpl) (hgf c hc) (hOrigTruth k q p c hOrig)
  · intro k _ qo _ po _ co hco hEdge q _ p _ c _ hPq hPp hPc
    have hq := parent_copy_zero_eq_d hM hC hT hA hPq
    have hp := parent_copy_zero_eq_d hM hC hT hA hPp
    have hc := parent_copy_zero_eq_d hM hC hT hA hPc
    subst q; subst p; subst c
    obtain ⟨hql,hpl⟩ := hCols k qo po co hEdge hco
    exact EdgeTruth.along (hgf qo hql) (hgf po hpl) (hgf co hco) (hOrigTruth k qo po co hEdge)
  · intro k _ qo _ po _ hEdge q _ p _ hPq hPp
    have hq := parent_copy_zero_eq_d hM hC hT hA hPq
    have hp := parent_copy_zero_eq_d hM hC hT hA hPp
    subst q; subst p
    obtain ⟨hql,hpl⟩ := hLastCols k qo po hEdge
    intro η hη a ha h1 h2
    exact hOrigTruth k qo po A.last hEdge η hη a ha beta hBetaCap ((hgf qo hql η).mp h1) ((hgf po hpl a).mp h2) hLast
  · intro cut _ control _ hEnc hPC θ hθ a ha h1 h2
    have hcut := encode_unique he hT hEnc (encode_zero_d hM hC hT hA hA.root)
    have hcontrol := parent_copy_zero_eq_d hM hC hT hA hPC
    subst cut; subst control
    have hRootLast := hA.below
    have hQLast : M.mem qControl A.last :=
      (hS.control.le_root_d hM hC hS.layers hS.bad).elim (fun h => h ▸ hRootLast) (hLastOrd.transitive A.root hRootLast qControl)
    exact hOrigTruth K qControl A.root A.last (control_atom_d hM hS) θ hθ a ha beta hBetaCap
      ((hgf qControl hQLast θ).mp h1) ((hgf A.root hRootLast a).mp h2) hLast

end KP1Y.OneYFinite.CopySeams
