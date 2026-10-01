import KP1Y.OneYCopySeamsStage

/-! 单块归纳步：实际表FR在控制查询处反射，模板经虚拟弱化与精确Adm给出需求，
拼接后四项不变量全部在下一块重新成立。 -/
namespace KP1Y.OneYFinite.CopySeams
open YesMetaZFC YesMetaZFC.SetTheory YesMetaZFC.SetTheory.Definitional
open KP1Y.Kuratowski KP1Y.Functions KP1Y.Naturals KP1Y.Bounded KP1Y.Reflection
open KP1Y.OneYFinite.CopyCoordinates KP1Y.OneYFinite.CopyInvariant KP1Y.OneYFinite.CopyGeometry
universe u

/-- 第b+1块宽度在统一大宽度Width(N)之内（b+1≤N）。 -/
theorem width_le_big_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {A : Context M.Domain} (hA : A.Valid M C) {b N width BigWidth : M.Domain}
    (hWidth : Width M C T A b width) (hBig : Width M C T A N BigWidth) (hbN : b=N ∨ M.mem b N) :
    M.MemberSubset width BigWidth := by
  rcases hbN with he | hlt
  · subst b
    have hEq := encode_unique hM.1 hT hWidth hBig
    subst BigWidth
    exact fun _ h => h
  · exact ((omega_isOrdinal_d hM hC.omega).mem (width_natural hM.1 hT hBig)).transitive width
      ((seam_lt_width_iff_d hM hC hT hA hWidth hBig).mpr hlt)

/-- 原末列以前的原边三列均在原last以前。 -/
theorem Scene.original_columns_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} {T : MatrixArithmetic M.Domain} {D : Reflection.Data M.Domain} {Tab : M.Domain}
    {A : Context M.Domain} {m : M.Domain} {L : LayerStateSpace M.Domain} {V P H Original K level B qControl : M.Domain}
    (hS : Scene M C T D Tab A m L V P H Original K level B qControl) {k q p c : M.Domain}
    (hEdge : EdgeAt M D Original k q p c) (hc : c=A.last ∨ M.mem c A.last) : M.mem q A.last ∧ M.mem p A.last := by
  have hLastOrd := (omega_isOrdinal_d hM hS.expression.omega).mem hS.context.last
  obtain ⟨_,_,_,hqp,hpc⟩ := (hS.original.diagram_d hM hS.expression hS.arithmetic hS.reflection hS.omega hS.layers).edge_columns_d
    hM hS.reflection hEdge
  have hpl : M.mem p A.last := hc.elim (fun h => h ▸ hpc) (fun h => hLastOrd.transitive c h p hpc)
  exact ⟨hqp.elim (fun h => h ▸ hpl) (hLastOrd.transitive p hpl q),hpl⟩

/-- 对象归纳步：Stage(b)且b+1≤N推出Stage(b+1)。唯一语义输入是实际R表的FR方程。 -/
theorem stage_step_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} {T : MatrixArithmetic M.Domain} {D : Reflection.Data M.Domain} {Tab : M.Domain}
    {A : Context M.Domain} {m : M.Domain} {L : LayerStateSpace M.Domain} {V P H Original K level B qControl : M.Domain}
    (hS : Scene M C T D Tab A m L V P H Original K level B qControl)
    {N BigWidth BigForests BigCodes BigG Big beta b next : M.Domain} (hBigWidth : Width M C T A N BigWidth)
    (hBigTower : CopyTower.Tower M C T A m L H K level B BigWidth BigForests BigCodes BigG)
    (hBig : CopyDiagram.Enumerated M C T D ⟨B,BigWidth,BigForests,BigCodes,BigG⟩ Big)
    (hBeta : M.mem beta D.cap) (hb : M.mem b C.omega) (hNext : M.SuccessorOf next b) (hNextN : next=N ∨ M.mem next N)
    (hStage : Stage M C T D A Tab Original Big B K qControl beta b) :
    Stage M C T D A Tab Original Big B K qControl beta next := by
  have hC := hS.expression
  have hT := hS.arithmetic
  have hD := hS.reflection
  have hA := hS.context
  have hOmega := hS.omega
  have he := hM.1
  have hw := omega_isOrdinal_d hM hC.omega
  obtain ⟨width,hwNat,f,_,hSt⟩ := hStage
  obtain ⟨width',nextWidth,cut,Old,New,Facts,Needs,hReal⟩ :=
    CopySplice.realized_exists_d hM hC hT hD hOmega hA hS.layers hS.original hS.bad hS.horizon hb
  have hGeo := hReal.geometry_d hM hC hT hD hOmega hA hS.layers hS.original hS.bad
  obtain ⟨next',wide,OldForests,OldCodes,OldTower,NewForests,NewCodes,NewTower,NeedForests,NeedCodes,NeedTower,
    len,Map,size,Base,Indices,hNext',hWidth',hWidthNext,hCut,hWide,hOldTower,hNewTower,hNeedTower,hOld,hNew,
    hBase,hFacts,hNeeds⟩ := hReal
  have hnn := Structure.SuccessorOf.eq he hNext' hNext
  subst next'
  have hww := encode_unique he hT hWidth' hSt.size
  subst width'
  have hBlock : Block M C T A b next width nextWidth cut := ⟨hNext,hSt.size,hWidthNext,hCut⟩
  have hWidthOrd := hw.mem hwNat
  have hNextBig := width_le_big_d hM hC hT hA hWidthNext hBigWidth hNextN
  have hWidthBig : M.MemberSubset width BigWidth := fun x hx => hNextBig x (hBlock.width_subset hM hC hT hA x hx)
  have hROld := copy_diagram_restriction_d hM hS hOldTower hBigTower hWidthBig hOld hBig
  have hRNew := copy_diagram_restriction_d hM hS hNewTower hBigTower hNextBig hNew hBig
  -- 当前标签表示第b块实际复制图
  have hRepOld : Representation M D Tab width Old f := by
    refine ⟨hGeo.1.oldDiagram,hSt.labeling,?_⟩
    intro k hk q hq p hp c _ hEdge
    obtain ⟨hcw,hBigE⟩ := (hROld.edges k q p c).mp hEdge
    exact hSt.edges k (hOmega ▸ hk) q (hOmega ▸ hq) p (hOmega ▸ hp) c hcw hBigE
  -- 控制查询
  have hCutW := hBlock.cut_mem hM hC hT hA
  obtain ⟨control,hcontrolNat,hPC⟩ := parent_copy_exists_d hM hC hT hA hb (hS.control.natural_d hM hC)
  have hControlLe := copy_root_le_cut_d hM hC hT hA hCut (hS.control.le_root_d hM hC hS.layers hS.bad) hPC
  have hControlW : M.mem control width := hControlLe.elim (fun h => h ▸ hCutW) (hWidthOrd.transitive cut hCutW control)
  obtain ⟨θ,hθ,hfθ⟩ := hSt.labeling.graph.total control hControlW
  obtain ⟨a,ha,hfa⟩ := hSt.labeling.graph.total cut hCutW
  have hQuery := hSt.control cut (hBlock.cut_nat hM hT) control hcontrolNat hCut hPC θ hθ a ha hfθ hfa
  have hReflect := hS.table.reflect_d hM hD hQuery
  -- 复制模板在beta成立，经虚拟弱化给出精确需要的端点条件
  have hOrigDiagram := hS.original.diagram_d hM hC hT hD hOmega hS.layers
  obtain ⟨tlen,TMap,tsize,OldNeeds,TI,hOldT⟩ :=
    original_templates_exists_d (horizon := B) (last := A.last) hM hC hD hOmega hOrigDiagram.2.1
  have hOldTTemplate := hOldT.template_d hM hD (hOmega.symm ▸ hA.last) hOrigDiagram
  obtain ⟨Templates,hTemplates,hTemplatesTemplate⟩ := copied_templates_exists_d hM hC hT hD hOmega hA hb hSt.size hOldTTemplate
  have hVirtual := hNeeds.virtual_d hM hC hT hD hOmega hS.layers hA hS.bad hNeedTower hSt.size hWide.predecessor_mem hCut
    hS.control hS.original hOldT hTemplates
  have hEndT : End M D Tab Templates f beta := by
    intro k _ q' hq' p' hp' hNeed
    obtain ⟨q,p,hOldNeed,hPq,hPp⟩ := (hTemplates.need_iff he hOmega).mp hNeed
    obtain ⟨hkB,hEdge⟩ := (hOldT.need_iff hM hD).mp hOldNeed
    have hb' := hEdge.bounds he hD
    exact hSt.templates k hkB q (hOmega ▸ hb'.2.1) p (hOmega ▸ hb'.2.2.1) hEdge q' (hOmega ▸ hq') p' (hOmega ▸ hp') hPq hPp
  have hEndNeeds := hVirtual.end_d hM hD hS.table hTemplatesTemplate hSt.labeling hEndT
  have hAdm := hNeeds.admissible_d hM hC hT hD hOmega hS.layers hA hS.bad hNeedTower hSt.size hWide.predecessor_mem hCut
    hS.control hPC hSt.labeling hfθ
  -- 真实FR
  have hDemand : Demand M D Tab K θ a beta width Old Needs cut f :=
    ⟨hGeo.2.2,hRepOld,hfa,hSt.below,hAdm,hEndNeeds⟩
  obtain ⟨g,_,hResp⟩ := hReflect width (hOmega.symm ▸ hwNat) Old hGeo.1.oldDiagram.2.1 Needs hGeo.2.2.2.1 cut hCutW f
    (hSt.labeling.sequence hD) hDemand
  -- 拼接
  obtain ⟨h,hSplice⟩ := splice_label_exists_d hM hC hT hD hOmega hA hBlock hSt.labeling hResp.representation.labeling
    hResp.prefix_eq hfa hResp.below
  have hFactsTruth : ∀ k q p c, EdgeAt M D Facts k q p c → EdgeTruth M D Tab f k q p c := by
    intro k q0 p0 c0 hEdge
    obtain ⟨qo,po,co,hBaseE,hPq,hPp,hPc⟩ := (hFacts.edge_iff he hOmega).mp hEdge
    obtain ⟨hkB,hcoLast,hOrigE⟩ := (hBase.edges_iff hM hD).mp hBaseE
    have hb' := hOrigE.bounds he hD
    have hb0 := hEdge.bounds he hD
    exact hSt.facts k hkB qo (hOmega ▸ hb'.2.1) po (hOmega ▸ hb'.2.2.1) co hcoLast hOrigE q0 (hOmega ▸ hb0.2.1)
      p0 (hOmega ▸ hb0.2.2.1) c0 (hOmega ▸ hb0.2.2.2) hPq hPp hPc
  have hRepNew := splice_representation_d hM hC hT hD hA hS.table hBlock hGeo.1 hGeo.2.1 hGeo.2.2 hSt.labeling hfa
    hFactsTruth hResp.representation hResp.below hResp.endpoint hSplice
  -- 平移列的读值
  have hMoveRead : ∀ p, M.mem p A.last → ∀ p', ParentCopy M C T A next p p' →
      ∃ p1, M.mem p1 width ∧ ParentCopy M C T A b p p1 ∧ ∀ x, MemPair M h p' x ↔ MemPair M f p1 x := by
    intro p hp p' hP'
    obtain ⟨p1,_,hP1⟩ := parent_copy_exists_d hM hC hT hA hb hP'.1
    have hp1 := parent_copy_below_encode_d hM hC hT hA hA.below hp hP1 hSt.size
    exact ⟨p1,hp1,hP1,hSplice.moved p1 hp1 p' ((hBlock.move_parent_copy hM hC hT hA hP1).mpr hP')⟩
  refine ⟨nextWidth,hBlock.widthNext_nat hM hT,h,hSplice.labeling.sequence hD,
    ⟨hWidthNext,hSplice.labeling,?_,?_,?_,?_,?_⟩⟩
  · exact SpliceLabel.below_d hM hC hT hD hA hBlock hSplice hSt.labeling hBeta hfa hSt.below hResp.below
  · intro k _ q _ p _ c hc hEdge
    have hb' := hEdge.bounds he hD
    exact hRepNew.edges k hb'.1 q hb'.2.1 p hb'.2.2.1 c hb'.2.2.2 ((hRNew.edges k q p c).mpr ⟨hc,hEdge⟩)
  · intro k hk qo hqo po hpo co hco hEdge q' _ p' _ c' _ hPq' hPp' hPc'
    obtain ⟨hql,hpl⟩ := hS.original_columns_d hM hEdge (Or.inr hco)
    obtain ⟨q1,hq1,hPq1,hq⟩ := hMoveRead qo hql q' hPq'
    obtain ⟨p1,hp1,hPp1,hp⟩ := hMoveRead po hpl p' hPp'
    obtain ⟨c1,hc1,hPc1,hc⟩ := hMoveRead co hco c' hPc'
    exact EdgeTruth.along hq hp hc (hSt.facts k hk qo hqo po hpo co hco hEdge q1 (hw.transitive width hwNat q1 hq1)
      p1 (hw.transitive width hwNat p1 hp1) c1 (hw.transitive width hwNat c1 hc1) hPq1 hPp1 hPc1)
  · intro k hk qo hqo po hpo hEdge q' _ p' _ hPq' hPp'
    obtain ⟨hql,hpl⟩ := hS.original_columns_d hM hEdge (Or.inl rfl)
    obtain ⟨q1,hq1,hPq1,hq⟩ := hMoveRead qo hql q' hPq'
    obtain ⟨p1,hp1,hPp1,hp⟩ := hMoveRead po hpl p' hPp'
    exact NeedTruth.along hq hp (hSt.templates k hk qo hqo po hpo hEdge q1 (hw.transitive width hwNat q1 hq1)
      p1 (hw.transitive width hwNat p1 hp1) hPq1 hPp1)
  · intro cut' _ control' _ hEnc' hPC' θ' _ a' _ h1 h2
    have hcc := encode_unique he hT hEnc' (width_is_next_cut_d hM hC hT hA hNext hSt.size)
    subst cut'
    have hMoveC := (hBlock.move_parent_copy hM hC hT hA hPC).mpr hPC'
    have hθθ := hSt.labeling.graph.unique control θ' θ ((hSplice.moved control hControlW control' hMoveC θ').mp h1) hfθ
    have haa := hSt.labeling.graph.unique cut a' a ((hSplice.moved cut hCutW width (hBlock.move_cut hM hC hT) a').mp h2) hfa
    subst θ'
    subst a'
    exact hQuery

end KP1Y.OneYFinite.CopySeams
