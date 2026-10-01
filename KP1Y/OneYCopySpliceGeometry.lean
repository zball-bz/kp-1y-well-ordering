import KP1Y.OneYCopyGeometry
import KP1Y.OneYCopySourceFacts
import KP1Y.OneYVirtualNeeds
import KP1Y.OneYCopyDiagram

/-! 真实下一复制块的根图三分分类；仅由实际塔、源事实和虚拟Needs推出。 -/
namespace KP1Y.OneYFinite.CopySplice
open YesMetaZFC YesMetaZFC.SetTheory YesMetaZFC.SetTheory.Definitional
open KP1Y.Kuratowski KP1Y.Functions KP1Y.Naturals KP1Y.Bounded
open KP1Y.OneYFinite.CopyCoordinates KP1Y.OneYFinite.CopyInvariant
open KP1Y.OneYFinite.CopiedMountain KP1Y.OneYFinite.CopyGeometry
universe u

def CopyCase (M : SetTheory.Structure.{u}) (C : ExpressionData M.Domain) (T : MatrixArithmetic M.Domain)
    (D : KP1Y.Reflection.Data M.Domain) (width cut Facts k q p c : M.Domain) : Prop :=
  ∃q0 p0 c0, KP1Y.Reflection.EdgeAt M D Facts k q0 p0 c0 ∧
    MoveColumn M C T width cut p0 p ∧ MoveColumn M C T width cut c0 c ∧
      (MoveColumn M C T width cut q0 q ∨ (M.mem q width ∧ (cut=q0 ∨ M.mem cut q0)))

def SeamCase (M : SetTheory.Structure.{u}) (D : KP1Y.Reflection.Data M.Domain)
    (width Needs k q p c : M.Domain) : Prop := c=width ∧ KP1Y.Reflection.NeedAt M D Needs k q p

structure SpliceGeometry (M : SetTheory.Structure.{u}) (C : ExpressionData M.Domain) (T : MatrixArithmetic M.Domain)
    (D : KP1Y.Reflection.Data M.Domain) (width nextWidth cut Old New Facts Needs : M.Domain) : Prop where
  oldDiagram : KP1Y.Reflection.Diagram M D width Old
  newDiagram : KP1Y.Reflection.Diagram M D nextWidth New
  cut_lt : M.mem cut width
  size : ∃delta, TruncatedDifference M C.omega C.zero width cut delta ∧ AddAt M T.addPairs T.plus width delta nextWidth
  classify : ∀k q p c, KP1Y.Reflection.EdgeAt M D New k q p c →
    KP1Y.Reflection.EdgeAt M D Old k q p c ∨ CopyCase M C T D width cut Facts k q p c ∨ SeamCase M D width Needs k q p c

theorem row_atom_occurrence_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} {B n Forests CodeSpace G width K level k r q p : M.Domain}
    (hI : (⟨B,n,Forests,CodeSpace,G⟩ : CopyDiagram.Input M.Domain).Valid M C)
    (hAtom : CopyDiagram.RowAtom M C ⟨B,n,Forests,CodeSpace,G⟩ k r q p width)
    (hLevel : M.mem k K ∨ (k=K ∧ M.mem r level)) :
    CopyNeeds.Occurrence M C ⟨B,n,Forests,CodeSpace,G,width,K,level⟩ k r q p := by
  obtain ⟨code,hCodeMember,hAt,heights,parents,hCode,F,hF,hRow,hParent,hRoot⟩ := hAtom
  have hX := (hI.values k code hAt).read hM.1 hCode
  have hP : ParentAt M (⟨n,heights,Forests,parents⟩ : CopiedMountain.Data M.Domain) r width p := ⟨F,hF,hRow,hParent⟩
  obtain ⟨height,hh,hHeight⟩ := hX.heights.total width (hP.bounds hM.1 hX).2.1
  exact ⟨code,hCodeMember,hAt,heights,parents,hCode,height,hh,hHeight,
    ⟨(hX.source r width height hHeight).mp ⟨p,hP⟩,hLevel⟩,hP,⟨F,hF,hRow,hRoot⟩⟩

/-- 相邻复制块的真实宽度、内部减法与加法符合原Splice大小式。 -/
theorem width_splice_size_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {A : Context M.Domain} (hA : A.Valid M C) {b next width nextWidth cut : M.Domain}
    (hNext : M.SuccessorOf next b) (hWidth : Width M C T A b width) (hWidthNext : Width M C T A next nextWidth)
    (hCut : Encode M C T A A.root b cut) :
    M.mem cut width ∧ M.mem width nextWidth ∧ TruncatedDifference M C.omega C.zero width cut A.length ∧
      AddAt M T.addPairs T.plus width A.length nextWidth := by
  have hNextCut := width_is_next_cut_d hM hC hT hA hNext hWidth
  exact ⟨cut_lt_width_d hM hC hT hA hWidth hCut,cut_lt_width_d hM hC hT hA hWidthNext hNextCut,
    width_minus_cut_d hM hC hT hA hWidth hCut,(hT.add.add_iff_sum hM (width_natural hM.1 hT hWidth) (hA.length_nat hM.1)).mpr
      (width_successor_d hM hC hT hA hNext hWidth hWidthNext)⟩

theorem row_source_copy_case_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {D : KP1Y.Reflection.Data M.Domain} (hD : D.Valid M) (hOmega : D.omega=C.omega)
    {m : M.Domain} {L : LayerStateSpace M.Domain} {V P H Original B len Map size Base Indices b next width cut Facts k W Q J s c pNew qNew : M.Domain}
    (hLayers : LayerRun M C m L V P H) (hOriginal : ExpressionDiagram.Enumerated M C T D m L V H Original)
    {A : Context M.Domain} (hA : A.Valid M C)
    (hBase : OriginalFacts M D Original B A.last len Map size Base Indices) (hFacts : CopiedFacts M C T D A b Base Facts)
    (hNext : M.SuccessorOf next b) (hWidth : Width M C T A b width) (hCut : Encode M C T A A.root b cut)
    (hk : M.mem k B) (hLayer : RowAt M L.states H k W Q) (hRun : RowRun M C m L.rows W Q J)
    {X : CopiedMountain.Data M.Domain} (hX : X.Valid M C) (hFrom : FromRun M C m L.rows W J X)
    (hs : M.mem s A.last) (hSource : RowSource M C T A X next width s c pNew qNew) :
    CopyCase M C T D width cut Facts k qNew pNew c := by
  obtain ⟨hMapChild,r,p,q,_,hParent,hRoot,hMapParent,hMapRoot⟩ := hSource
  have hActual := CopyNeeds.source_atom_d hM.1 hLayer hRun hX hFrom hParent hRoot
  have hw := omega_isOrdinal_d hM hC.omega
  obtain ⟨JMap,hJMap,hRows⟩ := parent_copy_graph_exists_d hM hC hT hA hWidth.2.1
  obtain ⟨childOld,_,hChildOld⟩ := hJMap.graph.total s hMapChild.1
  obtain ⟨parentOld,_,hP⟩ := hJMap.graph.total p hMapParent.1
  have hqω := hw.transitive X.width hX.width q (hRoot.bounds hM.1 hX).2.1
  obtain ⟨rootOld,_,hQ⟩ := hJMap.graph.total q hqω
  have hMapC := (hRows s childOld).mp hChildOld
  have hMapP := (hRows p parentOld).mp hP
  have hMapQ := (hRows q rootOld).mp hQ
  refine ⟨rootOld,parentOld,childOld,
    (actual_copied_facts_edges_iff_d hM hC hT hD hOmega hLayers hOriginal hBase hFacts).mpr
      ⟨q,p,s,⟨hk,hs,hActual⟩,hMapQ,hMapP,hMapC⟩,
    (move_parent_copy_successor_iff_d hM hC hT hA hNext hWidth hCut hMapP).mpr hMapParent,
    (move_parent_copy_successor_iff_d hM hC hT hA hNext hWidth hCut hMapC).mpr hMapChild,?_⟩
  rcases hMapRoot with hMapRoot | ⟨hBefore,hRootAfter⟩
  · exact Or.inl ((move_parent_copy_successor_iff_d hM hC hT hA hNext hWidth hCut hMapQ).mpr hMapRoot)
  · have hCutMap : ParentCopy M C T A b A.root cut :=
      (parent_copy_bad_iff (SetTheory.KP.mem_irrefl_d (KP1Y.models_weakKP hM) A.root)).mpr hCut
    have hJCut := (hRows A.root cut).mpr hCutMap
    refine Or.inr ⟨hBefore,?_⟩
    rcases hRootAfter with he | hAfter
    · exact Or.inl (hJMap.graph.unique A.root cut rootOld hJCut (he.symm ▸ hQ))
    · exact Or.inr (hJMap.strict A.root hA.root q hqω hAfter cut rootOld hJCut hQ)


/-- 给定三座实际塔（旧宽度、下一宽度、虚拟边界宽度），逐原子穷尽原来的三种情况。 -/
theorem actual_splice_geometry_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {D : KP1Y.Reflection.Data M.Domain} (hD : D.Valid M) (hOmega : D.omega=C.omega)
    {m : M.Domain} {L : LayerStateSpace M.Domain}
    {V P H Original K level B len Map size Base Indices b next width nextWidth cut wide
      OldForests OldCodes OldTower NewForests NewCodes NewTower NeedForests NeedCodes NeedTower Old New Facts Needs : M.Domain}
    (hLayers : LayerRun M C m L V P H) (hOriginal : ExpressionDiagram.Enumerated M C T D m L V H Original)
    {A : Context M.Domain} (hA : A.Valid M C) (hBad : BadAt M C m L H K level A.last A.root)
    (hBase : OriginalFacts M D Original B A.last len Map size Base Indices) (hFacts : CopiedFacts M C T D A b Base Facts)
    (hNext : M.SuccessorOf next b) (hWidth : Width M C T A b width) (hWidthNext : Width M C T A next nextWidth)
    (hCut : Encode M C T A A.root b cut) (hWide : M.SuccessorOf wide width)
    (hOldTower : CopyTower.Tower M C T A m L H K level B width OldForests OldCodes OldTower)
    (hNewTower : CopyTower.Tower M C T A m L H K level B nextWidth NewForests NewCodes NewTower)
    (hNeedTower : CopyTower.Tower M C T A m L H K level B wide NeedForests NeedCodes NeedTower)
    (hOld : CopyDiagram.Enumerated M C T D ⟨B,width,OldForests,OldCodes,OldTower⟩ Old)
    (hNew : CopyDiagram.Enumerated M C T D ⟨B,nextWidth,NewForests,NewCodes,NewTower⟩ New)
    (hNeeds : CopyNeeds.Lists M C T D ⟨B,wide,NeedForests,NeedCodes,NeedTower,width,K,level⟩ Needs) :
    SpliceGeometry M C T D width nextWidth cut Old New Facts Needs := by
  have hK := (CopyTower.bad_indices_d hM hC hLayers hBad).1
  have hLevel := (CopyTower.bad_indices_d hM hC hLayers hBad).2.1
  have hSize := width_splice_size_d hM hC hT hA hNext hWidth hWidthNext hCut
  have hw := omega_isOrdinal_d hM hC.omega
  have hOldI := CopyDiagram.tower_input_valid hOldTower
  have hNewI := CopyDiagram.tower_input_valid hNewTower
  have hNeedI := CopyDiagram.tower_input_valid hNeedTower
  have hNeedData := CopyNeeds.data_valid_of_tower_d hM hC hLayers hBad hNeedTower hWide.predecessor_mem
  have hOldSub : M.MemberSubset width nextWidth := (hw.mem hNewTower.width).transitive width hSize.2.1
  have hWideSub : M.MemberSubset wide nextWidth := by
    intro c hc
    rcases (hWide c).mp hc with hc | he
    · exact hOldSub c hc
    · exact (hM.1.eq_of_same_members c width he).symm ▸ hSize.2.1
  have hOldPrefix := CopyNeeds.tower_family_prefix_d hM hC hLayers hK hOldTower hNewTower hOldTower.width
    (fun _ h => h) hOldSub
  have hNeedPrefix := CopyNeeds.tower_family_prefix_d hM hC hLayers hK hNeedTower hNewTower hNeedTower.width
    (fun _ h => h) hWideSub
  have hNextCut := width_is_next_cut_d hM hC hT hA hNext hWidth
  refine ⟨hOld.diagram_d hM hC hT hD hOmega hOldI,hNew.diagram_d hM hC hT hD hOmega hNewI,
    hSize.1,⟨A.length,hSize.2.2⟩,?_⟩
  intro k q p c hEdge
  have hAtom := (hNew.edges_iff_d hM hC hT hD hOmega hNewI).mp hEdge
  have hSaved := hAtom
  obtain ⟨hk,r,hr,hRowAtom⟩ := hAtom
  have hc := (hRowAtom.bounds_d hM hC hNewI).2.2.1
  classical
  by_cases hOldColumn : M.mem c width
  · exact Or.inl ((hOld.edges_iff_d hM hC hT hD hOmega hOldI).mpr
      ((atom_prefix_iff_d hM hC hOldI hNewI rfl hOldPrefix hOldColumn).mpr hSaved))
  · by_cases hSeam : c=width
    · subst c
      by_cases hLowRow : M.mem k K ∨ (k=K ∧ M.mem r level)
      · have hNeedRow := (row_atom_prefix_iff_d hM hC hNeedI hNewI rfl hNeedPrefix hk hr hWide.predecessor_mem).mpr hRowAtom
        have hOcc := row_atom_occurrence_d hM hNeedI hNeedRow hLowRow
        exact Or.inr (Or.inr ⟨rfl,(hNeeds.need_iff_d hM hC hT hD hOmega hNeedData).mpr ⟨r,hOcc⟩⟩)
      · obtain ⟨X,Y,W,Q,J,hX,hY,hLayer,hRun,hFrom,hBranch,hParent,hRoot⟩ := tower_row_atom_read_d hM hC hNewTower hRowAtom
        have hNotLow : ¬M.mem k K := fun h => hLowRow (Or.inl h)
        have hRow : k=K → level=r ∨ M.mem level r := by
          intro he
          rcases hw.wellOrder.linear.compare level hLevel r hr with heq | hlt | hlt
          · exact Or.inl (hM.1.eq_of_same_members level r heq)
          · exact Or.inr hlt
          · exact False.elim (hLowRow (Or.inr ⟨he,hlt⟩))
        obtain ⟨pOld,qOld,hParentOld,hRootOld,hMapP,hMapQ⟩ := expanded_root_source_d hM hC hT hA hLayers hBad hLayer hRun hX hY hFrom hBranch hNotLow hRow
          hNextCut (hParent.bounds hM.1 hY).2.1 hParent hRoot
        have hMap : ParentCopy M C T A next A.root width :=
          (parent_copy_bad_iff (SetTheory.KP.mem_irrefl_d (KP1Y.models_weakKP hM) A.root)).mpr hNextCut
        exact Or.inr (Or.inl (row_source_copy_case_d hM hC hT hD hOmega hLayers hOriginal hA hBase hFacts hNext hWidth hCut hk
          hLayer hRun hX hFrom hA.below ⟨hMap,r,pOld,qOld,hr,hParentOld,hRootOld,hMapP,Or.inl hMapQ⟩))
    · have hAfter : M.mem width c := by
        rcases hw.wellOrder.linear.compare width hOldTower.width c (hw.transitive nextWidth hNewTower.width c hc) with he | hlt | hlt
        · exact False.elim (hSeam (hM.1.eq_of_same_members width c he).symm)
        · exact hlt
        · exact False.elim (hOldColumn hlt)
      obtain ⟨s,hAfterRoot,hsLast,hEncode⟩ := new_nonseam_coordinates_d hM hC hT hA hNext hWidth hWidthNext hAfter hc
      obtain ⟨X,Y,W,Q,J,hX,hY,hLayer,hRun,hFrom,hBranch,hParent,hRoot⟩ := tower_row_atom_read_d hM hC hNewTower hRowAtom
      have hSource := expanded_nonroot_source_d hM hC hT hA hLayers hBad hLayer hRun hX hY hFrom hBranch hAfterRoot hsLast hEncode
        (hParent.bounds hM.1 hY).2.1 hNextCut hParent hRoot
      exact Or.inr (Or.inl (row_source_copy_case_d hM hC hT hD hOmega hLayers hOriginal hA hBase hFacts hNext hWidth hCut hk
        hLayer hRun hX hFrom hsLast hSource))


/-- 实际构造见证包。三座ω父族都由已有真实塔工厂构造，并未预设函数空间。 -/
def Realized (M : SetTheory.Structure.{u}) (C : ExpressionData M.Domain) (T : MatrixArithmetic M.Domain)
    (D : KP1Y.Reflection.Data M.Domain) (A : Context M.Domain) (m : M.Domain) (L : LayerStateSpace M.Domain)
    (H Original K level B b width nextWidth cut Old New Facts Needs : M.Domain) : Prop :=
  ∃next wide OldForests OldCodes OldTower NewForests NewCodes NewTower NeedForests NeedCodes NeedTower len Map size Base Indices,
    M.SuccessorOf next b ∧ Width M C T A b width ∧ Width M C T A next nextWidth ∧
    Encode M C T A A.root b cut ∧ M.SuccessorOf wide width ∧
    CopyTower.Tower M C T A m L H K level B width OldForests OldCodes OldTower ∧
    CopyTower.Tower M C T A m L H K level B nextWidth NewForests NewCodes NewTower ∧
    CopyTower.Tower M C T A m L H K level B wide NeedForests NeedCodes NeedTower ∧
    CopyDiagram.Enumerated M C T D ⟨B,width,OldForests,OldCodes,OldTower⟩ Old ∧
    CopyDiagram.Enumerated M C T D ⟨B,nextWidth,NewForests,NewCodes,NewTower⟩ New ∧
    OriginalFacts M D Original B A.last len Map size Base Indices ∧ CopiedFacts M C T D A b Base Facts ∧
    CopyNeeds.Lists M C T D ⟨B,wide,NeedForests,NeedCodes,NeedTower,width,K,level⟩ Needs

theorem Realized.geometry_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {D : KP1Y.Reflection.Data M.Domain} (hD : D.Valid M) (hOmega : D.omega=C.omega)
    {A : Context M.Domain} (hA : A.Valid M C) {m : M.Domain} {L : LayerStateSpace M.Domain}
    {V P H Original K level B b width nextWidth cut Old New Facts Needs : M.Domain}
    (hLayers : LayerRun M C m L V P H) (hOriginal : ExpressionDiagram.Enumerated M C T D m L V H Original)
    (hBad : BadAt M C m L H K level A.last A.root)
    (h : Realized M C T D A m L H Original K level B b width nextWidth cut Old New Facts Needs) :
    SpliceGeometry M C T D width nextWidth cut Old New Facts Needs ∧
      KP1Y.Reflection.Diagram M D width Facts ∧ KP1Y.Reflection.Template M D width Needs := by
  obtain ⟨next,wide,OldForests,OldCodes,OldTower,NewForests,NewCodes,NewTower,NeedForests,NeedCodes,NeedTower,
    len,Map,size,Base,Indices,hNext,hWidth,hWidthNext,hCut,hWide,hOldTower,hNewTower,hNeedTower,hOld,hNew,hBase,hFacts,hNeeds⟩ := h
  have hBaseDiagram := hBase.diagram_d hM hD (hOmega.symm ▸ hA.last) (hOriginal.diagram_d hM hC hT hD hOmega hLayers)
  obtain ⟨Facts',hFacts',hFactsDiagram'⟩ := copied_facts_exists_d hM hC hT hD hOmega hA hWidth.2.1 hWidth hBaseDiagram
  have hFactsDiagram : KP1Y.Reflection.Diagram M D width Facts := by
    rw [hFacts.unique hM.1 hFacts']; exact hFactsDiagram'
  have hNeedData := CopyNeeds.data_valid_of_tower_d hM hC hLayers hBad hNeedTower hWide.predecessor_mem
  exact ⟨actual_splice_geometry_d hM hC hT hD hOmega hLayers hOriginal hA hBad hBase hFacts hNext hWidth hWidthNext hCut hWide
    hOldTower hNewTower hNeedTower hOld hNew hNeeds,hFactsDiagram,hNeeds.template_d hM hC hT hD hOmega hNeedData⟩

/-- 从源实际层运行及其规范原子表，构造一整个真实相邻复制步骤。 -/
theorem realized_exists_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {D : KP1Y.Reflection.Data M.Domain} (hD : D.Valid M) (hOmega : D.omega=C.omega)
    {A : Context M.Domain} (hA : A.Valid M C) {m : M.Domain} {L : LayerStateSpace M.Domain}
    {V P H Original K level B b : M.Domain}
    (hLayers : LayerRun M C m L V P H) (hOriginal : ExpressionDiagram.Enumerated M C T D m L V H Original)
    (hBad : BadAt M C m L H K level A.last A.root) (hB : M.mem B C.omega) (hb : M.mem b C.omega) :
    ∃width nextWidth cut Old New Facts Needs, Realized M C T D A m L H Original K level B b width nextWidth cut Old New Facts Needs := by
  obtain ⟨next,hNext,hNextNat⟩ := hC.omega.1.2 b hb
  obtain ⟨width,hWidthNat,hWidth⟩ := encode_exists_d hM hC hT hA hA.last hb
  obtain ⟨nextWidth,hNextWidthNat,hWidthNext⟩ := encode_exists_d hM hC hT hA hA.last hNextNat
  obtain ⟨cut,_,hCut⟩ := encode_exists_d hM hC hT hA hA.root hb
  obtain ⟨wide,hWide,hWideNat⟩ := hC.omega.1.2 width hWidthNat
  obtain ⟨OldForests,OldCodes,OldTower,hOldTower⟩ := CopyTower.tower_exists_d hM hC hT hLayers hA hBad hB hWidthNat
  obtain ⟨NewForests,NewCodes,NewTower,hNewTower⟩ := CopyTower.tower_exists_d hM hC hT hLayers hA hBad hB hNextWidthNat
  obtain ⟨NeedForests,NeedCodes,NeedTower,hNeedTower⟩ := CopyTower.tower_exists_d hM hC hT hLayers hA hBad hB hWideNat
  obtain ⟨Old,hOld,_,_⟩ := CopyDiagram.tower_diagram_exists_d hM hC hT hD hOmega hOldTower
  obtain ⟨New,hNew,_,_⟩ := CopyDiagram.tower_diagram_exists_d hM hC hT hD hOmega hNewTower
  obtain ⟨len,Map,size,Base,Indices,Facts,hBase,hFacts,_,_⟩ := actual_copied_facts_exists_d (horizon := B) hM hC hT hD hOmega hLayers hOriginal hA hb hWidth
  have hNeedData := CopyNeeds.data_valid_of_tower_d hM hC hLayers hBad hNeedTower hWide.predecessor_mem
  obtain ⟨Needs,hNeeds⟩ := CopyNeeds.lists_exists_d hM hC hT D hNeedData
  exact ⟨width,nextWidth,cut,Old,New,Facts,Needs,next,wide,OldForests,OldCodes,OldTower,NewForests,NewCodes,NewTower,
    NeedForests,NeedCodes,NeedTower,len,Map,size,Base,Indices,hNext,hWidth,hWidthNext,hCut,hWide,hOldTower,hNewTower,hNeedTower,
    hOld,hNew,hBase,hFacts,hNeeds⟩

/-- 最终出口含实际全部构造见证、真实两张Diagram、精确大小式、源Facts与Needs的有效性。 -/
theorem splice_geometry_exists_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {D : KP1Y.Reflection.Data M.Domain} (hD : D.Valid M) (hOmega : D.omega=C.omega)
    {A : Context M.Domain} (hA : A.Valid M C) {m : M.Domain} {L : LayerStateSpace M.Domain}
    {V P H Original K level B b : M.Domain}
    (hLayers : LayerRun M C m L V P H) (hOriginal : ExpressionDiagram.Enumerated M C T D m L V H Original)
    (hBad : BadAt M C m L H K level A.last A.root) (hB : M.mem B C.omega) (hb : M.mem b C.omega) :
    ∃width nextWidth cut Old New Facts Needs,
      Realized M C T D A m L H Original K level B b width nextWidth cut Old New Facts Needs ∧
      SpliceGeometry M C T D width nextWidth cut Old New Facts Needs ∧
      KP1Y.Reflection.Diagram M D width Facts ∧ KP1Y.Reflection.Template M D width Needs := by
  obtain ⟨width,nextWidth,cut,Old,New,Facts,Needs,h⟩ := realized_exists_d hM hC hT hD hOmega hA hLayers hOriginal hBad hB hb
  exact ⟨width,nextWidth,cut,Old,New,Facts,Needs,h,h.geometry_d hM hC hT hD hOmega hA hLayers hOriginal hBad⟩

end KP1Y.OneYFinite.CopySplice
