import KP1Y.OneYCopyNeedsSyntax
import KP1Y.OneYLowerCopyRoots
import KP1Y.OneYTerminalCopyRoots
import KP1Y.ReflectionTable
import KP1Y.OneYTowerReconstruction

/-! 精确虚拟边界需要：实际复制塔工厂、源模板归属和活动层允许性。 -/
namespace KP1Y.OneYFinite.CopyNeeds
open YesMetaZFC YesMetaZFC.SetTheory YesMetaZFC.SetTheory.Definitional
open KP1Y.Kuratowski KP1Y.Functions KP1Y.Naturals KP1Y.Bounded
open KP1Y.OneYFinite.CopyCoordinates KP1Y.OneYFinite.CopiedMountain
universe u

theorem data_valid_of_tower_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain}
    {A : Context M.Domain} {m : M.Domain} {L : LayerStateSpace M.Domain}
    {V P H K level B n Forests CodeSpace G boundary : M.Domain}
    (hLayers : LayerRun M C m L V P H) (hBad : BadAt M C m L H K level A.last A.root)
    (hTower : CopyTower.Tower M C T A m L H K level B n Forests CodeSpace G) (hBoundary : M.mem boundary n) :
    (⟨B,n,Forests,CodeSpace,G,boundary,K,level⟩ : Data M.Domain).Valid M C :=
  ⟨hTower.bound,hTower.width,hBoundary,(CopyTower.bad_indices_d hM hC hLayers hBad).1,
    (CopyTower.bad_indices_d hM hC hLayers hBad).2.1,hTower.graph,fun _ _ hAt => hTower.code_valid hAt⟩

/-- 只多读实际边界列；需求读取宽度succ(width b)，不是源末列过滤。 -/
theorem lists_from_bad_exists_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {R : KP1Y.Reflection.Data M.Domain} (hR : R.Valid M) (hOmega : R.omega=C.omega)
    {m : M.Domain} {L : LayerStateSpace M.Domain} {V P H K level B b : M.Domain}
    (hLayers : LayerRun M C m L V P H) {A : Context M.Domain} (hA : A.Valid M C)
    (hBad : BadAt M C m L H K level A.last A.root) (hB : M.mem B C.omega) (hb : M.mem b C.omega) :
    ∃ boundary wide Forests CodeSpace G N,
      Width M C T A b boundary ∧ M.SuccessorOf wide boundary ∧
      CopyTower.Tower M C T A m L H K level B wide Forests CodeSpace G ∧
      Lists M C T R ⟨B,wide,Forests,CodeSpace,G,boundary,K,level⟩ N ∧
      KP1Y.Reflection.Template M R boundary N := by
  obtain ⟨boundary,hBoundary,hWidth⟩ := encode_exists_d hM hC hT hA hA.last hb
  obtain ⟨wide,hSucc,hWide⟩ := hC.omega.1.2 boundary hBoundary
  obtain ⟨Forests,CodeSpace,G,hTower⟩ := CopyTower.tower_exists_d hM hC hT hLayers hA hBad hB hWide
  have hD := data_valid_of_tower_d hM hC hLayers hBad hTower hSucc.predecessor_mem
  obtain ⟨N,hN⟩ := lists_exists_d hM hC hT R hD
  exact ⟨boundary,wide,Forests,CodeSpace,G,N,hWidth,hSucc,hTower,hN,hN.template_d hM hC hT hR hOmega hD⟩

/-- 控制根直接读真实活动层源山形；不是复制几何的外加根假设。 -/
def Control (M : SetTheory.Structure.{u}) (C : ExpressionData M.Domain) (m : M.Domain)
    (L : LayerStateSpace M.Domain) (H K level last q : M.Domain) : Prop :=
  ∃ source heights parents, CopyTower.SourceAt M C m L H K source ∧ Codes M source heights parents ∧
    Lower.RootAt M C ⟨m,heights,L.rows.forests,parents⟩ level last q

theorem Control.read_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {m : M.Domain} {L : LayerStateSpace M.Domain}
    {V P H K level last q source heights parents : M.Domain}
    (hLayers : LayerRun M C m L V P H) (h : Control M C m L H K level last q)
    (hSource : CopyTower.SourceAt M C m L H K source) (hCode : Codes M source heights parents) :
    Lower.RootAt M C ⟨m,heights,L.rows.forests,parents⟩ level last q := by
  obtain ⟨source',heights',parents',hSource',hCode',hRoot⟩ := h
  have hSS := hSource'.unique_d hM hC hLayers hSource
  subst source'
  obtain ⟨hh,hp⟩ := codes_injective hM.1 hCode' hCode
  subst heights'
  subst parents'
  exact hRoot

theorem control_exists_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {m : M.Domain} {L : LayerStateSpace M.Domain}
    {V P H K level last root : M.Domain} (hLayers : LayerRun M C m L V P H)
    (hBad : BadAt M C m L H K level last root) : ∃q, Control M C m L H K level last q := by
  have hIndices := CopyTower.bad_indices_d hM hC hLayers hBad
  obtain ⟨source,hSource⟩ := CopyTower.SourceAt.exists_d hM hC hLayers hIndices.1
  obtain ⟨heights,parents,hCode⟩ := hSource.contents
  obtain ⟨_,_,_,_,_,hX,_⟩ := hSource.read hM.1 hCode
  obtain ⟨q,hRoot⟩ := Lower.root_at_exists_d hM hC hX hIndices.2.1 hIndices.2.2.1
  exact ⟨q,source,heights,parents,hSource,hCode,hRoot⟩

theorem Control.unique_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {m : M.Domain} {L : LayerStateSpace M.Domain}
    {V P H K level last q q' : M.Domain} (hLayers : LayerRun M C m L V P H)
    (h : Control M C m L H K level last q) (h' : Control M C m L H K level last q') : q=q' := by
  obtain ⟨source,heights,parents,hSource,hCode,hRoot⟩ := h
  obtain ⟨_,_,_,_,_,hX,_⟩ := hSource.read hM.1 hCode
  exact hRoot.unique_d hM hC hX (h'.read_d hM hC hLayers hSource hCode)

theorem source_atom_d {M : SetTheory.Structure.{u}} (_he : Extensional M)
    {C : ExpressionData M.Domain} {m : M.Domain} {L : LayerStateSpace M.Domain}
    {H k W Q J r c q p : M.Domain} {X : CopiedMountain.Data M.Domain}
    (hLayer : RowAt M L.states H k W Q) (hRun : RowRun M C m L.rows W Q J)
    (hX : X.Valid M C) (hFrom : FromRun M C m L.rows W J X)
    (hParent : ParentAt M X r c p) (hRoot : Lower.RootAt M C X r c q) :
    ExpressionDiagram.ActualAtom M C m L H k q p c := by
  obtain ⟨F,_,hF,hParent⟩ := hParent
  obtain ⟨F',_,hF',hRoot⟩ := hRoot
  have hFF := hX.parents.unique r F F' hF hF'
  subst F'
  obtain ⟨U,hRow⟩ := (hFrom.parents r F).mp hF
  exact ⟨W,Q,hLayer,L.rows,J,r,U,F,hRun,hRow,hParent,hFrom.width ▸ hRoot⟩

/-- 所需边的真实源记录；低层gap允许弱化根，活动层另返回严格控制根界。 -/
theorem Occurrence.source_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {m : M.Domain} {L : LayerStateSpace M.Domain} {V P H K level B n Forests CodeSpace G b boundary cut qControl k r q p : M.Domain}
    (hLayers : LayerRun M C m L V P H) {A : Context M.Domain} (hA : A.Valid M C)
    (hBad : BadAt M C m L H K level A.last A.root)
    (hTower : CopyTower.Tower M C T A m L H K level B n Forests CodeSpace G)
    (hWidth : Width M C T A b boundary) (hBoundary : M.mem boundary n)
    (hCut : Encode M C T A A.root b cut) (hControl : Control M C m L H K level A.last qControl)
    (h : Occurrence M C ⟨B,n,Forests,CodeSpace,G,boundary,K,level⟩ k r q p) :
    (∃ qOld pOld, ExpressionDiagram.ActualAtom M C m L H k qOld pOld A.last ∧
      ParentCopy M C T A b pOld p ∧
      (ParentCopy M C T A b qOld q ∨ (M.mem q cut ∧ (A.root=qOld ∨ M.mem A.root qOld)))) ∧
    (k=K → M.mem q qControl) := by
  obtain ⟨code,_,hAt,heights,parents,hCode,_,_,_,hNeed,hParent,hRoot⟩ := h
  obtain ⟨hY,source,sH,sP,hSource,hSC,hBranch⟩ := (((hTower.rows k code).mp hAt).2).read hM.1 hCode
  obtain ⟨W,Q,J,hLayer,hRun,hX,hFrom⟩ := hSource.read hM.1 hSC
  rcases hNeed.2 with hLow | ⟨hActive,hRowLow⟩
  · obtain ⟨D,hDA,hDX,hD,hCopy⟩ := hBranch.lower_d hM hC (CopyTower.bad_indices_d hM hC hLayers hBad).1 hLow
    have hRunFrom : FromRun M C m L.rows W J D.mountain := hDX.symm ▸ hFrom
    have hDWidth : Width M C T D.coordinates b boundary := hDA.symm ▸ hWidth
    have hDCut : Encode M C T D.coordinates D.coordinates.root b cut := hDA.symm ▸ hCut
    obtain ⟨u,qParent,qRoot,_,hOldP,hOldQ,hMapP,hMapQ⟩ := hCopy.seam_source_d hM hC hT hD hRun hRunFrom hY hDWidth hBoundary hDCut hParent hRoot
    refine ⟨⟨qRoot,qParent,?_,hDA ▸ hMapP,hDA ▸ hMapQ⟩,?_⟩
    · exact hDA ▸ source_atom_d hM.1 hLayer hRun hD.mountain hRunFrom hOldP hOldQ
    · intro he
      exact False.elim (SetTheory.KP.mem_irrefl_d (KP1Y.models_weakKP hM) K (he ▸ hLow))
  · subst k
    have hActive := Terminal.active_from_bad_d hM hC hLayers hBad hLayer hRun hX hFrom
    obtain ⟨pOld,hOldP,hOldQ,hMapP,hMapQ,hStrict⟩ :=
      hBranch.terminal_d hM |>.low_seam_source_d hM hC hT hA hX hY hRun hFrom
        (hLayers.at_rooted hM.1 hLayer).positive hActive hRowLow hWidth hParent hRoot
        (hControl.read_d hM hC hLayers hSource hSC)
    exact ⟨⟨q,pOld,source_atom_d hM.1 hLayer hRun hX hFrom hOldP hOldQ,hMapP,Or.inl hMapQ⟩,fun _ => hStrict⟩

theorem Control.le_root_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {A : Context M.Domain} {m : M.Domain} {L : LayerStateSpace M.Domain}
    {V P H K level q : M.Domain} (hLayers : LayerRun M C m L V P H)
    (hBad : BadAt M C m L H K level A.last A.root) (h : Control M C m L H K level A.last q) :
    q=A.root ∨ M.mem q A.root := by
  obtain ⟨source,heights,parents,hSource,hCode,hRoot⟩ := h
  obtain ⟨W,Q,J,hLayer,hRun,hX,hFrom⟩ := hSource.read hM.1 hCode
  exact (Terminal.active_from_bad_d hM hC hLayers hBad hLayer hRun hX hFrom).control_le_root_d hM hC hX hRoot

theorem Control.natural_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {m : M.Domain} {L : LayerStateSpace M.Domain}
    {H K level last q : M.Domain} (h : Control M C m L H K level last q) : M.mem q C.omega := by
  obtain ⟨source,heights,parents,hSource,hCode,hRoot⟩ := h
  obtain ⟨_,_,_,_,_,hX,_⟩ := hSource.read hM.1 hCode
  exact (omega_isOrdinal_d hM hC.omega).transitive m hX.width q (hRoot.bounds hM.1 hX).2.1

/-- ParentCopy不会把任何原来更小的自然数移到其像的右边。 -/
theorem parent_copy_member_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {A : Context M.Domain} {b q q' p : M.Domain} (hCopy : ParentCopy M C T A b q q') (hp : M.mem p q) : M.mem p q' := by
  rcases hCopy.2.2 with ⟨_,he⟩ | ⟨_,_,_,off,hOff,_,hSum⟩
  · exact he.symm ▸ hp
  · exact KP1Y.Arithmetic.sum_base_subset_d hM ((omega_isOrdinal_d hM hC.omega).mem hCopy.1)
      ((hT.add.add_iff_sum hM hCopy.1 hOff).mp hSum) p hp

/-- 任意实际有限标签上，活动需要的根标签严格小于控制标签。 -/
theorem Lists.admissible_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {R : KP1Y.Reflection.Data M.Domain} (hR : R.Valid M) (hOmega : R.omega=C.omega)
    {m : M.Domain} {L : LayerStateSpace M.Domain}
    {V P H K level B n Forests CodeSpace G b boundary cut qOld control N f theta : M.Domain}
    (hLayers : LayerRun M C m L V P H) {A : Context M.Domain} (hA : A.Valid M C)
    (hBad : BadAt M C m L H K level A.last A.root)
    (hTower : CopyTower.Tower M C T A m L H K level B n Forests CodeSpace G)
    (hWidth : Width M C T A b boundary) (hBoundary : M.mem boundary n)
    (hCut : Encode M C T A A.root b cut) (hControl : Control M C m L H K level A.last qOld)
    (hMap : ParentCopy M C T A b qOld control)
    (hN : Lists M C T R ⟨B,n,Forests,CodeSpace,G,boundary,K,level⟩ N)
    (hf : KP1Y.Reflection.Labeling M R boundary f) (hTheta : MemPair M f control theta) :
    KP1Y.Reflection.Admissible M R K theta N f cut := by
  have hD := data_valid_of_tower_d hM hC hLayers hBad hTower hBoundary
  have hControlLe := CopyInvariant.copy_root_le_cut_d hM hC hT hA hCut (hControl.le_root_d hM hC hLayers hBad) hMap
  have hCutNat : M.mem cut C.omega := by
    obtain ⟨_,_,_,_,_,hAdd⟩ := hCut
    exact (hAdd.bounds hM.1 hT.add).2.2
  intro k _ q _ p _ hNeed eta hEta hQ
  obtain ⟨r,hOcc⟩ := (hN.need_iff_d hM hC hT hR hOmega hD).mp hNeed
  rcases hOcc.levels with hLow | ⟨hK,_⟩
  · exact Or.inl hLow
  · have hStrictOld := (hOcc.source_d hM hC hT hLayers hA hBad hTower hWidth hBoundary hCut hControl).2 hK
    have hStrict := parent_copy_member_d hM hC hT hMap hStrictOld
    have hQCut : M.mem q cut := by
      rcases hControlLe with he | hlt
      · exact he ▸ hStrict
      · exact ((omega_isOrdinal_d hM hC.omega).mem hCutNat).transitive control hlt q hStrict
    exact Or.inr ⟨hK,hQCut,hf.increasing q (hf.graph.bounds hM.1 hQ).1 control (hf.graph.bounds hM.1 hTheta).1
      hStrict eta hEta theta (hf.graph.bounds hM.1 hTheta).2 hQ hTheta⟩

/-- 原VirtualCase：复制根精确匹配，或需要根在cut左侧而模板根在cut右侧。 -/
def Virtual (M : SetTheory.Structure.{u}) (R : KP1Y.Reflection.Data M.Domain) (cut Templates Needs : M.Domain) : Prop :=
  ∀ k q p, KP1Y.Reflection.NeedAt M R Needs k q p → ∃ qCopy, KP1Y.Reflection.NeedAt M R Templates k qCopy p ∧
    (q=qCopy ∨ (M.mem q cut ∧ (cut=qCopy ∨ M.mem cut qCopy)))

theorem Lists.virtual_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {R : KP1Y.Reflection.Data M.Domain} (hR : R.Valid M) (hOmega : R.omega=C.omega)
    {m : M.Domain} {L : LayerStateSpace M.Domain}
    {V P H K level B n Forests CodeSpace G b boundary cut qControl N Original len Map size OldNeeds I Templates : M.Domain}
    (hLayers : LayerRun M C m L V P H) {A : Context M.Domain} (hA : A.Valid M C)
    (hBad : BadAt M C m L H K level A.last A.root)
    (hTower : CopyTower.Tower M C T A m L H K level B n Forests CodeSpace G)
    (hWidth : Width M C T A b boundary) (hBoundary : M.mem boundary n)
    (hCut : Encode M C T A A.root b cut) (hControl : Control M C m L H K level A.last qControl)
    (hN : Lists M C T R ⟨B,n,Forests,CodeSpace,G,boundary,K,level⟩ N)
    (hOriginal : ExpressionDiagram.Enumerated M C T R m L V H Original)
    (hOld : CopyInvariant.OriginalTemplates M R Original B A.last len Map size OldNeeds I)
    (hTemplates : CopyInvariant.CopiedTemplates M C T R A b OldNeeds Templates) : Virtual M R cut Templates N := by
  have hD := data_valid_of_tower_d hM hC hLayers hBad hTower hBoundary
  obtain ⟨J,hJ,hJRows⟩ := parent_copy_graph_exists_d hM hC hT hA hWidth.2.1
  have hRootCopy : ParentCopy M C T A b A.root cut :=
    (parent_copy_bad_iff (SetTheory.KP.mem_irrefl_d (KP1Y.models_weakKP hM) A.root)).mpr hCut
  intro k q p hNeed
  obtain ⟨r,hOcc⟩ := (hN.need_iff_d hM hC hT hR hOmega hD).mp hNeed
  obtain ⟨qOld,pOld,hAtom,hMapP,hRootCase⟩ := (hOcc.source_d hM hC hT hLayers hA hBad hTower hWidth hBoundary hCut hControl).1
  have hEdge := (hOriginal.edges_iff_d hM hC hT hR hOmega hLayers).mpr hAtom
  have hOldNeed := (hOld.need_iff hM hR).mpr ⟨(hOcc.indices_d hM hC hD).1,hEdge⟩
  have hQOld := hOmega ▸ (hEdge.bounds hM.1 hR).2.1
  obtain ⟨qCopy,_,hAtCopy⟩ := hJ.graph.total qOld hQOld
  have hMapQ := (hJRows qOld qCopy).mp hAtCopy
  have hCopiedNeed := (hTemplates.need_iff hM.1 hOmega).mpr ⟨qOld,pOld,hOldNeed,hMapQ,hMapP⟩
  refine ⟨qCopy,hCopiedNeed,?_⟩
  rcases hRootCase with hExact | ⟨hLeft,hRight⟩
  · exact Or.inl (hJ.graph.unique qOld q qCopy ((hJRows qOld q).mpr hExact) hAtCopy)
  · refine Or.inr ⟨hLeft,?_⟩
    rcases hRight with he | hlt
    · subst qOld
      exact Or.inl (hJ.graph.unique A.root cut qCopy ((hJRows A.root cut).mpr hRootCopy) hAtCopy)
    · exact Or.inr (hJ.strict A.root hA.root qOld hQOld hlt cut qCopy ((hJRows A.root cut).mpr hRootCopy) hAtCopy)

/-- 虚拟根弱化将复制模板的真实关系端点条件传递给精确需要表。 -/
theorem Virtual.end_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {R : KP1Y.Reflection.Data M.Domain} (hR : R.Valid M)
    {Relation width cut Templates Needs f beta : M.Domain} (hTable : KP1Y.Reflection.Table M R Relation)
    (hTemplate : KP1Y.Reflection.Template M R width Templates)
    (hf : KP1Y.Reflection.Labeling M R width f) (hVirtual : Virtual M R cut Templates Needs)
    (hEnd : KP1Y.Reflection.End M R Relation Templates f beta) : KP1Y.Reflection.End M R Relation Needs f beta := by
  intro k hk q hq p hp hNeed eta hEta a ha hQ hP
  obtain ⟨qCopy,hCopied,hCase⟩ := hVirtual k q p hNeed
  have hBounds := hCopied.bounds hM.1 hR
  obtain ⟨hQP,hPWidth⟩ := hTemplate.2.2 k hk qCopy hBounds.2.1 p hp hCopied
  have hQWidth : M.mem qCopy width := by
    rcases hQP with he | hlt
    · exact he ▸ hPWidth
    · exact ((omega_isOrdinal_d hM hR.omega).mem hTemplate.1).transitive p hPWidth qCopy hlt
  obtain ⟨etaCopy,hEtaCopy,hQCopy⟩ := hf.graph.total qCopy hQWidth
  have hOldQuery := hEnd k hk qCopy hBounds.2.1 p hp hCopied etaCopy hEtaCopy a ha hQCopy hP
  apply hTable.root_weaken_d hM hR hOldQuery
  rcases hCase with he | ⟨hLeft,hRight⟩
  · subst qCopy
    exact Or.inl (hf.graph.unique q eta etaCopy hQ hQCopy)
  · have hQQ : M.mem q qCopy := by
      rcases hRight with he | hlt
      · exact he ▸ hLeft
      · exact ((omega_isOrdinal_d hM hR.omega).mem hBounds.2.1).transitive cut hlt q hLeft
    exact Or.inr (hf.increasing q (hf.graph.bounds hM.1 hQ).1 qCopy hQWidth hQQ eta hEta etaCopy hEtaCopy hQ hQCopy)

/-- 三分支点算法不依赖截断宽度；读取公共列时逐值逐父完全一致。 -/
theorem branch_same_columns_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain}
    {A : Context M.Domain} {X Y Z : CopiedMountain.Data M.Domain} {K level k n n' c : M.Domain}
    (hK : M.mem K C.omega) (hY : CopyTower.Branch M C T A X K level k n Y)
    (hZ : CopyTower.Branch M C T A X K level k n' Z) (hc : M.mem c n) (hc' : M.mem c n') :
    (∀v, MemPair M Y.heights c v ↔ MemPair M Z.heights c v) ∧
      ∀r p, ParentAt M Y r c p ↔ ParentAt M Z r c p := by
  rcases hY with ⟨hk,D,hDA,hDX,hD,hCopy⟩ | ⟨hk,hCopy⟩ | ⟨hk,hCopy⟩
  · obtain ⟨D',hDA',hDX',hD',hCopy'⟩ := hZ.lower_d hM hC hK hk
    have hDD := Lower.Context.unique_d hM hC hD hD' (hDA.trans hDA'.symm) (hDX.trans hDX'.symm)
    subst D'
    exact ⟨fun v => (hCopy.heights c v).trans ((and_iff_right hc).trans ((and_iff_right hc').symm.trans (hCopy'.heights c v).symm)),
      fun r p => (hCopy.parents r c p).trans ((and_iff_right hc).trans ((and_iff_right hc').symm.trans (hCopy'.parents r c p).symm))⟩
  · subst k
    have hCopy' := hZ.terminal_d hM
    exact ⟨fun v => (hCopy.heights c v).trans ((and_iff_right hc).trans ((and_iff_right hc').symm.trans (hCopy'.heights c v).symm)),
      fun r p => (hCopy.parents r c p).trans ((and_iff_right hc).trans ((and_iff_right hc').symm.trans (hCopy'.parents r c p).symm))⟩
  · have hCopy' := hZ.ordinary_d hM hC hK hk
    exact ⟨fun v => (hCopy.heights c v).trans ((and_iff_right hc).trans ((and_iff_right hc').symm.trans (hCopy'.heights c v).symm)),
      fun r p => (hCopy.parents r c p).trans ((and_iff_right hc).trans ((and_iff_right hc').symm.trans (hCopy'.parents r c p).symm))⟩

/-- 为读虚拟列而扩到succ(width)不会改动既有塔的任何保留列。 -/
theorem tower_family_prefix_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain}
    {A : Context M.Domain} {m : M.Domain} {L : LayerStateSpace M.Domain}
    {V P H K level B n n' Forests Forests' CodeSpace CodeSpace' G G' cut : M.Domain}
    (hLayers : LayerRun M C m L V P H) (hK : M.mem K C.omega)
    (hTower : CopyTower.Tower M C T A m L H K level B n Forests CodeSpace G)
    (hTower' : CopyTower.Tower M C T A m L H K level B n' Forests' CodeSpace' G')
    (hCut : M.mem cut C.omega) (hLeft : M.MemberSubset cut n) (hRight : M.MemberSubset cut n') :
    TowerReconstruction.FamilyPrefix M C n Forests G n' Forests' G' B cut := by
  refine ⟨hCut,hLeft,hRight,?_⟩
  intro k _ code code' heights parents heights' parents' hAt hAt' hCode hCode'
  obtain ⟨_,source,sH,sP,hSource,hSC,hBranch⟩ := (((hTower.rows k code).mp hAt).2).read hM.1 hCode
  obtain ⟨_,source',sH',sP',hSource',hSC',hBranch'⟩ := (((hTower'.rows k code').mp hAt').2).read hM.1 hCode'
  have hSS := hSource'.unique_d hM hC hLayers hSource
  subst source'
  obtain ⟨hh,hp⟩ := codes_injective hM.1 hSC' hSC
  subst sH'
  subst sP'
  exact ⟨fun c hc v => (branch_same_columns_d hM hC hK hBranch hBranch' (hLeft c hc) (hRight c hc)).1 v,
    fun c hc r _ p => (branch_same_columns_d hM hC hK hBranch hBranch' (hLeft c hc) (hRight c hc)).2 r p⟩

/-- 原真实图与坏根给出所有实际需要对象和源模板归属；允许性只等待实际标签读取。 -/
theorem virtual_needs_exists_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {R : KP1Y.Reflection.Data M.Domain} (hR : R.Valid M) (hOmega : R.omega=C.omega)
    {m : M.Domain} {L : LayerStateSpace M.Domain} {V P H K level B b Original : M.Domain}
    (hLayers : LayerRun M C m L V P H) {A : Context M.Domain} (hA : A.Valid M C)
    (hBad : BadAt M C m L H K level A.last A.root) (hB : M.mem B C.omega) (hb : M.mem b C.omega)
    (hOriginal : ExpressionDiagram.Enumerated M C T R m L V H Original) :
    ∃boundary wide Forests CodeSpace G N cut qOld control OldNeeds Templates,
      Width M C T A b boundary ∧ M.SuccessorOf wide boundary ∧
      CopyTower.Tower M C T A m L H K level B wide Forests CodeSpace G ∧
      Lists M C T R ⟨B,wide,Forests,CodeSpace,G,boundary,K,level⟩ N ∧
      Encode M C T A A.root b cut ∧ Control M C m L H K level A.last qOld ∧ ParentCopy M C T A b qOld control ∧
      (control=cut ∨ M.mem control cut) ∧ M.mem cut boundary ∧
      (∃len Map size I, CopyInvariant.OriginalTemplates M R Original B A.last len Map size OldNeeds I) ∧
      CopyInvariant.CopiedTemplates M C T R A b OldNeeds Templates ∧
      KP1Y.Reflection.Template M R boundary N ∧ KP1Y.Reflection.Template M R boundary Templates ∧
      Virtual M R cut Templates N ∧
      ∀f theta, KP1Y.Reflection.Labeling M R boundary f → MemPair M f control theta →
        KP1Y.Reflection.Admissible M R K theta N f cut := by
  obtain ⟨boundary,wide,Forests,CodeSpace,G,N,hWidth,hSucc,hTower,hN,hNTemplate⟩ :=
    lists_from_bad_exists_d hM hC hT hR hOmega hLayers hA hBad hB hb
  obtain ⟨cut,_,hCut⟩ := encode_exists_d hM hC hT hA hA.root hb
  obtain ⟨qOld,hControl⟩ := control_exists_d hM hC hLayers hBad
  obtain ⟨J,hJ,hJRows⟩ := parent_copy_graph_exists_d hM hC hT hA hb
  obtain ⟨control,_,hJControl⟩ := hJ.graph.total qOld (hControl.natural_d hM hC)
  have hMap := (hJRows qOld control).mp hJControl
  have hControlLe := CopyInvariant.copy_root_le_cut_d hM hC hT hA hCut (hControl.le_root_d hM hC hLayers hBad) hMap
  have hDiagram := hOriginal.diagram_d hM hC hT hR hOmega hLayers
  obtain ⟨len,Map,size,OldNeeds,I,hOld⟩ := CopyInvariant.original_templates_exists_d (horizon := B) hM hC hR hOmega hDiagram.2.1
  have hOldTemplate := hOld.template_d hM hR (hOmega.symm ▸ hA.last) hDiagram
  obtain ⟨Templates,hTemplates,hTemplate⟩ := CopyInvariant.copied_templates_exists_d hM hC hT hR hOmega hA hb hWidth hOldTemplate
  refine ⟨boundary,wide,Forests,CodeSpace,G,N,cut,qOld,control,OldNeeds,Templates,
    hWidth,hSucc,hTower,hN,hCut,hControl,hMap,hControlLe,cut_lt_width_d hM hC hT hA hWidth hCut,
    ⟨len,Map,size,I,hOld⟩,hTemplates,hNTemplate,hTemplate,?_,?_⟩
  · exact hN.virtual_d hM hC hT hR hOmega hLayers hA hBad hTower hWidth hSucc.predecessor_mem hCut hControl hOriginal hOld hTemplates
  · intro f theta hf hTheta
    exact hN.admissible_d hM hC hT hR hOmega hLayers hA hBad hTower hWidth hSucc.predecessor_mem hCut hControl hMap hf hTheta

theorem Lists.empty_of_no_occurrences_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} {R : KP1Y.Reflection.Data M.Domain}
    {D : Data M.Domain} {N : M.Domain} (h : Lists M C T R D N)
    (hNone : ∀k r q p, ¬Occurrence M C D k r q p) : N=C.zero := by
  obtain ⟨_,_,_,_,_,_,_,_,_,hMap,hFilter⟩ := h
  apply (hFilter.empty_d hM hC ?_).2.1
  intro i packet hAt
  obtain ⟨_,_,k,_,r,_,q,_,p,_,_,hOcc,_⟩ := (hMap.rows i packet).mp hAt
  exact hNone k r q p hOcc

theorem Lists.empty_horizon_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} {R : KP1Y.Reflection.Data M.Domain}
    {D : Data M.Domain} (hD : D.Valid M C) {N : M.Domain} (h : Lists M C T R D N) (hEmpty : D.horizon=C.zero) : N=C.zero := by
  apply h.empty_of_no_occurrences_d hM hC
  intro k r q p hOcc
  exact hC.zero_empty k (hEmpty ▸ (hOcc.indices_d hM hC hD).1)

/-- 每个发生行占一个实际输出位置，记录过滤前后索引以保留重复模板。 -/
theorem occurrence_filter_position_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {R : KP1Y.Reflection.Data M.Domain} (hR : R.Valid M) (hOmega : R.omega=C.omega)
    {D : Data M.Domain} (hD : D.Valid M C) {Heights rowBound size P len N I k r q p : M.Domain}
    (hHeights : NeedHeights M C D Heights) (hBound : SequenceBound M C D.horizon Heights rowBound)
    (hSize : KP1Y.Arithmetic.Product M D.horizon rowBound size) (hMap : NeedMap M C T R D rowBound size P)
    (hFilter : Filter.Filtered M C.omega P size R.needCodes len N I) (hOcc : Occurrence M C D k r q p) :
    ∃i j packet, CopyPosition M C.omega T.addPairs T.plus T.mulPairs T.times C.zero rowBound k r i ∧
      M.mem j len ∧ MemPair M I j i ∧ MemPair M N j packet ∧ KP1Y.Ranking.Packet M packet k q p := by
  obtain ⟨hk,hr,hq,hp⟩ := hOcc.indices_d hM hC hD
  have hkNat := (omega_isOrdinal_d hM hC.omega).transitive D.horizon hD.horizon k hk
  have hrBound := hOcc.row_bounded_d hM hC hD hHeights hBound
  obtain ⟨i,_,hPos⟩ := copy_position_exists_d hM hC hT.add hT.mul hC.zero_nat hBound.1.1 hkNat hr
  have hSizeNat := natural_product_closed_d hM hC hD.horizon hBound.1.1 hSize
  have hZeroSum := natural_sum_comm_d hM hC hSizeNat hC.zero_nat (KP1Y.Arithmetic.sum_zero_d hM size hC.zero_empty)
  have hi := copy_position_bounded_d hM hC hT.add hT.mul hC.zero_nat hBound.1.1 hD.horizon hSize hZeroSum hk hrBound hPos
  obtain ⟨packet,hPacket,hCode⟩ := KP1Y.Reflection.need_code_exists_d hM hR (hOmega.symm ▸ hkNat) (hOmega.symm ▸ hq) (hOmega.symm ▸ hp)
  have hAt := (hMap.rows i packet).mpr ⟨hi,hPacket,k,hk,r,hrBound,q,hq,p,hp,hPos,hOcc,hCode⟩
  obtain ⟨j,hj,hIndex,hEntry⟩ := (hFilter.entry_iff hM.1 hMap.graph).mp hAt
  exact ⟨i,j,packet,hPos,hj,hIndex,hEntry,hCode⟩

/-- 不同(k,row)即使生成相同Packet，仍占不同输出位置，绝不作集合去重。 -/
theorem Lists.distinct_occurrences_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {R : KP1Y.Reflection.Data M.Domain} (hR : R.Valid M) (hOmega : R.omega=C.omega)
    {D : Data M.Domain} (hD : D.Valid M C) {N k r q p k' r' q' p' : M.Domain}
    (hList : Lists M C T R D N) (hOcc : Occurrence M C D k r q p) (hOcc' : Occurrence M C D k' r' q' p')
    (hDifferent : k≠k' ∨ r≠r') :
    ∃j j' packet packet', j≠j' ∧ MemPair M N j packet ∧ KP1Y.Ranking.Packet M packet k q p ∧
      MemPair M N j' packet' ∧ KP1Y.Ranking.Packet M packet' k' q' p' := by
  obtain ⟨Heights,rowBound,size,P,len,I,hHeights,hBound,hSize,hMap,hFilter⟩ := hList
  obtain ⟨i,j,packet,hPos,_,hIndex,hEntry,hCode⟩ := occurrence_filter_position_d hM hC hT hR hOmega hD hHeights hBound hSize hMap hFilter hOcc
  obtain ⟨i',j',packet',hPos',_,hIndex',hEntry',hCode'⟩ := occurrence_filter_position_d hM hC hT hR hOmega hD hHeights hBound hSize hMap hFilter hOcc'
  refine ⟨j,j',packet,packet',?_,hEntry,hCode,hEntry',hCode'⟩
  intro hJJ
  subst j'
  have hII := hFilter.indices.unique j i i' hIndex hIndex'
  subst i'
  have hw := omega_isOrdinal_d hM hC.omega
  obtain ⟨hKK,hRR⟩ := copy_position_injective_d hM hC hT.add hT.mul hC.zero_nat hBound.1.1
    (hw.transitive D.horizon hD.horizon k (hOcc.indices_d hM hC hD).1)
    (hw.transitive D.horizon hD.horizon k' (hOcc'.indices_d hM hC hD).1)
    (hOcc.row_bounded_d hM hC hD hHeights hBound) (hOcc'.row_bounded_d hM hC hD hHeights hBound) hPos hPos'
  exact hDifferent.elim (fun h => h hKK) (fun h => h hRR)

/-- 从原表示和精确复制标签读取解除End；仅保留拼接时真实需验证的标签对应。 -/
theorem Virtual.end_of_original_representation_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} {T : MatrixArithmetic M.Domain}
    {R : KP1Y.Reflection.Data M.Domain} (hR : R.Valid M) (hOmega : R.omega=C.omega)
    {A : Context M.Domain} {m Original B len P size OldNeeds I Templates Needs Relation f g beta b boundary cut : M.Domain}
    (hOld : CopyInvariant.OriginalTemplates M R Original B A.last len P size OldNeeds I)
    (hTemplates : CopyInvariant.CopiedTemplates M C T R A b OldNeeds Templates)
    (hTable : KP1Y.Reflection.Table M R Relation) (hRepresentation : KP1Y.Reflection.Representation M R Relation m Original f)
    (hLast : MemPair M f A.last beta) (hTemplate : KP1Y.Reflection.Template M R boundary Templates)
    (hg : KP1Y.Reflection.Labeling M R boundary g)
    (hAlong : ∀i, M.mem i A.last → ∀target, ParentCopy M C T A b i target → ∀a, MemPair M g target a ↔ MemPair M f i a)
    (hVirtual : Virtual M R cut Templates Needs) : KP1Y.Reflection.End M R Relation Needs g beta := by
  have hOldTemplate := hOld.template_d hM hR
    ((omega_isOrdinal_d hM hR.omega).transitive m hRepresentation.labeling.length A.last (hRepresentation.labeling.graph.bounds hM.1 hLast).1)
    hRepresentation.diagram
  have hEnd := hOld.end_d hM hR hRepresentation hLast
  obtain ⟨J,transferLen,hJ,hTransfer⟩ := hTemplates
  have hJD : Graph M J R.omega R.omega := by simpa only [hOmega] using hJ.embedding.graph
  have hLabels : CopyInvariant.LabelsAlong M A.last J f g :=
    fun i hi target hAt a => hAlong i hi target ((hJ.rows i target).mp hAt) a
  exact hVirtual.end_d hM hR hTable hTemplate hg (hTransfer.end_d hM hR hJD hOldTemplate hEnd hLabels)

end KP1Y.OneYFinite.CopyNeeds
