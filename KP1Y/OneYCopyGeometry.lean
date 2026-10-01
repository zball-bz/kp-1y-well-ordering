import KP1Y.OneYCopyTower
import KP1Y.OneYLowerCopyRoots
import KP1Y.OneYTerminalCopyHighRoots
import KP1Y.OneYCopyIterationFacts
import KP1Y.OneYCopyDiagramAtoms
import KP1Y.OneYTowerReconstruction

/-! 从真实三分支复制导出源记录；后续一块扩展的几何分类使用同一个实际塔。 -/
namespace KP1Y.OneYFinite.CopyGeometry
open YesMetaZFC YesMetaZFC.SetTheory YesMetaZFC.SetTheory.Definitional
open KP1Y.Kuratowski KP1Y.Functions KP1Y.Naturals KP1Y.Bounded KP1Y.Arithmetic
open KP1Y.OneYFinite.CopyCoordinates KP1Y.OneYFinite.CopiedMountain
universe u

/-- 同一block的完整源记录；Lower插入参考行允许目标根严格落在cut左侧。 -/
def RowSource (M : SetTheory.Structure.{u}) (C : ExpressionData M.Domain) (T : MatrixArithmetic M.Domain)
    (A : Context M.Domain) (X : Data M.Domain) (b cut s c pNew qNew : M.Domain) : Prop :=
  ParentCopy M C T A b s c ∧ ∃ u p q, M.mem u C.omega ∧ ParentAt M X u s p ∧ Lower.RootAt M C X u s q ∧
    ParentCopy M C T A b p pNew ∧ (ParentCopy M C T A b q qNew ∨ (M.mem qNew cut ∧ (A.root=q ∨ M.mem A.root q)))

theorem expanded_nonroot_source_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {A : Context M.Domain} (hA : A.Valid M C) {m : M.Domain} {L : LayerStateSpace M.Domain}
    {V P H K level k W Q J : M.Domain} (hLayers : LayerRun M C m L V P H)
    (hBad : BadAt M C m L H K level A.last A.root) (hLayer : RowAt M L.states H k W Q)
    (hRun : RowRun M C m L.rows W Q J) {X Y : Data M.Domain} (hX : X.Valid M C) (hY : Y.Valid M C)
    (hFrom : FromRun M C m L.rows W J X) {n r b s c cut pNew qNew : M.Domain}
    (hBranch : CopyTower.Branch M C T A X K level k n Y)
    (hAfter : M.mem A.root s) (hBefore : M.mem s A.last) (hEncode : Encode M C T A s b c)
    (hc : M.mem c Y.width) (hCut : Encode M C T A A.root b cut)
    (hParent : ParentAt M Y r c pNew) (hRoot : Lower.RootAt M C Y r c qNew) :
    RowSource M C T A X b cut s c pNew qNew := by
  have hNotGood : ¬M.mem s A.root := fun h => SetTheory.KP.mem_irrefl_d (KP1Y.models_weakKP hM) s
    (((omega_isOrdinal_d hM hC.omega).mem hEncode.1).transitive A.root hAfter s h)
  have hMap := (parent_copy_bad_iff hNotGood).mpr hEncode
  refine ⟨hMap,?_⟩
  rcases hBranch with ⟨_,D,hDA,hDX,hD,hCopy⟩ | ⟨hSame,hCopy⟩ | ⟨_,hCopy⟩
  · have hFromD : FromRun M C m L.rows W J D.mountain := hDX.symm ▸ hFrom
    have hSourceD : Source M D.coordinates s := by simpa only [Source,hDA] using And.intro hAfter (Or.inr hBefore : s=A.last ∨ M.mem s A.last)
    have h := hCopy.encoded_source_d hM hC hT hD hRun hFromD hY hSourceD
      (by simpa only [hDA] using hEncode) hc (by simpa only [hDA] using hCut) hParent hRoot
    simpa only [hDA,hDX] using h
  · subst k
    have hActive := Terminal.active_from_bad_d hM hC hLayers hBad hLayer hRun hX hFrom
    have hNonroot : s≠A.root := fun he => SetTheory.KP.mem_irrefl_d (KP1Y.models_weakKP hM) A.root (he ▸ hAfter)
    obtain ⟨p,q,hP,hQ,hMapP,hMapQ⟩ := hCopy.nonroot_row_source_d hM hC hT hA hX hY hRun hFrom hActive hBefore hNonroot hMap hParent hRoot
    exact ⟨r,p,q,(hParent.bounds hM.1 hY).1,hP,hQ,hMapP,Or.inl hMapQ⟩
  · obtain ⟨p,_,hP,hMapP⟩ := (Ordinary.parent_parent_copy_iff_d hM hC hT hA hX hBefore hMap).mp
      ((hCopy.parents r c pNew).mp hParent).2
    obtain ⟨q,hQ,hMapQ⟩ := (hCopy.root_parent_copy_iff_d hM hC hT hA hX hY hBefore hc hMap).mp hRoot
    exact ⟨r,p,q,(hParent.bounds hM.1 hY).1,hP,hQ,hMapP,Or.inl hMapQ⟩

theorem expanded_root_source_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {A : Context M.Domain} (hA : A.Valid M C) {m : M.Domain} {L : LayerStateSpace M.Domain}
    {V P H K level k W Q J : M.Domain} (hLayers : LayerRun M C m L V P H)
    (hBad : BadAt M C m L H K level A.last A.root) (hLayer : RowAt M L.states H k W Q)
    (hRun : RowRun M C m L.rows W Q J) {X Y : Data M.Domain} (hX : X.Valid M C) (hY : Y.Valid M C)
    (hFrom : FromRun M C m L.rows W J X) {n r b c pNew qNew : M.Domain}
    (hBranch : CopyTower.Branch M C T A X K level k n Y) (hNotLow : ¬M.mem k K)
    (hRow : k=K → level=r ∨ M.mem level r) (hEncode : Encode M C T A A.root b c)
    (hc : M.mem c Y.width) (hParent : ParentAt M Y r c pNew) (hRoot : Lower.RootAt M C Y r c qNew) :
    ∃ p q, ParentAt M X r A.root p ∧ Lower.RootAt M C X r A.root q ∧
      ParentCopy M C T A b p pNew ∧ ParentCopy M C T A b q qNew := by
  have hMap := (parent_copy_bad_iff (SetTheory.KP.mem_irrefl_d (KP1Y.models_weakKP hM) A.root)).mpr hEncode
  rcases hBranch with ⟨hLow,_⟩ | ⟨hSame,hCopy⟩ | ⟨_,hCopy⟩
  · exact False.elim (hNotLow hLow)
  · subst k
    have hActive := Terminal.active_from_bad_d hM hC hLayers hBad hLayer hRun hX hFrom
    exact hCopy.row_source_at_d hM hC hT hA hX hY hRun hFrom hActive hA.below (.inr (hRow rfl)) hMap hParent hRoot
  · obtain ⟨p,_,hP,hMapP⟩ := (Ordinary.parent_parent_copy_iff_d hM hC hT hA hX hA.below hMap).mp
      ((hCopy.parents r c pNew).mp hParent).2
    obtain ⟨q,hQ,hMapQ⟩ := (hCopy.root_parent_copy_iff_d hM hC hT hA hX hY hA.below hc hMap).mp hRoot
    exact ⟨p,q,hP,hQ,hMapP,hMapQ⟩

/-- 新增块中严格越过seam的列，其raw坐标恰为下一block的非末源列。 -/
theorem new_nonseam_coordinates_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {A : Context M.Domain} (hA : A.Valid M C) {b next width nextWidth c : M.Domain}
    (hNext : M.SuccessorOf next b) (hWidth : Width M C T A b width) (hWidthNext : Width M C T A next nextWidth)
    (hAfter : M.mem width c) (hBefore : M.mem c nextWidth) :
    ∃ s, M.mem A.root s ∧ M.mem s A.last ∧ Encode M C T A s next c := by
  have hw := omega_isOrdinal_d hM hC.omega
  have hn := CopyInvariant.width_natural hM.1 hT hWidthNext
  have hc := hw.transitive nextWidth hn c hBefore
  have hRootWidth := retained_in_width_d hM hC hT hA (Or.inl rfl) hWidth
  have hRootC := (hw.mem hc).transitive width hAfter A.root hRootWidth
  obtain ⟨s,block,hDec⟩ := raw_decode_exists_d hM hC hT hA hc
  obtain ⟨hSource,hEncode⟩ := (raw_decoded_active_iff hRootC).mp hDec
  have hNotOld : ¬M.mem c width := fun h => SetTheory.KP.mem_irrefl_d (KP1Y.models_weakKP hM) c
    ((hw.mem hc).transitive width hAfter c h)
  rcases (encoded_lt_width_iff_d hM hC hT hA hSource hEncode hWidthNext).mp hBefore with hOldBlock | ⟨he,hS⟩
  · rcases (hNext block).mp hOldBlock with hBlockOld | hBlockEq
    · exact False.elim (hNotOld ((encoded_lt_width_iff_d hM hC hT hA hSource hEncode hWidth).mpr (.inl hBlockOld)))
    · have hEq := hM.1.eq_of_same_members block b hBlockEq
      subst block
      rcases hSource.2 with hLast | hS
      · subst s
        have hEq := encode_unique hM.1 hT hEncode hWidth
        exact False.elim (SetTheory.KP.mem_irrefl_d (KP1Y.models_weakKP hM) width (hEq ▸ hAfter))
      · exact False.elim (hNotOld ((encoded_lt_width_iff_d hM hC hT hA hSource hEncode hWidth).mpr (.inr ⟨rfl,hS⟩)))
  · exact ⟨s,hSource.1,hS,he ▸ hEncode⟩

theorem row_atom_read_iff {M : SetTheory.Structure.{u}} (he : Extensional M)
    {C : ExpressionData M.Domain} {I : CopyDiagram.Input M.Domain} (hI : I.Valid M C)
    {k r q p c code heights parents : M.Domain} (hAt : MemPair M I.tower k code) (hCode : Codes M code heights parents) :
    CopyDiagram.RowAtom M C I k r q p c ↔
      ParentAt M (⟨I.width,heights,I.forests,parents⟩ : Data M.Domain) r c p ∧
        Lower.RootAt M C ⟨I.width,heights,I.forests,parents⟩ r c q := by
  have hX := (hI.values k code hAt).read he hCode
  constructor
  · rintro ⟨code',_,hAt',heights',parents',hCode',F,hF,hRow,hParent,hRoot⟩
    have hCC := hI.tower.unique k code' code hAt' hAt
    subst code'
    obtain ⟨hhh,hpp⟩ := codes_injective he hCode' hCode
    subst heights'
    subst parents'
    exact ⟨⟨F,hF,hRow,hParent⟩,⟨F,hF,hRow,hRoot⟩⟩
  · rintro ⟨⟨F,hF,hRowF,hParent⟩,⟨G,_,hRowG,hRoot⟩⟩
    have hGF := hX.parents.unique r G F hRowG hRowF
    exact ⟨code,(hI.tower.bounds he hAt).2,hAt,heights,parents,hCode,F,hF,hRowF,hParent,hGF ▸ hRoot⟩

theorem tower_input_valid {M : SetTheory.Structure.{u}} {C : ExpressionData M.Domain} {T : MatrixArithmetic M.Domain}
    {A : Context M.Domain} {m : M.Domain} {L : LayerStateSpace M.Domain} {H K level B n Forests Codes G : M.Domain}
    (h : CopyTower.Tower M C T A m L H K level B n Forests Codes G) :
    (⟨B,n,Forests,Codes,G⟩ : CopyDiagram.Input M.Domain).Valid M C :=
  ⟨h.bound,h.width,h.graph,fun _ _ hAt => h.code_valid hAt⟩

/-- 真实原子读取同一个塔code，并恢复实际源RowRun及该层精确复制分支。 -/
theorem tower_row_atom_read_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} {A : Context M.Domain}
    {m : M.Domain} {L : LayerStateSpace M.Domain} {H K level B n Forests Codes G k r q p c : M.Domain}
    (hTower : CopyTower.Tower M C T A m L H K level B n Forests Codes G)
    (hAtom : CopyDiagram.RowAtom M C ⟨B,n,Forests,Codes,G⟩ k r q p c) :
    ∃ X Y W Q J, X.Valid M C ∧ Y.Valid M C ∧ RowAt M L.states H k W Q ∧
      RowRun M C m L.rows W Q J ∧ FromRun M C m L.rows W J X ∧
      CopyTower.Branch M C T A X K level k n Y ∧ ParentAt M Y r c p ∧ Lower.RootAt M C Y r c q := by
  have hk := (hAtom.bounds_d hM hC (tower_input_valid hTower)).1
  obtain ⟨code,heights,parents,_,hAt,hCode,hY,source,sH,sP,hSource,hSourceCode,hBranch⟩ := hTower.mountain_at_d hk
  obtain ⟨W,Q,J,hLayer,hRun,hX,hFrom⟩ := hSource.read hM.1 hSourceCode
  obtain ⟨hParent,hRoot⟩ := (row_atom_read_iff hM.1 (tower_input_valid hTower) hAt hCode).mp hAtom
  exact ⟨⟨m,sH,L.rows.forests,sP⟩,⟨n,heights,Forests,parents⟩,W,Q,J,hX,hY,hLayer,hRun,hFrom,hBranch,hParent,hRoot⟩

theorem root_at_prefix_iff_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {X Y : Data M.Domain} (hX : X.Valid M C) (hY : Y.Valid M C)
    (hSub : M.MemberSubset X.width Y.width) {r c q : M.Domain} (hr : M.mem r C.omega) (hc : M.mem c X.width)
    (hRows : ∀ a, M.mem a X.width → ∀ p, ParentAt M X r a p ↔ ParentAt M Y r a p) :
    Lower.RootAt M C X r c q ↔ Lower.RootAt M C Y r c q := by
  obtain ⟨F,hF,hRowF⟩ := hX.parents.total r hr
  obtain ⟨G,hG,hRowG⟩ := hY.parents.total r hr
  have hAt {Z : Data M.Domain} (hZ : Z.Valid M C) {P : M.Domain} (hP : MemPair M Z.parents r P) :
      Lower.RootAt M C Z r c q ↔ Root M C Z.width P c q := by
    constructor
    · rintro ⟨Q,_,hQ,hRoot⟩
      exact (hZ.parents.unique r Q P hQ hP) ▸ hRoot
    · intro hRoot
      exact ⟨P,(hZ.parents.bounds hM.1 hP).2,hP,hRoot⟩
  rw [hAt hX hRowF,hAt hY hRowG]
  apply (root_prefix_iff_d hM hC (hY.forest r G hRowG) hX.width hSub hc ?_).symm
  intro a ha p
  constructor
  · intro hParent
    obtain ⟨F',_,hF',hParent'⟩ := (hRows a ha p).mpr ⟨G,hG,hRowG,hParent⟩
    exact (hX.parents.unique r F' F hF' hRowF) ▸ hParent'
  · intro hParent
    obtain ⟨G',_,hG',hParent'⟩ := (hRows a ha p).mp ⟨F,hF,hRowF,hParent⟩
    exact (hY.parents.unique r G' G hG' hRowG) ▸ hParent'

theorem row_atom_prefix_iff_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {I J : CopyDiagram.Input M.Domain}
    (hI : I.Valid M C) (hJ : J.Valid M C) (hHorizon : I.horizon=J.horizon)
    (hPrefix : TowerReconstruction.FamilyPrefix M C I.width I.forests I.tower J.width J.forests J.tower I.horizon I.width)
    {k r q p c : M.Domain} (hk : M.mem k I.horizon) (hr : M.mem r C.omega) (hc : M.mem c I.width) :
    CopyDiagram.RowAtom M C I k r q p c ↔ CopyDiagram.RowAtom M C J k r q p c := by
  obtain ⟨code,_,hAt⟩ := hI.tower.total k hk
  obtain ⟨code',_,hAt'⟩ := hJ.tower.total k (hHorizon ▸ hk)
  obtain ⟨heights,parents,hCode,hX⟩ := hI.values k code hAt
  obtain ⟨heights',parents',hCode',hY⟩ := hJ.values k code' hAt'
  rw [row_atom_read_iff hM.1 hI hAt hCode,row_atom_read_iff hM.1 hJ hAt' hCode']
  have hRows := hPrefix.rows k hk code code' heights parents heights' parents' hAt hAt' hCode hCode'
  exact and_congr (hRows.2 c hc r hr p)
    (root_at_prefix_iff_d hM hC hX hY hPrefix.right_width hr hc (fun a ha p => hRows.2 a ha r hr p))

theorem atom_prefix_iff_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {I J : CopyDiagram.Input M.Domain}
    (hI : I.Valid M C) (hJ : J.Valid M C) (hHorizon : I.horizon=J.horizon)
    (hPrefix : TowerReconstruction.FamilyPrefix M C I.width I.forests I.tower J.width J.forests J.tower I.horizon I.width)
    {k q p c : M.Domain} (hc : M.mem c I.width) :
    CopyDiagram.Atom M C I k q p c ↔ CopyDiagram.Atom M C J k q p c := by
  constructor
  · rintro ⟨hk,r,hr,hRow⟩
    exact ⟨hHorizon ▸ hk,r,hr,(row_atom_prefix_iff_d hM hC hI hJ hHorizon hPrefix hk hr hc).mp hRow⟩
  · rintro ⟨hk,r,hr,hRow⟩
    have hk' := hHorizon.symm ▸ hk
    exact ⟨hk',r,hr,(row_atom_prefix_iff_d hM hC hI hJ hHorizon hPrefix hk' hr hc).mpr hRow⟩

end KP1Y.OneYFinite.CopyGeometry
