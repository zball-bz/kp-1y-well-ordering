import KP1Y.OneYLowerCopyNesting
import KP1Y.OneYReconstructionExtraction

/-! Lower伪父的实际几何运输；保留段及单收缩均比较真实对象候选图。 -/
namespace KP1Y.OneYFinite.CopiedMountain.Lower
open YesMetaZFC YesMetaZFC.SetTheory YesMetaZFC.SetTheory.Definitional
open KP1Y.Kuratowski KP1Y.Functions KP1Y.Naturals KP1Y.Bounded
universe u

theorem ancestor_row_prefix_iff_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {X Y : Data M.Domain} (hX : X.Valid M C) (hY : Y.Valid M C)
    {cut r F G c p : M.Domain} (hCut : M.mem cut C.omega) (hLeft : M.MemberSubset cut X.width)
    (hRight : M.MemberSubset cut Y.width) (hF : MemPair M X.parents r F) (hG : MemPair M Y.parents r G)
    (hParents : ∀d, M.mem d cut → ∀q, ParentAt M X r d q ↔ ParentAt M Y r d q) (hc : M.mem c cut) :
    Ancestor M C X.width F p c ↔ Ancestor M C Y.width G p c := by
  have hRows : RowsAgreeOn M F G cut := by
    intro d hd q
    constructor
    · intro hP
      obtain ⟨G',_,hG',hEdge⟩ := (hParents d hd q).mp ⟨F,(hX.parents.bounds hM.1 hF).2,hF,hP⟩
      exact hY.parents.unique r G' G hG' hG ▸ hEdge
    · intro hP
      obtain ⟨F',_,hF',hEdge⟩ := (hParents d hd q).mpr ⟨G,(hY.parents.bounds hM.1 hG).2,hG,hP⟩
      exact hX.parents.unique r F' F hF' hF ▸ hEdge
  exact (ancestor_prefix_iff_d hM hC (hX.forest r F hF) hCut hLeft hc hRows).trans
    (ancestor_prefix_iff_d hM hC (hY.forest r G hG) hCut hRight hc (fun _ _ _ => Iff.rfl)).symm

theorem graph_pseudo_candidate_prefix_iff_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {X Y : Data M.Domain} (hX : X.Valid M C) (hY : Y.Valid M C)
    {cut c p : M.Domain} (hCut : M.mem cut C.omega) (hLeft : M.MemberSubset cut X.width)
    (hRight : M.MemberSubset cut Y.width) (hHeights : RowsAgreeOn M X.heights Y.heights cut)
    (hParents : ∀r, M.mem r C.omega → ∀d, M.mem d cut → ∀q, ParentAt M X r d q ↔ ParentAt M Y r d q)
    (hc : M.mem c cut) : GraphPseudoCandidate M C X c p ↔ GraphPseudoCandidate M C Y c p := by
  have transfer {A B : Data M.Domain} (hA : A.Valid M C) (hB : B.Valid M C)
      (hLA : M.MemberSubset cut A.width) (hLB : M.MemberSubset cut B.width)
      (hH : RowsAgreeOn M A.heights B.heights cut)
      (hP : ∀r, M.mem r C.omega → ∀d, M.mem d cut → ∀q, ParentAt M A r d q ↔ ParentAt M B r d q)
      (h : GraphPseudoCandidate M C A c p) : GraphPseudoCandidate M C B c p := by
    obtain ⟨height,hHeight,hp,hpNat,r,hr,hHC,hHP,hSucc,F,_,hF,hAnc,hRel⟩ := h
    have hpCut := ((omega_isOrdinal_d hM hC.omega).mem hCut).transitive c hc p hAnc.1
    obtain ⟨G,hGMem,hG⟩ := hB.parents.total r hr
    exact ⟨height,hHeight,hp,hpNat,r,hr,(hH c hc height).mp hHC,(hH p hpCut hp).mp hHP,hSucc,G,hGMem,hG,
      (ancestor_row_prefix_iff_d hM hC hA hB hCut hLA hLB hF hG (hP r hr) hc).mp hAnc,hRel⟩
  exact ⟨transfer hX hY hLeft hRight hHeights hParents,
    transfer hY hX hRight hLeft (fun c hc h => (hHeights c hc h).symm)
      (fun r hr c hc p => (hParents r hr c hc p).symm)⟩

theorem graph_pseudo_parent_prefix_iff_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {X Y : Data M.Domain} (hX : X.Valid M C) (hY : Y.Valid M C)
    {cut c p : M.Domain} (hCut : M.mem cut C.omega) (hLeft : M.MemberSubset cut X.width)
    (hRight : M.MemberSubset cut Y.width) (hHeights : RowsAgreeOn M X.heights Y.heights cut)
    (hParents : ∀r, M.mem r C.omega → ∀d, M.mem d cut → ∀q, ParentAt M X r d q ↔ ParentAt M Y r d q)
    (hc : M.mem c cut) : GraphPseudoParent M C X c p ↔ GraphPseudoParent M C Y c p := by
  have hCand (q : M.Domain) := graph_pseudo_candidate_prefix_iff_d (p := q) hM hC hX hY hCut hLeft hRight hHeights hParents hc
  exact ⟨fun h => ⟨(hCand p).mp h.1,fun q hq hQ => h.2 q hq ((hCand q).mpr hQ)⟩,
    fun h => ⟨(hCand p).mpr h.1,fun q hq hQ => h.2 q hq ((hCand q).mp hQ)⟩⟩

/-- 连原末列本身也保持；此处不能将c≤last误写成Ordinary的c<last。 -/
theorem Copies.pseudo_parent_original_iff_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain}
    {D : Context M.Domain} (hD : D.Valid M C) {Y : Data M.Domain} (hY : Y.Valid M C)
    {n c p : M.Domain} (hCopy : Copies M C T D n Y) (hc : M.mem c n)
    (hOld : c=D.coordinates.last ∨ M.mem c D.coordinates.last) :
    GraphPseudoParent M C Y c p ↔ GraphPseudoParent M C D.mountain c p := by
  have hw := omega_isOrdinal_d hM hC.omega
  have hYc : M.mem c Y.width := hCopy.width.symm ▸ hc
  have hXc : M.mem c D.mountain.width := hOld.elim (fun he => he.symm ▸ hD.last)
    (fun h => (hw.mem hD.mountain.width).transitive D.coordinates.last hD.last c h)
  have hcNat := hw.transitive Y.width hY.width c hYc
  obtain ⟨cut,hSucc,hCut⟩ := hC.omega.1.2 c hcNat
  have hSub {width : M.Domain} (hwN : M.mem width C.omega) (hCW : M.mem c width) : M.MemberSubset cut width := by
    intro d hd
    rcases (hSucc d).mp hd with hlt | he
    · exact (hw.mem hwN).transitive c hCW d hlt
    · exact (hM.1.eq_of_same_members d c he).symm ▸ hCW
  have hDLast (d : M.Domain) (hd : M.mem d cut) : d=D.coordinates.last ∨ M.mem d D.coordinates.last := by
    rcases (hSucc d).mp hd with hlt | he
    · exact Or.inr (hOld.elim (fun he => he ▸ hlt) (fun h => (hw.mem hD.coordinates.last).transitive c h d hlt))
    · exact (hM.1.eq_of_same_members d c he).symm ▸ hOld
  exact graph_pseudo_parent_prefix_iff_d hM hC hY hD.mountain hCut (hSub hY.width hYc) (hSub hD.mountain.width hXc)
    (fun d hd v => hCopy.original_heights_d hM hC hD (hCopy.width ▸ hSub hY.width hYc d hd) (hDLast d hd))
    (fun r _ d hd p => hCopy.original_parents_d hM hC hD (hCopy.width ▸ hSub hY.width hYc d hd) (hDLast d hd)) hSucc.predecessor_mem

end KP1Y.OneYFinite.CopiedMountain.Lower
