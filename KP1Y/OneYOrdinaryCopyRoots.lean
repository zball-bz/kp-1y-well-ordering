import KP1Y.OneYOrdinaryCopy
import KP1Y.OneYLowerCopy
import KP1Y.OneYCopyPathTransport

/-! 普通复制的真实父/根运输；实际有限路径通过全ω列图后仍位于目标宽度内。 -/
namespace KP1Y.OneYFinite.CopiedMountain.Ordinary
open YesMetaZFC YesMetaZFC.SetTheory YesMetaZFC.SetTheory.Definitional
open KP1Y.Kuratowski KP1Y.Functions KP1Y.Naturals KP1Y.Bounded
open KP1Y.OneYFinite.CopyCoordinates
open KP1Y.OneYFinite.CopiedMountain.Lower (RootAt)
universe u

theorem parent_copy_of_edge_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {A : Context M.Domain} (hA : A.Valid M C) {X : Data M.Domain} (hX : X.Valid M C)
    {r b s p c q : M.Domain} (hSource : M.mem s A.last) (hParent : ParentAt M X r s p)
    (hMap : ParentCopy M C T A b s c) (hMapP : ParentCopy M C T A b p q) : Parent M C T A X r c q := by
  classical
  by_cases hGood : M.mem s A.root
  · have hCP := (parent_copy_good_iff hMap.2.1 hMap.1 hGood).mp hMap
    have hPGood := ((omega_isOrdinal_d hM hC.omega).mem hA.root).transitive s hGood p (hParent.bounds hM.1 hX).2.2.2
    have hQP := (parent_copy_good_iff hMapP.2.1 hMapP.1 hPGood).mp hMapP
    subst c
    subst q
    exact (parent_original_iff_d hM hC hT hA hX hSource).mpr hParent
  · exact ⟨s,hMap.1,b,hMap.2.1,p,hMapP.1,
      OrdinaryCoordinates.decoded_encode_d hM hC hT hA hSource hGood ((parent_copy_bad_iff hGood).mp hMap),hParent,hMapP⟩

theorem Copies.root_parent_copy_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {A : Context M.Domain} (hA : A.Valid M C) {X Y : Data M.Domain} (hX : X.Valid M C) (hY : Y.Valid M C)
    {n r b s c q z : M.Domain} (hCopy : Copies M C T A X n Y)
    (hSource : M.mem s A.last) (hChild : M.mem c Y.width)
    (hMap : ParentCopy M C T A b s c) (hRoot : RootAt M C X r s q) (hMapRoot : ParentCopy M C T A b q z) :
    RootAt M C Y r c z := by
  have hw := omega_isOrdinal_d hM hC.omega
  have hr := (hRoot.bounds hM.1 hX).1
  have hQLast : M.mem q A.last := by
    rcases (hRoot.bounds hM.1 hX).2.2.2 with he | hlt
    · exact he.symm ▸ hSource
    · exact (hw.mem hA.last).transitive s hSource q hlt
  obtain ⟨J,hJ,hRows⟩ := parent_copy_graph_exists_d hM hC hT hA hMap.2.1
  have hJSC := (hRows s c).mpr hMap
  have hJQZ := (hRows q z).mpr hMapRoot
  have hZ : M.mem z Y.width := by
    rcases (hRoot.bounds hM.1 hX).2.2.2 with he | hlt
    · have hzc := hJ.graph.unique s z c (he ▸ hJQZ) hJSC
      exact hzc.symm ▸ hChild
    · exact (hw.mem hY.width).transitive c hChild z (hJ.strict q hMapRoot.1 s hMap.1 hlt z c hJQZ hJSC)
  obtain ⟨F,hF,hRowF,hRootF⟩ := hRoot
  obtain ⟨G,hG,hRowG⟩ := hY.parents.total r hr
  have hNo : NoParent M Y.width G z := by
    intro p _ hP
    obtain ⟨height,_,hHeight⟩ := hX.heights.total q hRootF.1
    have hTargetHeight : MemPair M Y.heights z height := (hCopy.heights z height).mpr
      ⟨hCopy.width ▸ hZ,(Height.parent_copy_iff_d hM hC hT hA hQLast hMapRoot).mpr hHeight⟩
    have hRH := (hY.source r z height hTargetHeight).mp ⟨p,G,hG,hRowG,hP⟩
    obtain ⟨pOld,F',_,hRowF',hOldP⟩ := (hX.source r q height hHeight).mpr hRH
    have hEq := hX.parents.unique r F' F hRowF' hRowF
    subst F'
    exact hRootF.2.1 pOld ((hX.forest r F hRowF).bounds hM.1 hOldP).2 hOldP
  refine ⟨G,hG,hRowG,root_map_global_bounded_d hM hC (hX.forest r F hRowF) hY.width hJ hRootF hJQZ hJSC hChild hNo ?_⟩
  intro d p u v hD hP hDU hPV
  have hdLast : M.mem d A.last := by
    rcases hD with he | hAnc
    · exact he.symm ▸ hSource
    · exact (hw.mem hA.last).transitive s hSource d hAnc.1
  have hu : M.mem u Y.width := by
    rcases hD with he | hAnc
    · exact (hJ.graph.unique s u c (he ▸ hDU) hJSC).symm ▸ hChild
    · exact (hw.mem hY.width).transitive c hChild u
        (hJ.strict d (hJ.graph.bounds hM.1 hDU).1 s hMap.1 hAnc.1 u c hDU hJSC)
  have hParent := parent_copy_of_edge_d hM hC hT hA hX hdLast ⟨F,hF,hRowF,hP⟩
    ((hRows d u).mp hDU) ((hRows p v).mp hPV)
  obtain ⟨Q,_,hRowQ,hEdge⟩ := (hCopy.parents r u v).mpr ⟨hCopy.width ▸ hu,hParent⟩
  have hQG := hY.parents.unique r Q G hRowQ hRowG
  exact hQG ▸ hEdge

theorem parent_parent_copy_iff_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {A : Context M.Domain} (hA : A.Valid M C) {X : Data M.Domain} (hX : X.Valid M C)
    {r b s c q : M.Domain} (hSource : M.mem s A.last) (hMap : ParentCopy M C T A b s c) :
    Parent M C T A X r c q ↔ ∃ p, M.mem p C.omega ∧ ParentAt M X r s p ∧ ParentCopy M C T A b p q := by
  constructor
  · intro h
    have hSaved := h
    obtain ⟨source,_,block,_,p,hp,hDec,hP,_⟩ := h
    have hSourceEq := hDec.source_parent_copy_d hM hC hT hA hSource hMap
    subst source
    obtain ⟨J,hJ,hRows⟩ := parent_copy_graph_exists_d hM hC hT hA hMap.2.1
    obtain ⟨target,_,hTarget⟩ := hJ.graph.total p hp
    have hMapP := (hRows p target).mp hTarget
    have hNew := parent_copy_of_edge_d hM hC hT hA hX hSource hP hMap hMapP
    have hEq := hSaved.unique_d hM hC hT hA hX hNew
    exact ⟨p,hp,hP,hEq.symm ▸ hMapP⟩
  · rintro ⟨p,_,hP,hMapP⟩
    exact parent_copy_of_edge_d hM hC hT hA hX hSource hP hMap hMapP

theorem Copies.root_parent_copy_iff_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {A : Context M.Domain} (hA : A.Valid M C) {X Y : Data M.Domain} (hX : X.Valid M C) (hY : Y.Valid M C)
    {n r b s c z : M.Domain} (hCopy : Copies M C T A X n Y)
    (hSource : M.mem s A.last) (hChild : M.mem c Y.width) (hMap : ParentCopy M C T A b s c) :
    RootAt M C Y r c z ↔ ∃ q, RootAt M C X r s q ∧ ParentCopy M C T A b q z := by
  constructor
  · intro hRoot
    obtain ⟨height,_,hHeight⟩ := hY.heights.total c hChild
    have hOldHeight := (Height.parent_copy_iff_d hM hC hT hA hSource hMap).mp ((hCopy.heights c height).mp hHeight).2
    obtain ⟨q,hQ⟩ := Lower.root_at_exists_d hM hC hX (hRoot.bounds hM.1 hY).1 (hX.heights.bounds hM.1 hOldHeight).1
    have hQNat := (omega_isOrdinal_d hM hC.omega).transitive X.width hX.width q (hQ.bounds hM.1 hX).2.1
    obtain ⟨J,hJ,hRows⟩ := parent_copy_graph_exists_d hM hC hT hA hMap.2.1
    obtain ⟨target,_,hTarget⟩ := hJ.graph.total q hQNat
    have hMapQ := (hRows q target).mp hTarget
    have hNewRoot := hCopy.root_parent_copy_d hM hC hT hA hX hY hSource hChild hMap hQ hMapQ
    have hEq := hNewRoot.unique_d hM hC hY hRoot
    exact ⟨q,hQ,hEq ▸ hMapQ⟩
  · rintro ⟨q,hQ,hMapQ⟩
    exact hCopy.root_parent_copy_d hM hC hT hA hX hY hSource hChild hMap hQ hMapQ

/-- 普通复制的每个实际父/根记录都有完整源记录，三个列字段使用同一ParentCopy。 -/
theorem Copies.row_source_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {A : Context M.Domain} (hA : A.Valid M C) {X Y : Data M.Domain} (hX : X.Valid M C) (hY : Y.Valid M C)
    {n r c pNew qNew : M.Domain} (hCopy : Copies M C T A X n Y)
    (hParent : ParentAt M Y r c pNew) (hRoot : RootAt M C Y r c qNew) :
    ∃ s b p q, M.mem s A.last ∧ M.mem b C.omega ∧ ParentAt M X r s p ∧ RootAt M C X r s q ∧
      ParentCopy M C T A b s c ∧ ParentCopy M C T A b p pNew ∧ ParentCopy M C T A b q qNew := by
  have hc := (hParent.bounds hM.1 hY).2.1
  have hcNat := (omega_isOrdinal_d hM hC.omega).transitive Y.width hY.width c hc
  obtain ⟨s,b,hDec⟩ := OrdinaryCoordinates.decoded_exists_d hM hC hT hA hcNat
  have hSource := hDec.source_lt_last_d hM hC hT hA
  have hMap := hDec.parent_copy_reconstruct_d hM hC hT hA
  obtain ⟨p,_,hP,hMapP⟩ := (parent_parent_copy_iff_d hM hC hT hA hX hSource hMap).mp ((hCopy.parents r c pNew).mp hParent).2
  obtain ⟨q,hQ,hMapQ⟩ := (hCopy.root_parent_copy_iff_d hM hC hT hA hX hY hSource hc hMap).mp hRoot
  exact ⟨s,b,p,q,hSource,hMap.2.1,hP,hQ,hMap,hMapP,hMapQ⟩

end KP1Y.OneYFinite.CopiedMountain.Ordinary
