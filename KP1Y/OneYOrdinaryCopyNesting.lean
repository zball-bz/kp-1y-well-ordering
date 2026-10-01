import KP1Y.OneYCopyNestingDefs
import KP1Y.OneYOrdinaryCopyRoots

/-! 普通复制保留实际相邻行细化；全ω列图仅作用于内部有限祖先路径。 -/
namespace KP1Y.OneYFinite.CopiedMountain.Ordinary
open YesMetaZFC YesMetaZFC.SetTheory YesMetaZFC.SetTheory.Definitional
open KP1Y.Kuratowski KP1Y.Functions KP1Y.Naturals KP1Y.Bounded
open KP1Y.OneYFinite.CopyCoordinates
universe u

theorem Copies.ancestor_parent_copy_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {A : Context M.Domain} (hA : A.Valid M C) {X Y : Data M.Domain} (hX : X.Valid M C) (hY : Y.Valid M C)
    {n r F G a s x c b : M.Domain} (hCopy : Copies M C T A X n Y)
    (hF : MemPair M X.parents r F) (hG : MemPair M Y.parents r G)
    (hAnc : Ancestor M C X.width F a s) (hSource : M.mem s A.last)
    (hMapA : ParentCopy M C T A b a x) (hMapC : ParentCopy M C T A b s c) (hChild : M.mem c Y.width) :
    Ancestor M C Y.width G x c := by
  have hw := omega_isOrdinal_d hM hC.omega
  obtain ⟨J,hJ,hRows⟩ := parent_copy_graph_exists_d hM hC hT hA hMapC.2.1
  have hJC := (hRows s c).mpr hMapC
  apply ancestor_map_global_bounded_d hM hC (hX.forest r F hF) hY.width hJ hAnc
    ((hRows a x).mpr hMapA) hJC hChild
  intro d p u v hD hParent hDU hPV
  have hdLast : M.mem d A.last := by
    rcases hD with he | hAncD
    · exact he.symm ▸ hSource
    · exact (hw.mem hA.last).transitive s hSource d hAncD.1
  have hu : M.mem u Y.width := by
    rcases hD with he | hAncD
    · exact (hJ.graph.unique s u c (he ▸ hDU) hJC).symm ▸ hChild
    · exact (hw.mem hY.width).transitive c hChild u
        (hJ.strict d (hJ.graph.bounds hM.1 hDU).1 s hMapC.1 hAncD.1 u c hDU hJC)
  have hCopied := parent_copy_of_edge_d hM hC hT hA hX hdLast
    ⟨F,(hX.parents.bounds hM.1 hF).2,hF,hParent⟩ ((hRows d u).mp hDU) ((hRows p v).mp hPV)
  obtain ⟨G',_,hG',hEdge⟩ := (hCopy.parents r u v).mpr ⟨hCopy.width ▸ hu,hCopied⟩
  exact hY.parents.unique r G' G hG' hG ▸ hEdge

theorem Copies.nested_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {A : Context M.Domain} (hA : A.Valid M C) {X Y : Data M.Domain} (hX : X.Valid M C) (hY : Y.Valid M C)
    {m : M.Domain} {R : RowStateSpace M.Domain} {V P H n : M.Domain}
    (hRun : RowRun M C m R V P H) (hFrom : FromRun M C m R V H X)
    (hCopy : Copies M C T A X n Y) : Nested M C Y := by
  have hNested := hFrom.nested_d hM hC hRun hX
  intro r next F G hSucc hF hG c p hEdge
  have hParent : ParentAt M Y next c p := ⟨G,(hY.parents.bounds hM.1 hG).2,hG,hEdge⟩
  obtain ⟨_,s,_,b,_,pOld,_,hDec,hOldParent,hMapP⟩ := (hCopy.parents next c p).mp hParent
  have hSource := hDec.source_lt_last_d hM hC hT hA
  have hMapC := hDec.parent_copy_reconstruct_d hM hC hT hA
  obtain ⟨OldF,_,hOldF⟩ := hX.parents.total r (hY.parents.bounds hM.1 hF).1
  have hOldAnc := hNested.parent_lower_d hX hSucc hOldF hOldParent
  exact hCopy.ancestor_parent_copy_d hM hC hT hA hX hY hOldF hF hOldAnc hSource hMapP hMapC
    (hParent.bounds hM.1 hY).2.1

end KP1Y.OneYFinite.CopiedMountain.Ordinary
