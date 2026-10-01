import KP1Y.OneYCopyNestingDefs
import KP1Y.OneYLowerCopyRoots
import KP1Y.OneYCopyAncestryTransport
import KP1Y.OneYLowerRowShiftSuccessor

/-! 较低层复制的真实相邻行嵌套：低行、填充带、抬升带及锥外路径。 -/
namespace KP1Y.OneYFinite.CopiedMountain.Lower
open YesMetaZFC YesMetaZFC.SetTheory YesMetaZFC.SetTheory.Definitional
open KP1Y.Kuratowski KP1Y.Functions KP1Y.Naturals KP1Y.Bounded
open KP1Y.OneYFinite.CopyCoordinates
universe u

theorem Copies.low_parent_nonroot_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {D : Context M.Domain} (hD : D.Valid M C) {Y : Data M.Domain}
    {n r b s c p q : M.Domain} (hCopy : Copies M C T D n Y)
    (hLow : M.mem r D.floor) (hSource : s=D.coordinates.last ∨ M.mem s D.coordinates.last)
    (hNotRoot : s≠D.coordinates.root) (hMap : ParentCopy M C T D.coordinates b s c)
    (hMapP : ParentCopy M C T D.coordinates b p q) (hParent : ParentAt M D.mountain r s p)
    (hc : M.mem c n) : ParentAt M Y r c q := by
  have hr := (omega_isOrdinal_d hM hC.omega).transitive D.floor (hD.floor_nat hM.1) r hLow
  have hNoHigh : ¬(D.floor=r ∨ M.mem D.floor r) := by
    rintro (he | hlt)
    · exact SetTheory.KP.mem_irrefl_d (KP1Y.models_weakKP hM) r (he ▸ hLow)
    · exact SetTheory.KP.mem_irrefl_d (KP1Y.models_weakKP hM) D.floor
        (((omega_isOrdinal_d hM hC.omega).mem (hD.floor_nat hM.1)).transitive r hLow D.floor hlt)
  rcases hSource with he | hs
  · subst s
    have hNot : ¬M.mem D.coordinates.last D.coordinates.root := fun h =>
      SetTheory.KP.mem_irrefl_d (KP1Y.models_weakKP hM) D.coordinates.root
        (((omega_isOrdinal_d hM hC.omega).mem hD.coordinates.root).transitive D.coordinates.last h D.coordinates.root hD.coordinates.below)
    exact (hCopy.encoded_parent_iff_d hM hC hT hD hr ⟨hD.coordinates.below,Or.inl rfl⟩
      ((CopyCoordinates.parent_copy_bad_iff hNot).mp hMap) hc).mpr (Or.inr ⟨fun h => hNoHigh h.2,p,hMapP.1,hParent,hMapP⟩)
  · exact (hCopy.parents r c q).mpr ⟨hc,(parent_copy_nonroot_unmoved_d hM hC hT hD hr hs hNotRoot
      (fun h => hNoHigh h.2) hMap).mpr ⟨p,hMapP.1,hParent,hMapP⟩⟩

theorem Copies.prefix_ancestor_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {D : Context M.Domain} (hD : D.Valid M C) {Y : Data M.Domain} (hY : Y.Valid M C)
    {n r F G a c : M.Domain} (hCopy : Copies M C T D n Y)
    (hF : MemPair M D.mountain.parents r F) (hG : MemPair M Y.parents r G)
    (hAnc : Ancestor M C D.mountain.width F a c)
    (hOld : c=D.coordinates.last ∨ M.mem c D.coordinates.last) (hc : M.mem c Y.width) :
    Ancestor M C Y.width G a c := by
  have hw := omega_isOrdinal_d hM hC.omega
  have hCNat := hw.transitive D.mountain.width hD.mountain.width c (hAnc.bounds hM.1).2
  have hANat := hw.transitive D.mountain.width hD.mountain.width a (hAnc.bounds hM.1).1
  obtain ⟨J,hJ,hRows⟩ := CopyCoordinates.parent_copy_graph_exists_d hM hC hT hD.coordinates hC.zero_nat
  have hIdentity (p : M.Domain) (hp : M.mem p C.omega) : MemPair M J p p :=
    (hRows p p).mpr (CopyCoordinates.parent_copy_zero_d hM hC hT hD.coordinates hp)
  apply ancestor_map_refines_global_bounded_d hM hC (hD.mountain.forest r F hF) (hY.forest r G hG) hJ hAnc
    (hIdentity a hANat) (hIdentity c hCNat) hc
  intro d p u v hReach _ hParent hDU hPV hu
  have hUD := hJ.graph.unique d u d hDU (hIdentity d (hJ.graph.bounds hM.1 hDU).1)
  have hVP := hJ.graph.unique p v p hPV (hIdentity p (hJ.graph.bounds hM.1 hPV).1)
  subst u
  subst v
  have hdLast : d=D.coordinates.last ∨ M.mem d D.coordinates.last := by
    rcases hReach with he | hAncD
    · exact he.symm ▸ hOld
    · exact Or.inr (hOld.elim (fun he => he ▸ hAncD.1)
        (fun h => (hw.mem hD.coordinates.last).transitive c h d hAncD.1))
  have hAt := (hCopy.original_parents_d hM hC hD (hCopy.width ▸ hu) hdLast).mpr
    ⟨F,(hD.mountain.parents.bounds hM.1 hF).2,hF,hParent⟩
  obtain ⟨G',_,hG',hEdge⟩ := hAt
  exact ancestor_direct_d hM hC (hY.forest r G hG) (hY.parents.unique r G' G hG' hG ▸ hEdge)

theorem source_root_ancestor_last_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {D : Context M.Domain} (hD : D.Valid M C)
    {m : M.Domain} {R : RowStateSpace M.Domain} {V P H r F : M.Domain}
    (hRun : RowRun M C m R V P H) (hFrom : FromRun M C m R V H D.mountain)
    (hF : MemPair M D.mountain.parents r F) (hLe : r=D.floor ∨ M.mem r D.floor) :
    Ancestor M C D.mountain.width F D.coordinates.root D.coordinates.last := by
  obtain ⟨G,_,hG,hRoot⟩ := hD.last_root
  have hAnc : Ancestor M C D.mountain.width G D.coordinates.root D.coordinates.last := by
    rcases hRoot.2.2 with he | hAnc
    · exact False.elim (SetTheory.KP.mem_irrefl_d (KP1Y.models_weakKP hM) D.coordinates.last (he ▸ hD.coordinates.below))
    · exact hAnc
  obtain ⟨U,hAtF⟩ := (hFrom.parents r F).mp hF
  obtain ⟨W,hAtG⟩ := (hFrom.parents D.floor G).mp hG
  exact hFrom.width.symm ▸ hRun.ancestor_lower_d hM hC hAtF hAtG hLe (hFrom.width ▸ hAnc)

theorem Copies.low_ancestor_same_block_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {D : Context M.Domain} (hD : D.Valid M C) {Y : Data M.Domain} (hY : Y.Valid M C)
    {n r F G a s x c b : M.Domain} (hCopy : Copies M C T D n Y)
    (hLow : M.mem r D.floor)
    (hF : MemPair M D.mountain.parents r F) (hG : MemPair M Y.parents r G)
    (hAnc : Ancestor M C D.mountain.width F a s) (hAfter : D.coordinates.root=a ∨ M.mem D.coordinates.root a)
    (hSource : s=D.coordinates.last ∨ M.mem s D.coordinates.last)
    (hMapA : ParentCopy M C T D.coordinates b a x) (hMapC : ParentCopy M C T D.coordinates b s c) (hc : M.mem c Y.width) :
    Ancestor M C Y.width G x c := by
  have hw := omega_isOrdinal_d hM hC.omega
  obtain ⟨J,hJ,hRows⟩ := parent_copy_graph_exists_d hM hC hT hD.coordinates hMapC.2.1
  apply ancestor_map_refines_global_bounded_d hM hC (hD.mountain.forest r F hF) (hY.forest r G hG) hJ hAnc
    ((hRows a x).mpr hMapA) ((hRows s c).mpr hMapC) hc
  intro d p u v hReach hAP hParent hDU hPV hu
  have hpNat := (hJ.graph.bounds hM.1 hPV).1
  have hRootP : D.coordinates.root=p ∨ M.mem D.coordinates.root p := by
    rcases hAP with he | hap
    · exact he ▸ hAfter
    · exact Or.inr (hAfter.elim (fun he => he.symm ▸ hap) (fun h => (hw.mem hpNat).transitive a hap D.coordinates.root h))
  have hRootD : M.mem D.coordinates.root d := by
    have hpD := (hD.mountain.forest r F hF).left d p hParent
    exact hRootP.elim (fun he => he.symm ▸ hpD)
      (fun h => (hw.mem (hJ.graph.bounds hM.1 hDU).1).transitive p hpD D.coordinates.root h)
  have hDLast : d=D.coordinates.last ∨ M.mem d D.coordinates.last := by
    rcases hReach with he | hAncD
    · exact he.symm ▸ hSource
    · exact Or.inr (hSource.elim (fun he => he ▸ hAncD.1) (fun hs => (hw.mem hD.coordinates.last).transitive s hs d hAncD.1))
  have hParentAt := hCopy.low_parent_nonroot_d hM hC hT hD hLow hDLast
    (fun he => SetTheory.KP.mem_irrefl_d (KP1Y.models_weakKP hM) D.coordinates.root (he ▸ hRootD))
    ((hRows d u).mp hDU) ((hRows p v).mp hPV) ⟨F,(hD.mountain.parents.bounds hM.1 hF).2,hF,hParent⟩ (hCopy.width ▸ hu)
  obtain ⟨G',_,hG',hEdge⟩ := hParentAt
  exact ancestor_direct_d hM hC (hY.forest r G hG) (hY.parents.unique r G' G hG' hG ▸ hEdge)


private def rootPathSchema : Project.UnarySchema 18 where
  body := Project.Formula.forallMem (.bound 3)
    (.imp (parentCopyFormula ⟨.bound 19,.bound 18,.bound 17,.bound 16,.bound 15⟩
      ⟨.bound 14,.bound 13,.bound 12,.bound 11,.bound 10,.bound 9⟩ ⟨.bound 8,.bound 7,.bound 6,.bound 5⟩
      (.bound 1) (.bound 7) (.bound 0))
      (ancestorFormula ⟨.bound 19,.bound 18,.bound 17,.bound 16,.bound 15⟩ (.bound 4) (.bound 3) (.bound 2) (.bound 0)))
  freeClosed := by
    have hC : (⟨.bound 19,.bound 18,.bound 17,.bound 16,.bound 15⟩ : ExpressionData (Project.Term 20)).Closed := ⟨rfl,rfl,rfl,rfl,rfl⟩
    have hMap := parentCopyFormula_freeClosed hC
      (T := ⟨.bound 14,.bound 13,.bound 12,.bound 11,.bound 10,.bound 9⟩) ⟨rfl,rfl,rfl,rfl,rfl,rfl⟩
      (A := ⟨.bound 8,.bound 7,.bound 6,.bound 5⟩) ⟨rfl,rfl,rfl,rfl⟩ (.bound 1) (.bound 7) (.bound 0) rfl rfl rfl
    have hAnc := ancestorFormula_freeClosed hC (.bound 4) (.bound 3) (.bound 2) (.bound 0) rfl rfl rfl rfl
    simp [Project.Formula.forallMem,Definitional.Formula.FreeClosed,hMap,hAnc]

private def rootPathEnv {M : SetTheory.Structure.{u}} (C : ExpressionData M.Domain) (T : MatrixArithmetic M.Domain)
    (A : CopyCoordinates.Context M.Domain) (n G a : M.Domain) : Env M 18 :=
  (((((((((((((((((oneEnv C.omega).push C.zero).push C.one).push C.sequences).push C.expressions).push T.addPairs).push T.plus).push T.mulPairs).push T.times).push T.diffPairs).push T.difference).push A.last).push A.root).push A.length).push A.first).push n).push G).push a

private theorem rootPathSchema_iff {M : SetTheory.Structure.{u}} (he : Extensional M)
    (C : ExpressionData M.Domain) (T : MatrixArithmetic M.Domain) (A : CopyCoordinates.Context M.Domain) (n G a b : M.Domain) :
    Project.Formula.satisfies ((rootPathEnv C T A n G a).push b) rootPathSchema.body ↔
      ∀c, M.mem c n → ParentCopy M C T A b A.root c → Ancestor M C n G a c := by
  simp only [rootPathSchema,Project.Formula.satisfies_forallMem_iff,Project.Formula.satisfies_imp_iff,
    parentCopyFormula_iff he,ancestorFormula_iff he]
  rfl

/-- 原根左侧的祖先跨过任意内部有限个接缝，复制编号归纳完全位于对象ω。 -/
theorem Copies.root_good_ancestor_low_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {D : Context M.Domain} (hD : D.Valid M C) {Y : Data M.Domain} (hY : Y.Valid M C)
    {m : M.Domain} {R : RowStateSpace M.Domain} {V P H n r F G a b c : M.Domain}
    (hRun : RowRun M C m R V P H) (hFrom : FromRun M C m R V H D.mountain)
    (hCopy : Copies M C T D n Y) (hLow : M.mem r D.floor)
    (hF : MemPair M D.mountain.parents r F) (hG : MemPair M Y.parents r G)
    (hAnc : Ancestor M C D.mountain.width F a D.coordinates.root) (hMap : ParentCopy M C T D.coordinates b D.coordinates.root c) (hc : M.mem c Y.width) :
    Ancestor M C Y.width G a c := by
  have hw := omega_isOrdinal_d hM hC.omega
  have hRootLast := source_root_ancestor_last_d hM hC hD hRun hFrom hF (Or.inr hLow)
  have hNot : ¬M.mem D.coordinates.root D.coordinates.root := SetTheory.KP.mem_irrefl_d (KP1Y.models_weakKP hM) D.coordinates.root
  have hAll := natural_induction_d hM rootPathSchema (rootPathEnv C T D.coordinates Y.width G a) hC.omega
    (fun z hz => (rootPathSchema_iff hM.1 C T D.coordinates Y.width G a z).mpr (by
      intro child hChild hMap
      have hZ := hM.1.eq_of_same_members z C.zero (fun t => iff_of_false (hz t) (hC.zero_empty t))
      subst z
      have hChildEq := encode_unique hM.1 hT ((parent_copy_bad_iff hNot).mp hMap) (encode_zero_d hM hC hT hD.coordinates hD.coordinates.root)
      subst child
      exact hCopy.prefix_ancestor_d hM hC hT hD hY hF hG hAnc (Or.inr hD.coordinates.below) hChild))
    (fun block hBlock ih next hSucc => (rootPathSchema_iff hM.1 C T D.coordinates Y.width G a next).mpr (by
      intro child hChild hMap
      obtain ⟨boundary,_,hWidth⟩ := encode_exists_d hM hC hT hD.coordinates hD.coordinates.last hBlock
      have hChildEq := encode_unique hM.1 hT ((parent_copy_bad_iff hNot).mp hMap)
        (width_is_next_cut_d hM hC hT hD.coordinates hSucc hWidth)
      have hWidthChild : Width M C T D.coordinates block child := hChildEq.symm ▸ hWidth
      obtain ⟨cut,_,hCut⟩ := encode_exists_d hM hC hT hD.coordinates hD.coordinates.root hBlock
      have hRootCopy : ParentCopy M C T D.coordinates block D.coordinates.root cut := (parent_copy_bad_iff hNot).mpr hCut
      have hCutChild := cut_lt_width_d hM hC hT hD.coordinates hWidthChild hCut
      have hCutMem := (hw.mem hY.width).transitive child hChild cut hCutChild
      have hToCut := (rootPathSchema_iff hM.1 C T D.coordinates Y.width G a block).mp ih cut hCutMem hRootCopy
      have hLastNot : ¬M.mem D.coordinates.last D.coordinates.root := fun h => SetTheory.KP.mem_irrefl_d (KP1Y.models_weakKP hM) D.coordinates.root
        ((hw.mem hD.coordinates.root).transitive D.coordinates.last h D.coordinates.root hD.coordinates.below)
      have hLastCopy : ParentCopy M C T D.coordinates block D.coordinates.last child := (parent_copy_bad_iff hLastNot).mpr hWidthChild
      have hAcross := hCopy.low_ancestor_same_block_d hM hC hT hD hY hLow hF hG hRootLast
        (Or.inl rfl) (Or.inl rfl) hRootCopy hLastCopy hChild
      exact ancestor_trans_d hM hC (hY.forest r G hG) hToCut hAcross))
  exact (rootPathSchema_iff hM.1 C T D.coordinates Y.width G a b).mp (hAll b hMap.2.1) c hc hMap

/-- 低行完整祖先运输；源根父边可以替换为跨副本的非空路径。 -/
theorem Copies.low_ancestor_parent_copy_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {D : Context M.Domain} (hD : D.Valid M C) {Y : Data M.Domain} (hY : Y.Valid M C)
    {m : M.Domain} {R : RowStateSpace M.Domain} {V P H n r F G a s x c b : M.Domain}
    (hRun : RowRun M C m R V P H) (hFrom : FromRun M C m R V H D.mountain)
    (hCopy : Copies M C T D n Y) (hLow : M.mem r D.floor)
    (hF : MemPair M D.mountain.parents r F) (hG : MemPair M Y.parents r G)
    (hAnc : Ancestor M C D.mountain.width F a s) (hSource : s=D.coordinates.last ∨ M.mem s D.coordinates.last)
    (hMapA : ParentCopy M C T D.coordinates b a x) (hMapC : ParentCopy M C T D.coordinates b s c) (hc : M.mem c Y.width) :
    Ancestor M C Y.width G x c := by
  have hw := omega_isOrdinal_d hM hC.omega
  obtain ⟨J,hJ,hRows⟩ := parent_copy_graph_exists_d hM hC hT hD.coordinates hMapC.2.1
  apply ancestor_map_refines_global_bounded_d hM hC (hD.mountain.forest r F hF) (hY.forest r G hG) hJ hAnc
    ((hRows a x).mpr hMapA) ((hRows s c).mpr hMapC) hc
  intro d p u v hReach _ hParent hDU hPV hu
  have hDLast : d=D.coordinates.last ∨ M.mem d D.coordinates.last := by
    rcases hReach with he | hAncD
    · exact he.symm ▸ hSource
    · exact Or.inr (hSource.elim (fun he => he ▸ hAncD.1) (fun hs => (hw.mem hD.coordinates.last).transitive s hs d hAncD.1))
  classical
  by_cases hRoot : d=D.coordinates.root
  · subst d
    have hGood := (hD.mountain.forest r F hF).left D.coordinates.root p hParent
    have hVP := (parent_copy_good_iff hMapC.2.1 (hJ.graph.bounds hM.1 hPV).1 hGood).mp ((hRows p v).mp hPV)
    subst v
    exact hCopy.root_good_ancestor_low_d hM hC hT hD hY hRun hFrom hLow hF hG
      (ancestor_direct_d hM hC (hD.mountain.forest r F hF) hParent) ((hRows D.coordinates.root u).mp hDU) hu
  · have hAt := hCopy.low_parent_nonroot_d hM hC hT hD hLow hDLast hRoot
      ((hRows d u).mp hDU) ((hRows p v).mp hPV) ⟨F,(hD.mountain.parents.bounds hM.1 hF).2,hF,hParent⟩ (hCopy.width ▸ hu)
    obtain ⟨G',_,hG',hEdge⟩ := hAt
    exact ancestor_direct_d hM hC (hY.forest r G hG) (hY.parents.unique r G' G hG' hG ▸ hEdge)


/-- 锥外高行的全部经过节点仍在锥外，故父边保持普通复制。 -/
theorem Copies.outside_high_ancestor_copy_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {D : Context M.Domain} (hD : D.Valid M C) {Y : Data M.Domain} (hY : Y.Valid M C)
    {m : M.Domain} {R : RowStateSpace M.Domain} {V P H n r F G a s x c b : M.Domain}
    (hRun : RowRun M C m R V P H) (hFrom : FromRun M C m R V H D.mountain)
    (hCopy : Copies M C T D n Y) (hHigh : D.floor=r ∨ M.mem D.floor r)
    (hF : MemPair M D.mountain.parents r F) (hG : MemPair M Y.parents r G)
    (hAnc : Ancestor M C D.mountain.width F a s) (hSource : M.mem s D.coordinates.last)
    (hOut : ¬InCone M C D s) (hMapA : ParentCopy M C T D.coordinates b a x)
    (hMapC : ParentCopy M C T D.coordinates b s c) (hc : M.mem c Y.width) : Ancestor M C Y.width G x c := by
  have hw := omega_isOrdinal_d hM hC.omega
  have hr := (hD.mountain.parents.bounds hM.1 hF).1
  obtain ⟨J,hJ,hRows⟩ := parent_copy_graph_exists_d hM hC hT hD.coordinates hMapC.2.1
  apply ancestor_map_refines_global_bounded_d hM hC (hD.mountain.forest r F hF) (hY.forest r G hG) hJ hAnc
    ((hRows a x).mpr hMapA) ((hRows s c).mpr hMapC) hc
  intro d p u v hReach _ hParent hDU hPV hu
  have hOutD : ¬InCone M C D d := by
    rcases hReach with he | hAncD
    · exact he.symm ▸ hOut
    · exact fun h => hOut ((in_cone_ancestor_iff_d hM hC hD hRun hFrom hHigh hF hAncD).mp h)
  have hdLast : M.mem d D.coordinates.last := hReach.elim (fun he => he.symm ▸ hSource)
    (fun h => (hw.mem hD.coordinates.last).transitive s hSource d h.1)
  have hNonroot : d≠D.coordinates.root := fun he => hOutD (he.symm ▸ in_cone_root_d hM hD)
  have hAt := (hCopy.parents r u v).mpr ⟨hCopy.width ▸ hu,
    (parent_copy_nonroot_unmoved_d hM hC hT hD hr hdLast hNonroot (fun h => hOutD h.1) ((hRows d u).mp hDU)).mpr
      ⟨p,(hJ.graph.bounds hM.1 hPV).1,⟨F,(hD.mountain.parents.bounds hM.1 hF).2,hF,hParent⟩,(hRows p v).mp hPV⟩⟩
  obtain ⟨G',_,hG',hEdge⟩ := hAt
  exact ancestor_direct_d hM hC (hY.forest r G hG) (hY.parents.unique r G' G hG' hG ▸ hEdge)

private theorem low_of_not_high_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {a b : M.Domain} (ha : M.mem a C.omega) (hb : M.mem b C.omega)
    (hNot : ¬(a=b ∨ M.mem a b)) : M.mem b a := by
  rcases (omega_isOrdinal_d hM hC.omega).wellOrder.linear.compare a ha b hb with he | hlt | hgt
  · exact False.elim (hNot (Or.inl (hM.1.eq_of_same_members a b he)))
  · exact False.elim (hNot (Or.inr hlt))
  · exact hgt

private theorem high_of_not_low_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {a b : M.Domain} (ha : M.mem a C.omega) (hb : M.mem b C.omega)
    (hNot : ¬M.mem b a) : a=b ∨ M.mem a b := by
  rcases (omega_isOrdinal_d hM hC.omega).wellOrder.linear.compare a ha b hb with he | hlt | hgt
  · exact Or.inl (hM.1.eq_of_same_members a b he)
  · exact Or.inr hlt
  · exact False.elim (hNot hgt)

theorem Copies.unmoved_nested_step_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {D : Context M.Domain} (hD : D.Valid M C) {Y : Data M.Domain} (hY : Y.Valid M C)
    {m : M.Domain} {R : RowStateSpace M.Domain} {V P H n r next F s b c pOld p : M.Domain}
    (hRun : RowRun M C m R V P H) (hFrom : FromRun M C m R V H D.mountain)
    (hCopy : Copies M C T D n Y) (hSucc : M.SuccessorOf next r) (hF : MemPair M Y.parents r F)
    (hSource : Source M D.coordinates s) (hEncode : Encode M C T D.coordinates s b c) (hc : M.mem c n)
    (hNoMove : ¬(InCone M C D s ∧ (D.floor=next ∨ M.mem D.floor next)))
    (hOldParent : ParentAt M D.mountain next s pOld) (hMapP : ParentCopy M C T D.coordinates b pOld p) :
    Ancestor M C Y.width F p c := by
  have hw := omega_isOrdinal_d hM hC.omega
  have hr := (hY.parents.bounds hM.1 hF).1
  have hNext := (hOldParent.bounds hM.1 hD.mountain).1
  obtain ⟨OldF,_,hOldF⟩ := hD.mountain.parents.total r hr
  have hOldAnc := (hFrom.nested_d hM hC hRun hD.mountain).parent_lower_d hD.mountain hSucc hOldF hOldParent
  have hNotGood : ¬M.mem s D.coordinates.root := fun h => SetTheory.KP.mem_irrefl_d (KP1Y.models_weakKP hM) D.coordinates.root
    ((hw.mem hD.coordinates.root).transitive s h D.coordinates.root hSource.1)
  have hMapC : ParentCopy M C T D.coordinates b s c := (parent_copy_bad_iff hNotGood).mpr hEncode
  classical
  by_cases hLow : M.mem r D.floor
  · exact hCopy.low_ancestor_parent_copy_d hM hC hT hD hY hRun hFrom hLow hOldF hF hOldAnc hSource.2 hMapP hMapC (hCopy.width.symm ▸ hc)
  · have hHigh := high_of_not_low_d hM hC (hD.floor_nat hM.1) hr hLow
    have hOut : ¬InCone M C D s := by
      intro hCone
      have hHighNext : D.floor=next ∨ M.mem D.floor next := Or.inr
        (hHigh.elim (fun he => he.symm ▸ hSucc.predecessor_mem)
          (fun h => (hw.mem hNext).transitive r hSucc.predecessor_mem D.floor h))
      exact hNoMove ⟨hCone,hHighNext⟩
    have hSourceLt := hSource.2.resolve_left (fun he => hOut (he.symm ▸ in_cone_last hD))
    exact hCopy.outside_high_ancestor_copy_d hM hC hT hD hY hRun hFrom hHigh hOldF hF hOldAnc hSourceLt hOut
      hMapP hMapC (hCopy.width.symm ▸ hc)

theorem Copies.moved_nested_step_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {D : Context M.Domain} (hD : D.Valid M C) {Y : Data M.Domain} (hY : Y.Valid M C)
    {m : M.Domain} {R : RowStateSpace M.Domain} {V P H n r next F s b c p : M.Domain}
    (hRun : RowRun M C m R V P H) (hFrom : FromRun M C m R V H D.mountain)
    (hCopy : Copies M C T D n Y) (hSucc : M.SuccessorOf next r) (hF : MemPair M Y.parents r F)
    (hSource : Source M D.coordinates s) (hEncode : Encode M C T D.coordinates s b c) (hc : M.mem c n)
    (hMoves : InCone M C D s ∧ (D.floor=next ∨ M.mem D.floor next))
    (hMoved : MovedParent M C T D next s b p) : Ancestor M C Y.width F p c := by
  have hw := omega_isOrdinal_d hM hC.omega
  have hr := (hY.parents.bounds hM.1 hF).1
  obtain ⟨off,hOff,hTimes,upper,hUpper,hShiftUpper,pOld,_,hOldParent,hEncodeP⟩ := hMoved
  have hConeP := hMoves.1.high_parent_d hM hC hD (hShiftUpper.floor_le_d hM hC hT) hOldParent
  have hMapP : ParentCopy M C T D.coordinates b pOld p := (parent_copy_bad_iff (hConeP.not_good_d hM hC hD)).mpr hEncodeP
  have hNotGood : ¬M.mem s D.coordinates.root := fun h => SetTheory.KP.mem_irrefl_d (KP1Y.models_weakKP hM) D.coordinates.root
    ((hw.mem hD.coordinates.root).transitive s h D.coordinates.root hSource.1)
  have hMapC : ParentCopy M C T D.coordinates b s c := (parent_copy_bad_iff hNotGood).mpr hEncode
  have hNested := hFrom.nested_d hM hC hRun hD.mountain
  classical
  by_cases hLow : M.mem r D.floor
  · have hNextFloor : next=D.floor := by
      rcases hMoves.2 with he | hlt
      · exact he.symm
      · rcases (hSucc D.floor).mp hlt with hFloorR | he
        · exact False.elim (SetTheory.KP.mem_irrefl_d (KP1Y.models_weakKP hM) D.floor
            ((hw.mem (hD.floor_nat hM.1)).transitive r hLow D.floor hFloorR))
        · have hFloorEq := hM.1.eq_of_same_members D.floor r he
          exact False.elim (SetTheory.KP.mem_irrefl_d (KP1Y.models_weakKP hM) r (hFloorEq ▸ hLow))
    have hAtFloor : ShiftedRow M C T D.floor off D.floor upper := hNextFloor ▸ hShiftUpper
    have hUpperNext : upper=next := (hAtFloor.floor_value_d hM hC hT).trans hNextFloor.symm
    have hParentNext : ParentAt M D.mountain next s pOld := hUpperNext ▸ hOldParent
    obtain ⟨OldF,_,hOldF⟩ := hD.mountain.parents.total r hr
    exact hCopy.low_ancestor_parent_copy_d hM hC hT hD hY hRun hFrom hLow hOldF hF
      (hNested.parent_lower_d hD.mountain hSucc hOldF hParentNext) hSource.2 hMapP hMapC (hCopy.width.symm ▸ hc)
  · have hHigh := high_of_not_low_d hM hC (hD.floor_nat hM.1) hr hLow
    obtain ⟨lower,hShiftLower⟩ := shifted_row_exists_d hM hC hT (hD.floor_nat hM.1) hOff hr
    rcases hShiftLower.successor_cases_d hM hC hT hShiftUpper hSucc with hSame | hNext
    · have hParentLower : ParentAt M D.mountain lower s pOld := hSame ▸ hOldParent
      have hCurrent := (hCopy.encoded_parent_iff_d hM hC hT hD hr hSource hEncode hc).mpr
        (Or.inl ⟨⟨hMoves.1,hHigh⟩,off,hOff,hTimes,lower,hShiftLower.2.1,hShiftLower,pOld,hMapP.1,hParentLower,hEncodeP⟩)
      obtain ⟨F',_,hF',hEdge⟩ := hCurrent
      exact ancestor_direct_d hM hC (hY.forest r F hF) (hY.parents.unique r F' F hF' hF ▸ hEdge)
    · obtain ⟨OldF,_,hOldF⟩ := hD.mountain.parents.total lower hShiftLower.2.1
      exact hCopy.high_ancestor_copy_d hM hC hT hD hRun hFrom hY hSource hMoves.1 hHigh hTimes hShiftLower hEncode hc
        hOldF hF (hNested.parent_lower_d hD.mountain hNext hOldF hOldParent) hMapP

/-- 同一复制列的每个后继行父边，都在其前一行有实际有限祖先路径。 -/
theorem Copies.encoded_nested_step_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {D : Context M.Domain} (hD : D.Valid M C) {Y : Data M.Domain} (hY : Y.Valid M C)
    {m : M.Domain} {R : RowStateSpace M.Domain} {V P H n r next F s b c p : M.Domain}
    (hRun : RowRun M C m R V P H) (hFrom : FromRun M C m R V H D.mountain)
    (hCopy : Copies M C T D n Y) (hSucc : M.SuccessorOf next r) (hF : MemPair M Y.parents r F)
    (hSource : Source M D.coordinates s) (hEncode : Encode M C T D.coordinates s b c) (hc : M.mem c n)
    (hParent : ParentAt M Y next c p) : Ancestor M C Y.width F p c := by
  rcases (hCopy.encoded_parent_iff_d hM hC hT hD (hParent.bounds hM.1 hY).1 hSource hEncode hc).mp hParent with
    ⟨hMoves,hMoved⟩ | ⟨hNoMove,pOld,_,hOldParent,hMapP⟩
  · exact hCopy.moved_nested_step_d hM hC hT hD hY hRun hFrom hSucc hF hSource hEncode hc hMoves hMoved
  · exact hCopy.unmoved_nested_step_d hM hC hT hD hY hRun hFrom hSucc hF hSource hEncode hc hNoMove hOldParent hMapP

/-- 完整Lower复制嵌套；所需源Root/锥性质来自真实FromRun和已证明的Context.Valid。 -/
theorem Copies.nested_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {D : Context M.Domain} (hD : D.Valid M C) {Y : Data M.Domain} (hY : Y.Valid M C)
    {m : M.Domain} {R : RowStateSpace M.Domain} {V P H n : M.Domain}
    (hRun : RowRun M C m R V P H) (hFrom : FromRun M C m R V H D.mountain)
    (hCopy : Copies M C T D n Y) : Nested M C Y := by
  have hw := omega_isOrdinal_d hM hC.omega
  have hNested := hFrom.nested_d hM hC hRun hD.mountain
  intro r next F G hSucc hF hG c p hEdge
  have hParent : ParentAt M Y next c p := ⟨G,(hY.parents.bounds hM.1 hG).2,hG,hEdge⟩
  have hc := (hParent.bounds hM.1 hY).2.1
  have hSaved := ((hCopy.parents next c p).mp hParent).2
  rcases hSaved.2.2 with ⟨hOld,hOldParent⟩ | ⟨hNew,s,_,b,_,hRaw,_⟩
  · obtain ⟨OldF,_,hOldF⟩ := hD.mountain.parents.total r (hY.parents.bounds hM.1 hF).1
    exact hCopy.prefix_ancestor_d hM hC hT hD hY hOldF hF
      (hNested.parent_lower_d hD.mountain hSucc hOldF hOldParent) hOld hc
  · have hRootC : M.mem D.coordinates.root c :=
      (hw.mem (hw.transitive Y.width hY.width c hc)).transitive D.coordinates.last hNew D.coordinates.root hD.coordinates.below
    obtain ⟨hSource,hEncode⟩ := (raw_decoded_active_iff hRootC).mp hRaw
    exact hCopy.encoded_nested_step_d hM hC hT hD hY hRun hFrom hSucc hF hSource hEncode (hCopy.width ▸ hc) hParent

end KP1Y.OneYFinite.CopiedMountain.Lower
