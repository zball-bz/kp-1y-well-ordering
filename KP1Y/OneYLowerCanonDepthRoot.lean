import KP1Y.OneYLowerCanonDepth

/-! Lower复制：原列深度相等、root跨接缝祖先、好部父列的深度相等。 -/
namespace KP1Y.OneYFinite.CopiedMountain.Lower
open YesMetaZFC YesMetaZFC.SetTheory YesMetaZFC.SetTheory.Definitional
open KP1Y.Kuratowski KP1Y.Functions KP1Y.Naturals KP1Y.Bounded KP1Y.Arithmetic
open KP1Y.OneYFinite.CopyCoordinates KP1Y.OneYFinite.LowerCanon
universe u

private theorem not_mem_of_le' {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {a b : M.Domain} (hb : M.mem b C.omega)
    (hab : a=b ∨ M.mem a b) : ¬M.mem b a := by
  intro hba
  rcases hab with he | hab
  · exact SetTheory.KP.mem_irrefl_d (KP1Y.models_weakKP hM) b (he ▸ hba)
  · exact SetTheory.KP.mem_irrefl_d (KP1Y.models_weakKP hM) b
      (((omega_isOrdinal_d hM hC.omega).mem hb).transitive a hab b hba)

/-- 原列（≤last）在同一行的源/目标深度相等。 -/
theorem Copies.canon_depth_original_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {D : Context M.Domain} (hD : D.Valid M C) {Y : Data M.Domain} (hY : Y.Valid M C) {n : M.Domain}
    (hCopy : Copies M C T D n Y) {r F G c d : M.Domain}
    (hF : MemPair M D.mountain.parents r F) (hG : MemPair M Y.parents r G)
    (hcLast : c=D.coordinates.last ∨ M.mem c D.coordinates.last) (hc : M.mem c Y.width)
    (hDC : Depth M C D.mountain.width F c d) : Depth M C Y.width G c d := by
  have hw := omega_isOrdinal_d hM hC.omega
  have hFF := hD.mountain.forest r F hF
  obtain ⟨J,hJ,hRows⟩ := parent_copy_graph_exists_d hM hC hT hD.coordinates hC.zero_nat
  have hId (p : M.Domain) (hp : M.mem p C.omega) : MemPair M J p p := (hRows p p).mpr (parent_copy_zero_d hM hC hT hD.coordinates hp)
  have hIdEq {p v : M.Domain} (hPV : MemPair M J p v) : v=p :=
    hJ.graph.unique p v p hPV (hId p (hJ.graph.bounds hM.1 hPV).1)
  have hcNat := hw.transitive Y.width hY.width c hc
  have hChainLast (d : M.Domain) (hDC' : d=c ∨ Ancestor M C D.mountain.width F d c) :
      d=D.coordinates.last ∨ M.mem d D.coordinates.last := by
    rcases hDC' with he | hAnc
    · exact he.symm ▸ hcLast
    · exact Or.inr (hcLast.elim (fun he => he ▸ hAnc.1)
        (fun h => (hw.mem hD.coordinates.last).transitive c h d hAnc.1))
  have hChainWidth (d : M.Domain) (hDC' : d=c ∨ Ancestor M C D.mountain.width F d c) : M.mem d Y.width := by
    rcases hDC' with he | hAnc
    · exact he ▸ hc
    · exact (hw.mem hY.width).transitive c hc d hAnc.1
  apply depth_mapped_eq_d hM hC hFF (hY.forest r G hG) hJ (hId c hcNat) hc ?_ ?_ hDC
  · intro d p u v hDC' hDP hDU hPV
    have hud := hIdEq hDU
    have hvp := hIdEq hPV
    subst u
    subst v
    have hAt := (hCopy.original_parents_d hM hC hD (hCopy.width ▸ hChainWidth d hDC') (hChainLast d hDC')).mpr
      ⟨F,(hD.mountain.parents.bounds hM.1 hF).2,hF,hDP⟩
    exact (canon_row_parent_iff hM.1 hY hG).mp hAt
  · intro q x hQC hNo hQX p _ hP
    have hxq := hIdEq hQX
    subst x
    have hAt := (canon_row_parent_iff hM.1 hY hG).mpr hP
    have hOld := (hCopy.original_parents_d hM hC hD (hCopy.width ▸ hChainWidth q hQC) (hChainLast q hQC)).mp hAt
    have hPF := (canon_row_parent_iff hM.1 hD.mountain hF).mp hOld
    exact hNo p (hFF.bounds hM.1 hPF).2 hPF

private def seamEnv {M : SetTheory.Structure.{u}} (C : ExpressionData M.Domain) (T : MatrixArithmetic M.Domain)
    (A : CopyCoordinates.Context M.Domain) (n G : M.Domain) : Env M 17 :=
  ((((((((((((((((oneEnv C.omega).push C.zero).push C.one).push C.sequences).push C.expressions).push T.addPairs).push T.plus).push T.mulPairs).push T.times).push T.diffPairs).push T.difference).push A.last).push A.root).push A.length).push A.first).push n).push G

private def seamSchema : Project.UnarySchema 17 where
  body := Project.Formula.forallMem (.bound 2)
    (.imp (parentCopyFormula ⟨.bound 18,.bound 17,.bound 16,.bound 15,.bound 14⟩
      ⟨.bound 13,.bound 12,.bound 11,.bound 10,.bound 9,.bound 8⟩ ⟨.bound 7,.bound 6,.bound 5,.bound 4⟩
      (.bound 1) (.bound 6) (.bound 0))
      (.disj (Project.Formula.extensionalEq (.bound 6) (.bound 0))
        (ancestorFormula ⟨.bound 18,.bound 17,.bound 16,.bound 15,.bound 14⟩ (.bound 3) (.bound 2) (.bound 6) (.bound 0))))
  freeClosed := by
    have hC : (⟨.bound 18,.bound 17,.bound 16,.bound 15,.bound 14⟩ : ExpressionData (Project.Term 19)).Closed := ⟨rfl,rfl,rfl,rfl,rfl⟩
    have hMap := parentCopyFormula_freeClosed hC
      (T := ⟨.bound 13,.bound 12,.bound 11,.bound 10,.bound 9,.bound 8⟩) ⟨rfl,rfl,rfl,rfl,rfl,rfl⟩
      (A := ⟨.bound 7,.bound 6,.bound 5,.bound 4⟩) ⟨rfl,rfl,rfl,rfl⟩ (.bound 1) (.bound 6) (.bound 0) rfl rfl rfl
    have hAnc := ancestorFormula_freeClosed hC (.bound 3) (.bound 2) (.bound 6) (.bound 0) rfl rfl rfl rfl
    simp [Project.Formula.forallMem,Definitional.Formula.FreeClosed,hMap,hAnc,Project.Formula.extensionalEq]

private theorem seamSchema_iff {M : SetTheory.Structure.{u}} (he : Extensional M)
    (C : ExpressionData M.Domain) (T : MatrixArithmetic M.Domain) (A : CopyCoordinates.Context M.Domain) (n G b : M.Domain) :
    Project.Formula.satisfies ((seamEnv C T A n G).push b) seamSchema.body ↔
      ∀c, M.mem c n → ParentCopy M C T A b A.root c → (A.root=c ∨ Ancestor M C n G A.root c) := by
  simp only [seamSchema,Project.Formula.satisfies_forallMem_iff,Project.Formula.satisfies_imp_iff,
    parentCopyFormula_iff he,Project.Formula.satisfies_disj_iff,Project.Formula.satisfies_extensionalEq_iff_eq he,
    ancestorFormula_iff he]
  rfl

/-- 低行中，root本身是其任意副本（接缝列）的祖先或等于它；对内部块号作对象归纳。 -/
theorem Copies.canon_root_seam_low_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {D : Context M.Domain} (hD : D.Valid M C) {Y : Data M.Domain} (hY : Y.Valid M C) {n : M.Domain}
    (hCopy : Copies M C T D n Y) {m : M.Domain} {R : RowStateSpace M.Domain} {V P H : M.Domain}
    (hRun : RowRun M C m R V P H) (hFrom : FromRun M C m R V H D.mountain) {r F G b w : M.Domain}
    (hLow : M.mem r D.floor) (hF : MemPair M D.mountain.parents r F) (hG : MemPair M Y.parents r G)
    (hMap : ParentCopy M C T D.coordinates b D.coordinates.root w) (hw : M.mem w Y.width) :
    D.coordinates.root=w ∨ Ancestor M C Y.width G D.coordinates.root w := by
  have hω := omega_isOrdinal_d hM hC.omega
  have hRootLast := source_root_ancestor_last_d hM hC hD hRun hFrom hF (Or.inr hLow)
  have hNot : ¬M.mem D.coordinates.root D.coordinates.root := SetTheory.KP.mem_irrefl_d (KP1Y.models_weakKP hM) D.coordinates.root
  have hLastNot : ¬M.mem D.coordinates.last D.coordinates.root := fun h => SetTheory.KP.mem_irrefl_d (KP1Y.models_weakKP hM)
    D.coordinates.root ((hω.mem hD.coordinates.root).transitive D.coordinates.last h D.coordinates.root hD.coordinates.below)
  have hAll := natural_induction_d hM seamSchema (seamEnv C T D.coordinates Y.width G) hC.omega
    (fun z hz => (seamSchema_iff hM.1 C T D.coordinates Y.width G z).mpr (by
      intro child _ hMap
      have hZ := hM.1.eq_of_same_members z C.zero (fun t => iff_of_false (hz t) (hC.zero_empty t))
      subst z
      exact Or.inl (encode_unique hM.1 hT (encode_zero_d hM hC hT hD.coordinates hD.coordinates.root)
        ((parent_copy_bad_iff hNot).mp hMap))))
    (fun block hBlock ih next hSucc => (seamSchema_iff hM.1 C T D.coordinates Y.width G next).mpr (by
      intro child hChild hMap
      obtain ⟨boundary,_,hWidth⟩ := encode_exists_d hM hC hT hD.coordinates hD.coordinates.last hBlock
      have hChildEq := encode_unique hM.1 hT ((parent_copy_bad_iff hNot).mp hMap)
        (width_is_next_cut_d hM hC hT hD.coordinates hSucc hWidth)
      have hWidthChild : Width M C T D.coordinates block child := hChildEq.symm ▸ hWidth
      obtain ⟨cut,_,hCut⟩ := encode_exists_d hM hC hT hD.coordinates hD.coordinates.root hBlock
      have hRootCopy : ParentCopy M C T D.coordinates block D.coordinates.root cut := (parent_copy_bad_iff hNot).mpr hCut
      have hCutChild := cut_lt_width_d hM hC hT hD.coordinates hWidthChild hCut
      have hCutMem := (hω.mem hY.width).transitive child hChild cut hCutChild
      have hToCut := (seamSchema_iff hM.1 C T D.coordinates Y.width G block).mp ih cut hCutMem hRootCopy
      have hLastCopy : ParentCopy M C T D.coordinates block D.coordinates.last child :=
        (parent_copy_bad_iff hLastNot).mpr hWidthChild
      have hAcross := hCopy.low_ancestor_same_block_d hM hC hT hD hY hLow hF hG hRootLast
        (Or.inl rfl) (Or.inl rfl) hRootCopy hLastCopy hChild
      exact Or.inr (hToCut.elim (fun he => he ▸ hAcross)
        (fun h => ancestor_trans_d hM hC (hY.forest r G hG) h hAcross))))
  exact (seamSchema_iff hM.1 C T D.coordinates Y.width G b).mp (hAll b hMap.2.1) w hw hMap

/-- 低行中root为源列q的祖先（或q=root）时，root仍是q任意副本的祖先（或相等）。 -/
theorem Copies.canon_root_ancestor_low_copy_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {D : Context M.Domain} (hD : D.Valid M C) {Y : Data M.Domain} (hY : Y.Valid M C) {n : M.Domain}
    (hCopy : Copies M C T D n Y) {m : M.Domain} {R : RowStateSpace M.Domain} {V P H : M.Domain}
    (hRun : RowRun M C m R V P H) (hFrom : FromRun M C m R V H D.mountain) {r F G q b w : M.Domain}
    (hLow : M.mem r D.floor) (hF : MemPair M D.mountain.parents r F) (hG : MemPair M Y.parents r G)
    (hqLast : q=D.coordinates.last ∨ M.mem q D.coordinates.last)
    (hRQ : D.coordinates.root=q ∨ Ancestor M C D.mountain.width F D.coordinates.root q)
    (hMap : ParentCopy M C T D.coordinates b q w) (hw : M.mem w Y.width) :
    D.coordinates.root=w ∨ Ancestor M C Y.width G D.coordinates.root w := by
  rcases hRQ with he | hAnc
  · subst q
    exact hCopy.canon_root_seam_low_d hM hC hT hD hY hRun hFrom hLow hF hG hMap hw
  · have hNot : ¬M.mem D.coordinates.root D.coordinates.root :=
      SetTheory.KP.mem_irrefl_d (KP1Y.models_weakKP hM) D.coordinates.root
    obtain ⟨cut,_,hCut⟩ := encode_exists_d hM hC hT hD.coordinates hD.coordinates.root hMap.2.1
    have hMapCut : ParentCopy M C T D.coordinates b D.coordinates.root cut := (parent_copy_bad_iff hNot).mpr hCut
    have hAcross := hCopy.low_ancestor_parent_copy_d hM hC hT hD hY hRun hFrom hLow hF hG hAnc hqLast hMapCut hMap hw
    have hSeam := hCopy.canon_root_seam_low_d hM hC hT hD hY hRun hFrom hLow hF hG hMapCut (hAcross.bounds hM.1).1
    exact Or.inr (hSeam.elim (fun he => he ▸ hAcross) (fun h => ancestor_trans_d hM hC (hY.forest r G hG) h hAcross))

/-- 源行u的父为好部的非root坏部列在锥外。 -/
theorem canon_good_parent_out_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {D : Context M.Domain} (hD : D.Valid M C)
    {m : M.Domain} {R : RowStateSpace M.Domain} {V P H : M.Domain}
    (hRun : RowRun M C m R V P H) (hFrom : FromRun M C m R V H D.mountain) {u Fu c g : M.Domain}
    (hRootC : M.mem D.coordinates.root c) (hFu : MemPair M D.mountain.parents u Fu) (hGood : MemPair M Fu c g)
    (hg : M.mem g D.coordinates.root) : ¬InCone M C D c := by
  have hω := omega_isOrdinal_d hM hC.omega
  have hu := (hD.mountain.parents.bounds hM.1 hFu).1
  have hFuF := hD.mountain.forest u Fu hFu
  intro hCone
  rcases hω.wellOrder.linear.compare D.floor (hD.floor_nat hM.1) u hu with he | hlt | hgt
  · have hConeG := hCone.high_parent_d hM hC hD (Or.inl (hM.1.eq_of_same_members _ _ he))
      ⟨Fu,(hD.mountain.parents.bounds hM.1 hFu).2,hFu,hGood⟩
    exact not_mem_of_le' hM hC (hω.transitive _ hD.coordinates.root g hg) (hConeG.root_le hM.1 hD) hg
  · have hConeG := hCone.high_parent_d hM hC hD (Or.inr hlt) ⟨Fu,(hD.mountain.parents.bounds hM.1 hFu).2,hFu,hGood⟩
    exact not_mem_of_le' hM hC (hω.transitive _ hD.coordinates.root g hg) (hConeG.root_le hM.1 hD) hg
  · obtain ⟨_,_,_,_,F',_,hF',hRootF'⟩ := hCone
    have hAnc : Ancestor M C D.mountain.width F' D.coordinates.root c := by
      rcases hRootF'.2.2 with he | hAnc
      · exact False.elim (SetTheory.KP.mem_irrefl_d (KP1Y.models_weakKP hM) c (he ▸ hRootC))
      · exact hAnc
    have hAncU := canon_source_ancestor_lower_d hM hC hRun hFrom hFu hF' (Or.inr hgt) hAnc
    obtain ⟨p,hCP,hTail⟩ := ancestor_parent_cases_d hM hC hFuF hAncU
    have hpg := hFuF.unique c p g hCP hGood
    subst p
    have hRootG : D.coordinates.root=g ∨ M.mem D.coordinates.root g := hTail.imp_right And.left
    exact not_mem_of_le' hM hC (hω.transitive _ hD.coordinates.root g hg) hRootG hg

/-- 源行u的父为好部时，行r≥u上该非root坏部列的副本深度等于源深度。 -/
theorem Copies.canon_depth_good_eq_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {D : Context M.Domain} (hD : D.Valid M C) {Y : Data M.Domain} (hY : Y.Valid M C) {n : M.Domain}
    (hCopy : Copies M C T D n Y) {m : M.Domain} {R : RowStateSpace M.Domain} {V P H : M.Domain}
    (hRun : RowRun M C m R V P H) (hFrom : FromRun M C m R V H D.mountain) {u r Fu F G c g b y d : M.Domain}
    (hcLast : M.mem c D.coordinates.last) (hRootC : M.mem D.coordinates.root c)
    (hFu : MemPair M D.mountain.parents u Fu) (hGood : MemPair M Fu c g) (hg : M.mem g D.coordinates.root)
    (hUR : u=r ∨ M.mem u r) (hF : MemPair M D.mountain.parents r F) (hG : MemPair M Y.parents r G)
    (hMap : ParentCopy M C T D.coordinates b c y) (hy : M.mem y Y.width)
    (hDC : Depth M C D.mountain.width F c d) : Depth M C Y.width G y d := by
  have hω := omega_isOrdinal_d hM hC.omega
  have hr := (hD.mountain.parents.bounds hM.1 hF).1
  have hOut := canon_good_parent_out_d hM hC hD hRun hFrom hRootC hFu hGood hg
  have hFuF := hD.mountain.forest u Fu hFu
  rcases hω.wellOrder.linear.compare D.floor (hD.floor_nat hM.1) r hr with he | hlt | hgt
  · exact hCopy.canon_depth_out_eq_d hM hC hT hD hY hRun hFrom (Or.inl (hM.1.eq_of_same_members _ _ he)) hF hG hcLast hOut hMap hy hDC
  · exact hCopy.canon_depth_out_eq_d hM hC hT hD hY hRun hFrom (Or.inr hlt) hF hG hcLast hOut hMap hy hDC
  · refine hCopy.canon_depth_low_eq_d hM hC hT hD hY hgt hF hG (Or.inr hcLast)
      (fun he => SetTheory.KP.mem_irrefl_d (KP1Y.models_weakKP hM) c (he ▸ hRootC)) ?_ hMap hy hDC
    intro hAnc
    have hAncU := canon_source_ancestor_lower_d hM hC hRun hFrom hFu hF hUR hAnc
    obtain ⟨p,hCP,hTail⟩ := ancestor_parent_cases_d hM hC hFuF hAncU
    have hpg := hFuF.unique c p g hCP hGood
    subst p
    exact not_mem_of_le' hM hC (hω.transitive _ hD.coordinates.root g hg) (hTail.imp_right And.left) hg

end KP1Y.OneYFinite.CopiedMountain.Lower
