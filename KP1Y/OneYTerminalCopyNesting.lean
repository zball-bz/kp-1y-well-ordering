import KP1Y.OneYOrdinaryCopyNesting
import KP1Y.OneYTerminalCopyHighRoots
import KP1Y.OneYCopyAncestryTransport

/-! 活动层复制的相邻行嵌套，包含低行跨接缝路径与临界行切换。 -/
namespace KP1Y.OneYFinite.CopiedMountain.Terminal
open YesMetaZFC YesMetaZFC.SetTheory YesMetaZFC.SetTheory.Definitional
open KP1Y.Kuratowski KP1Y.Functions KP1Y.Naturals KP1Y.Bounded
open KP1Y.OneYFinite.CopyCoordinates
universe u

theorem Copies.low_parent_nonroot_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {A : Context M.Domain} (hA : A.Valid M C) {X Y : Data M.Domain} (hX : X.Valid M C)
    {level n r b s c p q : M.Domain} (hCopy : Copies M C T A X level n Y)
    (hLevel : M.mem level C.omega) (hLow : M.mem r level) (hSource : s=A.last ∨ M.mem s A.last)
    (hNotRoot : s≠A.root) (hMap : ParentCopy M C T A b s c) (hMapP : ParentCopy M C T A b p q)
    (hParent : ParentAt M X r s p) (hc : M.mem c n) : ParentAt M Y r c q := by
  rcases hSource with he | hs
  · subst s
    have hNot : ¬M.mem A.last A.root := fun h => SetTheory.KP.mem_irrefl_d (KP1Y.models_weakKP hM) A.root
      (((omega_isOrdinal_d hM hC.omega).mem hA.root).transitive A.last h A.root hA.below)
    have hWidth : Width M C T A b c := (parent_copy_bad_iff hNot).mp hMap
    exact (low_seam_parent_iff_d hM hC hT hA hCopy hWidth hc hLevel hLow).mpr ⟨p,hMapP.1,hParent,hMapP⟩
  · exact (hCopy.parents r c q).mpr ⟨hc,(parent_parent_copy_nonroot_d hM hC hT hA hX hs hNotRoot hMap).mpr
      ⟨p,hMapP.1,hParent,hMapP⟩⟩

theorem Copies.prefix_ancestor_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {A : Context M.Domain} (hA : A.Valid M C) {X Y : Data M.Domain} (hX : X.Valid M C) (hY : Y.Valid M C)
    {level n r F G a c : M.Domain} (hCopy : Copies M C T A X level n Y)
    (hF : MemPair M X.parents r F) (hG : MemPair M Y.parents r G)
    (hAnc : Ancestor M C X.width F a c) (hOld : M.mem c A.last) (hc : M.mem c Y.width) :
    Ancestor M C Y.width G a c := by
  have hw := omega_isOrdinal_d hM hC.omega
  have hCNat := hw.transitive X.width hX.width c (hAnc.bounds hM.1).2
  have hANat := hw.transitive X.width hX.width a (hAnc.bounds hM.1).1
  obtain ⟨J,hJ,hRows⟩ := parent_copy_graph_exists_d hM hC hT hA hC.zero_nat
  have hIdentity (p : M.Domain) (hp : M.mem p C.omega) : MemPair M J p p :=
    (hRows p p).mpr (parent_copy_zero_d hM hC hT hA hp)
  apply ancestor_map_refines_global_bounded_d hM hC (hX.forest r F hF) (hY.forest r G hG) hJ hAnc
    (hIdentity a hANat) (hIdentity c hCNat) hc
  intro d p u v hD _ hParent hDU hPV hu
  have hdNat := (hJ.graph.bounds hM.1 hDU).1
  have hpNat := (hJ.graph.bounds hM.1 hPV).1
  have hUD := hJ.graph.unique d u d hDU (hIdentity d hdNat)
  have hVP := hJ.graph.unique p v p hPV (hIdentity p hpNat)
  subst u
  subst v
  have hdLast : M.mem d A.last := hD.elim (fun he => he.symm ▸ hOld)
    (fun h => (hw.mem hA.last).transitive c hOld d h.1)
  have hParentAt : ParentAt M Y r d p := (hCopy.original_parents_d hM hC hA (hCopy.width ▸ hu) hdLast).mpr
    ⟨F,(hX.parents.bounds hM.1 hF).2,hF,hParent⟩
  obtain ⟨G',_,hG',hEdge⟩ := hParentAt
  have hGG := hY.parents.unique r G' G hG' hG
  exact ancestor_direct_d hM hC (hY.forest r G hG) (hGG ▸ hEdge)

/-- 整条路径在坏根右侧时，每条边直接位于同一副本。 -/
theorem Copies.low_ancestor_same_block_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {A : Context M.Domain} (hA : A.Valid M C) {X Y : Data M.Domain} (hX : X.Valid M C) (hY : Y.Valid M C)
    {level n r F G a s x c b : M.Domain} (hCopy : Copies M C T A X level n Y)
    (hLevel : M.mem level C.omega) (hLow : M.mem r level)
    (hF : MemPair M X.parents r F) (hG : MemPair M Y.parents r G)
    (hAnc : Ancestor M C X.width F a s) (hAfter : A.root=a ∨ M.mem A.root a)
    (hSource : s=A.last ∨ M.mem s A.last)
    (hMapA : ParentCopy M C T A b a x) (hMapC : ParentCopy M C T A b s c) (hc : M.mem c Y.width) :
    Ancestor M C Y.width G x c := by
  have hw := omega_isOrdinal_d hM hC.omega
  obtain ⟨J,hJ,hRows⟩ := parent_copy_graph_exists_d hM hC hT hA hMapC.2.1
  apply ancestor_map_refines_global_bounded_d hM hC (hX.forest r F hF) (hY.forest r G hG) hJ hAnc
    ((hRows a x).mpr hMapA) ((hRows s c).mpr hMapC) hc
  intro d p u v hD hAP hParent hDU hPV hu
  have hpNat := (hJ.graph.bounds hM.1 hPV).1
  have hRootP : A.root=p ∨ M.mem A.root p := by
    rcases hAP with he | hap
    · exact he ▸ hAfter
    · exact Or.inr (hAfter.elim (fun he => he.symm ▸ hap) (fun h => (hw.mem hpNat).transitive a hap A.root h))
  have hRootD : M.mem A.root d := by
    have hpD := (hX.forest r F hF).left d p hParent
    exact hRootP.elim (fun he => he.symm ▸ hpD)
      (fun h => (hw.mem (hJ.graph.bounds hM.1 hDU).1).transitive p hpD A.root h)
  have hDLast : d=A.last ∨ M.mem d A.last := by
    rcases hD with he | hAncD
    · exact he.symm ▸ hSource
    · exact Or.inr (hSource.elim (fun he => he ▸ hAncD.1) (fun hs => (hw.mem hA.last).transitive s hs d hAncD.1))
  have hParentAt := hCopy.low_parent_nonroot_d hM hC hT hA hX hLevel hLow hDLast
    (fun he => SetTheory.KP.mem_irrefl_d (KP1Y.models_weakKP hM) A.root (he ▸ hRootD))
    ((hRows d u).mp hDU) ((hRows p v).mp hPV) ⟨F,(hX.parents.bounds hM.1 hF).2,hF,hParent⟩ (hCopy.width ▸ hu)
  obtain ⟨G',_,hG',hEdge⟩ := hParentAt
  exact ancestor_direct_d hM hC (hY.forest r G hG) (hY.parents.unique r G' G hG' hG ▸ hEdge)

theorem source_root_ancestor_last_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {A : Context M.Domain} {X : Data M.Domain} (_hX : X.Valid M C)
    {m : M.Domain} {R : RowStateSpace M.Domain} {V P H r level F : M.Domain}
    (hRun : RowRun M C m R V P H) (hFrom : FromRun M C m R V H X)
    (hActive : Active M X A level) (hF : MemPair M X.parents r F) (hLe : r=level ∨ M.mem r level) :
    Ancestor M C X.width F A.root A.last := by
  obtain ⟨G,_,hG,hParent⟩ := hActive.parent
  obtain ⟨U,hAtF⟩ := (hFrom.parents r F).mp hF
  obtain ⟨W,hAtG⟩ := (hFrom.parents level G).mp hG
  exact hFrom.width.symm ▸ hRun.ancestor_lower_d hM hC hAtF hAtG hLe
    (ancestor_direct_d hM hC (hRun.at_numeric_d hM hC hAtG).forest hParent)

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
    (A : Context M.Domain) (n G a : M.Domain) : Env M 18 :=
  (((((((((((((((((oneEnv C.omega).push C.zero).push C.one).push C.sequences).push C.expressions).push T.addPairs).push T.plus).push T.mulPairs).push T.times).push T.diffPairs).push T.difference).push A.last).push A.root).push A.length).push A.first).push n).push G).push a

private theorem rootPathSchema_iff {M : SetTheory.Structure.{u}} (he : Extensional M)
    (C : ExpressionData M.Domain) (T : MatrixArithmetic M.Domain) (A : Context M.Domain) (n G a b : M.Domain) :
    Project.Formula.satisfies ((rootPathEnv C T A n G a).push b) rootPathSchema.body ↔
      ∀c, M.mem c n → ParentCopy M C T A b A.root c → Ancestor M C n G a c := by
  simp only [rootPathSchema,Project.Formula.satisfies_forallMem_iff,Project.Formula.satisfies_imp_iff,
    parentCopyFormula_iff he,ancestorFormula_iff he]
  rfl

/-- 原根左侧的祖先跨过任意内部有限个接缝，复制编号归纳完全位于对象ω。 -/
theorem Copies.root_good_ancestor_low_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {A : Context M.Domain} (hA : A.Valid M C) {X Y : Data M.Domain} (hX : X.Valid M C) (hY : Y.Valid M C)
    {m : M.Domain} {R : RowStateSpace M.Domain} {V P H level n r F G a b c : M.Domain}
    (hRun : RowRun M C m R V P H) (hFrom : FromRun M C m R V H X)
    (hActive : Active M X A level) (hCopy : Copies M C T A X level n Y) (hLow : M.mem r level)
    (hF : MemPair M X.parents r F) (hG : MemPair M Y.parents r G)
    (hAnc : Ancestor M C X.width F a A.root) (hMap : ParentCopy M C T A b A.root c) (hc : M.mem c Y.width) :
    Ancestor M C Y.width G a c := by
  have hw := omega_isOrdinal_d hM hC.omega
  have hLevel := (hActive.parent.bounds hM.1 hX).1
  have hRootLast := source_root_ancestor_last_d hM hC hX hRun hFrom hActive hF (Or.inr hLow)
  have hNot : ¬M.mem A.root A.root := SetTheory.KP.mem_irrefl_d (KP1Y.models_weakKP hM) A.root
  have hAll := natural_induction_d hM rootPathSchema (rootPathEnv C T A Y.width G a) hC.omega
    (fun z hz => (rootPathSchema_iff hM.1 C T A Y.width G a z).mpr (by
      intro child hChild hMap
      have hZ := hM.1.eq_of_same_members z C.zero (fun t => iff_of_false (hz t) (hC.zero_empty t))
      subst z
      have hChildEq := encode_unique hM.1 hT ((parent_copy_bad_iff hNot).mp hMap) (encode_zero_d hM hC hT hA hA.root)
      subst child
      exact hCopy.prefix_ancestor_d hM hC hT hA hX hY hF hG hAnc hA.below hChild))
    (fun block hBlock ih next hSucc => (rootPathSchema_iff hM.1 C T A Y.width G a next).mpr (by
      intro child hChild hMap
      obtain ⟨boundary,_,hWidth⟩ := encode_exists_d hM hC hT hA hA.last hBlock
      have hChildEq := encode_unique hM.1 hT ((parent_copy_bad_iff hNot).mp hMap)
        (width_is_next_cut_d hM hC hT hA hSucc hWidth)
      have hWidthChild : Width M C T A block child := hChildEq.symm ▸ hWidth
      obtain ⟨cut,_,hCut⟩ := encode_exists_d hM hC hT hA hA.root hBlock
      have hRootCopy : ParentCopy M C T A block A.root cut := (parent_copy_bad_iff hNot).mpr hCut
      have hCutChild := cut_lt_width_d hM hC hT hA hWidthChild hCut
      have hCutMem := (hw.mem hY.width).transitive child hChild cut hCutChild
      have hToCut := (rootPathSchema_iff hM.1 C T A Y.width G a block).mp ih cut hCutMem hRootCopy
      have hLastNot : ¬M.mem A.last A.root := fun h => SetTheory.KP.mem_irrefl_d (KP1Y.models_weakKP hM) A.root
        ((hw.mem hA.root).transitive A.last h A.root hA.below)
      have hLastCopy : ParentCopy M C T A block A.last child := (parent_copy_bad_iff hLastNot).mpr hWidthChild
      have hAcross := hCopy.low_ancestor_same_block_d hM hC hT hA hX hY hLevel hLow hF hG hRootLast
        (Or.inl rfl) (Or.inl rfl) hRootCopy hLastCopy hChild
      exact ancestor_trans_d hM hC (hY.forest r G hG) hToCut hAcross))
  exact (rootPathSchema_iff hM.1 C T A Y.width G a b).mp (hAll b hMap.2.1) c hc hMap

/-- 低行完整祖先运输；源根父边可以替换为跨副本的非空路径。 -/
theorem Copies.low_ancestor_parent_copy_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {A : Context M.Domain} (hA : A.Valid M C) {X Y : Data M.Domain} (hX : X.Valid M C) (hY : Y.Valid M C)
    {m : M.Domain} {R : RowStateSpace M.Domain} {V P H level n r F G a s x c b : M.Domain}
    (hRun : RowRun M C m R V P H) (hFrom : FromRun M C m R V H X)
    (hActive : Active M X A level) (hCopy : Copies M C T A X level n Y) (hLow : M.mem r level)
    (hF : MemPair M X.parents r F) (hG : MemPair M Y.parents r G)
    (hAnc : Ancestor M C X.width F a s) (hSource : s=A.last ∨ M.mem s A.last)
    (hMapA : ParentCopy M C T A b a x) (hMapC : ParentCopy M C T A b s c) (hc : M.mem c Y.width) :
    Ancestor M C Y.width G x c := by
  have hw := omega_isOrdinal_d hM hC.omega
  obtain ⟨J,hJ,hRows⟩ := parent_copy_graph_exists_d hM hC hT hA hMapC.2.1
  apply ancestor_map_refines_global_bounded_d hM hC (hX.forest r F hF) (hY.forest r G hG) hJ hAnc
    ((hRows a x).mpr hMapA) ((hRows s c).mpr hMapC) hc
  intro d p u v hD _ hParent hDU hPV hu
  have hDLast : d=A.last ∨ M.mem d A.last := by
    rcases hD with he | hAncD
    · exact he.symm ▸ hSource
    · exact Or.inr (hSource.elim (fun he => he ▸ hAncD.1) (fun hs => (hw.mem hA.last).transitive s hs d hAncD.1))
  classical
  by_cases hRoot : d=A.root
  · subst d
    have hGood := (hX.forest r F hF).left A.root p hParent
    have hVP := (parent_copy_good_iff hMapC.2.1 (hJ.graph.bounds hM.1 hPV).1 hGood).mp ((hRows p v).mp hPV)
    subst v
    exact hCopy.root_good_ancestor_low_d hM hC hT hA hX hY hRun hFrom hActive hLow hF hG
      (ancestor_direct_d hM hC (hX.forest r F hF) hParent) ((hRows A.root u).mp hDU) hu
  · have hAt := hCopy.low_parent_nonroot_d hM hC hT hA hX (hActive.parent.bounds hM.1 hX).1 hLow hDLast hRoot
      ((hRows d u).mp hDU) ((hRows p v).mp hPV) ⟨F,(hX.parents.bounds hM.1 hF).2,hF,hParent⟩ (hCopy.width ▸ hu)
    obtain ⟨G',_,hG',hEdge⟩ := hAt
    exact ancestor_direct_d hM hC (hY.forest r G hG) (hY.parents.unique r G' G hG' hG ▸ hEdge)

theorem Copies.high_ancestor_parent_copy_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {A : Context M.Domain} (hA : A.Valid M C) {X Y : Data M.Domain} (hX : X.Valid M C) (hY : Y.Valid M C)
    {level n r F G a s x c b : M.Domain} (hCopy : Copies M C T A X level n Y)
    (hLast : M.mem A.last X.width) (hHigh : level=r ∨ M.mem level r)
    (hF : MemPair M X.parents r F) (hG : MemPair M Y.parents r G)
    (hAnc : Ancestor M C X.width F a s) (hSource : M.mem s A.last)
    (hMapA : ParentCopy M C T A b a x) (hMapC : ParentCopy M C T A b s c) (hc : M.mem c Y.width) :
    Ancestor M C Y.width G x c := by
  have hn := hCopy.width ▸ hY.width
  obtain ⟨Z,hZ,hOrd⟩ := Ordinary.copy_exists_d hM hC hT hA hX hLast hn
  obtain ⟨Q,hQ,hRowQ⟩ := hZ.parents.total r (hY.parents.bounds hM.1 hG).1
  have hQG : Q=G := (hZ.forest r Q hRowQ).ext hM.1 (hY.forest r G hG) (by
    intro d p
    constructor
    · intro hP
      obtain ⟨G',_,hG',hEdge⟩ := (hCopy.high_parents_eq_ordinary_d hM hC hT hA hX hOrd hn hHigh).mpr ⟨Q,hQ,hRowQ,hP⟩
      exact hY.parents.unique r G' G hG' hG ▸ hEdge
    · intro hP
      obtain ⟨Q',_,hQ',hEdge⟩ := (hCopy.high_parents_eq_ordinary_d hM hC hT hA hX hOrd hn hHigh).mp
        ⟨G,(hY.parents.bounds hM.1 hG).2,hG,hP⟩
      exact hZ.parents.unique r Q' Q hQ' hRowQ ▸ hEdge)
  have hWidth : Z.width=Y.width := hOrd.width.trans hCopy.width.symm
  exact hQG ▸ hWidth ▸ hOrd.ancestor_parent_copy_d hM hC hT hA hX hZ hF hRowQ hAnc hSource hMapA hMapC (hWidth.symm ▸ hc)

/-- 上行低于或恰跨过活动层时的真实细化，单独处理ordinary source=root。 -/
theorem Copies.low_nested_step_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {A : Context M.Domain} (hA : A.Valid M C) {X Y : Data M.Domain} (hX : X.Valid M C) (hY : Y.Valid M C)
    {m : M.Domain} {R : RowStateSpace M.Domain} {V P H level n r next F G : M.Domain}
    (hRun : RowRun M C m R V P H) (hFrom : FromRun M C m R V H X)
    (hActive : Active M X A level) (hCopy : Copies M C T A X level n Y)
    (hLow : M.mem r level) (hSucc : M.SuccessorOf next r)
    (hF : MemPair M Y.parents r F) (hG : MemPair M Y.parents next G) : ForestRefines M C Y.width G F := by
  have hw := omega_isOrdinal_d hM hC.omega
  have hLevel := (hActive.parent.bounds hM.1 hX).1
  have hNext := (hY.parents.bounds hM.1 hG).1
  have hNested := hFrom.nested_d hM hC hRun hX
  obtain ⟨OldF,_,hOldF⟩ := hX.parents.total r (hY.parents.bounds hM.1 hF).1
  intro child parent hEdge
  have hParent : ParentAt M Y next child parent := ⟨G,(hY.parents.bounds hM.1 hG).2,hG,hEdge⟩
  have hChild := (hParent.bounds hM.1 hY).2.1
  have hChildN := hCopy.width ▸ hChild
  have hChildNat := hw.transitive Y.width hY.width child hChild
  obtain ⟨source,block,hDec⟩ := OrdinaryCoordinates.decoded_exists_d hM hC hT hA hChildNat
  have hSource := hDec.source_lt_last_d hM hC hT hA
  have hMap := hDec.parent_copy_reconstruct_d hM hC hT hA
  have hNewParent := ((hCopy.parents next child parent).mp hParent).2
  classical
  by_cases hRoot : source=A.root
  · subst source
    by_cases hHigh : level=next ∨ M.mem level next
    · have hOldParent := (parent_copied_root_high_iff_d hM hC hT hA hHigh hMap).mp hNewParent
      exact hCopy.root_good_ancestor_low_d hM hC hT hA hX hY hRun hFrom hActive hLow hOldF hF
        (hNested.parent_lower_d hX hSucc hOldF hOldParent) hMap hChild
    · have hLowNext : M.mem next level := by
        rcases hw.wellOrder.linear.compare next hNext level hLevel with he | hlt | hgt
        · exact False.elim (hHigh (Or.inl (hM.1.eq_of_same_members next level he).symm))
        · exact hlt
        · exact False.elim (hHigh (Or.inr hgt))
      rcases natural_cases hM hC.omega hMap.2.1 with hEmpty | ⟨previous,hPrevious,hNextBlock⟩
      · have hZero := hM.1.eq_of_same_members block C.zero (fun t => iff_of_false (hEmpty t) (hC.zero_empty t))
        subst block
        have hNot : ¬M.mem A.root A.root := SetTheory.KP.mem_irrefl_d (KP1Y.models_weakKP hM) A.root
        have hChildEq := encode_unique hM.1 hT ((parent_copy_bad_iff hNot).mp hMap) (encode_zero_d hM hC hT hA hA.root)
        subst child
        have hOldParent := (parent_original_iff_d hM hC hA hA.below).mp hNewParent
        exact hCopy.prefix_ancestor_d hM hC hT hA hX hY hOldF hF
          (hNested.parent_lower_d hX hSucc hOldF hOldParent) hA.below hChild
      · obtain ⟨boundary,_,hWidth⟩ := encode_exists_d hM hC hT hA hA.last hPrevious
        have hNot : ¬M.mem A.root A.root := SetTheory.KP.mem_irrefl_d (KP1Y.models_weakKP hM) A.root
        have hChildEq := encode_unique hM.1 hT ((parent_copy_bad_iff hNot).mp hMap)
          (width_is_next_cut_d hM hC hT hA hNextBlock hWidth)
        have hWidthChild : Width M C T A previous child := hChildEq.symm ▸ hWidth
        obtain ⟨pOld,_,hOldParent,hMapP⟩ := (low_seam_parent_iff_d hM hC hT hA hCopy hWidthChild hChildN hLevel hLowNext).mp hParent
        have hLastNot : ¬M.mem A.last A.root := fun h => SetTheory.KP.mem_irrefl_d (KP1Y.models_weakKP hM) A.root
          ((hw.mem hA.root).transitive A.last h A.root hA.below)
        have hLastMap : ParentCopy M C T A previous A.last child := (parent_copy_bad_iff hLastNot).mpr hWidthChild
        exact hCopy.low_ancestor_parent_copy_d hM hC hT hA hX hY hRun hFrom hActive hLow hOldF hF
          (hNested.parent_lower_d hX hSucc hOldF hOldParent) (Or.inl rfl) hMapP hLastMap hChild
  · obtain ⟨pOld,_,hOldParent,hMapP⟩ := (parent_parent_copy_nonroot_d hM hC hT hA hX hSource hRoot hMap).mp hNewParent
    exact hCopy.low_ancestor_parent_copy_d hM hC hT hA hX hY hRun hFrom hActive hLow hOldF hF
      (hNested.parent_lower_d hX hSucc hOldF hOldParent) (Or.inr hSource) hMapP hMap hChild

/-- 活动层复制保留全部相邻实际父森林的嵌套，含临界seam。 -/
theorem Copies.nested_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {A : Context M.Domain} (hA : A.Valid M C) {X Y : Data M.Domain} (hX : X.Valid M C) (hY : Y.Valid M C)
    {m : M.Domain} {R : RowStateSpace M.Domain} {V P H level n : M.Domain}
    (hRun : RowRun M C m R V P H) (hFrom : FromRun M C m R V H X)
    (hActive : Active M X A level) (hCopy : Copies M C T A X level n Y) : Nested M C Y := by
  intro r next F G hSucc hF hG
  have hw := omega_isOrdinal_d hM hC.omega
  have hLevel := (hActive.parent.bounds hM.1 hX).1
  have hr := (hY.parents.bounds hM.1 hF).1
  classical
  by_cases hLow : M.mem r level
  · exact hCopy.low_nested_step_d hM hC hT hA hX hY hRun hFrom hActive hLow hSucc hF hG
  · have hHigh : level=r ∨ M.mem level r := by
      rcases hw.wellOrder.linear.compare level hLevel r hr with he | hlt | hgt
      · exact Or.inl (hM.1.eq_of_same_members level r he)
      · exact Or.inr hlt
      · exact False.elim (hLow hgt)
    have hHighNext : level=next ∨ M.mem level next := Or.inr
      (hHigh.elim (fun he => he.symm ▸ hSucc.predecessor_mem)
        (fun h => ((hw.mem (hY.parents.bounds hM.1 hG).1).transitive r hSucc.predecessor_mem level h)))
    have hNested := hFrom.nested_d hM hC hRun hX
    obtain ⟨OldF,_,hOldF⟩ := hX.parents.total r hr
    intro child parent hEdge
    have hParent : ParentAt M Y next child parent := ⟨G,(hY.parents.bounds hM.1 hG).2,hG,hEdge⟩
    have hChild := (hParent.bounds hM.1 hY).2.1
    have hOrd := (parent_high_eq_ordinary_d hM hC hT hA hX (hw.transitive Y.width hY.width child hChild) hHighNext).mp
      ((hCopy.parents next child parent).mp hParent).2
    obtain ⟨source,_,block,_,pOld,_,hDec,hOldParent,hMapP⟩ := hOrd
    exact hCopy.high_ancestor_parent_copy_d hM hC hT hA hX hY (hActive.parent.bounds hM.1 hX).2.1 hHigh hOldF hF
      (hNested.parent_lower_d hX hSucc hOldF hOldParent) (hDec.source_lt_last_d hM hC hT hA)
      hMapP (hDec.parent_copy_reconstruct_d hM hC hT hA) hChild

end KP1Y.OneYFinite.CopiedMountain.Terminal
