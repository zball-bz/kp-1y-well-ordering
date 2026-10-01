import KP1Y.OneYLowerHelpForest
import KP1Y.OneYLowerCanonOrder
import KP1Y.OneYTowerCanonInterface
import KP1Y.OneYReconstructionExtraction

/-! LANE-B helper：源层与帧复制的根祖先事实。
* 真实源k层提取的伪父森林、Top图与选择（统一到 `D.mountain`）；
* BadAt 给出 root 是 last 在源k+1层父图中的祖先（原 `badAtLowerContext_pseudo_root`）；
* 帧复制中 root 是其每个副本的祖先或相等（原 `FrameCopy.root_ancestor_or_eq_copy`，块号对象归纳）；
* 收缩列的已选上层父在好部（原 `contractedSelectionGood_of_upper_transport` 的源侧部分）。 -/
namespace KP1Y.OneYFinite.LowerHelp
open YesMetaZFC YesMetaZFC.SetTheory YesMetaZFC.SetTheory.Definitional
open KP1Y.Kuratowski KP1Y.Functions KP1Y.Naturals KP1Y.Bounded
open KP1Y.OneYFinite KP1Y.OneYFinite.CopiedMountain KP1Y.OneYFinite.CopyCoordinates KP1Y.OneYFinite.TowerCanon
universe u

/-- 源k层真实提取统一到 `D.mountain`：伪父森林、Top图、选择与基行正值。 -/
theorem lower_layer_source_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} {m : M.Domain}
    {L : LayerStateSpace M.Domain} {V P H K : M.Domain} {A : CopyCoordinates.Context M.Domain}
    (hLayers : LayerRun M C m L V P H) {k n W Q J oldTop Qnext : M.Domain}
    {D : Lower.Context M.Domain} {Y : Data M.Domain}
    (hData : LowerLayerData M C T A m L H K k n W Q J oldTop Qnext D Y) :
    ∃ F, GraphPseudoForest M C D.mountain F ∧ PseudoForest M C m L.rows J D.mountain.heights F ∧
      TopValueGraph M C m L.rows J D.mountain.heights oldTop ∧ Selects true M C m F oldTop Qnext ∧
      (∀ c v, MemPair M W c v → M.mem C.zero v) := by
  obtain ⟨R,H',Heights,F,hRun',hHeights,hTop,hF,hSel⟩ := hData.extraction
  have hRR := row_state_space_unique hM.1 hRun'.space hData.run.space
  subst R
  have hHH := hRun'.unique_d hM hC hData.run
  subst H'
  have hHeq := hHeights.unique hM.1 hData.from_run.heights
  subst Heights
  exact ⟨F,(ReconstructionExtraction.pseudo_forest_iff_d hM hC hData.run hData.context.mountain hData.from_run).mpr hF,
    hF,hTop,hSel,(hLayers.at_rooted hM.1 hData.layer).positive⟩

/-- BadAt 在第K层给出 root 为 last 的祖先；下降到 k+1 层即源k层提取父图 Qnext。 -/
theorem lower_layer_next_root_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} {m : M.Domain}
    {L : LayerStateSpace M.Domain} {V P H K level : M.Domain} {A : CopyCoordinates.Context M.Domain}
    (hLayers : LayerRun M C m L V P H) (hBad : BadAt M C m L H K level A.last A.root)
    {k n W Q J oldTop Qnext : M.Domain} {D : Lower.Context M.Domain} {Y : Data M.Domain}
    (hData : LowerLayerData M C T A m L H K k n W Q J oldTop Qnext D Y) :
    Ancestor M C m Qnext A.root A.last := by
  obtain ⟨WK,_,QK,_,hAtK,JK,hRunK,U,_,Fr,_,hAtR,hParent,_⟩ := hBad
  have hFr := (hRunK.at_numeric_d hM hC hAtR).forest
  have hAncK : Ancestor M C m QK A.root A.last := hRunK.ancestor_base_d hM hC hAtR (ancestor_direct_d hM hC hFr hParent)
  have hKNat : M.mem K C.omega := by
    obtain ⟨_,_,hK,_⟩ := hAtK
    exact (hLayers.graph.bounds hM.1 hK).1
  have hkNat : M.mem k C.omega := (omega_isOrdinal_d hM hC.omega).transitive K hKNat k hData.lower
  obtain ⟨k',hSucc,hk'Nat⟩ := hC.omega.1.2 k hkNat
  obtain ⟨W',Q',hAt'⟩ := hLayers.at_exists_d hk'Nat
  have hNext := hLayers.at_next hM.1 hSucc hData.layer hAt'
  obtain ⟨_,hQQ⟩ := Extraction.unique_d hM hC hData.extraction hNext
  subst Q'
  exact hLayers.ancestor_lower_d hM hC hAt' hAtK (LowerCanon.nat_succ_le_of_lt hM hC hkNat hKNat hSucc hData.lower) hAncK

private def seamEnv {M : SetTheory.Structure.{u}} (C : ExpressionData M.Domain) (T : MatrixArithmetic M.Domain)
    (A : CopyCoordinates.Context M.Domain) (n G : M.Domain) : Env M 17 :=
  ((((((((((((((((oneEnv C.omega).push C.zero).push C.one).push C.sequences).push C.expressions).push T.addPairs).push T.plus).push
    T.mulPairs).push T.times).push T.diffPairs).push T.difference).push A.last).push A.root).push A.length).push A.first).push n).push G

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

/-- 帧复制：若 root 是 last 的源祖先，则 root 是其任意块副本的祖先或等于它（块号对象归纳）。 -/
theorem frame_root_seam_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {A : CopyCoordinates.Context M.Domain} (hA : A.Valid M C) {m P N n F' : M.Domain}
    (hP : Forest M C.omega m P) (hLastM : M.mem A.last m) (hCopies : FrameCopy.Copies M C T A P N n F')
    (hRoot : Ancestor M C m P A.root A.last) {b w : M.Domain}
    (hMap : ParentCopy M C T A b A.root w) (hw : M.mem w n) : A.root=w ∨ Ancestor M C n F' A.root w := by
  have hω := omega_isOrdinal_d hM hC.omega
  obtain ⟨count,_,hQ⟩ := hCopies
  obtain ⟨total,hTotal,hWidth⟩ := hQ.width_geometry
  have hnNat := hQ.forest.width
  have hNot : ¬M.mem A.root A.root := SetTheory.KP.mem_irrefl_d (KP1Y.models_weakKP hM) A.root
  have hLastNot : ¬M.mem A.last A.root := fun h => SetTheory.KP.mem_irrefl_d (KP1Y.models_weakKP hM)
    A.root ((hω.mem hA.root).transitive A.last h A.root hA.below)
  have hAll := natural_induction_d hM seamSchema (seamEnv C T A n F') hC.omega
    (fun z hz => (seamSchema_iff hM.1 C T A n F' z).mpr (by
      intro child _ hMap
      have hZ := hM.1.eq_of_same_members z C.zero (fun t => iff_of_false (hz t) (hC.zero_empty t))
      subst z
      exact Or.inl (encode_unique hM.1 hT (encode_zero_d hM hC hT hA hA.root) ((parent_copy_bad_iff hNot).mp hMap))))
    (fun block hBlock ih next hSucc => (seamSchema_iff hM.1 C T A n F' next).mpr (by
      intro child hChild hMap
      obtain ⟨boundary,_,hBoundary⟩ := encode_exists_d hM hC hT hA hA.last hBlock
      have hChildEq := encode_unique hM.1 hT ((parent_copy_bad_iff hNot).mp hMap)
        (width_is_next_cut_d hM hC hT hA hSucc hBoundary)
      have hWidthChild : Width M C T A block child := hChildEq.symm ▸ hBoundary
      obtain ⟨cut,_,hCut⟩ := encode_exists_d hM hC hT hA hA.root hBlock
      have hRootCopy : ParentCopy M C T A block A.root cut := (parent_copy_bad_iff hNot).mpr hCut
      have hCutChild := cut_lt_width_d hM hC hT hA hWidthChild hCut
      have hCutMem := (hω.mem hnNat).transitive child hChild cut hCutChild
      have hToCut := (seamSchema_iff hM.1 C T A n F' block).mp ih cut hCutMem hRootCopy
      obtain ⟨next',hNext'Nat,hs',hPos⟩ := encode_seam_bms_d hM hC hT hA hWidthChild
      have hNext'Count := (copy_position_lt_width_iff_d hM hC hT hA.root (hA.length_nat hM.1) hQ.count_nat hNext'Nat
        hTotal hWidth (hA.length_positive_d hM hC) hPos).mp hChild
      have hAcross : Ancestor M C n F' cut child :=
        (hQ.ancestor_previous_root_iff_d hM hC hT hA hP hLastM hNext'Count hBlock hs' hC.one_succ.predecessor_mem
          (Or.inl rfl) hA.below hRootCopy hPos).mpr hRoot
      exact Or.inr (hToCut.elim (fun he => he ▸ hAcross)
        (fun h => ancestor_trans_d hM hC hQ.forest h hAcross))))
  exact (seamSchema_iff hM.1 C T A n F' b).mp (hAll b hMap.2.1) w hw hMap

/-- 源侧收缩条件：伪父为 root 且与 root 同高的列，其已选源父严格在好部。 -/
theorem contracted_selected_good_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {m : M.Domain} {R : RowStateSpace M.Domain}
    {V P H Heights Top F Qs s y height q : M.Domain} (hRun : RowRun M C m R V P H)
    (hHeights : HeightGraph M C m R V H Heights) (hTop : TopValueGraph M C m R H Heights Top)
    (hF : PseudoForest M C m R H Heights F) (hPositive : ∀ i v, MemPair M V i v → M.mem C.zero v)
    (hSel : Selects true M C m F Top Qs) (hSY : MemPair M F s y)
    (hHS : MemPair M Heights s height) (hHY : MemPair M Heights y height) (hq : MemPair M Qs s q) : M.mem q y := by
  obtain ⟨⟨hAnc,tq,_,ts,_,hTq,hTs,hLt,_⟩,_⟩ := (hSel.parents s q).mp hq
  rcases ancestor_le_parent_d hM hC hF.forest hSY hAnc with he | hlt
  · subst q
    rcases hTop.same_height_pseudo_antitone_d hM hC hRun hHeights hF hPositive (ancestor_direct_d hM hC hF.forest hSY)
      hHY hHS hTq hTs with he | hle
    · subst ts
      exact False.elim (SetTheory.KP.mem_irrefl_d (KP1Y.models_weakKP hM) tq hLt)
    · exact False.elim (SetTheory.KP.mem_irrefl_d (KP1Y.models_weakKP hM) tq
        (((omega_isOrdinal_d hM hC.omega).mem (hTop.graph.bounds hM.1 hTq).2).transitive ts hle tq hLt))
  · exact hlt

end KP1Y.OneYFinite.LowerHelp
