import KP1Y.OneYLowerBottomPart
import KP1Y.OneYLowerCanonKeyZero
import KP1Y.OneYReconstructionExtraction

/-! Lower层间向下传递（原 `badAtLowerCopiedBase_upperFixed/_upperOrder`）：第k层复制的实际重建底值
满足第j=k-1层所需的 `UpperFixed` 与 `UpperOrder`。给出 `LowerLayer.DownPart` 字段形状的实际定理。 -/
namespace KP1Y.OneYFinite.LowerBlock
open YesMetaZFC YesMetaZFC.SetTheory YesMetaZFC.SetTheory.Definitional
open KP1Y.Kuratowski KP1Y.Functions KP1Y.Naturals KP1Y.Bounded KP1Y.Arithmetic
open KP1Y.OneYFinite KP1Y.OneYFinite.CopyCoordinates KP1Y.OneYFinite.CopiedMountain
open KP1Y.OneYFinite.CopiedMountain.Lower KP1Y.OneYFinite.LowerCanon
open KP1Y.OneYFinite.MountainReconstruction KP1Y.OneYFinite.ReconstructionCanonical
universe u

/-- 源第0行共同父的两列：底值弱序给出第1行起点的图层KeyLE。 -/
theorem source_bottom_key_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {m W Q J : M.Domain} {R : RowStateSpace M.Domain}
    (hRun : RowRun M C m R W Q J) (hPositive : ∀ c a, MemPair M W c a → M.mem C.zero a)
    {X : Data M.Domain} (hX : X.Valid M C) (hFrom : FromRun M C m R W J X)
    {Top : M.Domain} (hTop : TopValueGraph M C m R J X.heights Top)
    {s z p vs vz : M.Domain} (hQs : MemPair M Q s p) (hQz : MemPair M Q z p)
    (hVS : MemPair M W s vs) (hVZ : MemPair M W z vz) (hLe : vs=vz ∨ M.mem vs vz) :
    ∃ tc tz, MemPair M Top s tc ∧ MemPair M Top z tz ∧ ForestOrder.KeyLE M C X s z C.one tc tz := by
  have hRow0 := hRun.base
  have hAt0 := hRun.initial_row_at_d hM
  obtain ⟨W1,Q1,hAt1⟩ := hRun.at_exists_d hC.one_nat
  have hStep := hRun.at_next hM.1 hC.one_succ hAt0 hAt1
  have hRow1 := hRun.at_numeric_d hM hC hAt1
  have hsm : M.mem s m := (hRow0.forest.bounds hM.1 hQs).1
  have hzm : M.mem z m := (hRow0.forest.bounds hM.1 hQz).1
  obtain ⟨x,_,hXV⟩ := hRow1.values.total s hsm
  obtain ⟨y,_,hYV⟩ := hRow1.values.total z hzm
  have hLe1 := NumericOrder.difference_mono_common_parent_d hM hC hRow0 hStep.difference hQs hQz hVS hVZ hLe hXV hYV
  have hSame : ParentRowsEqual M Q s z := by
    intro e
    constructor
    · intro hParent
      exact (hRow0.forest.unique s e p hParent hQs).symm ▸ hQz
    · intro hParent
      exact (hRow0.forest.unique z e p hParent hQz).symm ▸ hQs
  have hCommon : NumericOrder.CommonAncestors M C m Q s z :=
    fun e _ => ancestor_iff_of_parent_rows_eq_d hM hC hRow0.forest hSame e
  obtain ⟨tc,_,hTC⟩ := hTop.graph.total s hsm
  obtain ⟨tz,_,hTZ⟩ := hTop.graph.total z hzm
  have hKey := NumericOrder.key_le_of_common_values_d hM hC hRun hPositive hFrom.heights hTop hTC hTZ hAt1
    hStep.selection (NumericOrder.row_next_zeros_at_roots_d hM hC hRow0 hStep) hCommon hXV hYV
    ((hRow0.difference_positive_iff_d hM hC hStep.difference hXV).mpr ⟨p,hQs⟩)
    ((hRow0.difference_positive_iff_d hM hC hStep.difference hYV).mpr ⟨p,hQz⟩) hLe1
  exact ⟨tc,tz,hTC,hTZ,(ForestOrder.from_run_key_iff_d hM hC hRun hX hFrom s z C.one tc tz).mpr hKey⟩

/-- 原 `value_copy_le_of_common_frame`：源底行由帧F选择，帧共同父且底值弱序的两列，其同块复制的
实际重建底值弱序。深度相等时用底行KeyLE运输，深度严格时用目标底行选择的深度单调性反证。 -/
theorem bottom_order_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {D : Lower.Context M.Domain} (hD : D.Valid M C) {Y : Data M.Domain} (hY : Y.Valid M C) {n : M.Domain}
    (hCopy : Copies M C T D n Y) (hKept : M.MemberSubset D.coordinates.last n)
    {m : M.Domain} {R : RowStateSpace M.Domain} {W Q J : M.Domain}
    (hRun : RowRun M C m R W Q J) (hRooted : RootedRow M C m W Q) (hFrom : FromRun M C m R W J D.mountain)
    {oldTop Qnext newTop Bottom : M.Domain}
    (hExtraction : Extraction M C m W Q oldTop Qnext) (hNewTop : Graph M newTop n C.omega)
    (hNewPos : ∀ c v, MemPair M newTop c v → M.mem C.zero v)
    (hPrefixTop : RowsAgreeOn M newTop oldTop D.coordinates.last) (hFixed : UpperFixed M C T D oldTop Qnext n newTop)
    (hOrder : ∀ Pseudo, GraphPseudoForest M C D.mountain Pseudo → UpperOrder M C T D Pseudo oldTop newTop)
    (hBound : ReconstructionSelection.PseudoTopBound M C Y newTop)
    (hRebuild : Rebuilds M C T.addPairs T.plus Y newTop Bottom)
    {F N : M.Domain} (hSel : Selects true M C m F W Q) (hN : Width M C T D.coordinates N n)
    {z s vs vz b cc zz tc tz : M.Domain} (hRootZ : M.mem D.coordinates.root z) (hzs : M.mem z s)
    (hsLast : s=D.coordinates.last ∨ M.mem s D.coordinates.last) (hFrame : ParentRowsEqual M F s z)
    (hVS : MemPair M W s vs) (hVZ : MemPair M W z vz) (hLe : vs=vz ∨ M.mem vs vz)
    (hMapS : ParentCopy M C T D.coordinates b s cc) (hMapZ : ParentCopy M C T D.coordinates b z zz)
    (hTC : MemPair M Bottom cc tc) (hTZ : MemPair M Bottom zz tz) : tc=tz ∨ M.mem tc tz := by
  have hn := hCopy.width
  subst hn
  have hw := omega_isOrdinal_d hM hC.omega
  have hPositive := hRooted.positive
  have hTopOld := Expansion.extraction_top_for_source_d hM hC hRun hFrom hExtraction
  have hBlockers := lower_decorated_blockers_d hM hC hT hD hY hCopy hRun hPositive hFrom hExtraction hNewTop
    hPrefixTop hFixed hOrder
  have hNested := hCopy.nested_d hM hC hT hD hY hRun hFrom
  obtain ⟨_,_,_,_,_,_,hBotPos⟩ := ReconstructionRecovery.structural_rebuild_run_exists_d hM hC hT.add hY hNewTop hNewPos
    hRebuild hNested hBound hBlockers
  obtain ⟨B,Parents,H,hB,hP,hH,hBot⟩ := id hRebuild
  have hRow0 : RowValues M (grid C Y newTop T.addPairs T.plus B Parents) H C.zero Bottom := by
    refine ⟨hBot.graph,?_⟩
    intro c v
    rw [hBot.rows c v]
    constructor
    · intro hCell
      have hSaved := hCell
      obtain ⟨f,_,hCf,_,_⟩ := hCell
      exact ⟨hC.zero_nat,(hH.graph.bounds hM.1 hCf).1,Or.inl hSaved⟩
    · intro hCell
      exact hCell.2.2.elim id (fun h => False.elim (h.1 hB.1.2.1))
  have hCanon : ∀ r s V W' F0 Q0, M.mem r C.omega → (C.zero=r ∨ M.mem C.zero r) → M.SuccessorOf s r →
      RowValues M (grid C Y newTop T.addPairs T.plus B Parents) H r V →
      RowValues M (grid C Y newTop T.addPairs T.plus B Parents) H s W' →
      MemPair M Y.parents r F0 → MemPair M Y.parents s Q0 → Selects true M C Y.width F0 W' Q0 :=
    fun _ _ _ _ _ _ _ _ hSucc _ hW' hF0 hQ0 => ReconstructionRecovery.structural_reconstruction_selects_d hM hC hT.add hY
      hNewTop hNewPos hB hP hH hNested hBound hBlockers hW' hF0 hQ0 hSucc
  have hQ0 : MemPair M D.mountain.parents C.zero Q := (hFrom.parents C.zero Q).mpr ⟨W,hRun.initial_row_at_d hM⟩
  have hsω : M.mem s C.omega := hsLast.elim (fun he => he ▸ hD.coordinates.last)
    (fun h => hw.transitive D.coordinates.last hD.coordinates.last s h)
  have hRootS : M.mem D.coordinates.root s := nat_lt_trans hM hC hsω hRootZ hzs
  have hzLast : M.mem z D.coordinates.last := nat_lt_of_lt_of_le hM hC hD.coordinates.last hzs hsLast
  have hcc : M.mem cc Y.width := (hRebuild.graph.bounds hM.1 hTC).1
  have hzz : M.mem zz Y.width := (hRebuild.graph.bounds hM.1 hTZ).1
  have hsm : M.mem s m := (hRun.base.values.bounds hM.1 hVS).1
  have hzm : M.mem z m := (hRun.base.values.bounds hM.1 hVZ).1
  obtain ⟨dc,hDC⟩ := depth_exists_d hM hC hRun.base.forest hsm
  obtain ⟨dz,hDZ⟩ := depth_exists_d hM hC hRun.base.forest hzm
  have hZero : NumericOrder.ZerosAtRoots M m F W C.zero :=
    fun c _ h0 => False.elim (nat_irrefl hM C.zero (hPositive c C.zero h0))
  have hCommon : NumericOrder.CommonAncestors M C m F s z :=
    fun a _ => ancestor_iff_of_parent_rows_eq_d hM hC hSel.inherited hFrame a
  have hCmp := NumericOrder.sparse_depth_compare_d hM hC hSel hZero hCommon hVS hVZ (hPositive s vs hVS)
    (hPositive z vz hVZ) hLe hDC hDZ
  obtain ⟨P0,_,hP0⟩ := hY.parents.total C.zero hC.zero_nat
  rcases hCmp.1 with heq | hlt
  · have hRows := hCmp.2 heq
    classical
    by_cases hSome : ∃ p0, MemPair M Q s p0
    · obtain ⟨p0,hQs⟩ := hSome
      have hQz := (hRows p0).mp hQs
      obtain ⟨tc0,tz0,hTC0,hTZ0,hKey0⟩ := source_bottom_key_d hM hC hRun hPositive hD.mountain hFrom hTopOld hQs hQz hVS hVZ hLe
      obtain ⟨tc',_,hTC'⟩ := hNewTop.total cc hcc
      obtain ⟨tz',_,hTZ'⟩ := hNewTop.total zz hzz
      have hKeyY := zero_key_transport_d hM hC hT hD hY hCopy hRun hFrom hOrder hQ0 hQs hQz hRootZ hzs hsLast hMapS hMapZ
        hcc hTC0 hTZ0 hTC' hTZ' hKey0
      obtain ⟨Jc,hJc,hRowsJ⟩ := parent_copy_graph_exists_d hM hC hT hD.coordinates hMapS.2.1
      obtain ⟨pp,_,hJp⟩ := hJc.graph.total p0 (hw.transitive m hRun.space.width p0 (hRun.base.forest.bounds hM.1 hQs).2)
      have hMapP := (hRowsJ p0 pp).mp hJp
      have hPcc : MemPair M P0 cc pp := (canon_row_parent_iff hM.1 hY hP0).mp
        ((zero_parent_copy_iff_d hM hC hT hD hCopy ⟨hRootS,hsLast⟩ hMapS hcc).mpr
          ⟨p0,(canon_row_parent_iff hM.1 hD.mountain hQ0).mpr hQs,hMapP⟩)
      have hPzz : MemPair M P0 zz pp := (canon_row_parent_iff hM.1 hY hP0).mp
        ((zero_parent_copy_iff_d hM hC hT hD hCopy ⟨hRootZ,Or.inr hzLast⟩ hMapZ hzz).mpr
          ⟨p0,(canon_row_parent_iff hM.1 hD.mountain hQ0).mpr hQz,hMapP⟩)
      exact key_value_le_d hM hC hT.add hY hNewTop hNewPos hB hP hH hCanon hC.zero_nat (Or.inl rfl) hC.one_succ hRow0 hP0
        hPcc hPzz hTC' hTZ' hKeyY tc tz hTC hTZ
    · have hNoneS : ∀ q, ¬MemPair M Q s q := fun q hq => hSome ⟨q,hq⟩
      have hNoneZ : ∀ q, ¬MemPair M Q z q := fun q hq => hSome ⟨q,(hRows q).mpr hq⟩
      have hsLast' : M.mem s D.coordinates.last := by
        rcases hsLast with he | hlt
        · exfalso
          have hRootLast := source_root_ancestor_last_d hM hC hD hRun hFrom hQ0 (zero_le_d hM hC (hD.floor_nat hM.1))
          obtain ⟨q,hq,_⟩ := ancestor_parent_cases_d hM hC (hD.mountain.forest C.zero Q hQ0) hRootLast
          exact hNoneS q (he ▸ hq)
        · exact hlt
      have hBS := (good_bottom_value_d hM hC hT hD hY hCopy hKept hRun hPositive hFrom hExtraction hNewTop hPrefixTop
        hFixed hRebuild hRootS hsLast' (fun q hq => False.elim (hNoneS q hq)) hMapS hcc).mp hTC
      have hBZ := (good_bottom_value_d hM hC hT hD hY hCopy hKept hRun hPositive hFrom hExtraction hNewTop hPrefixTop
        hFixed hRebuild hRootZ hzLast (fun q hq => False.elim (hNoneZ q hq)) hMapZ hzz).mp hTZ
      have h1 := hRooted.rootsOne s tc hBS (fun q _ hq => hNoneS q hq)
      have h2 := hRooted.rootsOne z tz hBZ (fun q _ hq => hNoneZ q hq)
      exact Or.inl (h1.trans h2.symm)
  · have hLtX : ForestOrder.DepthLtAt M C D.mountain s z C.zero :=
      ⟨dc,hDC.1,dz,hDZ.1,⟨Q,(hD.mountain.parents.bounds hM.1 hQ0).2,hQ0,hFrom.width.symm ▸ hDC⟩,
        ⟨Q,(hD.mountain.parents.bounds hM.1 hQ0).2,hQ0,hFrom.width.symm ▸ hDZ⟩,hlt⟩
    obtain ⟨a,ha,b',_,hDA,hDB,hab⟩ := (hCopy.canon_row_zero_d hM hC hT hD hY hRun hFrom hPositive hSel hFrame hRootS hsLast
      hRootZ (Or.inr hzLast) hMapS hMapZ hcc hzz).2 hLtX
    have htcω := (hRebuild.graph.bounds hM.1 hTC).2
    have htzω := (hRebuild.graph.bounds hM.1 hTZ).2
    rcases nat_le_or_lt hM hC htcω htzω with hle | hgt
    · exact hle
    exfalso
    obtain ⟨F',hFC⟩ := FrameCopy.copies_exists_d hM hC hT hD.coordinates hSel.inherited hN
    have hSelT := bottom_select_d hM hC hT hD hY hCopy hKept hRun hRooted hFrom hExtraction hNewTop hNewPos hPrefixTop
      hFixed hOrder hBound hRebuild hSel hFC hP0
    have hNotGoodS : ¬M.mem s D.coordinates.root := fun h => nat_irrefl hM _ ((hw.mem hD.coordinates.root).transitive s h _ hRootS)
    have hNotGoodZ : ¬M.mem z D.coordinates.root := fun h => nat_irrefl hM _ ((hw.mem hD.coordinates.root).transitive z h _ hRootZ)
    have hF'rows : ParentRowsEqual M F' zz cc := by
      intro t
      rw [FrameCopy.Copies.encoded_parent_iff_d hM hC hT hD.coordinates hSel.inherited hFC ⟨hRootZ,Or.inr hzLast⟩
          ((parent_copy_bad_iff hNotGoodZ).mp hMapZ) hzz t,
        FrameCopy.Copies.encoded_parent_iff_d hM hC hT hD.coordinates hSel.inherited hFC ⟨hRootS,hsLast⟩
          ((parent_copy_bad_iff hNotGoodS).mp hMapS) hcc t]
      exact exists_congr (fun p => and_congr Iff.rfl (and_congr (hFrame p).symm Iff.rfl))
    have hCommonT : NumericOrder.CommonAncestors M C Y.width F' zz cc :=
      fun a _ => ancestor_iff_of_parent_rows_eq_d hM hC hFC.forest hF'rows a
    have hZeroT : NumericOrder.ZerosAtRoots M Y.width F' Bottom C.zero :=
      fun c _ h0 => False.elim (nat_irrefl hM C.zero (hBotPos c C.zero h0))
    have hCmpT := NumericOrder.sparse_depth_compare_d hM hC hSelT hZeroT hCommonT hTZ hTC (hBotPos zz tz hTZ)
      (hBotPos cc tc hTC) (Or.inr hgt) ((ForestOrder.depth_at_row_iff hM.1 hY hP0 zz b').mp hDB)
      ((ForestOrder.depth_at_row_iff hM.1 hY hP0 cc a).mp hDA)
    exact nat_not_lt_of_le hM hC ha hCmpT.1 hab

/-- `LowerLayer.DownPart` 字段（LANE-B `OneYLowerLayerStep.lean`）的实际证明，类型与其定义体相同。
第j层的 oldTop'/Qnext' 由层运行识别为第k层底行(W,Q)；UpperFixed 用 `good_bottom_value_d`，
UpperOrder 用 `bottom_order_d`（第j层伪父森林即第k层底行的继承帧）。 -/
theorem down_part_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {A : CopyCoordinates.Context M.Domain} {m : M.Domain} {L : LayerStateSpace M.Domain} {V P H K k N n : M.Domain}
    (hLayers : LayerRun M C m L V P H) (hN : CopyCoordinates.Width M C T A N n) :
    ∀ {j W Q J oldTop Qnext newTop Pnext Bottom W' Q' J' oldTop' Qnext' : M.Domain}
      {D D' : Lower.Context M.Domain} {Y Y' : Data M.Domain}, M.SuccessorOf k j →
      TowerCanon.LowerLayerData M C T A m L H K j n W' Q' J' oldTop' Qnext' D' Y' →
      TowerCanon.LowerLayerData M C T A m L H K k n W Q J oldTop Qnext D Y →
      Graph M newTop n C.omega → (∀ c v, MemPair M newTop c v → M.mem C.zero v) →
      TowerCanon.LowerInputs M C T D m N n oldTop Qnext newTop Pnext →
      ReconstructionSelection.PseudoTopBound M C Y newTop →
      MountainReconstruction.Rebuilds M C T.addPairs T.plus Y newTop Bottom →
      Lower.UpperFixed M C T D' oldTop' Qnext' n Bottom ∧
        ∀ Pseudo, GraphPseudoForest M C D'.mountain Pseudo → Lower.UpperOrder M C T D' Pseudo oldTop' Bottom := by
  intro j W Q J oldTop Qnext newTop Pnext Bottom W' Q' J' oldTop' Qnext' D D' Y Y' hSucc hData' hData hNew hPos
    hInputs hBound hRebuild
  have hExt := hLayers.at_next hM.1 hSucc hData'.layer hData.layer
  obtain ⟨hTopEq,hQEq⟩ := hData'.extraction.unique_d hM hC hExt
  subst hTopEq
  subst hQEq
  have hCoords : D'.coordinates=D.coordinates := hData'.coordinates.trans hData.coordinates.symm
  have hA := hData.coordinates
  subst hA
  have hKept := width_kept_d hM hC hT hData.context.coordinates hN
  have hRooted := hLayers.at_rooted hM.1 hData.layer
  constructor
  · intro s hRoot hLast hGood b c v hMap hc hWs
    rw [hCoords] at hRoot hLast hMap
    exact (good_bottom_value_d hM hC hT hData.context hData.target hData.copies hKept hData.run hRooted.positive
      hData.from_run hData.extraction hNew hInputs.prefixTop hInputs.fixed hRebuild hRoot hLast
      (fun q hq => hCoords ▸ hGood q hq) hMap hc).mpr hWs
  · intro Pseudo hPseudo z s hRootZ hzs hsLast hFrame vs vz hVS hVZ hLe b cc zz tc tz hMapS hMapZ hTC hTZ
    rw [hCoords] at hRootZ hsLast hMapS hMapZ
    have hTopJ := Expansion.extraction_top_for_source_d hM hC hData'.run hData'.from_run hExt
    obtain ⟨F0,Q0,hF0,hSel0,hExt0⟩ := ReconstructionExtraction.extraction_graph_exists_d hM hC hData'.run
      hData'.context.mountain hData'.from_run hTopJ
    have hQQ := (hExt0.unique_d hM hC hExt).2
    subst hQQ
    have hPP := hPseudo.unique hM.1 hF0
    subst hPP
    exact bottom_order_d hM hC hT hData.context hData.target hData.copies hKept hData.run hRooted hData.from_run
      hData.extraction hNew hPos hInputs.prefixTop hInputs.fixed hInputs.order hBound hRebuild hSel0 hN
      hRootZ hzs hsLast hFrame hVS hVZ hLe hMapS hMapZ hTC hTZ

end KP1Y.OneYFinite.LowerBlock
