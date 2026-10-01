import KP1Y.OneYLowerBottomRows

/-! Lower复制的单列数值运输：两个实际重建网格中高度、Top与逐行父项贡献相同的列，其各行值相同。
用于好部（或无）底父列：复制列的重建底值恰为源底值（原 `value_copy_of_good_base_parent`）。 -/
namespace KP1Y.OneYFinite.LowerBlock
open YesMetaZFC YesMetaZFC.SetTheory YesMetaZFC.SetTheory.Definitional
open KP1Y.Kuratowski KP1Y.Functions KP1Y.Naturals KP1Y.Bounded KP1Y.Arithmetic
open KP1Y.OneYFinite KP1Y.OneYFinite.CopyCoordinates KP1Y.OneYFinite.CopiedMountain
open KP1Y.OneYFinite.CopiedMountain.Lower KP1Y.OneYFinite.LowerCanon
open KP1Y.OneYFinite.MountainReconstruction KP1Y.OneYFinite.Reconstruction
universe u

/-- 内部ω中 0≤r。 -/
theorem zero_le_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {r : M.Domain} (hr : M.mem r C.omega) : C.zero=r ∨ M.mem C.zero r := by
  classical
  by_cases hz : r=C.zero
  · exact Or.inl hz.symm
  · exact Or.inr ((hC.zero_mem_iff hM hr).mpr hz)

/-- 两个网格（同自然数与加法表）中单列的数值运输；行界可以不同。 -/
theorem column_transport_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {Pairs Plus : M.Domain} (hPlus : AdditionTable M C Pairs Plus)
    {X Y : Data M.Domain} {Top Top' B B' Parents Parents' H J c c' h top : M.Domain}
    (hD : (grid C X Top Pairs Plus B Parents).Valid M) (hE : (grid C Y Top' Pairs Plus B' Parents').Valid M)
    (hH : Reconstructs M (grid C X Top Pairs Plus B Parents) H)
    (hJ : Reconstructs M (grid C Y Top' Pairs Plus B' Parents') J)
    (hc : M.mem c X.width) (hc' : M.mem c' Y.width)
    (hHeight : MemPair M X.heights c h) (hHeight' : MemPair M Y.heights c' h)
    (hTop : MemPair M Top c top) (hTop' : MemPair M Top' c' top)
    (hContrib : ∀ r, M.mem r h → ∀ x, M.mem x C.omega →
      (Contributes M (grid C X Top Pairs Plus B Parents) H c r x ↔ Contributes M (grid C Y Top' Pairs Plus B' Parents') J c' r x))
    {r x : M.Domain} (hr : M.mem r C.omega) :
    PreviousValue M (grid C X Top Pairs Plus B Parents) H c r x ↔
      PreviousValue M (grid C Y Top' Pairs Plus B' Parents') J c' r x := by
  have hw := omega_isOrdinal_d hM hC.omega
  obtain ⟨f,_,hCf⟩ := hH.graph.total c hc
  obtain ⟨g,_,hCg⟩ := hJ.graph.total c' hc'
  obtain ⟨K,hK⟩ := contribution_graph_exists_d hM hD hH.graph c
  obtain ⟨L,hL⟩ := contribution_graph_exists_d hM hE hJ.graph c'
  have hF := (hH.column hM.1 hCf).to_filled_column hM hD hK hHeight hTop
  have hG := (hJ.column hM.1 hCg).to_filled_column hM hE hL hHeight' hTop'
  have hRows : RowsAgreeOn M K L h := by
    intro s hs y
    have hsω := hw.transitive B hF.rows s ((hw.mem hF.rows).transitive h hF.height s hs)
    constructor
    · intro hsy
      have hy := (hK.graph.bounds hM.1 hsy).2
      exact (hL.rows s hsω y hy).mpr ((hContrib s hs y hy).mp ((hK.rows s hsω y hy).mp hsy))
    · intro hsy
      have hy := (hL.graph.bounds hM.1 hsy).2
      exact (hK.rows s hsω y hy).mpr ((hContrib s hs y hy).mpr ((hL.rows s hsω y hy).mp hsy))
  obtain ⟨len,f',hF',hPrefF⟩ := hF.lower_d hM hC
  obtain ⟨len',g',hG',hPrefG⟩ := hG.lower_d hM hC
  have hLen := Structure.SuccessorOf.eq hM.1 hF'.length hG'.length
  subst len'
  have hfg := hF'.unique_of_contributions_d hM hC hK.graph hPlus hRows hG'
  subst g'
  rw [hH.previous_value_iff hM.1 hCf,hJ.previous_value_iff hM.1 hCg]
  change (MemPair M f r x ∨ (¬M.mem r B ∧ x=C.zero)) ↔ (MemPair M g r x ∨ (¬M.mem r B' ∧ x=C.zero))
  have hAbove {Bx fx Kx : M.Domain} (hX : FilledColumn M C Pairs Plus Kx Bx h top fx) (hhr : M.mem h r) :
      (MemPair M fx r x ∨ (¬M.mem r Bx ∧ x=C.zero)) ↔ x=C.zero := by
    classical
    constructor
    · rintro (hrx | ⟨_,hx⟩)
      · exact hX.absent r (hX.graph.bounds hM.1 hrx).1 x hrx hhr
      · exact hx
    · intro hx
      by_cases hrB : M.mem r Bx
      · obtain ⟨y,_,hry⟩ := hX.graph.total r hrB
        have hy := hX.absent r hrB y hry hhr
        exact Or.inl ((hx.trans hy.symm).symm ▸ hry)
      · exact Or.inr ⟨hrB,hx⟩
  rcases hw.wellOrder.linear.compare r hr h hF'.height with he | hrh | hhr
  · have hre := hM.1.eq_of_same_members r h he
    subst hre
    have hrLen : M.mem r len := hF'.length.predecessor_mem
    have hV := (hPrefF.all_rows hM.1 hF.graph r hrLen x).symm.trans (hPrefG.all_rows hM.1 hG.graph r hrLen x)
    exact ⟨fun h' => h'.elim (fun hf => Or.inl (hV.mp hf)) (fun h'' => False.elim (h''.1 hF.height)),
      fun h' => h'.elim (fun hg => Or.inl (hV.mpr hg)) (fun h'' => False.elim (h''.1 hG.height))⟩
  · have hrLen : M.mem r len := (hF'.length r).mpr (Or.inl hrh)
    have hrB := (hw.mem hF.rows).transitive h hF.height r hrh
    have hrB' := (hw.mem hG.rows).transitive h hG.height r hrh
    have hV := (hPrefF.all_rows hM.1 hF.graph r hrLen x).symm.trans (hPrefG.all_rows hM.1 hG.graph r hrLen x)
    exact ⟨fun h' => h'.elim (fun hf => Or.inl (hV.mp hf)) (fun h'' => False.elim (h''.1 hrB)),
      fun h' => h'.elim (fun hg => Or.inl (hV.mpr hg)) (fun h'' => False.elim (h''.1 hrB'))⟩
  · exact (hAbove hF hhr).trans (hAbove hG hhr).symm

/-- 网格中唯一父项的列贡献即父项的取值。 -/
theorem contributes_parent_iff {M : SetTheory.Structure.{u}}
    {D : GridData M.Domain} (hD : D.Valid M) {H c r p x : M.Domain}
    (hParent : Reconstruction.ParentAt M D r c p) (hpc : M.mem p c) :
    Contributes M D H c r x ↔ PreviousValue M D H p r x := by
  have hUnique (q : M.Domain) (hq : Reconstruction.ParentAt M D r c q) : q=p := by
    obtain ⟨F,_,hF,hFq⟩ := hq
    obtain ⟨F',_,hF',hFp⟩ := hParent
    have hFF := hD.parents.unique r F F' hF hF'
    subst F'
    exact (hD.forests r F hF).unique c q p hFq hFp
  constructor
  · rintro (⟨q,_,hq,hValue⟩ | ⟨_,hNo⟩)
    · exact hUnique q hq ▸ hValue
    · exact False.elim (hNo p hpc hParent)
  · exact fun hValue => Or.inl ⟨p,hpc,hParent,hValue⟩

/-- 源与Lower复制的重建网格在原末列前缀一致（所有行）。 -/
theorem lower_prefix_data_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain}
    {D : Lower.Context M.Domain} (hD : D.Valid M C) {Y : Data M.Domain} (hY : Y.Valid M C) {n : M.Domain}
    (hCopy : Copies M C T D n Y) (hKept : M.MemberSubset D.coordinates.last n)
    {oldTop newTop B B' Parents Parents' : M.Domain}
    (hB : SequenceBound M C D.mountain.width D.mountain.heights B) (hP : Prefix M Parents D.mountain.parents B D.mountain.forests)
    (hB' : SequenceBound M C Y.width Y.heights B') (hP' : Prefix M Parents' Y.parents B' Y.forests)
    (hPrefixTop : RowsAgreeOn M newTop oldTop D.coordinates.last) :
    PrefixData M (grid C D.mountain oldTop T.addPairs T.plus B Parents) (grid C Y newTop T.addPairs T.plus B' Parents')
      D.coordinates.last := by
  have hw := omega_isOrdinal_d hM hC.omega
  have hLeft : M.MemberSubset D.coordinates.last D.mountain.width :=
    fun c hc => (hw.mem hD.mountain.width).transitive D.coordinates.last hD.last c hc
  have hRight : M.MemberSubset D.coordinates.last Y.width := fun c hc => hCopy.width.symm ▸ hKept c hc
  refine ⟨rfl,hD.coordinates.last,hLeft,hRight,?_,?_,?_⟩
  · intro c hc h
    exact (hCopy.original_heights_d hM hC hD (hKept c hc) (Or.inr hc)).symm
  · intro c hc v
    exact (hPrefixTop c hc v).symm
  · intro c hc r _ p
    exact (grid_parent_iff_d hM hC hD.mountain hB hP).trans
      ((hCopy.original_parents_d hM hC hD (hKept c hc) (Or.inr hc)).symm.trans (grid_parent_iff_d hM hC hY hB' hP').symm)

/-- 源第0行父项为好部或不存在时，提取父项也只能在好部（无父时提取父不存在）。 -/
theorem extracted_parent_good_zero_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {D : Lower.Context M.Domain} (hD : D.Valid M C)
    {m : M.Domain} {R : RowStateSpace M.Domain} {V P H : M.Domain} (hRun : RowRun M C m R V P H)
    (hFrom : FromRun M C m R V H D.mountain)
    {oldTop Qnext : M.Domain} (hExtraction : Extraction M C m V P oldTop Qnext) {s : M.Domain}
    (hGood : ∀ q, ParentAt M D.mountain C.zero s q → M.mem q D.coordinates.root) :
    ∀ q, MemPair M Qnext s q → M.mem q D.coordinates.root := by
  intro q hq
  classical
  by_cases hSome : ∃ g, ParentAt M D.mountain C.zero s g
  · obtain ⟨g,hg⟩ := hSome
    exact extracted_parent_bound_d hM hC hRun hD.mountain hFrom hExtraction hg (hGood g hg) hD.coordinates.root hq
  · exfalso
    obtain ⟨R',H',Heights,F,hRun',hHeights,_,hPF,hSel⟩ := hExtraction
    have hRR := row_state_space_unique hM.1 hRun'.space hRun.space
    subst R'
    have hHH := hRun'.unique_d hM hC hRun
    subst H'
    have hHeightsEq := hHeights.unique hM.1 hFrom.heights
    subst Heights
    obtain ⟨a,hFa,_⟩ := ancestor_parent_cases_d hM hC hPF.forest ((hSel.parents s q).mp hq).1.1
    obtain ⟨⟨hc,_,hHC,hPos⟩,_,_⟩ := (hPF.parents s a).mp hFa
    exact hSome ((hD.mountain.source C.zero s hc hHC).mpr hPos)

/-- 原 `value_copy_of_good_base_parent`：源第0行父项为好部或不存在的非root源列 root<s<last，
其任一复制的实际重建底值恰为源底值。只用上层 `prefixTop/fixed`。 -/
theorem good_bottom_value_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {D : Lower.Context M.Domain} (hD : D.Valid M C) {Y : Data M.Domain} (hY : Y.Valid M C) {n : M.Domain}
    (hCopy : Copies M C T D n Y) (hKept : M.MemberSubset D.coordinates.last n)
    {m : M.Domain} {R : RowStateSpace M.Domain} {W Q J : M.Domain}
    (hRun : RowRun M C m R W Q J) (hPositive : ∀ c a, MemPair M W c a → M.mem C.zero a)
    (hFrom : FromRun M C m R W J D.mountain) {oldTop Qnext newTop Bottom : M.Domain}
    (hExtraction : Extraction M C m W Q oldTop Qnext) (hNewTop : Graph M newTop n C.omega)
    (hPrefixTop : RowsAgreeOn M newTop oldTop D.coordinates.last) (hFixed : UpperFixed M C T D oldTop Qnext n newTop)
    (hRebuild : Rebuilds M C T.addPairs T.plus Y newTop Bottom)
    {s b c v : M.Domain} (hRoot : M.mem D.coordinates.root s) (hLast : M.mem s D.coordinates.last)
    (hGood : ∀ q, MemPair M Q s q → M.mem q D.coordinates.root)
    (hMap : ParentCopy M C T D.coordinates b s c) (hc : M.mem c n) : MemPair M Bottom c v ↔ MemPair M W s v := by
  have hw := omega_isOrdinal_d hM hC.omega
  have hTopOld := Expansion.extraction_top_for_source_d hM hC hRun hFrom hExtraction
  have hQ0 : MemPair M D.mountain.parents C.zero Q := (hFrom.parents C.zero Q).mpr ⟨W,hRun.initial_row_at_d hM⟩
  have hGoodAt (q : M.Domain) (hq : ParentAt M D.mountain C.zero s q) : M.mem q D.coordinates.root :=
    hGood q ((canon_row_parent_iff hM.1 hD.mountain hQ0).mp hq)
  have hsX : M.mem s D.mountain.width := (hw.mem hD.mountain.width).transitive D.coordinates.last hD.last s hLast
  have hsω := hw.transitive D.coordinates.last hD.coordinates.last s hLast
  have hsNe : s≠D.coordinates.root := fun he => nat_irrefl hM s (he.symm ▸ hRoot)
  obtain ⟨h,hh,hHS⟩ := hD.mountain.heights.total s hsX
  have hGoodRow (r : M.Domain) (hrh : M.mem r h) (p : M.Domain) (hP : ParentAt M D.mountain r s p) :
      M.mem p D.coordinates.root := by
    have hr := (hP.bounds hM.1 hD.mountain).1
    have h0 : M.mem C.zero h := nat_lt_of_le_of_lt hM hC hh (zero_le_d hM hC hr) hrh
    obtain ⟨g,hg⟩ := (hD.mountain.source C.zero s h hHS).mpr h0
    obtain ⟨Fr,_,hFr,hFrP⟩ := hP
    have hAnc := canon_source_ancestor_lower_d hM hC hRun hFrom hQ0 hFr (zero_le_d hM hC hr)
      (ancestor_direct_d hM hC (hD.mountain.forest r Fr hFr) hFrP)
    have hpg := ancestor_le_parent_d hM hC (hD.mountain.forest C.zero Q hQ0) ((canon_row_parent_iff hM.1 hD.mountain hQ0).mp hg) hAnc
    exact nat_lt_of_le_of_lt hM hC hD.coordinates.root hpg (hGoodAt g hg)
  have hOut : ¬InCone M C D s := by
    intro hCone
    have hFloorH := hCone.height_strict_d hM hC hD hRoot hHS
    have h0 : M.mem C.zero h := nat_lt_of_le_of_lt hM hC hh (zero_le_d hM hC (hD.floor_nat hM.1)) hFloorH
    obtain ⟨g,hg⟩ := (hD.mountain.source C.zero s h hHS).mpr h0
    have hgGood := hGoodAt g hg
    obtain ⟨F0,_,hF0,hF0g⟩ := hg
    have hF0Q := hD.mountain.parents.unique C.zero F0 Q hF0 hQ0
    subst F0
    exact canon_good_parent_out_d hM hC hD hRun hFrom hRoot hQ0 hF0g hgGood hCone
  have hcY : M.mem c Y.width := hCopy.width.symm ▸ hc
  have hHeightY : MemPair M Y.heights c h := (hCopy.parent_copy_heights_d hM hC hT hD hLast hc hMap hHS).mpr (Or.inr ⟨hOut,rfl⟩)
  have hExtrGood := extracted_parent_good_zero_d hM hC hD hRun hFrom hExtraction hGoodAt
  obtain ⟨top,_,hTopS⟩ := hTopOld.graph.total s (hFrom.width ▸ hsX)
  have hTopC : MemPair M newTop c top := hFixed s hRoot hLast hExtrGood b c top hMap hc hTopS
  obtain ⟨B,Parents,H,hB,hP,hH,hBot⟩ := rebuild_original_d hM hC hT.add hRun hPositive hD.mountain hFrom hTopOld
  obtain ⟨B',Parents',H',hB',hP',hH',hBot'⟩ := hRebuild
  have hDv := grid_valid_d hM hC hD.mountain (hFrom.width.symm ▸ hTopOld.graph) hT.add hB hP
  have hEv := grid_valid_d hM hC hY (hCopy.width.symm ▸ hNewTop) hT.add hB' hP'
  have hPre := lower_prefix_data_d hM hC hD hY hCopy hKept hB hP hB' hP' hPrefixTop
  have hValuesPre := reconstruction_prefix_values_d hM hDv hEv hPre hH hH'
  have hRootC : M.mem D.coordinates.root c := (parent_copy_source_le_d hM hC hT hMap).elim (fun he => he ▸ hRoot)
    (fun h' => (hw.mem (hw.transitive Y.width hY.width c hcY)).transitive s h' D.coordinates.root hRoot)
  have hContrib : ∀ r, M.mem r h → ∀ x, M.mem x C.omega →
      (Contributes M (grid C D.mountain oldTop T.addPairs T.plus B Parents) H s r x ↔
        Contributes M (grid C Y newTop T.addPairs T.plus B' Parents') H' c r x) := by
    intro r hrh x hx
    obtain ⟨p,hPX⟩ := (hD.mountain.source r s h hHS).mpr hrh
    have hpGood := hGoodRow r hrh p hPX
    have hr := (hPX.bounds hM.1 hD.mountain).1
    have hpω := hw.transitive D.coordinates.root hD.coordinates.root p hpGood
    have hPY : ParentAt M Y r c p := (hCopy.parents r c p).mpr ⟨hc,
      (parent_copy_nonroot_unmoved_d hM hC hT hD hr hLast hsNe (fun h' => hOut h'.1) hMap).mpr
        ⟨p,hpω,hPX,parent_copy_good_d hM hC hD.coordinates hMap.2.1 hpGood⟩⟩
    have hps : M.mem p s := (hPX.bounds hM.1 hD.mountain).2.2.2
    have hpc : M.mem p c := (hw.mem (hw.transitive Y.width hY.width c hcY)).transitive D.coordinates.root hRootC p hpGood
    have hpLast := (hw.mem hD.coordinates.last).transitive D.coordinates.root hD.coordinates.below p hpGood
    exact (contributes_parent_iff hDv ((grid_parent_iff_d hM hC hD.mountain hB hP).mpr hPX) hps).trans
      ((hValuesPre p hpLast r hr x hx).trans
        (contributes_parent_iff hEv ((grid_parent_iff_d hM hC hY hB' hP').mpr hPY) hpc).symm)
  have hCol := column_transport_d hM hC hT.add hDv hEv hH hH' hsX hcY hHS hHeightY hTopS hTopC hContrib
    (r := C.zero) (x := v) hC.zero_nat
  exact (hBot'.previous_iff hM.1 hH' hB'.1.2.1 hcY).symm.trans (hCol.symm.trans (hBot.previous_iff hM.1 hH hB.1.2.1 hsX))

end KP1Y.OneYFinite.LowerBlock
