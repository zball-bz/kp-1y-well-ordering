import KP1Y.OneYCanonHelperKey

/-! 共同第0行父项的数值弱序沿实际同块复制保持：源图层Key（由源数值行得到）经真实扩展帧
`copied_key_le_d`/`seam_key_le_d`运输为目标图层Key，再由目标网格比较回到目标底值。 -/
namespace KP1Y.OneYFinite.TerminalBase
open YesMetaZFC YesMetaZFC.SetTheory YesMetaZFC.SetTheory.Definitional
open KP1Y.Kuratowski KP1Y.Functions KP1Y.Naturals KP1Y.Bounded KP1Y.Arithmetic
open ReconstructionCanonical Reconstruction MountainReconstruction ReconstructionRecovery
universe u

theorem parent_copy_unique_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {A : CopyCoordinates.Context M.Domain} (hA : A.Valid M C) {b p x y : M.Domain}
    (hx : CopyCoordinates.ParentCopy M C T A b p x) (hy : CopyCoordinates.ParentCopy M C T A b p y) : x=y := by
  obtain ⟨J,hJ,hRows⟩ := CopyCoordinates.parent_copy_graph_exists_d hM hC hT hA hx.2.1
  exact hJ.graph.unique p x y ((hRows p x).mpr hx) ((hRows p y).mpr hy)

theorem parent_copy_exists_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {A : CopyCoordinates.Context M.Domain} (hA : A.Valid M C) {b p : M.Domain}
    (hb : M.mem b C.omega) (hp : M.mem p C.omega) : ∃ q, CopyCoordinates.ParentCopy M C T A b p q := by
  obtain ⟨J,hJ,hRows⟩ := CopyCoordinates.parent_copy_graph_exists_d hM hC hT hA hb
  obtain ⟨q,_,hq⟩ := hJ.graph.total p hp
  exact ⟨q,(hRows p q).mp hq⟩

section
variable {M : SetTheory.Structure.{u}} {C : ExpressionData M.Domain} {T : MatrixArithmetic M.Domain}
  {m V P H level index n OldTop NewTop Bottom : M.Domain} {R : RowStateSpace M.Domain}
  {X Y : CopiedMountain.Data M.Domain} {A : CopyCoordinates.Context M.Domain}

/-- 源：共同第0行父项与源底值弱序给出自第1行起的图层Key。 -/
theorem Base.source_key_d (hM : M.Models KP1Y.theory) (hC : C.Valid M)
    (h : Base M C T m V P H level index n OldTop NewTop Bottom R X Y A) {s z p vs vz ts tz : M.Domain}
    (hSP : MemPair M P s p) (hZP : MemPair M P z p) (hVS : MemPair M V s vs) (hVZ : MemPair M V z vz)
    (hLe : vs=vz ∨ M.mem vs vz) (hTS : MemPair M OldTop s ts) (hTZ : MemPair M OldTop z tz) :
    ForestOrder.KeyLE M C X s z C.one ts tz := by
  have hRow0 := h.run.base
  obtain ⟨W1,Q1,hAt1⟩ := h.run.at_exists_d hC.one_nat
  have hNext := h.run.at_next hM.1 hC.one_succ (h.run.initial_row_at_d hM) hAt1
  have hRow1 := h.run.at_numeric_d hM hC hAt1
  have hs := (hRow0.forest.bounds hM.1 hSP).1
  have hz := (hRow0.forest.bounds hM.1 hZP).1
  obtain ⟨x1,_,hX1⟩ := hRow1.values.total s hs
  obtain ⟨y1,_,hY1⟩ := hRow1.values.total z hz
  have hx1 := (hRow0.difference_positive_iff_d hM hC hNext.difference hX1).mpr ⟨p,hSP⟩
  have hy1 := (hRow0.difference_positive_iff_d hM hC hNext.difference hY1).mpr ⟨p,hZP⟩
  have hLe1 := NumericOrder.difference_mono_common_parent_d hM hC hRow0 hNext.difference hSP hZP hVS hVZ hLe hX1 hY1
  have hParents : ∀ q, MemPair M P s q ↔ MemPair M P z q := fun q =>
    ⟨fun hq => (hRow0.forest.unique s p q hSP hq) ▸ hZP,fun hq => (hRow0.forest.unique z p q hZP hq) ▸ hSP⟩
  have hCommon : NumericOrder.CommonAncestors M C m P s z :=
    fun q _ => ancestor_iff_of_parent_rows_eq_d hM hC hRow0.forest hParents q
  have hKey := NumericOrder.key_le_of_common_values_d hM hC h.run h.rooted.positive h.fromRun.heights h.oldTop hTS hTZ
    hAt1 hNext.selection (NumericOrder.row_next_zeros_at_roots_d hM hC hRow0 hNext) hCommon hX1 hY1 hx1 hy1 hLe1
  exact (ForestOrder.from_run_key_iff_d hM hC h.run h.source h.fromRun s z C.one ts tz).mpr hKey

/-- 同块普通副本的图层Key运输（共同第0行父项）。 -/
theorem Base.copied_key_d (hM : M.Models KP1Y.theory) (hC : C.Valid M) (hT : T.Valid M C)
    (h : Base M C T m V P H level index n OldTop NewTop Bottom R X Y A) {s z b cs cz ts tz : M.Domain}
    (hRootS : M.mem A.root s) (hs : M.mem s A.last) (hRootZ : M.mem A.root z) (hz : M.mem z A.last)
    (hSame : ParentRowsEqual M P s z) (hb : b=index ∨ M.mem b index)
    (hMapS : CopyCoordinates.ParentCopy M C T A b s cs) (hMapZ : CopyCoordinates.ParentCopy M C T A b z cz)
    (hTS : MemPair M OldTop s ts) (hTZ : MemPair M OldTop z tz) (hKey : ForestOrder.KeyLE M C X s z C.one ts tz) :
    MemPair M NewTop cs ts ∧ MemPair M NewTop cz tz ∧ ForestOrder.KeyLE M C Y cs cz C.one ts tz := by
  obtain ⟨Frame,B,L,BF,BR,BL,Heights,Top,active,hFrame,hCap,hTrim,_,hFrameRaw,hBRun,hI,hHeights,hTop,hTopGraph,_,hActive,hContext,hS⟩ :=
    NumericOrder.row_bad_active_frame_decorated_exists_d hM hC hT h.run h.rooted h.lastWidth h.bad
  have hHeightEq := hHeights.unique hM.1 h.fromRun.heights
  subst Heights
  have hTopEq := hTop.unique hM.1 h.oldTop
  subst Top
  obtain ⟨D,DF,DR,DL,NewTop',hExpansion,_,hDRun,_,_,hExpandedTop,_⟩ :=
    matrix_expansion_decorated_exists_d hM hC hTrim.matrix hT hBRun h.indexNat hTopGraph hI hS
  have hWidthD := hExpansion.width_coordinates_d hM hC hTrim.matrix hT h.coords hBRun hContext h.indexNat
  have hWidthEq := CopyCoordinates.encode_unique hM.1 hT hWidthD h.widthN
  have hCopy' : CopiedMountain.Terminal.Copies M C T A X level D.width Y := hWidthEq.symm ▸ h.copies
  have hCopiedTop := TerminalCanonical.expanded_top_copied_d hM hC hTrim.matrix hBRun h.coords hContext hExpandedTop
  have hNewEq : NewTop'=NewTop := hCopiedTop.unique hM.1 ((hWidthEq.trans h.width_eq.symm).symm ▸ h.newTop)
  subst hNewEq
  exact ForestOrder.copied_key_le_d hM hC hT h.run hFrame hCap hFrameRaw hTrim hBRun hDRun h.source h.fromRun h.coords
    (hActive.bounds hM.1 hT.add).2.1 hActive hContext h.indexNat hExpansion h.target hCopy' hTopGraph hCopiedTop hTS hTZ
    hC.zero_nat hC.one_succ (h.run.initial_row_at_d hM) hSame hs hz hRootS hRootZ hb hMapS hMapZ hKey

/-- 低seam的图层Key运输：左侧为实际seam列及其复制Top读数。 -/
theorem Base.seam_key_d (hM : M.Models KP1Y.theory) (hC : C.Valid M) (hT : T.Valid M C)
    (h : Base M C T m V P H level index n OldTop NewTop Bottom R X Y A) {z b next seam cz tl tz : M.Domain}
    (hLow : M.mem C.zero level) (hRootZ : M.mem A.root z) (hz : M.mem z A.last)
    (hSame : ParentRowsEqual M P A.last z) (hNext : M.SuccessorOf next b) (hNextBound : next=index ∨ M.mem next index)
    (hEncode : CopyCoordinates.Encode M C T A A.last b seam) (hMapZ : CopyCoordinates.ParentCopy M C T A b z cz)
    (hTL : MemPair M OldTop A.last tl) (hTZ : MemPair M OldTop z tz) (hKey : ForestOrder.KeyLE M C X A.last z C.one tl tz) :
    ∃ topSeam, M.mem topSeam C.omega ∧ MemPair M NewTop seam topSeam ∧ MemPair M NewTop cz tz ∧
      ForestOrder.KeyLE M C Y seam cz C.one topSeam tz := by
  obtain ⟨Frame,B,L,BF,BR,BL,Heights,Top,active,hFrame,hCap,hTrim,_,hFrameRaw,hBRun,hI,hHeights,hTop,hTopGraph,_,hActive,hContext,hS⟩ :=
    NumericOrder.row_bad_active_frame_decorated_exists_d hM hC hT h.run h.rooted h.lastWidth h.bad
  have hHeightEq := hHeights.unique hM.1 h.fromRun.heights
  subst Heights
  have hTopEq := hTop.unique hM.1 h.oldTop
  subst Top
  obtain ⟨D,DF,DR,DL,NewTop',hExpansion,_,hDRun,_,_,hExpandedTop,_⟩ :=
    matrix_expansion_decorated_exists_d hM hC hTrim.matrix hT hBRun h.indexNat hTopGraph hI hS
  have hWidthD := hExpansion.width_coordinates_d hM hC hTrim.matrix hT h.coords hBRun hContext h.indexNat
  have hWidthEq := CopyCoordinates.encode_unique hM.1 hT hWidthD h.widthN
  have hCopy' : CopiedMountain.Terminal.Copies M C T A X level D.width Y := hWidthEq.symm ▸ h.copies
  have hCopiedTop := TerminalCanonical.expanded_top_copied_d hM hC hTrim.matrix hBRun h.coords hContext hExpandedTop
  have hNewEq : NewTop'=NewTop := hCopiedTop.unique hM.1 ((hWidthEq.trans h.width_eq.symm).symm ▸ h.newTop)
  subst hNewEq
  exact ForestOrder.seam_key_le_d hM hC hT h.run hFrame hCap hFrameRaw hTrim hBRun hDRun h.source h.fromRun h.coords
    (hActive.bounds hM.1 hT.add).2.1 hActive hContext h.indexNat hExpansion h.target hCopy' hTopGraph hCopiedTop hTL hTZ
    hC.zero_nat hLow hC.one_succ (h.run.initial_row_at_d hM) hSame hz hRootZ hNext hNextBound hEncode hMapZ hKey

theorem Base.block_bound_d (hM : M.Models KP1Y.theory) (hC : C.Valid M) (hT : T.Valid M C)
    (h : Base M C T m V P H level index n OldTop NewTop Bottom R X Y A) {s b c : M.Domain}
    (hRoot : M.mem A.root s) (hs : s=A.last ∨ M.mem s A.last)
    (hMap : CopyCoordinates.ParentCopy M C T A b s c) (hc : M.mem c n) : b=index ∨ M.mem b index := by
  have hNotGood : ¬M.mem s A.root := fun hg => SetTheory.KP.mem_irrefl_d (KP1Y.models_weakKP hM) A.root
    (((omega_isOrdinal_d hM hC.omega).mem h.coords.root).transitive s hg A.root hRoot)
  have hEncode := (CopyCoordinates.parent_copy_bad_iff hNotGood).mp hMap
  rcases (CopyCoordinates.encoded_lt_width_iff_d hM hC hT h.coords ⟨hRoot,hs⟩ hEncode h.widthN).mp hc with hb | ⟨he,_⟩
  · exact Or.inr hb
  · exact Or.inl he

/-- (O1) 同块非root副本：共同第0行父项下源底值弱序保持到目标底值。 -/
theorem Base.copy_order_d (hM : M.Models KP1Y.theory) (hC : C.Valid M) (hT : T.Valid M C)
    (h : Base M C T m V P H level index n OldTop NewTop Bottom R X Y A) {P0 : M.Domain}
    (hP0 : MemPair M Y.parents C.zero P0) {s z p b cs cz vs vz xs xz : M.Domain}
    (hRootS : M.mem A.root s) (hs : M.mem s A.last) (hRootZ : M.mem A.root z) (hz : M.mem z A.last)
    (hSP : MemPair M P s p) (hZP : MemPair M P z p) (hVS : MemPair M V s vs) (hVZ : MemPair M V z vz)
    (hLe : vs=vz ∨ M.mem vs vz) (hMapS : CopyCoordinates.ParentCopy M C T A b s cs)
    (hMapZ : CopyCoordinates.ParentCopy M C T A b z cz) (hcs : M.mem cs n) (hcz : M.mem cz n)
    (hXS : MemPair M Bottom cs xs) (hXZ : MemPair M Bottom cz xz) : xs=xz ∨ M.mem xs xz := by
  have hw := omega_isOrdinal_d hM hC.omega
  have hsm := (h.run.base.forest.bounds hM.1 hSP).1
  have hzm := (h.run.base.forest.bounds hM.1 hZP).1
  obtain ⟨ts,_,hTS⟩ := h.oldTop.graph.total s hsm
  obtain ⟨tz,_,hTZ⟩ := h.oldTop.graph.total z hzm
  have hKeyX := h.source_key_d hM hC hSP hZP hVS hVZ hLe hTS hTZ
  have hSame : ParentRowsEqual M P s z := fun q =>
    ⟨fun hq => (h.run.base.forest.unique s p q hSP hq) ▸ hZP,fun hq => (h.run.base.forest.unique z p q hZP hq) ▸ hSP⟩
  obtain ⟨hNS,hNZ,hKeyY⟩ := h.copied_key_d hM hC hT hRootS hs hRootZ hz hSame
    (h.block_bound_d hM hC hT hRootS (Or.inr hs) hMapS hcs) hMapS hMapZ hTS hTZ hKeyX
  have hpNat := hw.transitive m h.m_nat p (h.run.base.forest.bounds hM.1 hSP).2
  obtain ⟨p',hMapP⟩ := parent_copy_exists_d hM hC hT h.coords hMapS.2.1 hpNat
  have hCS := (h.nonroot_iff_d hM hC hT hP0 hRootS hs hMapS hcs).mpr ⟨p,hSP,hMapP⟩
  have hCZ := (h.nonroot_iff_d hM hC hT hP0 hRootZ hz hMapZ hcz).mpr ⟨p,hZP,hMapP⟩
  exact (h.key_value_iff_d hM hC hT hP0 hCS hCZ hNS hNZ hXS hXZ).mp hKeyY

/-- (O2) 低seam：源末列与非root列共同第0行父项时，seam副本底值不超过同块副本。 -/
theorem Base.seam_order_d (hM : M.Models KP1Y.theory) (hC : C.Valid M) (hT : T.Valid M C)
    (h : Base M C T m V P H level index n OldTop NewTop Bottom R X Y A) {P0 : M.Domain}
    (hP0 : MemPair M Y.parents C.zero P0) {z p b seam cz vl vz xs xz : M.Domain}
    (hLow : M.mem C.zero level) (hRootZ : M.mem A.root z) (hz : M.mem z A.last)
    (hLP : MemPair M P A.last p) (hZP : MemPair M P z p) (hVL : MemPair M V A.last vl) (hVZ : MemPair M V z vz)
    (hLe : vl=vz ∨ M.mem vl vz) (hEncode : CopyCoordinates.Encode M C T A A.last b seam)
    (hMapZ : CopyCoordinates.ParentCopy M C T A b z cz) (hSeam : M.mem seam n) (hcz : M.mem cz n)
    (hXS : MemPair M Bottom seam xs) (hXZ : MemPair M Bottom cz xz) : xs=xz ∨ M.mem xs xz := by
  have hw := omega_isOrdinal_d hM hC.omega
  have hzm := (h.run.base.forest.bounds hM.1 hZP).1
  obtain ⟨tl,_,hTL⟩ := h.oldTop.graph.total A.last h.last_m
  obtain ⟨tz,_,hTZ⟩ := h.oldTop.graph.total z hzm
  have hKeyX := h.source_key_d hM hC hLP hZP hVL hVZ hLe hTL hTZ
  have hSame : ParentRowsEqual M P A.last z := fun q =>
    ⟨fun hq => (h.run.base.forest.unique A.last p q hLP hq) ▸ hZP,fun hq => (h.run.base.forest.unique z p q hZP hq) ▸ hLP⟩
  have hbIndex := (CopyCoordinates.seam_lt_width_iff_d hM hC hT h.coords hEncode h.widthN).mp hSeam
  obtain ⟨next,hNext,hNextNat⟩ := hC.omega.1.2 b hEncode.2.1
  have hNextBound : next=index ∨ M.mem next index :=
    ordinal_subset_cases_d hM (hw.mem hNextNat) (hw.mem h.indexNat) (fun t ht => by
      rcases (hNext t).mp ht with htb | he
      · exact (hw.mem h.indexNat).transitive b hbIndex t htb
      · exact (hM.1.eq_of_same_members t b he).symm ▸ hbIndex)
  obtain ⟨topSeam,_,hNS,hNZ,hKeyY⟩ := h.seam_key_d hM hC hT hLow hRootZ hz hSame hNext hNextBound hEncode hMapZ hTL hTZ hKeyX
  have hpNat := hw.transitive m h.m_nat p (h.run.base.forest.bounds hM.1 hLP).2
  obtain ⟨p',hMapP⟩ := parent_copy_exists_d hM hC hT h.coords hEncode.2.1 hpNat
  have hLevel := h.level_nat hM hC
  have hCS : MemPair M P0 seam p' := (h.target_zero_iff hM hP0 seam p').mp
    ((CopiedMountain.Terminal.low_seam_parent_iff_d hM hC hT h.coords h.copies hEncode hSeam hLevel hLow).mpr
      ⟨p,hpNat,(h.source_zero_iff hM A.last p).mpr hLP,hMapP⟩)
  have hCZ := (h.nonroot_iff_d hM hC hT hP0 hRootZ hz hMapZ hcz).mpr ⟨p,hZP,hMapP⟩
  exact (h.key_value_iff_d hM hC hT hP0 hCS hCZ hNS hNZ hXS hXZ).mp hKeyY

end

end KP1Y.OneYFinite.TerminalBase
