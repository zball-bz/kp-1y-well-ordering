import KP1Y.OneYCanonHelperSelect
import KP1Y.OneYOrdinaryValueTransport

/-! H4：共同继承帧F父项下，源底值弱序沿同块复制保持到目标底值。
活动层0：目标山形是普通复制，底值由普通source0读取。低活动层：目标第0行恰是P的低行BM4复制，
祖先关系双向运输；若目标逆序，则由H1目标选择与源选择的祖先单调性得到源两列祖先集相等，
从而第0行父项相同，再由共同父项的数值运输得出矛盾。 -/
namespace KP1Y.OneYFinite.TerminalBase
open YesMetaZFC YesMetaZFC.SetTheory YesMetaZFC.SetTheory.Definitional
open KP1Y.Kuratowski KP1Y.Functions KP1Y.Naturals KP1Y.Bounded KP1Y.Arithmetic
open ReconstructionCanonical Reconstruction MountainReconstruction ReconstructionRecovery
universe u

theorem parent_rows_of_ancestors_eq_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {m Q c z : M.Domain} (hQ : Forest M C.omega m Q)
    (hEq : ∀ a, Ancestor M C m Q a c ↔ Ancestor M C m Q a z) : ∀ p, MemPair M Q c p ↔ MemPair M Q z p := by
  have hw := omega_isOrdinal_d hM hC.omega
  have dir (c z : M.Domain) (hEq : ∀ a, Ancestor M C m Q a c ↔ Ancestor M C m Q a z) (p : M.Domain)
      (hcp : MemPair M Q c p) : MemPair M Q z p := by
    have hpz := (hEq p).mp (ancestor_direct_d hM hC hQ hcp)
    obtain ⟨q,hzq,_⟩ := ancestor_parent_cases_d hM hC hQ hpz
    have h1 := ancestor_le_parent_d hM hC hQ hzq hpz
    have h2 := ancestor_le_parent_d hM hC hQ hcp ((hEq q).mpr (ancestor_direct_d hM hC hQ hzq))
    have hqNat := hw.transitive m hQ.width q (hQ.bounds hM.1 hzq).2
    have he := le_antisymm_d hM hC hqNat h1 h2
    exact he ▸ hzq
  exact fun p => ⟨dir c z hEq p,dir z c (fun a => (hEq a).symm) p⟩

section
variable {M : SetTheory.Structure.{u}} {C : ExpressionData M.Domain} {T : MatrixArithmetic M.Domain}
  {m V P H level index n OldTop NewTop Bottom : M.Domain} {R : RowStateSpace M.Domain}
  {X Y : CopiedMountain.Data M.Domain} {A : CopyCoordinates.Context M.Domain}

/-- 活动层0：目标底值是源底值的普通source0复制。 -/
theorem Base.ordinary_value_d (hM : M.Models KP1Y.theory) (hC : C.Valid M) (hT : T.Valid M C)
    (h : Base M C T m V P H level index n OldTop NewTop Bottom R X Y A) (hZero : level=C.zero) {s b c : M.Domain}
    (hs : M.mem s A.last) (hMap : CopyCoordinates.ParentCopy M C T A b s c) (hc : M.mem c n) (v : M.Domain) :
    MemPair M Bottom c v ↔ MemPair M V s v := by
  obtain ⟨B,Parents,G,hB,hParents,hG,hBottom⟩ := h.rebuild
  have hw := omega_isOrdinal_d hM hC.omega
  have hHigh (r : M.Domain) (hr : M.mem r C.omega) : level=r ∨ M.mem level r := by
    rw [hZero]
    classical
    by_cases he : r=C.zero
    · exact Or.inl he.symm
    · exact Or.inr ((hC.zero_mem_iff hM hr).mpr he)
  have hCopyO : CopiedMountain.Ordinary.Copies M C T A X n Y := by
    refine ⟨h.copies.width,h.copies.forests,h.copies.heights,?_⟩
    intro r t p
    rw [h.copies.parents r t p]
    constructor
    · rintro ⟨ht,hP⟩
      have hr := hP.row_natural hM.1 h.source
      exact ⟨ht,(CopiedMountain.Terminal.parent_high_eq_ordinary_d hM hC hT h.coords h.source
        (hw.transitive n h.n_nat t ht) (hHigh r hr)).mp hP⟩
    · rintro ⟨ht,hP⟩
      have hr : M.mem r C.omega := by
        obtain ⟨_,_,_,_,_,_,_,hPX,_⟩ := hP
        exact (hPX.bounds hM.1 h.source).1
      exact ⟨ht,(CopiedMountain.Terminal.parent_high_eq_ordinary_d hM hC hT h.coords h.source
        (hw.transitive n h.n_nat t ht) (hHigh r hr)).mpr hP⟩
  have hTopCopy : CopiedMountain.Ordinary.ValueCopies M C T A OldTop n C.omega NewTop := by
    refine ⟨h.width_eq ▸ h.newTop.graph,?_⟩
    intro t src blk hDec u
    rw [h.newTop.rows t u]
    constructor
    · rintro ⟨ht,src',_,blk',_,hDec',hOld⟩
      exact ⟨h.width_eq ▸ ht,(hDec'.unique_d hM hC hT h.coords hDec).1 ▸ hOld⟩
    · rintro ⟨ht,hOld⟩
      exact ⟨h.width_eq.symm ▸ ht,src,hDec.2.1,blk,hDec.2.2.1,hDec,hOld⟩
  have hW : RowValues M (grid C Y NewTop T.addPairs T.plus B Parents) G C.zero Bottom := by
    refine ⟨hBottom.graph,fun t x => ⟨fun hX => ⟨hC.zero_nat,(hBottom.graph.bounds hM.1 hX).1,Or.inl ((hBottom.rows t x).mp hX)⟩,
      fun hCell => (hBottom.rows t x).mpr (hCell.inside hB.1.2.1)⟩⟩
  have hVC := hCopyO.row_values_copy_d hM hC hT h.coords hT.add h.run h.rooted.positive h.source h.target h.fromRun
    h.oldTop hTopCopy hB hParents hG hC.zero_nat (h.run.initial_row_at_d hM) hW
  exact (hVC.parent_copy_iff_d hM hC hT h.coords hs hMap).trans ⟨And.right,fun hv => ⟨hc,hv⟩⟩

/-- 低活动层：目标第0行父图恰是源第0行P的低行BM4复制。 -/
theorem Base.zero_copy_forest_d (hM : M.Models KP1Y.theory) (hC : C.Valid M) (hT : T.Valid M C)
    (h : Base M C T m V P H level index n OldTop NewTop Bottom R X Y A) (hLow : M.mem C.zero level) {P0 : M.Domain}
    (hP0 : MemPair M Y.parents C.zero P0) :
    ∃ count, M.SuccessorOf count index ∧ MatrixCopy.CopyForest M C T A P C.zero C.one count n P0 := by
  have hw := omega_isOrdinal_d hM hC.omega
  obtain ⟨Q,hQ⟩ := FrameCopy.copies_exists_d hM hC hT h.coords h.run.base.forest h.widthN
  have hQForest := hQ.forest
  obtain ⟨count,hCount,hCF⟩ := hQ
  have hCut : M.mem C.zero C.one ↔ M.mem C.zero level := ⟨fun _ => hLow,fun _ => hC.one_succ.predecessor_mem⟩
  have hRows (t q : M.Domain) : MemPair M P0 t q ↔ MemPair M Q t q := by
    have hForest0 : Forest M C.omega n P0 := h.width_eq ▸ h.target.forest C.zero P0 hP0
    classical
    by_cases ht : M.mem t n
    · rw [← h.target_zero_iff hM hP0 t q,h.copies.parents C.zero t q,
        ActiveFrameTransport.copied_forest_terminal_parent_iff_d hM hC hT h.coords h.source h.run.base.forest hCF
          hC.zero_nat (h.level_nat hM hC) hCut (fun a b => (h.source_zero_iff hM a b).symm) ht q]
      exact ⟨And.right,fun hq => ⟨ht,hq⟩⟩
    · exact iff_of_false (fun hq => ht (hForest0.bounds hM.1 hq).1) (fun hq => ht (hQForest.bounds hM.1 hq).1)
  have he : P0=Q := (h.width_eq ▸ h.target.forest C.zero P0 hP0 : Forest M C.omega n P0).ext hM.1 hQForest hRows
  subst he
  exact ⟨count,hCount,hCF⟩

/-- 列的外部帧复制父项（非root副本或seam）。 -/
theorem Base.frame_copy_parent_d (hM : M.Models KP1Y.theory) (hC : C.Valid M) (hT : T.Valid M C)
    (h : Base M C T m V P H level index n OldTop NewTop Bottom R X Y A) {F F' : M.Domain}
    (hF : Forest M C.omega m F) (hF' : FrameCopy.Copies M C T A F index n F') {s b c : M.Domain}
    (hRoot : M.mem A.root s) (hs : s=A.last ∨ M.mem s A.last) (hMap : CopyCoordinates.ParentCopy M C T A b s c)
    (hc : M.mem c n) (t : M.Domain) :
    MemPair M F' c t ↔ ∃ p, M.mem p A.last ∧ MemPair M F s p ∧ CopyCoordinates.ParentCopy M C T A b p t := by
  have hw := omega_isOrdinal_d hM hC.omega
  have hNotGood : ¬M.mem s A.root := fun hg => SetTheory.KP.mem_irrefl_d (KP1Y.models_weakKP hM) A.root
    ((hw.mem h.coords.root).transitive s hg A.root hRoot)
  exact hF'.encoded_parent_iff_d hM hC hT h.coords hF ⟨hRoot,hs⟩ ((CopyCoordinates.parent_copy_bad_iff hNotGood).mp hMap) hc t

/-- 低活动层：目标第0行P0中某列无父，当且仅当其源列无父。 -/
theorem Base.copy_no_parent_d (hM : M.Models KP1Y.theory) (hC : C.Valid M) (hT : T.Valid M C)
    (h : Base M C T m V P H level index n OldTop NewTop Bottom R X Y A) (hLow : M.mem C.zero level) {P0 : M.Domain}
    (hP0 : MemPair M Y.parents C.zero P0) {s b c : M.Domain} (hRoot : M.mem A.root s) (hs : s=A.last ∨ M.mem s A.last)
    (hMap : CopyCoordinates.ParentCopy M C T A b s c) (hc : M.mem c n) (hNone : ∀ p, ¬MemPair M P s p) :
    ∀ q, ¬CopiedMountain.ParentAt M Y C.zero c q := by
  have hw := omega_isOrdinal_d hM hC.omega
  intro q hq
  rcases hs with hsl | hsx
  · subst hsl
    have hNotGood : ¬M.mem A.last A.root := fun hg => SetTheory.KP.mem_irrefl_d (KP1Y.models_weakKP hM) A.root
      ((hw.mem h.coords.root).transitive A.last hg A.root hRoot)
    obtain ⟨p0,_,hP0X,_⟩ := (CopiedMountain.Terminal.low_seam_parent_iff_d hM hC hT h.coords h.copies
      ((CopyCoordinates.parent_copy_bad_iff hNotGood).mp hMap) hc (h.level_nat hM hC) hLow).mp hq
    exact hNone p0 ((h.source_zero_iff hM A.last p0).mp hP0X)
  · obtain ⟨p,hp,_⟩ := (h.nonroot_iff_d hM hC hT hP0 hRoot hsx hMap hc).mp ((h.target_zero_iff hM hP0 c q).mp hq)
    exact hNone p hp

/-- seam副本的BM4坐标：下一副本号、root的复制像、CopyPosition及副本号界。 -/
theorem Base.seam_coords_d (hM : M.Models KP1Y.theory) (hC : C.Valid M) (hT : T.Valid M C)
    (h : Base M C T m V P H level index n OldTop NewTop Bottom R X Y A) {b cc count : M.Domain}
    (hMapC : CopyCoordinates.ParentCopy M C T A b A.last cc) (hcn : M.mem cc n) (hCount : M.SuccessorOf count index) :
    ∃ next, CopyCoordinates.Encode M C T A A.last b cc ∧ M.SuccessorOf next b ∧ M.mem next count ∧
      CopyCoordinates.ParentCopy M C T A next A.root cc ∧
      CopyPosition M C.omega T.addPairs T.plus T.mulPairs T.times A.root A.length next C.zero cc := by
  have hw := omega_isOrdinal_d hM hC.omega
  have hNotGood : ¬M.mem A.last A.root := fun hg => SetTheory.KP.mem_irrefl_d (KP1Y.models_weakKP hM) A.root
    ((hw.mem h.coords.root).transitive A.last hg A.root h.coords.below)
  have hEnc := (CopyCoordinates.parent_copy_bad_iff hNotGood).mp hMapC
  obtain ⟨next,_,hSucc,hPos⟩ := CopyCoordinates.encode_seam_bms_d hM hC hT h.coords hEnc
  have hbIndex := (CopyCoordinates.seam_lt_width_iff_d hM hC hT h.coords hEnc h.widthN).mp hcn
  exact ⟨next,hEnc,hSucc,count_mem_of_le hCount (successor_le_of_mem_d hM hC h.indexNat hSucc hbIndex),
    seam_root_copy_d hM hC hT h.coords hSucc hEnc,hPos⟩

/-- 共同帧父项下的目标底值弱序（逐字的UpperOrder单点形式）。 -/
theorem Base.upper_order_d (hM : M.Models KP1Y.theory) (hC : C.Valid M) (hT : T.Valid M C)
    (h : Base M C T m V P H level index n OldTop NewTop Bottom R X Y A) {F : M.Domain}
    (hF : Selects true M C m F V P) {z c vc vz b cc zz tc tz : M.Domain}
    (hRootZ : M.mem A.root z) (hzc : M.mem z c) (hcLast : c=A.last ∨ M.mem c A.last) (hFrame : ParentRowsEqual M F c z)
    (hVC : MemPair M V c vc) (hVZ : MemPair M V z vz) (hLe : vc=vz ∨ M.mem vc vz)
    (hMapC : CopyCoordinates.ParentCopy M C T A b c cc) (hMapZ : CopyCoordinates.ParentCopy M C T A b z zz)
    (hTC : MemPair M Bottom cc tc) (hTZ : MemPair M Bottom zz tz) : tc=tz ∨ M.mem tc tz := by
  have hw := omega_isOrdinal_d hM hC.omega
  have hcn : M.mem cc n := h.width_eq ▸ (h.bottom_graph.bounds hM.1 hTC).1
  have hzn : M.mem zz n := h.width_eq ▸ (h.bottom_graph.bounds hM.1 hTZ).1
  have htcNat := (h.bottom_graph.bounds hM.1 hTC).2
  have htzNat := (h.bottom_graph.bounds hM.1 hTZ).2
  have hzLast : M.mem z A.last := hcLast.elim (fun he => he ▸ hzc) (fun hcl => (hw.mem h.coords.last).transitive c hcl z hzc)
  have hcNat : M.mem c C.omega := hcLast.elim (fun he => he ▸ h.coords.last) (fun hcl => hw.transitive A.last h.coords.last c hcl)
  have hRootC : M.mem A.root c := (hw.mem hcNat).transitive z hzc A.root hRootZ
  rcases h.zero_le_level hM hC with hZ | hLow
  · have hZero := hZ.symm
    have htz : tz=vz := h.run.base.values.unique z tz vz ((h.ordinary_value_d hM hC hT hZero hzLast hMapZ hzn tz).mp hTZ) hVZ
    rw [htz]
    rcases hcLast with hcl | hcl
    · subst hcl
      obtain ⟨count,hCount,_⟩ := hC.omega.1.2 index h.indexNat
      obtain ⟨_,_,_,_,hRootMap,_⟩ := h.seam_coords_d hM hC hT hMapC hcn hCount
      have hTCv := (h.root_copy_high_value_d hM hC hT hZero hRootMap hcn tc).mp hTC
      have hLX : CopiedMountain.ParentAt M X C.zero A.last A.root := hZero ▸ (h.active_d hM hC).parent
      have hLP := (h.source_zero_iff hM A.last A.root).mp hLX
      have hlt := (h.run.base.parentValues A.last A.root tc vc hLP hTCv hVC).2
      rcases hLe with he | hlt'
      · exact Or.inr (he ▸ hlt)
      · exact Or.inr ((hw.mem (h.run.base.values.bounds hM.1 hVZ).2).transitive vc hlt' tc hlt)
    · have htc : tc=vc := h.run.base.values.unique c tc vc ((h.ordinary_value_d hM hC hT hZero hcl hMapC hcn tc).mp hTC) hVC
      rw [htc]
      exact hLe
  · rcases hw.wellOrder.linear.compare tc htcNat tz htzNat with he | hlt | hgt
    · exact Or.inl (hM.1.eq_of_same_members tc tz he)
    · exact Or.inr hlt
    · exfalso
      obtain ⟨P0,_,hP0⟩ := h.target.parents.total C.zero hC.zero_nat
      obtain ⟨F',hF'⟩ := FrameCopy.copies_exists_d hM hC hT h.coords hF.inherited h.widthN
      have hSel := h.select_d hM hC hT hF hF' hP0
      obtain ⟨_,hPos⟩ := h.bottom_numeric_d hM hC hT hP0
      have hSelF := selects_false_of_true hSel hPos
      have hF'Rows : ∀ t, MemPair M F' zz t ↔ MemPair M F' cc t := by
        intro t
        rw [h.frame_copy_parent_d hM hC hT hF.inherited hF' hRootZ (Or.inr hzLast) hMapZ hzn t,
          h.frame_copy_parent_d hM hC hT hF.inherited hF' hRootC hcLast hMapC hcn t]
        constructor
        · rintro ⟨p,hp,hzp,hmp⟩
          exact ⟨p,hp,(hFrame p).mpr hzp,hmp⟩
        · rintro ⟨p,hp,hcp,hmp⟩
          exact ⟨p,hp,(hFrame p).mp hcp,hmp⟩
      have hMonoT : ∀ a, Ancestor M C n P0 a zz → Ancestor M C n P0 a cc :=
        fun a hA => hSelF.ancestor_mono_of_common_parent_d hM hC hF'Rows hTZ hTC (Or.inr hgt) hA
      obtain ⟨count,hCount,hCF⟩ := h.zero_copy_forest_d hM hC hT hLow hP0
      have hRootLast : M.mem C.zero C.one → Ancestor M C m P A.root A.last := fun _ => h.root_last_d hM hC
      have hbCount := count_mem_of_le hCount (h.block_bound_d hM hC hT hRootZ (Or.inr hzLast) hMapZ hzn)
      have hDown : ∀ a a', Ancestor M C m P a z → CopyCoordinates.ParentCopy M C T A b a a' → Ancestor M C n P0 a' zz := by
        intro a a' hAz hMapA
        have haLast : M.mem a A.last := (hw.mem h.coords.last).transitive z hzLast a hAz.1
        classical
        by_cases haGood : M.mem a A.root
        · have he := (CopyCoordinates.parent_copy_good_iff hMapA.2.1 hMapA.1 haGood).mp hMapA
          subst he
          exact (MatrixCopy.CopyForest.ancestor_good_iff_d hM hC hT h.coords h.run.base.forest hCF h.last_m hbCount haGood
            hRootLast hzLast hMapZ).mpr hAz
        · exact (MatrixCopy.CopyForest.ancestor_copy_iff_d hM hC hT h.coords h.run.base.forest hCF h.last_m hbCount hRootLast
            haLast hzLast hMapA hMapZ).mpr hAz
      have hUp : ∀ a a', M.mem a A.last → CopyCoordinates.ParentCopy M C T A b a a' → Ancestor M C n P0 a' cc →
          Ancestor M C m P a c := by
        intro a a' haLast hMapA hAcc
        have haNat := hw.transitive A.last h.coords.last a haLast
        classical
        rcases hcLast with hcl | hcl
        · subst hcl
          obtain ⟨next,_,hSucc,hNextCount,hRootMap,hPos⟩ := h.seam_coords_d hM hC hT hMapC hcn hCount
          by_cases haGood : M.mem a A.root
          · have he := (CopyCoordinates.parent_copy_good_iff hMapA.2.1 hMapA.1 haGood).mp hMapA
            subst he
            have hAR := (MatrixCopy.CopyForest.ancestor_good_iff_d hM hC hT h.coords h.run.base.forest hCF h.last_m hNextCount
              haGood hRootLast h.coords.below hRootMap).mp hAcc
            exact ancestor_trans_d hM hC h.run.base.forest hAR (h.root_last_d hM hC)
          · exact (MatrixCopy.CopyForest.ancestor_previous_root_iff_d hM hC hT h.coords h.run.base.forest hCF h.last_m hNextCount
              hMapA.2.1 hSucc hC.one_succ.predecessor_mem (root_le_of_not_good_d hM hC h.coords haNat haGood) haLast hMapA hPos).mp hAcc
        · by_cases haGood : M.mem a A.root
          · have he := (CopyCoordinates.parent_copy_good_iff hMapA.2.1 hMapA.1 haGood).mp hMapA
            subst he
            exact (MatrixCopy.CopyForest.ancestor_good_iff_d hM hC hT h.coords h.run.base.forest hCF h.last_m hbCount haGood
              hRootLast hcl hMapC).mp hAcc
          · exact (MatrixCopy.CopyForest.ancestor_copy_iff_d hM hC hT h.coords h.run.base.forest hCF h.last_m hbCount hRootLast
              haLast hcl hMapA hMapC).mp hAcc
      have hPull : ∀ a, Ancestor M C m P a z → Ancestor M C m P a c := by
        intro a hAz
        have haLast : M.mem a A.last := (hw.mem h.coords.last).transitive z hzLast a hAz.1
        obtain ⟨a',hMapA⟩ := parent_copy_exists_d hM hC hT h.coords hMapZ.2.1 (hw.transitive A.last h.coords.last a haLast)
        exact hUp a a' haLast hMapA (hMonoT a' (hDown a a' hAz hMapA))
      have hMonoS : ∀ a, Ancestor M C m P a c → Ancestor M C m P a z :=
        fun a hA => (selects_false_of_true hF h.rooted.positive).ancestor_mono_of_common_parent_d hM hC hFrame hVC hVZ hLe hA
      have hPar := parent_rows_of_ancestors_eq_d hM hC h.run.base.forest (fun a => ⟨hMonoS a,hPull a⟩)
      classical
      by_cases hSome : ∃ p, MemPair M P c p
      · obtain ⟨p,hCP⟩ := hSome
        have hZP := (hPar p).mp hCP
        have hRes : tc=tz ∨ M.mem tc tz := by
          rcases hcLast with hcl | hcl
          · subst hcl
            obtain ⟨_,hEnc,_,_,_,_⟩ := h.seam_coords_d hM hC hT hMapC hcn hCount
            exact h.seam_order_d hM hC hT hP0 hLow hRootZ hzLast hCP hZP hVC hVZ hLe hEnc hMapZ hcn hzn hTC hTZ
          · exact h.copy_order_d hM hC hT hP0 hRootC hcl hRootZ hzLast hCP hZP hVC hVZ hLe hMapC hMapZ hcn hzn hTC hTZ
        exact not_reverse_d hM hC htzNat hRes hgt
      · have hNoC : ∀ p, ¬MemPair M P c p := fun p hp => hSome ⟨p,hp⟩
        have hNoZ : ∀ p, ¬MemPair M P z p := fun p hp => hNoC p ((hPar p).mpr hp)
        have h1 := h.no_parent_one_d hM hC hT (h.copy_no_parent_d hM hC hT hLow hP0 hRootC hcLast hMapC hcn hNoC) hTC
        have h2 := h.no_parent_one_d hM hC hT (h.copy_no_parent_d hM hC hT hLow hP0 hRootZ (Or.inr hzLast) hMapZ hzn hNoZ) hTZ
        rw [h1,h2] at hgt
        exact SetTheory.KP.mem_irrefl_d (KP1Y.models_weakKP hM) C.one hgt

end

/-- H4：原 badAtTerminalBase_upperOrder / badAtTerminalBase_order_of_common_frame。 -/
theorem terminal_base_upper_order_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {m V P H level index n OldTop NewTop Bottom : M.Domain} {R : RowStateSpace M.Domain}
    (hRun : RowRun M C m R V P H) (hBase : RootedRow M C m V P)
    {X Y : CopiedMountain.Data M.Domain} (hX : X.Valid M C) (hFrom : CopiedMountain.FromRun M C m R V H X)
    (hOldTop : TopValueGraph M C m R H X.heights OldTop)
    {A : CopyCoordinates.Context M.Domain} (hA : A.Valid M C) (hWidth : M.SuccessorOf m A.last)
    (hBad : RowBadAt M C R H level A.last A.root) (hIndex : M.mem index C.omega)
    (hN : CopyCoordinates.Width M C T A index n) (hY : Y.Valid M C)
    (hCopy : CopiedMountain.Terminal.Copies M C T A X level n Y)
    (hTop : CopiedTop M C T A OldTop Y.width NewTop)
    (hRebuild : Rebuilds M C T.addPairs T.plus Y NewTop Bottom)
    {D : CopiedMountain.Lower.Context M.Domain} (hD : D.coordinates=A)
    {F : M.Domain} (hF : Selects true M C m F V P) : CopiedMountain.Lower.UpperOrder M C T D F V Bottom := by
  have h := Base.mk hRun hBase hX hFrom hOldTop hA hWidth hBad hIndex hN hY hCopy hTop hRebuild
  subst hD
  intro z c hRootZ hzc hcLast hFrame vc vz hVC hVZ hLe b cc zz tc tz hMapC hMapZ hTC hTZ
  exact h.upper_order_d hM hC hT hF hRootZ hzc hcLast hFrame hVC hVZ hLe hMapC hMapZ hTC hTZ

end KP1Y.OneYFinite.TerminalBase
