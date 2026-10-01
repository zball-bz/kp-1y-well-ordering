import KP1Y.OneYLowerBlockBad

/-! Lower复制目标Y的全部装饰阻挡：原列、好部父、未移动坏部父、floor参考行、抬升行五支汇合。
唯一未在本文件内证明的是坏部父KeyLE运输 `KeyTransport`（原 `keyLE_succ_rowCopy`，由 LANE-B 的
canon_key_* 与 `UpperOrder` 解除）。 -/
namespace KP1Y.OneYFinite.LowerBlock
open YesMetaZFC YesMetaZFC.SetTheory YesMetaZFC.SetTheory.Definitional
open KP1Y.Kuratowski KP1Y.Functions KP1Y.Naturals KP1Y.Bounded KP1Y.Arithmetic
open KP1Y.OneYFinite KP1Y.OneYFinite.CopyCoordinates KP1Y.OneYFinite.CopiedMountain
open KP1Y.OneYFinite.CopiedMountain.Lower KP1Y.OneYFinite.LowerCanon
universe u

private theorem row_pair_d {M : SetTheory.Structure.{u}} {C : ExpressionData M.Domain} {X : Data M.Domain}
    (hX : X.Valid M C) {i Fi a p : M.Domain} (hFi : MemPair M X.parents i Fi) (h : ParentAt M X i a p) :
    MemPair M Fi a p := by
  obtain ⟨F',_,hF',hP⟩ := h
  exact hX.parents.unique i F' Fi hF' hFi ▸ hP

/-- 目标行s移动（锥内且floor≤s）时的共同部分：源上行us，下行v（抬升行v=ur或floor参考v=r）。 -/
private theorem moved_case_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {D : Lower.Context M.Domain} (hD : D.Valid M C) {Y : Data M.Domain} (hY : Y.Valid M C) {n : M.Domain}
    (hCopy : Copies M C T D n Y) {m : M.Domain} {R : RowStateSpace M.Domain} {V P H : M.Domain}
    (hRun : RowRun M C m R V P H) (hPositive : ∀ c a, MemPair M V c a → M.mem C.zero a)
    (hFrom : FromRun M C m R V H D.mountain) {oldTop newTop : M.Domain}
    (hTopOld : TopValueGraph M C m R H D.mountain.heights oldTop) (hNewTop : Graph M newTop n C.omega)
    (hKeyT : KeyTransport M C T D Y oldTop newTop)
    {s t Q c q p s0 b off us p0 v q0 : M.Domain} (hs : M.mem s C.omega) (hNext : M.SuccessorOf t s)
    (hQ : MemPair M Y.parents s Q) (hNe : p≠q) (hSource : Source M D.coordinates s0)
    (hEnc : Encode M C T D.coordinates s0 b c) (hc : M.mem c n)
    (hCone : InCone M C D s0) (hHigh : D.floor=s ∨ M.mem D.floor s)
    (hOff : M.mem off C.omega) (hMul : MulAt M T.mulPairs T.times b D.rise off) (hus : M.mem us C.omega)
    (hShift : ShiftedRow M C T D.floor off s us) (hp0 : M.mem p0 C.omega) (hPS0 : ParentAt M D.mountain us s0 p0)
    (hEncP : Encode M C T D.coordinates p0 b p)
    (hSuccU : M.SuccessorOf us v) (hPR0 : ParentAt M D.mountain v s0 q0) (hMapQ : ParentCopy M C T D.coordinates b q0 q)
    (hLifted : LiftedRow M C T D s0 b v us s) : BlockerAt M C Y newTop Q c q p t := by
  have hw := omega_isOrdinal_d hM hC.omega
  have hcY : M.mem c Y.width := hCopy.width.symm ▸ hc
  have hNotGood : ¬M.mem s0 D.coordinates.root := fun h =>
    nat_irrefl hM _ ((hw.mem hD.coordinates.root).transitive s0 h _ hSource.1)
  have hMap : ParentCopy M C T D.coordinates b s0 c := (parent_copy_bad_iff hNotGood).mpr hEnc
  have hv : M.mem v C.omega := (hPR0.bounds hM.1 hD.mountain).1
  obtain ⟨F0,_,hF0⟩ := hD.mountain.parents.total v hv
  obtain ⟨Q0,_,hQ0⟩ := hD.mountain.parents.total us hus
  have hOld0 := row_pair_d hD.mountain hF0 hPR0
  have hNew0 := row_pair_d hD.mountain hQ0 hPS0
  have hFloorUs := hShift.floor_le_d hM hC hT
  have hConeP0 := hCone.high_parent_d hM hC hD hFloorUs hPS0
  have hBadP0 := hConeP0.not_good_d hM hC hD
  have hMapP : ParentCopy M C T D.coordinates b p0 p := (parent_copy_bad_iff hBadP0).mpr hEncP
  have hNe0 : p0≠q0 := fun he => hNe (by subst he; exact parent_copy_unique_d hM hC hT hD.coordinates hMapP hMapQ)
  have hq0s : M.mem q0 s0 := (hD.mountain.forest v F0 hF0).left s0 q0 hOld0
  have hq0Last : q0=D.coordinates.last ∨ M.mem q0 D.coordinates.last :=
    Or.inr (nat_lt_of_lt_of_le hM hC hD.coordinates.last hq0s hSource.2)
  have hqc : M.mem q c := parent_copy_below_encode_d hM hC hT hD.coordinates hSource.1 hq0s hMapQ hEnc
  have hqn : M.mem q n := (hw.mem (hCopy.width ▸ hY.width)).transitive c hc q hqc
  have hConeOf (a : M.Domain) (hAP : MemPair M Q0 a p0) : InCone M C D a :=
    (in_cone_ancestor_iff_d hM hC hD hRun hFrom hFloorUs hQ0
      (ancestor_direct_d hM hC (hD.mountain.forest us Q0 hQ0) hAP)).mp hConeP0
  obtain ⟨t0,hNextU,_⟩ := hC.omega.1.2 us hus
  apply bad_blocker_core_d hM hC hT hD hY hCopy hRun hPositive hFrom hTopOld hNewTop hSuccU hNextU hF0 hQ0
    hOld0 hNew0 hNe0 hBadP0 hMap hc hMapQ
  · intro a x hAP hRootA hAnc hMapA _
    have hConeQ0 := (in_cone_ancestor_iff_d hM hC hD hRun hFrom hFloorUs hQ0 hAnc).mp (hConeOf a hAP)
    have hEncQ : Encode M C T D.coordinates q0 b q := (parent_copy_bad_iff (hConeQ0.not_good_d hM hC hD)).mp hMapQ
    have hq0ω := hw.transitive s0 hEnc.1 q0 hq0s
    exact hCopy.high_ancestor_copy_d hM hC hT hD hRun hFrom hY ⟨nat_lt_trans hM hC hq0ω hRootA hAnc.1,hq0Last⟩
      hConeQ0 hHigh hMul hShift hEncQ hqn hQ0 hQ hAnc hMapA
  · intro a x hAP hRootA has hMapA hxY
    have haLast := nat_lt_of_lt_of_le hM hC hD.coordinates.last has hSource.2
    have hEncA : Encode M C T D.coordinates a b x := (parent_copy_bad_iff ((hConeOf a hAP).not_good_d hM hC hD)).mp hMapA
    have hPY := (hCopy.encoded_parent_iff_d hM hC hT hD hs ⟨hRootA,Or.inr haLast⟩ hEncA (hCopy.width ▸ hxY)).mpr
      (Or.inl ⟨⟨hConeOf a hAP,hHigh⟩,off,hOff,hMul,us,hus,hShift,p0,hp0,
        ⟨Q0,(hD.mountain.parents.bounds hM.1 hQ0).2,hQ0,hAP⟩,hEncP⟩)
    exact (canon_row_parent_iff hM.1 hY hQ).mp hPY
  · intro a x tc ta tc' ta' hAP _ has hMapA hxY hTC hTA hTC' hTA' hKey
    exact hKeyT v us s t0 t Q0 s0 a p0 b c x tc ta tc' ta' hSuccU hQ0 hNew0 hAP hBadP0 has hSource.2 hLifted
      hNextU hNext hMap hMapA hcY hxY hTC hTA hTC' hTA' hKey

/-- 目标Lower复制图的全部装饰阻挡（原 LowerCopyCanonical/Blocker/BadBlocker 的阻挡分支）。 -/
theorem decorated_blockers_of_key_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {D : Lower.Context M.Domain} (hD : D.Valid M C) {Y : Data M.Domain} (hY : Y.Valid M C) {n : M.Domain}
    (hCopy : Copies M C T D n Y) {m : M.Domain} {R : RowStateSpace M.Domain} {V P H : M.Domain}
    (hRun : RowRun M C m R V P H) (hPositive : ∀ c a, MemPair M V c a → M.mem C.zero a)
    (hFrom : FromRun M C m R V H D.mountain) {oldTop Qnext newTop : M.Domain}
    (hExtraction : Extraction M C m V P oldTop Qnext) (hNewTop : Graph M newTop n C.omega)
    (hPrefixTop : RowsAgreeOn M newTop oldTop D.coordinates.last) (hFixed : UpperFixed M C T D oldTop Qnext n newTop)
    (hKeyT : KeyTransport M C T D Y oldTop newTop) : ReconstructionRecovery.DecoratedBlockers M C Y newTop := by
  intro r s t F Q c q p hSucc hNext hF hQ hOld hNew hNe
  have hw := omega_isOrdinal_d hM hC.omega
  have hTopOld := Expansion.extraction_top_for_source_d hM hC hRun hFrom hExtraction
  have hr : M.mem r C.omega := (hY.parents.bounds hM.1 hF).1
  have hs : M.mem s C.omega := (hY.parents.bounds hM.1 hQ).1
  have hcY : M.mem c Y.width := ((hY.forest s Q hQ).bounds hM.1 hNew).1
  have hc : M.mem c n := hCopy.width ▸ hcY
  have hcω := hw.transitive Y.width hY.width c hcY
  have hOldY : ParentAt M Y r c q := (canon_row_parent_iff hM.1 hY hF).mpr hOld
  have hNewY : ParentAt M Y s c p := (canon_row_parent_iff hM.1 hY hQ).mpr hNew
  obtain ⟨F0,_,hF0⟩ := hD.mountain.parents.total r hr
  obtain ⟨Q0,_,hQ0⟩ := hD.mountain.parents.total s hs
  classical
  by_cases hcLast : M.mem c D.coordinates.last
  · have hOldX := (hCopy.original_parents_d hM hC hD hc (Or.inr hcLast)).mp hOldY
    have hNewX := (hCopy.original_parents_d hM hC hD hc (Or.inr hcLast)).mp hNewY
    exact original_blocker_d hM hC hT hD hY hCopy hRun hPositive hFrom hTopOld hPrefixTop hSucc hNext hF0 hQ0 hQ
      (row_pair_d hD.mountain hF0 hOldX) (row_pair_d hD.mountain hQ0 hNewX) hNe hcLast hcY
  have hLastLe := nat_le_of_not_lt hM hC hcω hD.coordinates.last hcLast
  have hRootC : M.mem D.coordinates.root c := nat_lt_of_lt_of_le hM hC hcω hD.coordinates.below hLastLe
  obtain ⟨s0,b,hRaw⟩ := raw_decode_exists_d hM hC hT hD.coordinates hcω
  obtain ⟨hSource,hEnc⟩ := (raw_decoded_active_iff hRootC).mp hRaw
  have hb := hEnc.2.1
  have hNotGood : ¬M.mem s0 D.coordinates.root := fun h =>
    nat_irrefl hM _ ((hw.mem hD.coordinates.root).transitive s0 h _ hSource.1)
  have hMap : ParentCopy M C T D.coordinates b s0 c := (parent_copy_bad_iff hNotGood).mpr hEnc
  have hParR := (hCopy.encoded_parent_iff_d hM hC hT hD hr hSource hEnc hc).mp hOldY
  have hParS := (hCopy.encoded_parent_iff_d hM hC hT hD hs hSource hEnc hc).mp hNewY
  have hrs : r=s ∨ M.mem r s := Or.inr hSucc.predecessor_mem
  rcases hParS with ⟨hMovS,off,hOff,hMul,us,hus,hShiftS,p0,hp0,hPS0,hEncP⟩ | ⟨hNoMovS,p0,hp0,hPS0,hMapP⟩
  · rcases hParR with ⟨hMovR,off',_,hMul',ur,hur,hShiftR,q0,_,hPR0,hEncQ⟩ | ⟨hNoMovR,q0,_,hPR0,hMapQ⟩
    · have hoo := hT.mul.mul_unique hM.1 hMul' hMul
      subst off'
      have hConeQ0 := hMovS.1.high_parent_d hM hC hD (hShiftR.floor_le_d hM hC hT) hPR0
      have hMapQ : ParentCopy M C T D.coordinates b q0 q := (parent_copy_bad_iff (hConeQ0.not_good_d hM hC hD)).mpr hEncQ
      rcases hShiftR.successor_cases_d hM hC hT hShiftS hSucc with hEq | hUS
      · subst us
        have hpq := hPS0.unique hD.mountain hPR0
        subst q0
        exact False.elim (hNe (encode_unique hM.1 hT hEncP hEncQ))
      · obtain ⟨level,_,hLevel,_⟩ := hShiftS.2.2
        have hNotGap : ¬M.mem s level := by
          intro hGap
          have hUF := hShiftS.gap_value hM.1 hT hLevel hGap
          have hFU : M.mem D.floor us := nat_lt_of_le_of_lt hM hC hus (hShiftR.floor_le_d hM hC hT) hUS.predecessor_mem
          exact nat_irrefl hM us (hUF ▸ hFU)
        have hAdd := hShiftS.high_sum_d hM hC hT hLevel hNotGap
        exact moved_case_d hM hC hT hD hY hCopy hRun hPositive hFrom hTopOld hNewTop hKeyT hs hNext hQ hNe hSource hEnc hc
          hMovS.1 hMovS.2 hOff hMul hus hShiftS hp0 hPS0 hEncP hUS hPR0 hMapQ
          (Or.inr ⟨⟨hMovS.1,hShiftR.floor_le_d hM hC hT⟩,off,hOff,hMul,hAdd⟩)
    · have hLowR : M.mem r D.floor := by
        rcases nat_le_or_lt hM hC (hD.floor_nat hM.1) hr with hle | hlt
        · exact False.elim (hNoMovR ⟨hMovS.1,hle⟩)
        · exact hlt
      have hsFloor : s=D.floor := by
        rcases nat_succ_le_of_lt hM hC hr (hD.floor_nat hM.1) hSucc hLowR with he | hlt
        · exact he
        · rcases hMovS.2 with he | hfs
          · exact he.symm
          · exact False.elim (nat_irrefl hM s ((hw.mem hs).transitive _ hfs s hlt))
      have hUsFloor : us=D.floor := (hsFloor ▸ hShiftS).floor_value_d hM hC hT
      have hUsS : us=s := hUsFloor.trans hsFloor.symm
      have hSuccU : M.SuccessorOf us r := hUsS ▸ hSucc
      exact moved_case_d hM hC hT hD hY hCopy hRun hPositive hFrom hTopOld hNewTop hKeyT hs hNext hQ hNe hSource hEnc hc
        hMovS.1 hMovS.2 hOff hMul hus hShiftS hp0 hPS0 hEncP hSuccU hPR0 hMapQ (Or.inl ⟨hNoMovR,hUsS.symm⟩)
  · rcases hParR with ⟨hMovR,_⟩ | ⟨_,q0,_,hPR0,hMapQ⟩
    · exact False.elim (hNoMovS ⟨hMovR.1,nat_le_trans hM hC hs hMovR.2 hrs⟩)
    have hOld0 := row_pair_d hD.mountain hF0 hPR0
    have hNew0 := row_pair_d hD.mountain hQ0 hPS0
    have hNe0 : p0≠q0 := fun he => hNe (by subst he; exact parent_copy_unique_d hM hC hT hD.coordinates hMapP hMapQ)
    by_cases hGood : M.mem p0 D.coordinates.root
    · have hpp : p=p0 := (parent_copy_good_iff hb hp0 hGood).mp hMapP
      subst hpp
      exact good_blocker_d hM hC hT hD hY hCopy hRun hPositive hFrom hExtraction hPrefixTop hFixed hSucc hNext hF0 hQ0 hQ
        hOld0 hNew0 hNe0 hGood hSource.1 hSource.2 hMap hc hMapQ
    have hq0s : M.mem q0 s0 := (hD.mountain.forest r F0 hF0).left s0 q0 hOld0
    have hq0Last : q0=D.coordinates.last ∨ M.mem q0 D.coordinates.last :=
      Or.inr (nat_lt_of_lt_of_le hM hC hD.coordinates.last hq0s hSource.2)
    have hqY : M.mem q Y.width :=
      (hw.mem hY.width).transitive c hcY q (parent_copy_below_encode_d hM hC hT hD.coordinates hSource.1 hq0s hMapQ hEnc)
    have hOutOf (a : M.Domain) (hAP : MemPair M Q0 a p0) : ¬(InCone M C D a ∧ (D.floor=s ∨ M.mem D.floor s)) := by
      rintro ⟨hConeA,hHigh⟩
      have hConeP := hConeA.high_parent_d hM hC hD hHigh ⟨Q0,(hD.mountain.parents.bounds hM.1 hQ0).2,hQ0,hAP⟩
      have hConeS := (in_cone_ancestor_iff_d hM hC hD hRun hFrom hHigh hQ0
        (ancestor_direct_d hM hC (hD.mountain.forest s Q0 hQ0) hNew0)).mp hConeP
      exact hNoMovS ⟨hConeS,hHigh⟩
    obtain ⟨t0,_,_⟩ := hC.omega.1.2 s hs
    apply bad_blocker_core_d hM hC hT hD hY hCopy hRun hPositive hFrom hTopOld hNewTop hSucc hNext hF0 hQ0
      hOld0 hNew0 hNe0 hGood hMap hc hMapQ
    · intro a x hAP _ hAnc hMapA _
      apply copy_ancestor_d hM hC hT hD hY hCopy hRun hFrom hs hQ0 hQ hAnc hq0Last hMapA hMapQ hqY
      by_cases hLow : M.mem s D.floor
      · exact Or.inl hLow
      · exact Or.inr (fun hConeA => hOutOf a hAP ⟨hConeA,nat_le_of_not_lt hM hC hs (hD.floor_nat hM.1) hLow⟩)
    · intro a x hAP hRootA has hMapA hxY
      have haLast := nat_lt_of_lt_of_le hM hC hD.coordinates.last has hSource.2
      have haNe : a≠D.coordinates.root := fun he => nat_irrefl hM a (he.symm ▸ hRootA)
      have hPar := (parent_copy_nonroot_unmoved_d hM hC hT hD hs haLast haNe (hOutOf a hAP) hMapA).mpr
        ⟨p0,hp0,⟨Q0,(hD.mountain.parents.bounds hM.1 hQ0).2,hQ0,hAP⟩,hMapP⟩
      exact (canon_row_parent_iff hM.1 hY hQ).mp ((hCopy.parents s x p).mpr ⟨hCopy.width ▸ hxY,hPar⟩)
    · intro a x tc ta tc' ta' hAP _ has hMapA hxY hTC hTA hTC' hTA' hKey
      exact hKeyT r s s t t Q0 s0 a p0 b c x tc ta tc' ta' hSucc hQ0 hNew0 hAP hGood has hSource.2
        (Or.inl ⟨fun h => hNoMovS ⟨h.1,nat_le_trans hM hC hs h.2 hrs⟩,rfl⟩) hNext hNext hMap hMapA hcY hxY hTC hTA hTC' hTA' hKey

end KP1Y.OneYFinite.LowerBlock
