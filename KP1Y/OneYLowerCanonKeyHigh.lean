import KP1Y.OneYLowerCanonKeyStart

/-! 图层Key的floor起点、抬升起点与锥外起点运输。 -/
namespace KP1Y.OneYFinite.CopiedMountain.Lower
open YesMetaZFC YesMetaZFC.SetTheory YesMetaZFC.SetTheory.Definitional
open KP1Y.Kuratowski KP1Y.Functions KP1Y.Naturals KP1Y.Bounded KP1Y.Arithmetic
open KP1Y.OneYFinite.CopyCoordinates KP1Y.OneYFinite.LowerCanon
universe u

private theorem copy_lt_width {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {D : Context M.Domain} (hD : D.Valid M C) {Y : Data M.Domain} (hY : Y.Valid M C) {b c z cc zz : M.Domain}
    (hzc : M.mem z c) (hMapC : ParentCopy M C T D.coordinates b c cc) (hMapZ : ParentCopy M C T D.coordinates b z zz)
    (hcc : M.mem cc Y.width) : M.mem zz Y.width := by
  obtain ⟨J,hJ,hRowsJ⟩ := parent_copy_graph_exists_d hM hC hT hD.coordinates hMapC.2.1
  exact ((omega_isOrdinal_d hM hC.omega).mem hY.width).transitive cc hcc zz
    (hJ.strict z hMapZ.1 c hMapC.1 hzc zz cc ((hRowsJ z zz).mpr hMapZ) ((hRowsJ c cc).mpr hMapC))

private theorem common_init' {M : SetTheory.Structure.{u}} (he : Extensional M)
    {C : ExpressionData M.Domain} {X : Data M.Domain} (hX : X.Valid M C) {u c z p : M.Domain}
    (hPC : ParentAt M X u c p) (hPZ : ParentAt M X u z p) :
    ∀ F, MemPair M X.parents u F → ParentRowsEqual M F c z := by
  intro F hF q
  have hFor := hX.forest u F hF
  constructor
  · intro hq
    have := hFor.unique c q p hq ((canon_row_parent_iff he hX hF).mp hPC)
    subst this
    exact (canon_row_parent_iff he hX hF).mp hPZ
  · intro hq
    have := hFor.unique z q p hq ((canon_row_parent_iff he hX hF).mp hPZ)
    subst this
    exact (canon_row_parent_iff he hX hF).mp hPC

/-- 行号不变的运输（全部行在floor以上且两列锥外）。 -/
private theorem key_identity_out {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {D : Context M.Domain} (hD : D.Valid M C) {Y : Data M.Domain} (hY : Y.Valid M C) {n : M.Domain}
    (hCopy : Copies M C T D n Y) {m : M.Domain} {R : RowStateSpace M.Domain} {V P H : M.Domain}
    (hRun : RowRun M C m R V P H) (hFrom : FromRun M C m R V H D.mountain)
    {t c z b cc zz tc tz tcc tzz : M.Domain} (hFloorT : M.mem D.floor t)
    (hcLast : M.mem c D.coordinates.last) (hzLast : M.mem z D.coordinates.last)
    (hOutC : ¬InCone M C D c) (hOutZ : ¬InCone M C D z)
    (hMapC : ParentCopy M C T D.coordinates b c cc) (hMapZ : ParentCopy M C T D.coordinates b z zz)
    (hcc : M.mem cc Y.width) (hzz : M.mem zz Y.width)
    (hTop : ForestOrder.DepthEqFrom M C D.mountain c z t → (tc=tz ∨ M.mem tc tz) → (tcc=tzz ∨ M.mem tcc tzz))
    (hKey : ForestOrder.KeyLE M C D.mountain c z t tc tz) : ForestOrder.KeyLE M C Y cc zz t tcc tzz := by
  have hRow (σ : M.Domain) (hσ : M.mem σ C.omega) (hTσ : t=σ ∨ M.mem t σ) :=
    hCopy.canon_row_out_d hM hC hT hD hY hRun hFrom hσ (Or.inr (nat_lt_of_lt_of_le hM hC hσ hFloorT hTσ))
      hcLast hzLast hOutC hOutZ hMapC hMapZ hcc hzz
  apply canon_key_of_parts (canon_key_transfer_d hM hC (fun ρ σ => σ=ρ) (fun ρ hρ hT => ⟨ρ,hρ,hT,rfl⟩) ?_ ?_) hTop hKey
  · intro ρ σ _ _ hσ hTσ hR _ hEqσ
    subst hR
    exact (hRow σ hσ hTσ).1 hEqσ
  · intro σ hσ hTσ _ hLtσ
    refine ⟨σ,hσ,hTσ,(hRow σ hσ hTσ).2 hLtσ,?_⟩
    intro ρ' hρ' _ σ' hR'
    exact hR' ▸ hρ'

/-- floor起点：共同父位于floor行，Key从floor+1起。 -/
theorem Copies.canon_key_floor_start_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {D : Context M.Domain} (hD : D.Valid M C) {Y : Data M.Domain} (hY : Y.Valid M C) {n : M.Domain}
    (hCopy : Copies M C T D n Y) {m : M.Domain} {R : RowStateSpace M.Domain} {V P H : M.Domain}
    (hRun : RowRun M C m R V P H) (hFrom : FromRun M C m R V H D.mountain)
    {Pseudo oldTop newTop t c z b cc zz tc tz tcc tzz : M.Domain}
    (hUpper : UpperOrder M C T D Pseudo oldTop newTop) (hPseudo : GraphPseudoForest M C D.mountain Pseudo)
    (ht : M.SuccessorOf t D.floor)
    (hRootZ : M.mem D.coordinates.root z) (hzc : M.mem z c) (hcLast : c=D.coordinates.last ∨ M.mem c D.coordinates.last)
    (hCommon : ∃ p, ParentAt M D.mountain D.floor c p ∧ ParentAt M D.mountain D.floor z p)
    (hMapC : ParentCopy M C T D.coordinates b c cc) (hMapZ : ParentCopy M C T D.coordinates b z zz)
    (hcc : M.mem cc Y.width)
    (hTC : MemPair M oldTop c tc) (hTZ : MemPair M oldTop z tz) (hNTC : MemPair M newTop cc tcc) (hNTZ : MemPair M newTop zz tzz)
    (hKey : ForestOrder.KeyLE M C D.mountain c z t tc tz) : ForestOrder.KeyLE M C Y cc zz t tcc tzz := by
  have hw := omega_isOrdinal_d hM hC.omega
  have hFloorNat := hD.floor_nat hM.1
  have htNat := natural_successor_mem_d hM hC hFloorNat ht
  have hRootC : M.mem D.coordinates.root c := nat_lt_trans hM hC hMapC.1 hRootZ hzc
  have hzLast : z=D.coordinates.last ∨ M.mem z D.coordinates.last := Or.inr (nat_lt_of_lt_of_le hM hC hD.coordinates.last hzc hcLast)
  have hzz := copy_lt_width hM hC hT hD hY hzc hMapC hMapZ hcc
  obtain ⟨p,hPC,hPZ⟩ := hCommon
  have hInit := common_init' hM.1 hD.mountain hPC hPZ
  have hTop : ForestOrder.DepthEqFrom M C D.mountain c z t → (tc=tz ∨ M.mem tc tz) → (tcc=tzz ∨ M.mem tcc tzz) :=
    fun hE hLe => canon_upper_top_d hM hC hD hRun hFrom hUpper hPseudo hFloorNat ht hRootZ hzc hcLast hInit ⟨p,hPC⟩ hE
      hTC hTZ hLe hMapC hMapZ hNTC hNTZ
  obtain ⟨F,_,hF⟩ := hD.mountain.parents.total D.floor hFloorNat
  have hConeVia (a : M.Domain) (hPA : ParentAt M D.mountain D.floor a p) : InCone M C D p ↔ InCone M C D a :=
    in_cone_ancestor_iff_d hM hC hD hRun hFrom (Or.inl rfl) hF
      (ancestor_direct_d hM hC (hD.mountain.forest D.floor F hF) ((canon_row_parent_iff hM.1 hD.mountain hF).mp hPA))
  have hStatus : InCone M C D c ↔ InCone M C D z := (hConeVia c hPC).symm.trans (hConeVia z hPZ)
  classical
  by_cases hConeC : InCone M C D c
  · have hConeZ := hStatus.mp hConeC
    obtain ⟨off,hOff,hTimes⟩ := hT.mul.mul_exists_d hM hC hMapC.2.1 (hD.rise_nat hM.1)
    obtain ⟨level,_,hLevel⟩ := hT.add.add_exists_d hM hC hFloorNat hOff
    have hEncC := (parent_copy_bad_iff (nat_not_lt_of_le hM hC hMapC.1 (Or.inr hRootC))).mp hMapC
    have hEncZ := (parent_copy_bad_iff (nat_not_lt_of_le hM hC hMapZ.1 (Or.inr hRootZ))).mp hMapZ
    have hEqFloor := canon_depth_eq_of_common_parent_d hM hC hD.mountain hPC hPZ
    have hKeyF := canon_key_prepend_d hM hC hFloorNat ht hEqFloor hKey
    have hTopF : ForestOrder.DepthEqFrom M C D.mountain c z D.floor → (tc=tz ∨ M.mem tc tz) → (tcc=tzz ∨ M.mem tcc tzz) :=
      fun hE hLe => hTop (fun r hr hTr => hE r hr (Or.inr (nat_lt_of_lt_of_le hM hC hr ht.predecessor_mem hTr))) hLe
    apply canon_key_of_parts (canon_key_transfer_d hM hC (fun ρ σ => ShiftedRow M C T D.floor off ρ σ) ?_ ?_ ?_) hTopF hKeyF
    · intro ρ hρ _
      obtain ⟨σ,hShift⟩ := shifted_row_exists_d hM hC hT hFloorNat hOff hρ
      exact ⟨σ,hShift.2.1,hShift.floor_le_d hM hC hT,hShift⟩
    · intro ρ σ hρ hTρ _ _ hShift _ hEqσ
      have hHighR : D.floor=ρ ∨ M.mem D.floor ρ := Or.inr (nat_lt_of_lt_of_le hM hC hρ ht.predecessor_mem hTρ)
      by_cases hGap : M.mem ρ level
      · have he := hShift.gap_value hM.1 hT hLevel hGap
        subst he
        exact (hCopy.canon_row_gap_d hM hC hT hD hY hRun hFrom hρ hHighR hTimes hShift hConeC hConeZ hRootC hcLast
          hRootZ hzLast hEncC hEncZ hcc hzz).1 hEqσ
      · exact (hCopy.canon_row_lift_d hM hC hT hD hY hRun hFrom hρ hTimes hShift hLevel hGap hConeC hConeZ hcLast hzLast
          hEncC hEncZ hcc hzz).1 hEqσ
    · intro σ hσ hTσ _ hLtσ
      rcases hTσ with he | hgt
      · subst he
        exact False.elim (canon_eq_lt_absurd hM hEqFloor hLtσ)
      · obtain ⟨ρ,hρ,hAdd⟩ := hT.add.add_exists_d hM hC hσ hOff
        obtain ⟨hShift,hNotGap⟩ := canon_shift_high_d hM hC hT hLevel hσ (Or.inr hgt) hAdd
        have hσρ : σ=ρ ∨ M.mem σ ρ := ordinal_subset_cases_d hM (hw.mem hσ) (hw.mem hρ)
          (sum_base_subset_d hM (hw.mem hσ) ((hT.add.add_iff_sum hM hσ hOff).mp hAdd))
        have hTρ := nat_le_trans hM hC hρ (nat_succ_le_of_lt hM hC hFloorNat hσ ht hgt) hσρ
        refine ⟨ρ,hρ,hTρ,(hCopy.canon_row_lift_d hM hC hT hD hY hRun hFrom hρ hTimes hShift hLevel hNotGap hConeC hConeZ
          hcLast hzLast hEncC hEncZ hcc hzz).2 hLtσ,?_⟩
        intro ρ' hρ' _ σ' hShift'
        exact canon_shift_before_d hM hC hT hgt hAdd hρ' hShift'
  · have hConeZ : ¬InCone M C D z := fun h => hConeC (hStatus.mpr h)
    have hcLast' : M.mem c D.coordinates.last := hcLast.resolve_left (fun he => hConeC (he ▸ in_cone_last hD))
    have hzLast' : M.mem z D.coordinates.last := hzLast.resolve_left (fun he => hConeZ (he ▸ in_cone_last hD))
    exact key_identity_out hM hC hT hD hY hCopy hRun hFrom ht.predecessor_mem hcLast' hzLast' hConeC hConeZ
      hMapC hMapZ hcc hzz hTop hKey

/-- 抬升起点：共同父在源行u≥floor（皆在锥内），目标共同父在u+b·rise，Key起点同时平移。 -/
theorem Copies.canon_key_lifted_start_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {D : Context M.Domain} (hD : D.Valid M C) {Y : Data M.Domain} (hY : Y.Valid M C) {n : M.Domain}
    (hCopy : Copies M C T D n Y) {m : M.Domain} {R : RowStateSpace M.Domain} {V P H : M.Domain}
    (hRun : RowRun M C m R V P H) (hFrom : FromRun M C m R V H D.mountain)
    {Pseudo oldTop newTop u v t t' off c z b cc zz tc tz tcc tzz : M.Domain}
    (hUpper : UpperOrder M C T D Pseudo oldTop newTop) (hPseudo : GraphPseudoForest M C D.mountain Pseudo)
    (hHighU : D.floor=u ∨ M.mem D.floor u) (ht : M.SuccessorOf t u)
    (hTimes : MulAt M T.mulPairs T.times b D.rise off) (hV : AddAt M T.addPairs T.plus u off v) (ht' : M.SuccessorOf t' v)
    (hConeC : InCone M C D c) (hConeZ : InCone M C D z)
    (hRootZ : M.mem D.coordinates.root z) (hzc : M.mem z c) (hcLast : c=D.coordinates.last ∨ M.mem c D.coordinates.last)
    (hCommon : ∃ p, ParentAt M D.mountain u c p ∧ ParentAt M D.mountain u z p)
    (hMapC : ParentCopy M C T D.coordinates b c cc) (hMapZ : ParentCopy M C T D.coordinates b z zz)
    (hcc : M.mem cc Y.width)
    (hTC : MemPair M oldTop c tc) (hTZ : MemPair M oldTop z tz) (hNTC : MemPair M newTop cc tcc) (hNTZ : MemPair M newTop zz tzz)
    (hKey : ForestOrder.KeyLE M C D.mountain c z t tc tz) : ForestOrder.KeyLE M C Y cc zz t' tcc tzz := by
  have hw := omega_isOrdinal_d hM hC.omega
  have hFloorNat := hD.floor_nat hM.1
  have hVB := hV.bounds hM.1 hT.add
  have hu := hVB.1
  have hOff := hVB.2.1
  have htNat := natural_successor_mem_d hM hC hu ht
  have hRootC : M.mem D.coordinates.root c := nat_lt_trans hM hC hMapC.1 hRootZ hzc
  have hzLast : z=D.coordinates.last ∨ M.mem z D.coordinates.last := Or.inr (nat_lt_of_lt_of_le hM hC hD.coordinates.last hzc hcLast)
  have hzz := copy_lt_width hM hC hT hD hY hzc hMapC hMapZ hcc
  have hEncC := (parent_copy_bad_iff (nat_not_lt_of_le hM hC hMapC.1 (Or.inr hRootC))).mp hMapC
  have hEncZ := (parent_copy_bad_iff (nat_not_lt_of_le hM hC hMapZ.1 (Or.inr hRootZ))).mp hMapZ
  obtain ⟨p,hPC,hPZ⟩ := hCommon
  have hInit := common_init' hM.1 hD.mountain hPC hPZ
  have hTop : ForestOrder.DepthEqFrom M C D.mountain c z t → (tc=tz ∨ M.mem tc tz) → (tcc=tzz ∨ M.mem tcc tzz) :=
    fun hE hLe => canon_upper_top_d hM hC hD hRun hFrom hUpper hPseudo hu ht hRootZ hzc hcLast hInit ⟨p,hPC⟩ hE
      hTC hTZ hLe hMapC hMapZ hNTC hNTZ
  obtain ⟨level,_,hLevel⟩ := hT.add.add_exists_d hM hC hFloorNat hOff
  obtain ⟨t'',ht''Nat,hTT⟩ := hT.add.add_exists_d hM hC htNat hOff
  have hTT' : t''=t' := Structure.SuccessorOf.eq hM.1 (natural_sum_left_successor_d hM hC hOff ht
    ((hT.add.add_iff_sum hM hu hOff).mp hV) ((hT.add.add_iff_sum hM htNat hOff).mp hTT)) ht'
  subst hTT'
  have hFloorT : M.mem D.floor t := nat_lt_of_le_of_lt hM hC htNat hHighU ht.predecessor_mem
  apply canon_key_of_parts (canon_key_transfer_d hM hC (fun ρ σ => AddAt M T.addPairs T.plus σ off ρ) ?_ ?_ ?_) hTop hKey
  · intro ρ hρ hTρ
    have hOffT : off=t'' ∨ M.mem off t'' := ordinal_subset_cases_d hM (hw.mem hOff) (hw.mem ht''Nat)
      (sum_base_subset_d hM (hw.mem hOff) (natural_sum_comm_d hM hC htNat hOff ((hT.add.add_iff_sum hM htNat hOff).mp hTT)))
    have hOffR := nat_le_trans hM hC hρ hOffT hTρ
    obtain ⟨σ,hσ,hDiff⟩ := truncated_difference_exists_d hM hC hρ hOff
    have hSum := truncated_difference_add_inverse_d hM hC hDiff hOffR
    have hAdd : AddAt M T.addPairs T.plus σ off ρ :=
      (hT.add.add_iff_sum hM hσ hOff).mpr (natural_sum_comm_d hM hC hOff hσ hSum)
    exact ⟨σ,hσ,(add_same_right_le_iff_d hM hC hT hTT hAdd).mp hTρ,hAdd⟩
  · intro ρ σ hρ _ hσ hTσ hAdd _ hEqσ
    obtain ⟨hShift,hNotGap⟩ := canon_shift_high_d hM hC hT hLevel hσ (Or.inr (nat_lt_of_lt_of_le hM hC hσ hFloorT hTσ)) hAdd
    exact (hCopy.canon_row_lift_d hM hC hT hD hY hRun hFrom hρ hTimes hShift hLevel hNotGap hConeC hConeZ hcLast hzLast
      hEncC hEncZ hcc hzz).1 hEqσ
  · intro σ hσ hTσ _ hLtσ
    obtain ⟨ρ,hρ,hAdd⟩ := hT.add.add_exists_d hM hC hσ hOff
    obtain ⟨hShift,hNotGap⟩ := canon_shift_high_d hM hC hT hLevel hσ (Or.inr (nat_lt_of_lt_of_le hM hC hσ hFloorT hTσ)) hAdd
    refine ⟨ρ,hρ,(add_same_right_le_iff_d hM hC hT hTT hAdd).mpr hTσ,(hCopy.canon_row_lift_d hM hC hT hD hY hRun hFrom hρ
      hTimes hShift hLevel hNotGap hConeC hConeZ hcLast hzLast hEncC hEncZ hcc hzz).2 hLtσ,?_⟩
    intro ρ' hρ' _ σ' hAdd'
    exact (add_same_right_lt_iff_d hM hC hT hAdd' hAdd).mp hρ'

/-- 锥外起点：共同父在源行u≥floor，两列皆在锥外；行号不变。 -/
theorem Copies.canon_key_outside_start_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {D : Context M.Domain} (hD : D.Valid M C) {Y : Data M.Domain} (hY : Y.Valid M C) {n : M.Domain}
    (hCopy : Copies M C T D n Y) {m : M.Domain} {R : RowStateSpace M.Domain} {V P H : M.Domain}
    (hRun : RowRun M C m R V P H) (hFrom : FromRun M C m R V H D.mountain)
    {Pseudo oldTop newTop u t c z b cc zz tc tz tcc tzz : M.Domain}
    (hUpper : UpperOrder M C T D Pseudo oldTop newTop) (hPseudo : GraphPseudoForest M C D.mountain Pseudo)
    (hHighU : D.floor=u ∨ M.mem D.floor u) (ht : M.SuccessorOf t u)
    (hOutC : ¬InCone M C D c) (hOutZ : ¬InCone M C D z)
    (hRootZ : M.mem D.coordinates.root z) (hzc : M.mem z c) (hcLast : M.mem c D.coordinates.last)
    (hCommon : ∃ p, ParentAt M D.mountain u c p ∧ ParentAt M D.mountain u z p)
    (hMapC : ParentCopy M C T D.coordinates b c cc) (hMapZ : ParentCopy M C T D.coordinates b z zz)
    (hcc : M.mem cc Y.width)
    (hTC : MemPair M oldTop c tc) (hTZ : MemPair M oldTop z tz) (hNTC : MemPair M newTop cc tcc) (hNTZ : MemPair M newTop zz tzz)
    (hKey : ForestOrder.KeyLE M C D.mountain c z t tc tz) : ForestOrder.KeyLE M C Y cc zz t tcc tzz := by
  have hu : M.mem u C.omega := by
    obtain ⟨p,hPC,_⟩ := hCommon
    exact (hPC.bounds hM.1 hD.mountain).1
  have htNat := natural_successor_mem_d hM hC hu ht
  have hzLast : M.mem z D.coordinates.last := nat_lt_trans hM hC hD.coordinates.last hzc hcLast
  have hzz := copy_lt_width hM hC hT hD hY hzc hMapC hMapZ hcc
  obtain ⟨p,hPC,hPZ⟩ := hCommon
  have hInit := common_init' hM.1 hD.mountain hPC hPZ
  have hTop : ForestOrder.DepthEqFrom M C D.mountain c z t → (tc=tz ∨ M.mem tc tz) → (tcc=tzz ∨ M.mem tcc tzz) :=
    fun hE hLe => canon_upper_top_d hM hC hD hRun hFrom hUpper hPseudo hu ht hRootZ hzc (Or.inr hcLast) hInit ⟨p,hPC⟩ hE
      hTC hTZ hLe hMapC hMapZ hNTC hNTZ
  exact key_identity_out hM hC hT hD hY hCopy hRun hFrom (nat_lt_of_le_of_lt hM hC htNat hHighU ht.predecessor_mem)
    hcLast hzLast hOutC hOutZ hMapC hMapZ hcc hzz hTop hKey

end KP1Y.OneYFinite.CopiedMountain.Lower
