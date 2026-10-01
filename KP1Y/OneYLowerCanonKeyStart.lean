import KP1Y.OneYLowerCanonKeyRows

/-! 图层Key在Lower复制中的四种起点运输（原 keyLE_low_start/floor_start/lifted_start/outside_start）。
全部行号为内部ω元素；目标深度由实际复制图读取，Top比较只经上层 UpperOrder。 -/
namespace KP1Y.OneYFinite.CopiedMountain.Lower
open YesMetaZFC YesMetaZFC.SetTheory YesMetaZFC.SetTheory.Definitional
open KP1Y.Kuratowski KP1Y.Functions KP1Y.Naturals KP1Y.Bounded KP1Y.Arithmetic
open KP1Y.OneYFinite.CopyCoordinates KP1Y.OneYFinite.LowerCanon
universe u

/-- σ≥floor 时 σ+off 行不在填充段，且其shift行恰为σ。 -/
theorem canon_shift_high_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {floor off level σ ρ : M.Domain} (hLevel : AddAt M T.addPairs T.plus floor off level)
    (hσ : M.mem σ C.omega) (hFloorσ : floor=σ ∨ M.mem floor σ) (hAdd : AddAt M T.addPairs T.plus σ off ρ) :
    ShiftedRow M C T floor off ρ σ ∧ ¬M.mem ρ level := by
  have hLB := hLevel.bounds hM.1 hT.add
  have hAB := hAdd.bounds hM.1 hT.add
  have hNotGap : ¬M.mem ρ level :=
    nat_not_lt_of_le hM hC hAB.2.2 ((add_same_right_le_iff_d hM hC hT hLevel hAdd).mpr hFloorσ)
  have hSum := natural_sum_comm_d hM hC hAB.1 hAB.2.1 ((hT.add.add_iff_sum hM hAB.1 hAB.2.1).mp hAdd)
  have hDiff := (difference_read_iff_d hM hT hAB.2.2 hAB.2.1).mpr (truncated_difference_of_sum_d hM hC hAB.2.1 hσ hSum)
  exact ⟨⟨hAB.2.2,hσ,level,hLB.2.2,hLevel,Or.inr ⟨hNotGap,hDiff⟩⟩,hNotGap⟩

/-- σ+off 之前的移动行的shift行都严格小于σ（σ>floor）。 -/
theorem canon_shift_before_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {floor off σ ρ ρ' σ' : M.Domain} (hFloorσ : M.mem floor σ)
    (hAdd : AddAt M T.addPairs T.plus σ off ρ) (hρ' : M.mem ρ' ρ) (hShift : ShiftedRow M C T floor off ρ' σ') :
    M.mem σ' σ := by
  obtain ⟨_,_,level,_,hLevel,_⟩ := id hShift
  classical
  by_cases hGap : M.mem ρ' level
  · have he := hShift.gap_value hM.1 hT hLevel hGap
    exact he ▸ hFloorσ
  · exact (add_same_right_lt_iff_d hM hC hT (hShift.high_sum_d hM hC hT hLevel hGap) hAdd).mp hρ'

theorem canon_eq_lt_absurd {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} {X : Data M.Domain} {c z r : M.Domain}
    (hEq : ForestOrder.DepthEqAt M C X c z r) (hLt : ForestOrder.DepthLtAt M C X c z r) : False := by
  obtain ⟨a,ha,b,hb,hA,hB,hab⟩ := hLt
  have he := hEq a ha b hb hA hB
  subst he
  exact nat_irrefl hM a hab

/-- 同一父项的两列在该行深度相同。 -/
theorem canon_depth_eq_of_common_parent_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {X : Data M.Domain} (hX : X.Valid M C) {r c z p : M.Domain}
    (hPC : ParentAt M X r c p) (hPZ : ParentAt M X r z p) : ForestOrder.DepthEqAt M C X c z r := by
  intro a _ b _ hA hB
  obtain ⟨F,_,hF,hDa⟩ := hA
  obtain ⟨F',_,hF',hDb⟩ := hB
  have hFF := hX.parents.unique r F' F hF' hF
  subst F'
  have hFor := hX.forest r F hF
  obtain ⟨dp,hDp⟩ := depth_exists_d hM hC hFor (hFor.bounds hM.1 ((canon_row_parent_iff hM.1 hX hF).mp hPC)).2
  have h1 := depth_parent_successor_d hM hC hFor ((canon_row_parent_iff hM.1 hX hF).mp hPC) hDa hDp
  have h2 := depth_parent_successor_d hM hC hFor ((canon_row_parent_iff hM.1 hX hF).mp hPZ) hDb hDp
  exact Structure.SuccessorOf.eq hM.1 h1 h2

private theorem common_init {M : SetTheory.Structure.{u}} (he : Extensional M)
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

/-- 低起点：共同父位于低行u<floor，Key从u+1起。 -/
theorem Copies.canon_key_low_start_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {D : Context M.Domain} (hD : D.Valid M C) {Y : Data M.Domain} (hY : Y.Valid M C) {n : M.Domain}
    (hCopy : Copies M C T D n Y) {m : M.Domain} {R : RowStateSpace M.Domain} {V P H : M.Domain}
    (hRun : RowRun M C m R V P H) (hFrom : FromRun M C m R V H D.mountain)
    {Pseudo oldTop newTop u t c z b cc zz tc tz tcc tzz : M.Domain}
    (hUpper : UpperOrder M C T D Pseudo oldTop newTop) (hPseudo : GraphPseudoForest M C D.mountain Pseudo)
    (hLow : M.mem u D.floor) (ht : M.SuccessorOf t u)
    (hRootZ : M.mem D.coordinates.root z) (hzc : M.mem z c) (hcLast : c=D.coordinates.last ∨ M.mem c D.coordinates.last)
    (hCommon : ∃ p, ParentAt M D.mountain u c p ∧ ParentAt M D.mountain u z p)
    (hMapC : ParentCopy M C T D.coordinates b c cc) (hMapZ : ParentCopy M C T D.coordinates b z zz)
    (hcc : M.mem cc Y.width)
    (hTC : MemPair M oldTop c tc) (hTZ : MemPair M oldTop z tz) (hNTC : MemPair M newTop cc tcc) (hNTZ : MemPair M newTop zz tzz)
    (hKey : ForestOrder.KeyLE M C D.mountain c z t tc tz) : ForestOrder.KeyLE M C Y cc zz t tcc tzz := by
  have hw := omega_isOrdinal_d hM hC.omega
  have hFloorNat := hD.floor_nat hM.1
  have hu := nat_mem_omega hM hC hFloorNat hLow
  have htNat := natural_successor_mem_d hM hC hu ht
  have hTFloor : t=D.floor ∨ M.mem t D.floor := nat_succ_le_of_lt hM hC hu hFloorNat ht hLow
  have hRootC : M.mem D.coordinates.root c := nat_lt_trans hM hC hMapC.1 hRootZ hzc
  have hcX := canon_last_in_width hM hC hD hcLast
  have hzX : M.mem z D.mountain.width := (hw.mem hD.mountain.width).transitive c hcX z hzc
  have hzLast : z=D.coordinates.last ∨ M.mem z D.coordinates.last := Or.inr (nat_lt_of_lt_of_le hM hC hD.coordinates.last hzc hcLast)
  obtain ⟨J,hJ,hRowsJ⟩ := parent_copy_graph_exists_d hM hC hT hD.coordinates hMapC.2.1
  have hzz : M.mem zz Y.width := (hw.mem hY.width).transitive cc hcc zz
    (hJ.strict z hMapZ.1 c hMapC.1 hzc zz cc ((hRowsJ z zz).mpr hMapZ) ((hRowsJ c cc).mpr hMapC))
  obtain ⟨p,hPC,hPZ⟩ := hCommon
  have hInit := common_init hM.1 hD.mountain hPC hPZ
  have hProp (σ π : M.Domain) (hσ : M.mem σ C.omega) (hSucc : M.SuccessorOf σ π) (hTσ : t=σ ∨ M.mem t σ)
      (hBefore : ∀ q, M.mem q σ → (t=q ∨ M.mem t q) → ForestOrder.DepthEqAt M C D.mountain c z q) :
      ∀ F, MemPair M D.mountain.parents π F → ParentRowsEqual M F c z := by
    have hπ := nat_mem_omega hM hC hσ hSucc.predecessor_mem
    have huσ : M.mem u σ := nat_lt_of_succ_le hM hC hσ ht hTσ
    exact canon_parent_rows_propagate_d hM hC hRun hD.mountain hFrom hσ hcX hzX hInit
      (fun q hq huq => hBefore q hq (nat_succ_le_of_lt hM hC hu (nat_mem_omega hM hC hσ hq) ht huq))
      π hπ ((nat_lt_succ_iff hM hSucc).mp huσ) hSucc.predecessor_mem
  have hPred (σ : M.Domain) (hσ : M.mem σ C.omega) (hTσ : t=σ ∨ M.mem t σ) : ∃ π, M.SuccessorOf σ π := by
    rcases natural_cases hM hC.omega hσ with hEmpty | ⟨π,_,hSucc⟩
    · exact False.elim (hEmpty u (nat_lt_of_succ_le hM hC hσ ht hTσ))
    · exact ⟨π,hSucc⟩
  have hTop : ForestOrder.DepthEqFrom M C D.mountain c z t → (tc=tz ∨ M.mem tc tz) → (tcc=tzz ∨ M.mem tcc tzz) :=
    fun hE hLe => canon_upper_top_d hM hC hD hRun hFrom hUpper hPseudo hu ht hRootZ hzc hcLast hInit ⟨p,hPC⟩ hE
      hTC hTZ hLe hMapC hMapZ hNTC hNTZ
  -- 低行运输
  have hRowLow (σ : M.Domain) (hσ : M.mem σ C.omega) (hσLow : M.mem σ D.floor) (hTσ : t=σ ∨ M.mem t σ)
      (hBefore : ∀ q, M.mem q σ → (t=q ∨ M.mem t q) → ForestOrder.DepthEqAt M C D.mountain c z q) :=
    let ⟨π,hSucc⟩ := hPred σ hσ hTσ
    let ⟨Fπ,_,hFπ⟩ := hD.mountain.parents.total π (nat_mem_omega hM hC hσ hSucc.predecessor_mem)
    hCopy.canon_row_low_d hM hC hT hD hY hRun hFrom hσLow hSucc hFπ (hProp σ π hσ hSucc hTσ hBefore Fπ hFπ)
      hRootC hcLast hRootZ hzLast hMapC hMapZ hcc hzz
  have hFloorData (hBefore : ∀ q, M.mem q D.floor → (t=q ∨ M.mem t q) → ForestOrder.DepthEqAt M C D.mountain c z q) :
      ∃ π Fπ, M.SuccessorOf D.floor π ∧ MemPair M D.mountain.parents π Fπ ∧ ParentRowsEqual M Fπ c z := by
    obtain ⟨π,hSucc⟩ := hPred D.floor hFloorNat hTFloor
    obtain ⟨Fπ,_,hFπ⟩ := hD.mountain.parents.total π (nat_mem_omega hM hC hFloorNat hSucc.predecessor_mem)
    exact ⟨π,Fπ,hSucc,hFπ,hProp D.floor π hFloorNat hSucc hTFloor hBefore Fπ hFπ⟩
  classical
  by_cases hBoth : InCone M C D c ∧ InCone M C D z
  · -- 两列皆在锥内：floor以上用shift行
    obtain ⟨off,hOff,hTimes⟩ := hT.mul.mul_exists_d hM hC hMapC.2.1 (hD.rise_nat hM.1)
    obtain ⟨level,_,hLevel⟩ := hT.add.add_exists_d hM hC hFloorNat hOff
    have hEncC := (parent_copy_bad_iff (nat_not_lt_of_le hM hC hMapC.1 (Or.inr hRootC))).mp hMapC
    have hEncZ := (parent_copy_bad_iff (nat_not_lt_of_le hM hC hMapZ.1 (Or.inr hRootZ))).mp hMapZ
    obtain ⟨u0,hShiftFloor⟩ := shifted_row_exists_d hM hC hT hFloorNat hOff hFloorNat
    have hu0 := hShiftFloor.floor_value_d hM hC hT
    subst hu0
    let Rows : M.Domain → M.Domain → Prop := fun ρ σ =>
      (M.mem ρ D.floor ∧ σ=ρ) ∨ ((D.floor=ρ ∨ M.mem D.floor ρ) ∧ ShiftedRow M C T D.floor off ρ σ)
    apply canon_key_of_parts (canon_key_transfer_d hM hC Rows ?_ ?_ ?_) hTop hKey
    · intro ρ hρ hTρ
      rcases nat_le_or_lt hM hC hFloorNat hρ with hle | hlt
      · obtain ⟨σ,hShift⟩ := shifted_row_exists_d hM hC hT hFloorNat hOff hρ
        exact ⟨σ,hShift.2.1,nat_le_trans hM hC hShift.2.1 hTFloor (hShift.floor_le_d hM hC hT),Or.inr ⟨hle,hShift⟩⟩
      · exact ⟨ρ,hρ,hTρ,Or.inl ⟨hlt,rfl⟩⟩
    · intro ρ σ hρ hTρ hσ hTσ hR hBefore hEqσ
      rcases hR with ⟨hρLow,he⟩ | ⟨hHigh,hShift⟩
      · subst he
        exact (hRowLow σ hσ hρLow hTσ hBefore).1 hEqσ
      · by_cases hGap : M.mem ρ level
        · have he := hShift.gap_value hM.1 hT hLevel hGap
          subst he
          exact (hCopy.canon_row_gap_d hM hC hT hD hY hRun hFrom hρ hHigh hTimes hShift hBoth.1 hBoth.2 hRootC hcLast
            hRootZ hzLast hEncC hEncZ hcc hzz).1 hEqσ
        · exact (hCopy.canon_row_lift_d hM hC hT hD hY hRun hFrom hρ hTimes hShift hLevel hGap hBoth.1 hBoth.2 hcLast hzLast
            hEncC hEncZ hcc hzz).1 hEqσ
    · intro σ hσ hTσ hBefore hLtσ
      rcases nat_le_or_lt hM hC hσ hFloorNat with hle | hgt
      · rcases hle with he | hσLow
        · rw [he] at hLtσ hTσ ⊢
          refine ⟨D.floor,hFloorNat,hTσ,(hCopy.canon_row_gap_d hM hC hT hD hY hRun hFrom hFloorNat (Or.inl rfl) hTimes hShiftFloor
            hBoth.1 hBoth.2 hRootC hcLast hRootZ hzLast hEncC hEncZ hcc hzz).2 hLtσ,?_⟩
          intro ρ' hρ' _ σ' hR'
          rcases hR' with ⟨_,he'⟩ | ⟨hHigh',_⟩
          · exact he' ▸ hρ'
          · exact False.elim (nat_not_lt_of_le hM hC (nat_mem_omega hM hC hFloorNat hρ') hHigh' hρ')
        · refine ⟨σ,hσ,hTσ,(hRowLow σ hσ hσLow hTσ hBefore).2 hLtσ,?_⟩
          intro ρ' hρ' _ σ' hR'
          rcases hR' with ⟨_,he'⟩ | ⟨hHigh',_⟩
          · exact he' ▸ hρ'
          · exact False.elim (nat_not_lt_of_le hM hC (nat_mem_omega hM hC hσ hρ') hHigh'
              (nat_lt_trans hM hC hFloorNat hρ' hσLow))
      · obtain ⟨ρ,hρ,hAdd⟩ := hT.add.add_exists_d hM hC hσ hOff
        obtain ⟨hShift,hNotGap⟩ := canon_shift_high_d hM hC hT hLevel hσ (Or.inr hgt) hAdd
        have hσρ : σ=ρ ∨ M.mem σ ρ := ordinal_subset_cases_d hM (hw.mem hσ) (hw.mem hρ)
          (sum_base_subset_d hM (hw.mem hσ) ((hT.add.add_iff_sum hM hσ hOff).mp hAdd))
        refine ⟨ρ,hρ,nat_le_trans hM hC hρ hTσ hσρ,(hCopy.canon_row_lift_d hM hC hT hD hY hRun hFrom hρ hTimes hShift hLevel
          hNotGap hBoth.1 hBoth.2 hcLast hzLast hEncC hEncZ hcc hzz).2 hLtσ,?_⟩
        intro ρ' hρ' _ σ' hR'
        rcases hR' with ⟨hρ'Low,he'⟩ | ⟨_,hShift'⟩
        · exact he' ▸ nat_lt_trans hM hC hσ hρ'Low hgt
        · exact canon_shift_before_d hM hC hT hgt hAdd hρ' hShift'
  · -- 至少一列不在锥内：行号不变
    have hRowAll (σ : M.Domain) (hσ : M.mem σ C.omega) (hTσ : t=σ ∨ M.mem t σ)
        (hBefore : ∀ q, M.mem q σ → (t=q ∨ M.mem t q) → ForestOrder.DepthEqAt M C D.mountain c z q) :
        (ForestOrder.DepthEqAt M C D.mountain c z σ → ForestOrder.DepthEqAt M C Y cc zz σ) ∧
          (ForestOrder.DepthLtAt M C D.mountain c z σ → ForestOrder.DepthLtAt M C Y cc zz σ) := by
      rcases nat_le_or_lt hM hC hσ hFloorNat with hle | hgt
      · rcases hle with he | hσLow
        · subst he
          obtain ⟨π,Fπ,hSucc,hFπ,hSame⟩ := hFloorData hBefore
          exact hCopy.canon_row_floor_d hM hC hT hD hY hRun hFrom hSucc hFπ hSame hRootC hcLast hRootZ hzLast hMapC hMapZ hcc hzz
        · exact hRowLow σ hσ hσLow hTσ hBefore
      · obtain ⟨π,Fπ,hSucc,hFπ,hSame⟩ := hFloorData (fun q hq hTq => hBefore q (nat_lt_trans hM hC hσ hq hgt) hTq)
        have hEqFloor := hBefore D.floor hgt hTFloor
        have hStatus := canon_cone_status_eq_d hM hC hD hRun hFrom hSucc hFπ hSame hRootC hRootZ hcX hzX hEqFloor
        have hOutC : ¬InCone M C D c := fun h => hBoth ⟨h,hStatus.mp h⟩
        have hOutZ : ¬InCone M C D z := fun h => hBoth ⟨hStatus.mpr h,h⟩
        have hcLast' : M.mem c D.coordinates.last := hcLast.resolve_left (fun he => hOutC (he ▸ in_cone_last hD))
        have hzLast' : M.mem z D.coordinates.last := hzLast.resolve_left (fun he => hOutZ (he ▸ in_cone_last hD))
        exact hCopy.canon_row_out_d hM hC hT hD hY hRun hFrom hσ (Or.inr hgt) hcLast' hzLast' hOutC hOutZ hMapC hMapZ hcc hzz
    apply canon_key_of_parts (canon_key_transfer_d hM hC (fun ρ σ => σ=ρ) (fun ρ hρ hT => ⟨ρ,hρ,hT,rfl⟩) ?_ ?_) hTop hKey
    · intro ρ σ _ _ hσ hTσ hR hBefore hEqσ
      subst hR
      exact (hRowAll σ hσ hTσ hBefore).1 hEqσ
    · intro σ hσ hTσ hBefore hLtσ
      refine ⟨σ,hσ,hTσ,(hRowAll σ hσ hTσ hBefore).2 hLtσ,?_⟩
      intro ρ' hρ' _ σ' hR'
      exact hR' ▸ hρ'

end KP1Y.OneYFinite.CopiedMountain.Lower
