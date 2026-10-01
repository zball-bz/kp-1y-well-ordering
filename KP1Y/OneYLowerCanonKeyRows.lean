import KP1Y.OneYLowerCanonKeyCore

/-! Key单行运输：低行、参考行(floor/填充)、抬升行与锥外高行；深度由实际复制图计算。 -/
namespace KP1Y.OneYFinite.CopiedMountain.Lower
open YesMetaZFC YesMetaZFC.SetTheory YesMetaZFC.SetTheory.Definitional
open KP1Y.Kuratowski KP1Y.Functions KP1Y.Naturals KP1Y.Bounded KP1Y.Arithmetic
open KP1Y.OneYFinite.CopyCoordinates KP1Y.OneYFinite.LowerCanon
universe u

theorem canon_last_in_width {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {D : Context M.Domain} (hD : D.Valid M C) {c : M.Domain}
    (hcLast : c=D.coordinates.last ∨ M.mem c D.coordinates.last) : M.mem c D.mountain.width :=
  hcLast.elim (fun he => he ▸ hD.last)
    (fun h => ((omega_isOrdinal_d hM hC.omega).mem hD.mountain.width).transitive _ hD.last c h)

/-- floor行上，root之后的列在锥内当且仅当root是其祖先。 -/
theorem canon_in_cone_iff_anc_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {D : Context M.Domain} (hD : D.Valid M C) {F c : M.Domain}
    (hF : MemPair M D.mountain.parents D.floor F) (hRootC : M.mem D.coordinates.root c) (hc : M.mem c D.mountain.width) :
    InCone M C D c ↔ Ancestor M C D.mountain.width F D.coordinates.root c := by
  have hFF := hD.mountain.forest D.floor F hF
  constructor
  · rintro ⟨_,_,_,_,F',_,hF',hRoot⟩
    have hFF' := hD.mountain.parents.unique D.floor F' F hF' hF
    subst F'
    rcases hRoot.2.2 with he | hAnc
    · exact False.elim (nat_irrefl hM c (he ▸ hRootC))
    · exact hAnc
  · intro hAnc
    obtain ⟨h,hh,hH⟩ := hD.mountain.heights.total c hc
    obtain ⟨p,hCP,_⟩ := ancestor_parent_cases_d hM hC hFF hAnc
    have hFloorH := (hD.mountain.source D.floor c h hH).mp ⟨p,(canon_row_parent_iff hM.1 hD.mountain hF).mpr hCP⟩
    exact ⟨h,hh,hH,Or.inr hFloorH,F,(hD.mountain.parents.bounds hM.1 hF).2,hF,(hAnc.bounds hM.1).1,
      canon_no_parent_of_height hM.1 hD.mountain hF hD.floor (nat_irrefl hM D.floor),Or.inr hAnc⟩

/-- 低行单行运输：前一行父行相同，从而root祖先性单调。 -/
theorem Copies.canon_row_low_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {D : Context M.Domain} (hD : D.Valid M C) {Y : Data M.Domain} (hY : Y.Valid M C) {n : M.Domain}
    (hCopy : Copies M C T D n Y) {m : M.Domain} {R : RowStateSpace M.Domain} {V P H : M.Domain}
    (hRun : RowRun M C m R V P H) (hFrom : FromRun M C m R V H D.mountain)
    {π ρ Fπ c z b cc zz : M.Domain}
    (hLow : M.mem ρ D.floor) (hSucc : M.SuccessorOf ρ π) (hFπ : MemPair M D.mountain.parents π Fπ)
    (hSame : ParentRowsEqual M Fπ c z)
    (hRootC : M.mem D.coordinates.root c) (hcLast : c=D.coordinates.last ∨ M.mem c D.coordinates.last)
    (hRootZ : M.mem D.coordinates.root z) (hzLast : z=D.coordinates.last ∨ M.mem z D.coordinates.last)
    (hMapC : ParentCopy M C T D.coordinates b c cc) (hMapZ : ParentCopy M C T D.coordinates b z zz)
    (hcc : M.mem cc Y.width) (hzz : M.mem zz Y.width) :
    (ForestOrder.DepthEqAt M C D.mountain c z ρ → ForestOrder.DepthEqAt M C Y cc zz ρ) ∧
      (ForestOrder.DepthLtAt M C D.mountain c z ρ → ForestOrder.DepthLtAt M C Y cc zz ρ) := by
  have hρ := nat_mem_omega hM hC (hD.floor_nat hM.1) hLow
  obtain ⟨F,_,hF⟩ := hD.mountain.parents.total ρ hρ
  obtain ⟨G,_,hG⟩ := hY.parents.total ρ hρ
  have hFF := hD.mountain.forest ρ F hF
  have hGF := hY.forest ρ G hG
  have hcX := canon_last_in_width hM hC hD hcLast
  have hzX := canon_last_in_width hM hC hD hzLast
  obtain ⟨dc,hDc⟩ := depth_exists_d hM hC hFF hcX
  obtain ⟨dz,hDz⟩ := depth_exists_d hM hC hFF hzX
  obtain ⟨dcc,hDcc⟩ := depth_exists_d hM hC hGF hcc
  obtain ⟨dzz,hDzz⟩ := depth_exists_d hM hC hGF hzz
  have hMono {a a' da da' : M.Domain} (hSameAA : ParentRowsEqual M Fπ a a')
      (hDa : Depth M C D.mountain.width F a da) (hDa' : Depth M C D.mountain.width F a' da')
      (hLe : da=da' ∨ M.mem da da') (hAnc : Ancestor M C D.mountain.width F D.coordinates.root a) :
      Ancestor M C D.mountain.width F D.coordinates.root a' :=
    source_ancestor_mono_of_previous_depth_d hM hC hRun hD.mountain hFrom hSucc hFπ hF hSameAA hDa hDa' hLe hAnc
  have hSame' : ParentRowsEqual M Fπ z c := fun q => (hSame q).symm
  have hRootNot : ¬M.mem D.coordinates.root D.coordinates.root := nat_irrefl hM _
  obtain ⟨W0,_,hW0⟩ := encode_exists_d hM hC hT hD.coordinates hD.coordinates.root hMapC.2.1
  have hMapW0 : ParentCopy M C T D.coordinates b D.coordinates.root W0 := (parent_copy_bad_iff hRootNot).mpr hW0
  have hRootX : M.mem D.coordinates.root D.mountain.width :=
    ((omega_isOrdinal_d hM hC.omega).mem hD.mountain.width).transitive _ hD.last _ hD.coordinates.below
  obtain ⟨dr,hDr⟩ := depth_exists_d hM hC hFF hRootX
  have hNotRootC : c≠D.coordinates.root := fun he => nat_irrefl hM c (he ▸ hRootC)
  have hNotRootZ : z≠D.coordinates.root := fun he => nat_irrefl hM z (he ▸ hRootZ)
  -- 跨接缝副本W0的深度不小于root深度。
  have hSeamGe (hW0Y : M.mem W0 Y.width) {dw : M.Domain} (hDw : Depth M C Y.width G W0 dw) : dr=dw ∨ M.mem dr dw := by
    have hSeam := hCopy.canon_root_seam_low_d hM hC hT hD hY hRun hFrom hLow hF hG hMapW0 hW0Y
    have hRootY : M.mem D.coordinates.root Y.width := hSeam.elim (fun he => he ▸ hW0Y) (fun h => (h.bounds hM.1).1)
    have hDrY := hCopy.canon_depth_original_d hM hC hT hD hY hF hG (Or.inr hD.coordinates.below) hRootY hDr
    rcases hSeam with he | hAnc
    · subst he
      exact Or.inl (depth_unique_d hM hC hGF hDrY hDw)
    · exact Or.inr (depth_ancestor_lt_d hM hC hGF hAnc hDrY hDw)
  have hAtX (a d : M.Domain) (h : Depth M C D.mountain.width F a d) : ForestOrder.DepthAt M C D.mountain a ρ d :=
    ⟨F,(hD.mountain.parents.bounds hM.1 hF).2,hF,h⟩
  have hAtY (a d : M.Domain) (h : Depth M C Y.width G a d) : ForestOrder.DepthAt M C Y a ρ d :=
    ⟨G,(hY.parents.bounds hM.1 hG).2,hG,h⟩
  have hBoth (hAC : Ancestor M C D.mountain.width F D.coordinates.root c)
      (hAZ : Ancestor M C D.mountain.width F D.coordinates.root z) :
      (dc=dz ↔ dcc=dzz) ∧ (M.mem dc dz ↔ M.mem dcc dzz) := by
    have hW0Y := ((hCopy.low_ancestor_parent_copy_d hM hC hT hD hY hRun hFrom hLow hF hG hAC hcLast hMapW0 hMapC hcc).bounds hM.1).1
    obtain ⟨dw,hDw⟩ := depth_exists_d hM hC hGF hW0Y
    obtain ⟨e1,he1,hS1,hS1'⟩ := hCopy.canon_depth_low_diff_d hM hC hT hD hY hLow hF hG (Or.inl rfl) hcLast (Or.inr hAC)
      hMapW0 hMapC hcc hDr hDc hDw hDcc
    obtain ⟨e2,he2,hS2,hS2'⟩ := hCopy.canon_depth_low_diff_d hM hC hT hD hY hLow hF hG (Or.inl rfl) hzLast (Or.inr hAZ)
      hMapW0 hMapZ hzz hDr hDz hDw hDzz
    exact sum_pair_compare_iff_d hM hC hDr.1 hDw.1 he1 he2 hS1 hS2 hS1' hS2'
  have hNeither (hAC : ¬Ancestor M C D.mountain.width F D.coordinates.root c)
      (hAZ : ¬Ancestor M C D.mountain.width F D.coordinates.root z) : dcc=dc ∧ dzz=dz :=
    ⟨depth_unique_d hM hC hGF hDcc (hCopy.canon_depth_low_eq_d hM hC hT hD hY hLow hF hG hcLast hNotRootC hAC hMapC hcc hDc),
      depth_unique_d hM hC hGF hDzz (hCopy.canon_depth_low_eq_d hM hC hT hD hY hLow hF hG hzLast hNotRootZ hAZ hMapZ hzz hDz)⟩
  classical
  have hEqImp : dc=dz → dcc=dzz := by
    intro he
    by_cases hAC : Ancestor M C D.mountain.width F D.coordinates.root c
    · by_cases hAZ : Ancestor M C D.mountain.width F D.coordinates.root z
      · exact (hBoth hAC hAZ).1.mp he
      · exact False.elim (hAZ (hMono hSame hDc hDz (Or.inl he) hAC))
    · by_cases hAZ : Ancestor M C D.mountain.width F D.coordinates.root z
      · exact False.elim (hAC (hMono hSame' hDz hDc (Or.inl he.symm) hAZ))
      · obtain ⟨h1,h2⟩ := hNeither hAC hAZ
        rw [h1,h2]
        exact he
  have hLtImp : M.mem dc dz → M.mem dcc dzz := by
    intro hlt
    by_cases hAC : Ancestor M C D.mountain.width F D.coordinates.root c
    · by_cases hAZ : Ancestor M C D.mountain.width F D.coordinates.root z
      · exact (hBoth hAC hAZ).2.mp hlt
      · exact False.elim (hAZ (hMono hSame hDc hDz (Or.inr hlt) hAC))
    · by_cases hAZ : Ancestor M C D.mountain.width F D.coordinates.root z
      · have h1 := depth_unique_d hM hC hGF hDcc
          (hCopy.canon_depth_low_eq_d hM hC hT hD hY hLow hF hG hcLast hNotRootC hAC hMapC hcc hDc)
        subst dcc
        have hW0Y := ((hCopy.low_ancestor_parent_copy_d hM hC hT hD hY hRun hFrom hLow hF hG hAZ hzLast hMapW0 hMapZ hzz).bounds hM.1).1
        obtain ⟨dw,hDw⟩ := depth_exists_d hM hC hGF hW0Y
        obtain ⟨e2,he2,hS2,hS2'⟩ := hCopy.canon_depth_low_diff_d hM hC hT hD hY hLow hF hG (Or.inl rfl) hzLast (Or.inr hAZ)
          hMapW0 hMapZ hzz hDr hDz hDw hDzz
        have hle := nat_sum_le_left hM hC hDr.1 hDw.1 he2 hS2 hS2' (hSeamGe hW0Y hDw)
        exact nat_lt_of_lt_of_le hM hC hDzz.1 hlt hle
      · obtain ⟨h1,h2⟩ := hNeither hAC hAZ
        rw [h1,h2]
        exact hlt
  exact canon_row_transfer_d hM hC hD.mountain hY (hAtX c dc hDc) (hAtX z dz hDz) (hAtY cc dcc hDcc) (hAtY zz dzz hDzz)
    hEqImp hLtImp


/-- 参考行（移动行且shift行恰为floor）：锥内两列的目标深度差等于源floor行深度差。 -/
theorem Copies.canon_row_gap_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {D : Context M.Domain} (hD : D.Valid M C) {Y : Data M.Domain} (hY : Y.Valid M C) {n : M.Domain}
    (hCopy : Copies M C T D n Y) {m : M.Domain} {R : RowStateSpace M.Domain} {V P H : M.Domain}
    (hRun : RowRun M C m R V P H) (hFrom : FromRun M C m R V H D.mountain)
    {ρ off c z b cc zz : M.Domain}
    (hρ : M.mem ρ C.omega) (hHighR : D.floor=ρ ∨ M.mem D.floor ρ)
    (hTimes : MulAt M T.mulPairs T.times b D.rise off) (hShift : ShiftedRow M C T D.floor off ρ D.floor)
    (hConeC : InCone M C D c) (hConeZ : InCone M C D z)
    (hRootC : M.mem D.coordinates.root c) (hcLast : c=D.coordinates.last ∨ M.mem c D.coordinates.last)
    (hRootZ : M.mem D.coordinates.root z) (hzLast : z=D.coordinates.last ∨ M.mem z D.coordinates.last)
    (hEncC : Encode M C T D.coordinates c b cc) (hEncZ : Encode M C T D.coordinates z b zz)
    (hcc : M.mem cc Y.width) (hzz : M.mem zz Y.width) :
    (ForestOrder.DepthEqAt M C D.mountain c z D.floor → ForestOrder.DepthEqAt M C Y cc zz ρ) ∧
      (ForestOrder.DepthLtAt M C D.mountain c z D.floor → ForestOrder.DepthLtAt M C Y cc zz ρ) := by
  obtain ⟨F,_,hF⟩ := hD.mountain.parents.total D.floor (hD.floor_nat hM.1)
  obtain ⟨G,_,hG⟩ := hY.parents.total ρ hρ
  have hFF := hD.mountain.forest D.floor F hF
  have hGF := hY.forest ρ G hG
  have hcX := canon_last_in_width hM hC hD hcLast
  have hzX := canon_last_in_width hM hC hD hzLast
  have hAC := (canon_in_cone_iff_anc_d hM hC hD hF hRootC hcX).mp hConeC
  have hAZ := (canon_in_cone_iff_anc_d hM hC hD hF hRootZ hzX).mp hConeZ
  have hRootNot : ¬M.mem D.coordinates.root D.coordinates.root := nat_irrefl hM _
  obtain ⟨W0,_,hW0⟩ := encode_exists_d hM hC hT hD.coordinates hD.coordinates.root hEncC.2.1
  have hMapW0 : ParentCopy M C T D.coordinates b D.coordinates.root W0 := (parent_copy_bad_iff hRootNot).mpr hW0
  have hSourceC : Source M D.coordinates c := ⟨hRootC,hcLast⟩
  have hW0Y := ((hCopy.high_ancestor_copy_d hM hC hT hD hRun hFrom hY hSourceC hConeC hHighR hTimes hShift hEncC
    (hCopy.width ▸ hcc) hF hG hAC hMapW0).bounds hM.1).1
  have hRootX : M.mem D.coordinates.root D.mountain.width :=
    ((omega_isOrdinal_d hM hC.omega).mem hD.mountain.width).transitive _ hD.last _ hD.coordinates.below
  obtain ⟨dr,hDr⟩ := depth_exists_d hM hC hFF hRootX
  obtain ⟨dw,hDw⟩ := depth_exists_d hM hC hGF hW0Y
  obtain ⟨dc,hDc⟩ := depth_exists_d hM hC hFF hcX
  obtain ⟨dz,hDz⟩ := depth_exists_d hM hC hFF hzX
  obtain ⟨dcc,hDcc⟩ := depth_exists_d hM hC hGF hcc
  obtain ⟨dzz,hDzz⟩ := depth_exists_d hM hC hGF hzz
  obtain ⟨e1,he1,hS1,hS1'⟩ := hCopy.canon_depth_moved_diff_d hM hC hT hD hY hRun hFrom hρ hHighR hTimes hShift hF hG
    (in_cone_root_d hM hD) hConeC hcLast (Or.inr hAC) hW0 hEncC hcc hDr hDc hDw hDcc
  obtain ⟨e2,he2,hS2,hS2'⟩ := hCopy.canon_depth_moved_diff_d hM hC hT hD hY hRun hFrom hρ hHighR hTimes hShift hF hG
    (in_cone_root_d hM hD) hConeZ hzLast (Or.inr hAZ) hW0 hEncZ hzz hDr hDz hDw hDzz
  have hCmp := sum_pair_compare_iff_d hM hC hDr.1 hDw.1 he1 he2 hS1 hS2 hS1' hS2'
  exact canon_row_transfer_d hM hC hD.mountain hY ⟨F,(hD.mountain.parents.bounds hM.1 hF).2,hF,hDc⟩
    ⟨F,(hD.mountain.parents.bounds hM.1 hF).2,hF,hDz⟩ ⟨G,(hY.parents.bounds hM.1 hG).2,hG,hDcc⟩
    ⟨G,(hY.parents.bounds hM.1 hG).2,hG,hDzz⟩ hCmp.1.mp hCmp.2.mp

/-- 抬升行：锥内两列的目标深度等于源shift行深度。 -/
theorem Copies.canon_row_lift_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {D : Context M.Domain} (hD : D.Valid M C) {Y : Data M.Domain} (hY : Y.Valid M C) {n : M.Domain}
    (hCopy : Copies M C T D n Y) {m : M.Domain} {R : RowStateSpace M.Domain} {V P H : M.Domain}
    (hRun : RowRun M C m R V P H) (hFrom : FromRun M C m R V H D.mountain)
    {ρ σ off level c z b cc zz : M.Domain}
    (hρ : M.mem ρ C.omega) (hTimes : MulAt M T.mulPairs T.times b D.rise off) (hShift : ShiftedRow M C T D.floor off ρ σ)
    (hLevel : AddAt M T.addPairs T.plus D.floor off level) (hNotGap : ¬M.mem ρ level)
    (hConeC : InCone M C D c) (hConeZ : InCone M C D z)
    (hcLast : c=D.coordinates.last ∨ M.mem c D.coordinates.last) (hzLast : z=D.coordinates.last ∨ M.mem z D.coordinates.last)
    (hEncC : Encode M C T D.coordinates c b cc) (hEncZ : Encode M C T D.coordinates z b zz)
    (hcc : M.mem cc Y.width) (hzz : M.mem zz Y.width) :
    (ForestOrder.DepthEqAt M C D.mountain c z σ → ForestOrder.DepthEqAt M C Y cc zz ρ) ∧
      (ForestOrder.DepthLtAt M C D.mountain c z σ → ForestOrder.DepthLtAt M C Y cc zz ρ) := by
  obtain ⟨F,_,hF⟩ := hD.mountain.parents.total σ hShift.2.1
  obtain ⟨G,_,hG⟩ := hY.parents.total ρ hρ
  have hFF := hD.mountain.forest σ F hF
  obtain ⟨dc,hDc⟩ := depth_exists_d hM hC hFF (canon_last_in_width hM hC hD hcLast)
  obtain ⟨dz,hDz⟩ := depth_exists_d hM hC hFF (canon_last_in_width hM hC hD hzLast)
  have hDcc := hCopy.canon_depth_lifted_d hM hC hT hD hY hRun hFrom hρ hTimes hShift hLevel hNotGap hF hG hConeC hcLast hEncC hcc hDc
  have hDzz := hCopy.canon_depth_lifted_d hM hC hT hD hY hRun hFrom hρ hTimes hShift hLevel hNotGap hF hG hConeZ hzLast hEncZ hzz hDz
  exact canon_row_transfer_d hM hC hD.mountain hY ⟨F,(hD.mountain.parents.bounds hM.1 hF).2,hF,hDc⟩
    ⟨F,(hD.mountain.parents.bounds hM.1 hF).2,hF,hDz⟩ ⟨G,(hY.parents.bounds hM.1 hG).2,hG,hDcc⟩
    ⟨G,(hY.parents.bounds hM.1 hG).2,hG,hDzz⟩ id id

/-- 锥外高行：两列的目标深度等于源同行深度。 -/
theorem Copies.canon_row_out_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {D : Context M.Domain} (hD : D.Valid M C) {Y : Data M.Domain} (hY : Y.Valid M C) {n : M.Domain}
    (hCopy : Copies M C T D n Y) {m : M.Domain} {R : RowStateSpace M.Domain} {V P H : M.Domain}
    (hRun : RowRun M C m R V P H) (hFrom : FromRun M C m R V H D.mountain)
    {ρ c z b cc zz : M.Domain} (hρ : M.mem ρ C.omega) (hHighR : D.floor=ρ ∨ M.mem D.floor ρ)
    (hcLast : M.mem c D.coordinates.last) (hzLast : M.mem z D.coordinates.last)
    (hOutC : ¬InCone M C D c) (hOutZ : ¬InCone M C D z)
    (hMapC : ParentCopy M C T D.coordinates b c cc) (hMapZ : ParentCopy M C T D.coordinates b z zz)
    (hcc : M.mem cc Y.width) (hzz : M.mem zz Y.width) :
    (ForestOrder.DepthEqAt M C D.mountain c z ρ → ForestOrder.DepthEqAt M C Y cc zz ρ) ∧
      (ForestOrder.DepthLtAt M C D.mountain c z ρ → ForestOrder.DepthLtAt M C Y cc zz ρ) := by
  obtain ⟨F,_,hF⟩ := hD.mountain.parents.total ρ hρ
  obtain ⟨G,_,hG⟩ := hY.parents.total ρ hρ
  have hFF := hD.mountain.forest ρ F hF
  obtain ⟨dc,hDc⟩ := depth_exists_d hM hC hFF (canon_last_in_width hM hC hD (Or.inr hcLast))
  obtain ⟨dz,hDz⟩ := depth_exists_d hM hC hFF (canon_last_in_width hM hC hD (Or.inr hzLast))
  have hDcc := hCopy.canon_depth_out_eq_d hM hC hT hD hY hRun hFrom hHighR hF hG hcLast hOutC hMapC hcc hDc
  have hDzz := hCopy.canon_depth_out_eq_d hM hC hT hD hY hRun hFrom hHighR hF hG hzLast hOutZ hMapZ hzz hDz
  exact canon_row_transfer_d hM hC hD.mountain hY ⟨F,(hD.mountain.parents.bounds hM.1 hF).2,hF,hDc⟩
    ⟨F,(hD.mountain.parents.bounds hM.1 hF).2,hF,hDz⟩ ⟨G,(hY.parents.bounds hM.1 hG).2,hG,hDcc⟩
    ⟨G,(hY.parents.bounds hM.1 hG).2,hG,hDzz⟩ id id

/-- floor行深度相等且前一行父行相同，则两列锥状态相同。 -/
theorem canon_cone_status_eq_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {D : Context M.Domain} (hD : D.Valid M C)
    {m : M.Domain} {R : RowStateSpace M.Domain} {V P H : M.Domain}
    (hRun : RowRun M C m R V P H) (hFrom : FromRun M C m R V H D.mountain)
    {π Fπ c z : M.Domain} (hSucc : M.SuccessorOf D.floor π) (hFπ : MemPair M D.mountain.parents π Fπ)
    (hSame : ParentRowsEqual M Fπ c z) (hRootC : M.mem D.coordinates.root c) (hRootZ : M.mem D.coordinates.root z)
    (hcX : M.mem c D.mountain.width) (hzX : M.mem z D.mountain.width)
    (hEq : ForestOrder.DepthEqAt M C D.mountain c z D.floor) : InCone M C D c ↔ InCone M C D z := by
  obtain ⟨F,_,hF⟩ := hD.mountain.parents.total D.floor (hD.floor_nat hM.1)
  have hFF := hD.mountain.forest D.floor F hF
  obtain ⟨dc,hDc⟩ := depth_exists_d hM hC hFF hcX
  obtain ⟨dz,hDz⟩ := depth_exists_d hM hC hFF hzX
  have he := hEq dc hDc.1 dz hDz.1 ⟨F,(hD.mountain.parents.bounds hM.1 hF).2,hF,hDc⟩ ⟨F,(hD.mountain.parents.bounds hM.1 hF).2,hF,hDz⟩
  rw [canon_in_cone_iff_anc_d hM hC hD hF hRootC hcX,canon_in_cone_iff_anc_d hM hC hD hF hRootZ hzX]
  exact ⟨source_ancestor_mono_of_previous_depth_d hM hC hRun hD.mountain hFrom hSucc hFπ hF hSame hDc hDz (Or.inl he),
    source_ancestor_mono_of_previous_depth_d hM hC hRun hD.mountain hFrom hSucc hFπ hF (fun q => (hSame q).symm)
      hDz hDc (Or.inl he.symm)⟩

/-- 低起点Key的floor行（含锥状态混合情形）。 -/
theorem Copies.canon_row_floor_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {D : Context M.Domain} (hD : D.Valid M C) {Y : Data M.Domain} (hY : Y.Valid M C) {n : M.Domain}
    (hCopy : Copies M C T D n Y) {m : M.Domain} {R : RowStateSpace M.Domain} {V P H : M.Domain}
    (hRun : RowRun M C m R V P H) (hFrom : FromRun M C m R V H D.mountain)
    {π Fπ c z b cc zz : M.Domain}
    (hSucc : M.SuccessorOf D.floor π) (hFπ : MemPair M D.mountain.parents π Fπ) (hSame : ParentRowsEqual M Fπ c z)
    (hRootC : M.mem D.coordinates.root c) (hcLast : c=D.coordinates.last ∨ M.mem c D.coordinates.last)
    (hRootZ : M.mem D.coordinates.root z) (hzLast : z=D.coordinates.last ∨ M.mem z D.coordinates.last)
    (hMapC : ParentCopy M C T D.coordinates b c cc) (hMapZ : ParentCopy M C T D.coordinates b z zz)
    (hcc : M.mem cc Y.width) (hzz : M.mem zz Y.width) :
    (ForestOrder.DepthEqAt M C D.mountain c z D.floor → ForestOrder.DepthEqAt M C Y cc zz D.floor) ∧
      (ForestOrder.DepthLtAt M C D.mountain c z D.floor → ForestOrder.DepthLtAt M C Y cc zz D.floor) := by
  have hFloorNat := hD.floor_nat hM.1
  obtain ⟨off,hOff,hTimes⟩ := hT.mul.mul_exists_d hM hC hMapC.2.1 (hD.rise_nat hM.1)
  obtain ⟨u,hShift⟩ := shifted_row_exists_d hM hC hT hFloorNat hOff hFloorNat
  have hu := hShift.floor_value_d hM hC hT
  subst hu
  have hEncC := (parent_copy_bad_iff (nat_not_lt_of_le hM hC hMapC.1 (Or.inr hRootC))).mp hMapC
  have hEncZ := (parent_copy_bad_iff (nat_not_lt_of_le hM hC hMapZ.1 (Or.inr hRootZ))).mp hMapZ
  have hcX := canon_last_in_width hM hC hD hcLast
  have hzX := canon_last_in_width hM hC hD hzLast
  obtain ⟨F,_,hF⟩ := hD.mountain.parents.total D.floor hFloorNat
  obtain ⟨G,_,hG⟩ := hY.parents.total D.floor hFloorNat
  have hFF := hD.mountain.forest D.floor F hF
  have hGF := hY.forest D.floor G hG
  obtain ⟨dc,hDc⟩ := depth_exists_d hM hC hFF hcX
  obtain ⟨dz,hDz⟩ := depth_exists_d hM hC hFF hzX
  obtain ⟨dcc,hDcc⟩ := depth_exists_d hM hC hGF hcc
  obtain ⟨dzz,hDzz⟩ := depth_exists_d hM hC hGF hzz
  have hAtX (a d : M.Domain) (h : Depth M C D.mountain.width F a d) : ForestOrder.DepthAt M C D.mountain a D.floor d :=
    ⟨F,(hD.mountain.parents.bounds hM.1 hF).2,hF,h⟩
  have hAtY (a d : M.Domain) (h : Depth M C Y.width G a d) : ForestOrder.DepthAt M C Y a D.floor d :=
    ⟨G,(hY.parents.bounds hM.1 hG).2,hG,h⟩
  have hMono {a a' da da' : M.Domain} (hSameAA : ParentRowsEqual M Fπ a a')
      (hDa : Depth M C D.mountain.width F a da) (hDa' : Depth M C D.mountain.width F a' da')
      (hLe : da=da' ∨ M.mem da da') (hAnc : Ancestor M C D.mountain.width F D.coordinates.root a) :
      Ancestor M C D.mountain.width F D.coordinates.root a' :=
    source_ancestor_mono_of_previous_depth_d hM hC hRun hD.mountain hFrom hSucc hFπ hF hSameAA hDa hDa' hLe hAnc
  have hSame' : ParentRowsEqual M Fπ z c := fun q => (hSame q).symm
  have hConeIff (a : M.Domain) (hRA : M.mem D.coordinates.root a) (haX : M.mem a D.mountain.width) :=
    canon_in_cone_iff_anc_d hM hC hD hF hRA haX
  classical
  by_cases hCC : InCone M C D c <;> by_cases hCZ : InCone M C D z
  · exact hCopy.canon_row_gap_d hM hC hT hD hY hRun hFrom hFloorNat (Or.inl rfl) hTimes hShift hCC hCZ hRootC hcLast
      hRootZ hzLast hEncC hEncZ hcc hzz
  · refine canon_row_transfer_d hM hC hD.mountain hY (hAtX c dc hDc) (hAtX z dz hDz) (hAtY cc dcc hDcc) (hAtY zz dzz hDzz)
      (fun he => False.elim (hCZ ((hConeIff z hRootZ hzX).mpr (hMono hSame hDc hDz (Or.inl he) ((hConeIff c hRootC hcX).mp hCC)))))
      (fun hlt => False.elim (hCZ ((hConeIff z hRootZ hzX).mpr (hMono hSame hDc hDz (Or.inr hlt) ((hConeIff c hRootC hcX).mp hCC)))))
  · have hcLast' : M.mem c D.coordinates.last := hcLast.resolve_left (fun he => hCC (he ▸ in_cone_last hD))
    have h1 := depth_unique_d hM hC hGF hDcc
      (hCopy.canon_depth_out_eq_d hM hC hT hD hY hRun hFrom (Or.inl rfl) hF hG hcLast' hCC hMapC hcc hDc)
    subst dcc
    refine canon_row_transfer_d hM hC hD.mountain hY (hAtX c dc hDc) (hAtX z dz hDz) (hAtY cc dc hDcc) (hAtY zz dzz hDzz)
      (fun he => False.elim (hCC ((hConeIff c hRootC hcX).mpr (hMono hSame' hDz hDc (Or.inl he.symm) ((hConeIff z hRootZ hzX).mp hCZ)))))
      ?_
    intro hlt
    have hRootNot : ¬M.mem D.coordinates.root D.coordinates.root := nat_irrefl hM _
    obtain ⟨W0,_,hW0⟩ := encode_exists_d hM hC hT hD.coordinates hD.coordinates.root hMapZ.2.1
    have hMapW0 : ParentCopy M C T D.coordinates b D.coordinates.root W0 := (parent_copy_bad_iff hRootNot).mpr hW0
    have hAZ := (hConeIff z hRootZ hzX).mp hCZ
    have hW0Y := ((hCopy.high_ancestor_copy_d hM hC hT hD hRun hFrom hY ⟨hRootZ,hzLast⟩ hCZ (Or.inl rfl) hTimes hShift hEncZ
      (hCopy.width ▸ hzz) hF hG hAZ hMapW0).bounds hM.1).1
    have hRootX : M.mem D.coordinates.root D.mountain.width :=
      ((omega_isOrdinal_d hM hC.omega).mem hD.mountain.width).transitive _ hD.last _ hD.coordinates.below
    obtain ⟨dr,hDr⟩ := depth_exists_d hM hC hFF hRootX
    have hdr : dr=C.zero := depth_of_no_parent_d hM hC hFF
      (canon_no_parent_of_height hM.1 hD.mountain hF hD.floor (nat_irrefl hM D.floor)) hDr
    subst dr
    obtain ⟨dw,hDw⟩ := depth_exists_d hM hC hGF hW0Y
    obtain ⟨e2,he2,hS2,hS2'⟩ := hCopy.canon_depth_moved_diff_d hM hC hT hD hY hRun hFrom hFloorNat (Or.inl rfl) hTimes hShift hF hG
      (in_cone_root_d hM hD) hCZ hzLast (Or.inr hAZ) hW0 hEncZ hzz hDr hDz hDw hDzz
    have he2z := natural_sum_left_zero_d hM hC he2 hS2
    subst he2z
    exact nat_lt_of_lt_of_le hM hC hDzz.1 hlt (nat_le_sum_right hM hC hDw.1 hDz.1 hS2')
  · have hcLast' : M.mem c D.coordinates.last := hcLast.resolve_left (fun he => hCC (he ▸ in_cone_last hD))
    have hzLast' : M.mem z D.coordinates.last := hzLast.resolve_left (fun he => hCZ (he ▸ in_cone_last hD))
    exact hCopy.canon_row_out_d hM hC hT hD hY hRun hFrom hFloorNat (Or.inl rfl) hcLast' hzLast' hCC hCZ hMapC hMapZ hcc hzz

end KP1Y.OneYFinite.CopiedMountain.Lower
