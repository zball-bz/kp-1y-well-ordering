import KP1Y.OneYLowerCanonKeyRows

/-! 底行（行0）在外部继承候选帧F上的深度比较运输（原 depth_zero_lt_copy_of_common_frame）。
F 只需选出源底父图；单调性来自真实稀疏选择的深度恢复。 -/
namespace KP1Y.OneYFinite.CopiedMountain.Lower
open YesMetaZFC YesMetaZFC.SetTheory YesMetaZFC.SetTheory.Definitional
open KP1Y.Kuratowski KP1Y.Functions KP1Y.Naturals KP1Y.Bounded KP1Y.Arithmetic
open KP1Y.OneYFinite.CopyCoordinates KP1Y.OneYFinite.LowerCanon
universe u

/-- 在共同候选帧F下，选择森林中的祖先关系随深度单调。 -/
theorem canon_frame_mono_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {m F V P c z a dc dz : M.Domain}
    (hSel : Selects true M C m F V P) (hPos : ∀ c v, MemPair M V c v → M.mem C.zero v)
    (hFrame : ParentRowsEqual M F c z)
    (hDc : Depth M C m P c dc) (hDz : Depth M C m P z dz) (hLe : dc=dz ∨ M.mem dc dz)
    (hAnc : Ancestor M C m P a c) : Ancestor M C m P a z := by
  obtain ⟨Depths,hDepths,hRows⟩ := depth_graph_exists_d hM hC hSel.forest
  have hSelD := hSel.sparse_depth_selection_d hM hC
    (fun c hZero => False.elim (hC.zero_empty C.zero (hPos c C.zero hZero)))
    (hDepths.mono_values (fun d hd => (omega_isOrdinal_d hM hC.omega).transitive m hSel.forest.width d hd)) hRows
  exact hSelD.ancestor_mono_of_common_chain_d hM hC
    (fun p => ancestor_iff_of_parent_rows_eq_d hM hC hSel.inherited hFrame p)
    ((hRows c dc).mpr hDc) ((hRows z dz).mpr hDz) hLe hAnc

/-- 行0运输：源底父图由外部帧F选出，c,z在F中父项相同。 -/
theorem Copies.canon_row_zero_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {D : Context M.Domain} (hD : D.Valid M C) {Y : Data M.Domain} (hY : Y.Valid M C) {n : M.Domain}
    (hCopy : Copies M C T D n Y) {m : M.Domain} {R : RowStateSpace M.Domain} {V P H : M.Domain}
    (hRun : RowRun M C m R V P H) (hFrom : FromRun M C m R V H D.mountain)
    (hPos : ∀ c v, MemPair M V c v → M.mem C.zero v)
    {F c z b cc zz : M.Domain} (hSel : Selects true M C m F V P) (hFrame : ParentRowsEqual M F c z)
    (hRootC : M.mem D.coordinates.root c) (hcLast : c=D.coordinates.last ∨ M.mem c D.coordinates.last)
    (hRootZ : M.mem D.coordinates.root z) (hzLast : z=D.coordinates.last ∨ M.mem z D.coordinates.last)
    (hMapC : ParentCopy M C T D.coordinates b c cc) (hMapZ : ParentCopy M C T D.coordinates b z zz)
    (hcc : M.mem cc Y.width) (hzz : M.mem zz Y.width) :
    (ForestOrder.DepthEqAt M C D.mountain c z C.zero → ForestOrder.DepthEqAt M C Y cc zz C.zero) ∧
      (ForestOrder.DepthLtAt M C D.mountain c z C.zero → ForestOrder.DepthLtAt M C Y cc zz C.zero) := by
  have hFloorNat := hD.floor_nat hM.1
  obtain ⟨F0,_,hF0⟩ := hD.mountain.parents.total C.zero hC.zero_nat
  obtain ⟨G,_,hG⟩ := hY.parents.total C.zero hC.zero_nat
  have hP0 : F0=P := by
    obtain ⟨U,hAt⟩ := (hFrom.parents C.zero F0).mp hF0
    exact (hRun.at_unique hM.1 hAt (hRun.initial_row_at_d hM)).2
  subst F0
  have hFF := hD.mountain.forest C.zero P hF0
  have hGF := hY.forest C.zero G hG
  have hcX := canon_last_in_width hM hC hD hcLast
  have hzX := canon_last_in_width hM hC hD hzLast
  obtain ⟨dc,hDc⟩ := depth_exists_d hM hC hFF hcX
  obtain ⟨dz,hDz⟩ := depth_exists_d hM hC hFF hzX
  obtain ⟨dcc,hDcc⟩ := depth_exists_d hM hC hGF hcc
  obtain ⟨dzz,hDzz⟩ := depth_exists_d hM hC hGF hzz
  have hSel' : Selects true M C D.mountain.width F V P := hFrom.width.symm ▸ hSel
  have hMono {a a' da da' : M.Domain} (hFr : ParentRowsEqual M F a a')
      (hDa : Depth M C D.mountain.width P a da) (hDa' : Depth M C D.mountain.width P a' da')
      (hLe : da=da' ∨ M.mem da da') (hAnc : Ancestor M C D.mountain.width P D.coordinates.root a) :
      Ancestor M C D.mountain.width P D.coordinates.root a' :=
    canon_frame_mono_d hM hC hSel' hPos hFr hDa hDa' hLe hAnc
  have hFrame' : ParentRowsEqual M F z c := fun q => (hFrame q).symm
  have hAtX (a d : M.Domain) (h : Depth M C D.mountain.width P a d) : ForestOrder.DepthAt M C D.mountain a C.zero d :=
    ⟨P,(hD.mountain.parents.bounds hM.1 hF0).2,hF0,h⟩
  have hAtY (a d : M.Domain) (h : Depth M C Y.width G a d) : ForestOrder.DepthAt M C Y a C.zero d :=
    ⟨G,(hY.parents.bounds hM.1 hG).2,hG,h⟩
  have hRootNot : ¬M.mem D.coordinates.root D.coordinates.root := nat_irrefl hM _
  obtain ⟨W0,_,hW0⟩ := encode_exists_d hM hC hT hD.coordinates hD.coordinates.root hMapC.2.1
  have hMapW0 : ParentCopy M C T D.coordinates b D.coordinates.root W0 := (parent_copy_bad_iff hRootNot).mpr hW0
  have hRootX : M.mem D.coordinates.root D.mountain.width :=
    ((omega_isOrdinal_d hM hC.omega).mem hD.mountain.width).transitive _ hD.last _ hD.coordinates.below
  obtain ⟨dr,hDr⟩ := depth_exists_d hM hC hFF hRootX
  classical
  rcases natural_cases hM hC.omega hFloorNat with hEmpty | ⟨π,_,hFloorSucc⟩
  · -- floor=0：行0即参考行
    have hFloorZero : D.floor=C.zero := hM.1.eq_of_same_members _ _ (fun t => iff_of_false (hEmpty t) (hC.zero_empty t))
    have hFZ : MemPair M D.mountain.parents D.floor P := hFloorZero ▸ hF0
    have hConeIff (a : M.Domain) (hRA : M.mem D.coordinates.root a) (haX : M.mem a D.mountain.width) :
        InCone M C D a ↔ Ancestor M C D.mountain.width P D.coordinates.root a :=
      canon_in_cone_iff_anc_d hM hC hD hFZ hRA haX
    by_cases hCC : InCone M C D c <;> by_cases hCZ : InCone M C D z
    · obtain ⟨off,hOff,hTimes⟩ := hT.mul.mul_exists_d hM hC hMapC.2.1 (hD.rise_nat hM.1)
      obtain ⟨u0,hShift⟩ := shifted_row_exists_d hM hC hT hFloorNat hOff hFloorNat
      have hu0 := hShift.floor_value_d hM hC hT
      subst hu0
      have hEncC := (parent_copy_bad_iff (nat_not_lt_of_le hM hC hMapC.1 (Or.inr hRootC))).mp hMapC
      have hEncZ := (parent_copy_bad_iff (nat_not_lt_of_le hM hC hMapZ.1 (Or.inr hRootZ))).mp hMapZ
      have h := hCopy.canon_row_gap_d hM hC hT hD hY hRun hFrom hFloorNat (Or.inl rfl) hTimes hShift hCC hCZ hRootC hcLast
        hRootZ hzLast hEncC hEncZ hcc hzz
      rw [hFloorZero] at h
      exact h
    · refine canon_row_transfer_d hM hC hD.mountain hY (hAtX c dc hDc) (hAtX z dz hDz) (hAtY cc dcc hDcc) (hAtY zz dzz hDzz)
        (fun he => False.elim (hCZ ((hConeIff z hRootZ hzX).mpr (hMono hFrame hDc hDz (Or.inl he) ((hConeIff c hRootC hcX).mp hCC)))))
        (fun hlt => False.elim (hCZ ((hConeIff z hRootZ hzX).mpr (hMono hFrame hDc hDz (Or.inr hlt) ((hConeIff c hRootC hcX).mp hCC)))))
    · have hcLast' : M.mem c D.coordinates.last := hcLast.resolve_left (fun he => hCC (he ▸ in_cone_last hD))
      have hFG : MemPair M Y.parents D.floor G := hFloorZero ▸ hG
      have h1 := depth_unique_d hM hC hGF hDcc
        (hCopy.canon_depth_out_eq_d hM hC hT hD hY hRun hFrom (Or.inl rfl) hFZ hFG hcLast' hCC hMapC hcc hDc)
      subst dcc
      refine canon_row_transfer_d hM hC hD.mountain hY (hAtX c dc hDc) (hAtX z dz hDz) (hAtY cc dc hDcc) (hAtY zz dzz hDzz)
        (fun he => False.elim (hCC ((hConeIff c hRootC hcX).mpr (hMono hFrame' hDz hDc (Or.inl he.symm) ((hConeIff z hRootZ hzX).mp hCZ)))))
        ?_
      intro hlt
      obtain ⟨off,hOff,hTimes⟩ := hT.mul.mul_exists_d hM hC hMapZ.2.1 (hD.rise_nat hM.1)
      obtain ⟨u0,hShift⟩ := shifted_row_exists_d hM hC hT hFloorNat hOff hFloorNat
      have hu0 := hShift.floor_value_d hM hC hT
      subst hu0
      have hEncZ := (parent_copy_bad_iff (nat_not_lt_of_le hM hC hMapZ.1 (Or.inr hRootZ))).mp hMapZ
      have hAZ := (hConeIff z hRootZ hzX).mp hCZ
      have hW0Y := ((hCopy.high_ancestor_copy_d hM hC hT hD hRun hFrom hY ⟨hRootZ,hzLast⟩ hCZ (Or.inl rfl) hTimes hShift hEncZ
        (hCopy.width ▸ hzz) hFZ hFG hAZ hMapW0).bounds hM.1).1
      have hDrF : Depth M C D.mountain.width P D.coordinates.root dr := hDr
      have hdr : dr=C.zero := depth_of_no_parent_d hM hC hFF
        (canon_no_parent_of_height hM.1 hD.mountain hFZ hD.floor (nat_irrefl hM D.floor)) hDrF
      subst dr
      obtain ⟨dw,hDw⟩ := depth_exists_d hM hC hGF hW0Y
      obtain ⟨e2,he2,hS2,hS2'⟩ := hCopy.canon_depth_moved_diff_d hM hC hT hD hY hRun hFrom hFloorNat (Or.inl rfl) hTimes hShift
        hFZ hFG (in_cone_root_d hM hD) hCZ hzLast (Or.inr hAZ) hW0 hEncZ hzz hDr hDz hDw hDzz
      have he2z := natural_sum_left_zero_d hM hC he2 hS2
      subst he2z
      exact nat_lt_of_lt_of_le hM hC hDzz.1 hlt (nat_le_sum_right hM hC hDw.1 hDz.1 hS2')
    · have hcLast' : M.mem c D.coordinates.last := hcLast.resolve_left (fun he => hCC (he ▸ in_cone_last hD))
      have hzLast' : M.mem z D.coordinates.last := hzLast.resolve_left (fun he => hCZ (he ▸ in_cone_last hD))
      have h := hCopy.canon_row_out_d hM hC hT hD hY hRun hFrom hFloorNat (Or.inl rfl) hcLast' hzLast' hCC hCZ hMapC hMapZ hcc hzz
      rw [hFloorZero] at h
      exact h
  · -- floor>0：行0为低行
    have hLow : M.mem C.zero D.floor := (hC.zero_mem_iff hM hFloorNat).mpr (fun he => hC.zero_empty π (he ▸ hFloorSucc.predecessor_mem))
    have hNotRootC : c≠D.coordinates.root := fun he => nat_irrefl hM c (he ▸ hRootC)
    have hNotRootZ : z≠D.coordinates.root := fun he => nat_irrefl hM z (he ▸ hRootZ)
    have hSeamGe (hW0Y : M.mem W0 Y.width) {dw : M.Domain} (hDw : Depth M C Y.width G W0 dw) : dr=dw ∨ M.mem dr dw := by
      have hSeam := hCopy.canon_root_seam_low_d hM hC hT hD hY hRun hFrom hLow hF0 hG hMapW0 hW0Y
      have hRootY : M.mem D.coordinates.root Y.width := hSeam.elim (fun he => he ▸ hW0Y) (fun h => (h.bounds hM.1).1)
      have hDrY := hCopy.canon_depth_original_d hM hC hT hD hY hF0 hG (Or.inr hD.coordinates.below) hRootY hDr
      rcases hSeam with he | hAnc
      · subst he
        exact Or.inl (depth_unique_d hM hC hGF hDrY hDw)
      · exact Or.inr (depth_ancestor_lt_d hM hC hGF hAnc hDrY hDw)
    have hBoth (hAC : Ancestor M C D.mountain.width P D.coordinates.root c)
        (hAZ : Ancestor M C D.mountain.width P D.coordinates.root z) :
        (dc=dz ↔ dcc=dzz) ∧ (M.mem dc dz ↔ M.mem dcc dzz) := by
      have hW0Y := ((hCopy.low_ancestor_parent_copy_d hM hC hT hD hY hRun hFrom hLow hF0 hG hAC hcLast hMapW0 hMapC hcc).bounds hM.1).1
      obtain ⟨dw,hDw⟩ := depth_exists_d hM hC hGF hW0Y
      obtain ⟨e1,he1,hS1,hS1'⟩ := hCopy.canon_depth_low_diff_d hM hC hT hD hY hLow hF0 hG (Or.inl rfl) hcLast (Or.inr hAC)
        hMapW0 hMapC hcc hDr hDc hDw hDcc
      obtain ⟨e2,he2,hS2,hS2'⟩ := hCopy.canon_depth_low_diff_d hM hC hT hD hY hLow hF0 hG (Or.inl rfl) hzLast (Or.inr hAZ)
        hMapW0 hMapZ hzz hDr hDz hDw hDzz
      exact sum_pair_compare_iff_d hM hC hDr.1 hDw.1 he1 he2 hS1 hS2 hS1' hS2'
    have hNeither (hAC : ¬Ancestor M C D.mountain.width P D.coordinates.root c)
        (hAZ : ¬Ancestor M C D.mountain.width P D.coordinates.root z) : dcc=dc ∧ dzz=dz :=
      ⟨depth_unique_d hM hC hGF hDcc (hCopy.canon_depth_low_eq_d hM hC hT hD hY hLow hF0 hG hcLast hNotRootC hAC hMapC hcc hDc),
        depth_unique_d hM hC hGF hDzz (hCopy.canon_depth_low_eq_d hM hC hT hD hY hLow hF0 hG hzLast hNotRootZ hAZ hMapZ hzz hDz)⟩
    have hEqImp : dc=dz → dcc=dzz := by
      intro he
      by_cases hAC : Ancestor M C D.mountain.width P D.coordinates.root c
      · by_cases hAZ : Ancestor M C D.mountain.width P D.coordinates.root z
        · exact (hBoth hAC hAZ).1.mp he
        · exact False.elim (hAZ (hMono hFrame hDc hDz (Or.inl he) hAC))
      · by_cases hAZ : Ancestor M C D.mountain.width P D.coordinates.root z
        · exact False.elim (hAC (hMono hFrame' hDz hDc (Or.inl he.symm) hAZ))
        · obtain ⟨h1,h2⟩ := hNeither hAC hAZ
          rw [h1,h2]
          exact he
    have hLtImp : M.mem dc dz → M.mem dcc dzz := by
      intro hlt
      by_cases hAC : Ancestor M C D.mountain.width P D.coordinates.root c
      · by_cases hAZ : Ancestor M C D.mountain.width P D.coordinates.root z
        · exact (hBoth hAC hAZ).2.mp hlt
        · exact False.elim (hAZ (hMono hFrame hDc hDz (Or.inr hlt) hAC))
      · by_cases hAZ : Ancestor M C D.mountain.width P D.coordinates.root z
        · have h1 := depth_unique_d hM hC hGF hDcc
            (hCopy.canon_depth_low_eq_d hM hC hT hD hY hLow hF0 hG hcLast hNotRootC hAC hMapC hcc hDc)
          subst dcc
          have hW0Y := ((hCopy.low_ancestor_parent_copy_d hM hC hT hD hY hRun hFrom hLow hF0 hG hAZ hzLast hMapW0 hMapZ hzz).bounds hM.1).1
          obtain ⟨dw,hDw⟩ := depth_exists_d hM hC hGF hW0Y
          obtain ⟨e2,he2,hS2,hS2'⟩ := hCopy.canon_depth_low_diff_d hM hC hT hD hY hLow hF0 hG (Or.inl rfl) hzLast (Or.inr hAZ)
            hMapW0 hMapZ hzz hDr hDz hDw hDzz
          have hle := nat_sum_le_left hM hC hDr.1 hDw.1 he2 hS2 hS2' (hSeamGe hW0Y hDw)
          exact nat_lt_of_lt_of_le hM hC hDzz.1 hlt hle
        · obtain ⟨h1,h2⟩ := hNeither hAC hAZ
          rw [h1,h2]
          exact hlt
    exact canon_row_transfer_d hM hC hD.mountain hY (hAtX c dc hDc) (hAtX z dz hDz) (hAtY cc dcc hDcc) (hAtY zz dzz hDzz)
      hEqImp hLtImp

end KP1Y.OneYFinite.CopiedMountain.Lower
