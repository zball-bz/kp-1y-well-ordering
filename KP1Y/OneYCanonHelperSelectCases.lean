import KP1Y.OneYCanonHelperFrame
import KP1Y.OneYCanonHelperFixed

/-! H1的逐列情形：目标第0行父项P0在外部帧复制F'与目标底值上恰为最右较小值选择。
本模块只处理已有目标父项的列（前缀、非root副本、高/低seam），各自给出直接父或真实阻挡；
无父列与列归纳在`OneYCanonHelperSelect`中。 -/
namespace KP1Y.OneYFinite.TerminalBase
open YesMetaZFC YesMetaZFC.SetTheory YesMetaZFC.SetTheory.Definitional
open KP1Y.Kuratowski KP1Y.Functions KP1Y.Naturals KP1Y.Bounded KP1Y.Arithmetic
open ReconstructionCanonical Reconstruction MountainReconstruction ReconstructionRecovery
universe u

section
variable {M : SetTheory.Structure.{u}} {C : ExpressionData M.Domain} {T : MatrixArithmetic M.Domain}
  {m V P H level index n OldTop NewTop Bottom : M.Domain} {R : RowStateSpace M.Domain}
  {X Y : CopiedMountain.Data M.Domain} {A : CopyCoordinates.Context M.Domain}

theorem root_le_of_not_good_d (hM : M.Models KP1Y.theory) (hC : C.Valid M) (hA : A.Valid M C) {p : M.Domain}
    (hp : M.mem p C.omega) (hNot : ¬M.mem p A.root) : A.root=p ∨ M.mem A.root p := by
  rcases (omega_isOrdinal_d hM hC.omega).wellOrder.linear.compare A.root hA.root p hp with he | hlt | hgt
  · exact Or.inl (hM.1.eq_of_same_members A.root p he)
  · exact Or.inr hlt
  · exact False.elim (hNot hgt)

/-- 由阻挡数据关闭一列（目标网格的数值行、正值和P0细化F'都已内建）。 -/
theorem Base.blocker_close_d (hM : M.Models KP1Y.theory) (hC : C.Valid M) (hT : T.Valid M C)
    (h : Base M C T m V P H level index n OldTop NewTop Bottom R X Y A) {F F' P0 : M.Domain}
    (hF : Selects true M C m F V P) (hF' : FrameCopy.Copies M C T A F index n F')
    (hP0 : MemPair M Y.parents C.zero P0) {c q p z : M.Domain}
    (hQ : MemPair M F' c q) (hCP : MemPair M P0 c p)
    (hPrefix : ∀ i, M.mem i c → ∀ a, MemPair M P0 i a ↔ RestrictedParent true M C n F' Bottom i a)
    (hPath : z=q ∨ Ancestor M C n P0 z q) (hZP : MemPair M P0 z p)
    (hUpper : ∀ x y, MemPair M Bottom c x → MemPair M Bottom z y → x=y ∨ M.mem x y) :
    RestrictedParent true M C n F' Bottom c p := by
  obtain ⟨hRow,hPos⟩ := h.bottom_numeric_d hM hC hT hP0
  have hZeros : NumericOrder.ZerosAtRoots M n F' Bottom C.zero :=
    fun a _ hZero => False.elim (hC.zero_empty C.zero (hPos a C.zero hZero))
  exact ReconstructionSelection.restricted_parent_of_blocker_d hM hC hRow hF'.forest hZeros hQ hCP
    (h.zero_refines_d hM hC hT hF hF' hP0 hCP) hPrefix hPath hZP hUpper

/-- 前缀列：目标选择与源选择逐字相同。 -/
theorem Base.select_prefix_d (hM : M.Models KP1Y.theory) (hC : C.Valid M) (hT : T.Valid M C)
    (h : Base M C T m V P H level index n OldTop NewTop Bottom R X Y A) {F F' P0 : M.Domain}
    (hF : Selects true M C m F V P) (hF' : FrameCopy.Copies M C T A F index n F')
    (hP0 : MemPair M Y.parents C.zero P0) {c : M.Domain} (hcl : M.mem c A.last) (p : M.Domain) :
    MemPair M P0 c p ↔ RestrictedParent true M C n F' Bottom c p := by
  have hw := omega_isOrdinal_d hM hC.omega
  have hcn := h.last_subset_d hM hC hT c hcl
  have hLastM : M.MemberSubset A.last m := fun t ht => (hw.mem h.m_nat).transitive A.last h.last_m t ht
  have hVals : RowsAgreeOn M V Bottom A.last := fun i hi v => (h.prefix_values_d hM hC hT i hi v).symm
  rw [← h.target_zero_iff hM hP0 c p,h.copies.original_parents_d hM hC h.coords hcn hcl,h.source_zero_iff hM c p,
    hF.parents c p]
  exact restricted_prefix_iff_d hM hC true hF.inherited hF'.forest h.coords.last hLastM (h.last_subset_d hM hC hT) hcl
    (h.frame_prefix_d hM hC hT hF.inherited hF') hVals

/-- 非root副本列：直接父、好部阻挡（含root特例）或坏部阻挡（数值序由图层Key运输）。 -/
theorem Base.select_nonroot_d (hM : M.Models KP1Y.theory) (hC : C.Valid M) (hT : T.Valid M C)
    (h : Base M C T m V P H level index n OldTop NewTop Bottom R X Y A) {F F' P0 : M.Domain}
    (hF : Selects true M C m F V P) (hF' : FrameCopy.Copies M C T A F index n F')
    (hP0 : MemPair M Y.parents C.zero P0) {s b c p : M.Domain}
    (hRoot : M.mem A.root s) (hs : M.mem s A.last) (hMap : CopyCoordinates.ParentCopy M C T A b s c) (hc : M.mem c n)
    (hPrefix : ∀ i, M.mem i c → ∀ a, MemPair M P0 i a ↔ RestrictedParent true M C n F' Bottom i a)
    (hCP : MemPair M P0 c p) : RestrictedParent true M C n F' Bottom c p := by
  have hw := omega_isOrdinal_d hM hC.omega
  have hNonroot : s≠A.root := fun he => SetTheory.KP.mem_irrefl_d (KP1Y.models_weakKP hM) A.root (he ▸ hRoot)
  obtain ⟨ps,hSP,hMapP⟩ := (h.nonroot_iff_d hM hC hT hP0 hRoot hs hMap hc).mp hCP
  have hsm : M.mem s m := (hw.mem h.m_nat).transitive A.last h.last_m s hs
  obtain ⟨qf,hSQ,_⟩ := ancestor_parent_cases_d hM hC hF.inherited (hF.parent_ancestor hSP)
  have hqfS : M.mem qf s := hF.inherited.left s qf hSQ
  have hqfLast : M.mem qf A.last := (hw.mem h.coords.last).transitive s hs qf hqfS
  obtain ⟨qf',hMapQ⟩ := parent_copy_exists_d hM hC hT h.coords hMap.2.1 (hw.transitive A.last h.coords.last qf hqfLast)
  have hF'C : MemPair M F' c qf' :=
    (hF'.nonroot_parent_iff_d hM hC hT h.coords hF.inherited hs hNonroot hMap hc qf').mpr ⟨qf,hqfLast,hSQ,hMapQ⟩
  have hqf'n : M.mem qf' n := (hw.mem h.n_nat).transitive c hc qf' (parent_copy_strict_d hM hC hT h.coords hqfS hMapQ hMap)
  obtain ⟨hRow,_⟩ := h.bottom_numeric_d hM hC hT hP0
  classical
  by_cases hEq : ps=qf
  · subst hEq
    have he : qf'=p := parent_copy_unique_d hM hC hT h.coords hMapQ hMapP
    subst he
    exact ReconstructionSelection.restricted_parent_of_direct_d hM hC hRow hF'.forest hCP hF'C
  · obtain ⟨z,hzm,hPath,hZP,hValues⟩ := (selects_false_of_true hF h.rooted.positive).blocker_d hM hC hSQ hSP hEq
    have hzs : M.mem z s := by
      rcases hPath with he | hA
      · exact he.symm ▸ hqfS
      · exact (hw.mem (hw.transitive m h.m_nat s hsm)).transitive qf hqfS z hA.1
    have hzLast : M.mem z A.last := (hw.mem h.coords.last).transitive s hs z hzs
    have hzNat : M.mem z C.omega := hw.transitive m h.m_nat z hzm
    obtain ⟨vs,_,hVS⟩ := h.run.base.values.total s hsm
    obtain ⟨vz,_,hVZ⟩ := h.run.base.values.total z hzm
    have hLe := hValues vs vz hVS hVZ
    have hTransport (z2 : M.Domain) (hMapZ : CopyCoordinates.ParentCopy M C T A b z z2) :
        z2=qf' ∨ Ancestor M C n P0 z2 qf' := by
      rcases hPath with he | hA
      · subst he
        exact Or.inl (parent_copy_unique_d hM hC hT h.coords hMapZ hMapQ)
      · exact Or.inr (h.target_ancestor_d hM hC hT hP0 hA hqfLast hMapZ hMapQ hqf'n)
    by_cases hGood : M.mem ps A.root
    · have hpEq : p=ps := (CopyCoordinates.parent_copy_good_iff hMapP.2.1 hMapP.1 hGood).mp hMapP
      subst hpEq
      have hGoodS : ∀ q, MemPair M P s q → M.mem q A.root := fun q hq => h.run.base.forest.unique s p q hSP hq ▸ hGood
      have hBS : ∀ v, MemPair M Bottom c v ↔ MemPair M V s v := fun v => h.fixed_value_d hM hC hT hRoot hs hGoodS hMap hc
      have hBlock : ∃ z2, MemPair M P0 z2 p ∧ (z2=qf' ∨ Ancestor M C n P0 z2 qf') ∧
          ∀ v, MemPair M Bottom z2 v ↔ MemPair M V z v := by
        by_cases hzGood : M.mem z A.root
        · have hzn := h.last_subset_d hM hC hT z hzLast
          have hMapZ : CopyCoordinates.ParentCopy M C T A b z z := (CopyCoordinates.parent_copy_good_iff hMap.2.1 hzNat hzGood).mpr rfl
          exact ⟨z,(h.target_zero_iff hM hP0 z p).mp ((h.copies.original_parents_d hM hC h.coords hzn hzLast).mpr
            ((h.source_zero_iff hM z p).mpr hZP)),hTransport z hMapZ,h.prefix_values_d hM hC hT z hzLast⟩
        · by_cases hzRoot : z=A.root
          · subst hzRoot
            obtain ⟨z2,hMapZ⟩ := parent_copy_exists_d hM hC hT h.coords hMap.2.1 h.coords.root
            have hz2n : M.mem z2 n := (hw.mem h.n_nat).transitive c hc z2 (parent_copy_strict_d hM hC hT h.coords hRoot hMapZ hMap)
            rcases h.zero_le_level hM hC with hZ | hLow
            · exact ⟨z2,(h.root_copy_high_parent_d hM hC hT hZ.symm hP0 hMapZ hz2n).mpr hZP,hTransport z2 hMapZ,
                h.root_copy_high_value_d hM hC hT hZ.symm hMapZ hz2n⟩
            · have hRootN := h.last_subset_d hM hC hT A.root h.coords.below
              refine ⟨A.root,(h.target_zero_iff hM hP0 A.root p).mp ((h.copies.original_parents_d hM hC h.coords hRootN
                h.coords.below).mpr ((h.source_zero_iff hM A.root p).mpr hZP)),?_,h.prefix_values_d hM hC hT A.root h.coords.below⟩
              have hForest0 : Forest M C.omega n P0 := h.width_eq ▸ h.target.forest C.zero P0 hP0
              rcases h.root_chain_d hM hC hT hP0 hLow hMapZ hz2n with he | hA
              · rw [he]
                exact hTransport z2 hMapZ
              · rcases hTransport z2 hMapZ with he' | hA'
                · exact Or.inr (he' ▸ hA)
                · exact Or.inr (ancestor_trans_d hM hC hForest0 hA hA')
          · have hRootZ : M.mem A.root z :=
              (root_le_of_not_good_d hM hC h.coords hzNat hzGood).resolve_left (fun he => hzRoot he.symm)
            obtain ⟨z2,hMapZ⟩ := parent_copy_exists_d hM hC hT h.coords hMap.2.1 hzNat
            have hz2n : M.mem z2 n := (hw.mem h.n_nat).transitive c hc z2 (parent_copy_strict_d hM hC hT h.coords hzs hMapZ hMap)
            have hGoodZ : ∀ q, MemPair M P z q → M.mem q A.root := fun q hq => h.run.base.forest.unique z p q hZP hq ▸ hGood
            have hMapPP : CopyCoordinates.ParentCopy M C T A b p p :=
              (CopyCoordinates.parent_copy_good_iff hMap.2.1 (hw.transitive A.root h.coords.root p hGood) hGood).mpr rfl
            exact ⟨z2,(h.nonroot_iff_d hM hC hT hP0 hRootZ hzLast hMapZ hz2n).mpr ⟨p,hZP,hMapPP⟩,hTransport z2 hMapZ,
              fun v => h.fixed_value_d hM hC hT hRootZ hzLast hGoodZ hMapZ hz2n⟩
      obtain ⟨z2,hZ2P,hZ2Path,hZ2V⟩ := hBlock
      refine h.blocker_close_d hM hC hT hF hF' hP0 hF'C hCP hPrefix hZ2Path hZ2P ?_
      intro x y hX hY
      have hx := h.run.base.values.unique s x vs ((hBS x).mp hX) hVS
      have hy := h.run.base.values.unique z y vz ((hZ2V y).mp hY) hVZ
      rw [hx,hy]
      exact hLe
    · have hpsNat := hw.transitive m h.m_nat ps (h.run.base.forest.bounds hM.1 hSP).2
      have hRootP := root_le_of_not_good_d hM hC h.coords hpsNat hGood
      have hpsZ := h.run.base.forest.left z ps hZP
      have hRootZ : M.mem A.root z := by
        rcases hRootP with he | hlt
        · exact he ▸ hpsZ
        · exact (hw.mem hzNat).transitive ps hpsZ A.root hlt
      obtain ⟨z2,hMapZ⟩ := parent_copy_exists_d hM hC hT h.coords hMap.2.1 hzNat
      have hz2n : M.mem z2 n := (hw.mem h.n_nat).transitive c hc z2 (parent_copy_strict_d hM hC hT h.coords hzs hMapZ hMap)
      have hZ2P := (h.nonroot_iff_d hM hC hT hP0 hRootZ hzLast hMapZ hz2n).mpr ⟨ps,hZP,hMapP⟩
      refine h.blocker_close_d hM hC hT hF hF' hP0 hF'C hCP hPrefix (hTransport z2 hMapZ) hZ2P ?_
      intro x y hX hY
      exact h.copy_order_d hM hC hT hP0 hRoot hs hRootZ hzLast hSP hZP hVS hVZ hLe hMap hMapZ hc hz2n hX hY

/-- 末列的F父项及其复制、seam列的F'父项。 -/
theorem Base.seam_frame_d (hM : M.Models KP1Y.theory) (hC : C.Valid M) (hT : T.Valid M C)
    (h : Base M C T m V P H level index n OldTop NewTop Bottom R X Y A) {F F' : M.Domain}
    (hF : Selects true M C m F V P) (hF' : FrameCopy.Copies M C T A F index n F') {b c pl : M.Domain}
    (hEnc : CopyCoordinates.Encode M C T A A.last b c) (hc : M.mem c n) (hLP : MemPair M P A.last pl) :
    ∃ qf qf', MemPair M F A.last qf ∧ M.mem qf A.last ∧ CopyCoordinates.ParentCopy M C T A b qf qf' ∧
      MemPair M F' c qf' ∧ M.mem qf' n := by
  have hw := omega_isOrdinal_d hM hC.omega
  obtain ⟨qf,hSQ,_⟩ := ancestor_parent_cases_d hM hC hF.inherited (hF.parent_ancestor hLP)
  have hqfLast : M.mem qf A.last := hF.inherited.left A.last qf hSQ
  obtain ⟨qf',hMapQ⟩ := parent_copy_exists_d hM hC hT h.coords hEnc.2.1 (hw.transitive A.last h.coords.last qf hqfLast)
  have hNotLast : ¬M.mem A.last A.root := fun hl => SetTheory.KP.mem_irrefl_d (KP1Y.models_weakKP hM) A.root
    ((hw.mem h.coords.root).transitive A.last hl A.root h.coords.below)
  have hLastMap : CopyCoordinates.ParentCopy M C T A b A.last c := (CopyCoordinates.parent_copy_bad_iff hNotLast).mpr hEnc
  have hF'C : MemPair M F' c qf' := (hF'.encoded_parent_iff_d hM hC hT h.coords hF.inherited ⟨h.coords.below,Or.inl rfl⟩
    hEnc hc qf').mpr ⟨qf,hqfLast,hSQ,hMapQ⟩
  exact ⟨qf,qf',hSQ,hqfLast,hMapQ,hF'C,(hw.mem h.n_nat).transitive c hc qf'
    (parent_copy_strict_d hM hC hT h.coords hqfLast hMapQ hLastMap)⟩

/-- 活动层0的seam列：阻挡列是同块root副本，两者底值都等于源root底值。 -/
theorem Base.select_seam_high_d (hM : M.Models KP1Y.theory) (hC : C.Valid M) (hT : T.Valid M C)
    (h : Base M C T m V P H level index n OldTop NewTop Bottom R X Y A) {F F' P0 : M.Domain}
    (hF : Selects true M C m F V P) (hF' : FrameCopy.Copies M C T A F index n F')
    (hP0 : MemPair M Y.parents C.zero P0) (hZero : level=C.zero) {b c p : M.Domain}
    (hEnc : CopyCoordinates.Encode M C T A A.last b c) (hc : M.mem c n)
    (hPrefix : ∀ i, M.mem i c → ∀ a, MemPair M P0 i a ↔ RestrictedParent true M C n F' Bottom i a)
    (hCP : MemPair M P0 c p) : RestrictedParent true M C n F' Bottom c p := by
  have hw := omega_isOrdinal_d hM hC.omega
  obtain ⟨next,_,hSucc,_⟩ := CopyCoordinates.encode_seam_bms_d hM hC hT h.coords hEnc
  have hRootMapC := seam_root_copy_d hM hC hT h.coords hSucc hEnc
  have hPR := (h.root_copy_high_parent_d hM hC hT hZero hP0 hRootMapC hc).mp hCP
  have hLX : CopiedMountain.ParentAt M X C.zero A.last A.root := hZero ▸ (h.active_d hM hC).parent
  have hLP := (h.source_zero_iff hM A.last A.root).mp hLX
  obtain ⟨qf,qf',hSQ,hqfLast,hMapQ,hF'C,hqf'n⟩ := h.seam_frame_d hM hC hT hF hF' hEnc hc hLP
  have hSourcePath : A.root=qf ∨ Ancestor M C m P A.root qf := by
    classical
    by_cases hrq : A.root=qf
    · exact Or.inl hrq
    · obtain ⟨z,_,hPath,hZP,_⟩ := (selects_false_of_true hF h.rooted.positive).blocker_d hM hC hSQ hLP hrq
      have hRZ := ancestor_direct_d hM hC h.run.base.forest hZP
      rcases hPath with he | hA
      · exact Or.inr (he ▸ hRZ)
      · exact Or.inr (ancestor_trans_d hM hC h.run.base.forest hRZ hA)
  obtain ⟨z2,hMapZ⟩ := parent_copy_exists_d hM hC hT h.coords hEnc.2.1 h.coords.root
  have hNotLast : ¬M.mem A.last A.root := fun hl => SetTheory.KP.mem_irrefl_d (KP1Y.models_weakKP hM) A.root
    ((hw.mem h.coords.root).transitive A.last hl A.root h.coords.below)
  have hz2n : M.mem z2 n := (hw.mem h.n_nat).transitive c hc z2 (parent_copy_strict_d hM hC hT h.coords h.coords.below hMapZ
    ((CopyCoordinates.parent_copy_bad_iff hNotLast).mpr hEnc))
  have hZ2P := (h.root_copy_high_parent_d hM hC hT hZero hP0 hMapZ hz2n).mpr hPR
  have hPath : z2=qf' ∨ Ancestor M C n P0 z2 qf' := by
    rcases hSourcePath with he | hA
    · rw [← he] at hMapQ
      exact Or.inl (parent_copy_unique_d hM hC hT h.coords hMapZ hMapQ)
    · exact Or.inr (h.target_ancestor_d hM hC hT hP0 hA hqfLast hMapZ hMapQ hqf'n)
  refine h.blocker_close_d hM hC hT hF hF' hP0 hF'C hCP hPrefix hPath hZ2P ?_
  intro x y hX hY
  have hx := (h.root_copy_high_value_d hM hC hT hZero hRootMapC hc x).mp hX
  have hy := (h.root_copy_high_value_d hM hC hT hZero hMapZ hz2n y).mp hY
  exact Or.inl (h.run.base.values.unique A.root x y hx hy)

/-- 低活动层的seam列：直接父，或阻挡列的同块副本（数值序由低seam图层Key运输）。 -/
theorem Base.select_seam_low_d (hM : M.Models KP1Y.theory) (hC : C.Valid M) (hT : T.Valid M C)
    (h : Base M C T m V P H level index n OldTop NewTop Bottom R X Y A) {F F' P0 : M.Domain}
    (hF : Selects true M C m F V P) (hF' : FrameCopy.Copies M C T A F index n F')
    (hP0 : MemPair M Y.parents C.zero P0) (hLow : M.mem C.zero level) {b c p : M.Domain}
    (hEnc : CopyCoordinates.Encode M C T A A.last b c) (hc : M.mem c n)
    (hPrefix : ∀ i, M.mem i c → ∀ a, MemPair M P0 i a ↔ RestrictedParent true M C n F' Bottom i a)
    (hCP : MemPair M P0 c p) : RestrictedParent true M C n F' Bottom c p := by
  have hw := omega_isOrdinal_d hM hC.omega
  obtain ⟨p0,_,hP0X,hMapP⟩ := (CopiedMountain.Terminal.low_seam_parent_iff_d hM hC hT h.coords h.copies hEnc hc
    (h.level_nat hM hC) hLow).mp ((h.target_zero_iff hM hP0 c p).mpr hCP)
  have hLP := (h.source_zero_iff hM A.last p0).mp hP0X
  obtain ⟨qf,qf',hSQ,hqfLast,hMapQ,hF'C,hqf'n⟩ := h.seam_frame_d hM hC hT hF hF' hEnc hc hLP
  obtain ⟨hRow,_⟩ := h.bottom_numeric_d hM hC hT hP0
  classical
  by_cases hEq : p0=qf
  · subst hEq
    have he : qf'=p := parent_copy_unique_d hM hC hT h.coords hMapQ hMapP
    subst he
    exact ReconstructionSelection.restricted_parent_of_direct_d hM hC hRow hF'.forest hCP hF'C
  · obtain ⟨z,hzm,hPath,hZP,hValues⟩ := (selects_false_of_true hF h.rooted.positive).blocker_d hM hC hSQ hLP hEq
    have hzLast : M.mem z A.last := by
      rcases hPath with he | hA
      · exact he.symm ▸ hqfLast
      · exact (hw.mem h.coords.last).transitive qf hqfLast z hA.1
    have hzNat : M.mem z C.omega := hw.transitive m h.m_nat z hzm
    have hp0Z := h.run.base.forest.left z p0 hZP
    have hRootZ : M.mem A.root z := by
      rcases h.last_parent_bad_d hM hC hLP with he | hlt
      · exact he ▸ hp0Z
      · exact (hw.mem hzNat).transitive p0 hp0Z A.root hlt
    obtain ⟨vl,_,hVL⟩ := h.run.base.values.total A.last h.last_m
    obtain ⟨vz,_,hVZ⟩ := h.run.base.values.total z hzm
    have hLe := hValues vl vz hVL hVZ
    obtain ⟨z2,hMapZ⟩ := parent_copy_exists_d hM hC hT h.coords hEnc.2.1 hzNat
    have hNotLast : ¬M.mem A.last A.root := fun hl => SetTheory.KP.mem_irrefl_d (KP1Y.models_weakKP hM) A.root
      ((hw.mem h.coords.root).transitive A.last hl A.root h.coords.below)
    have hz2n : M.mem z2 n := (hw.mem h.n_nat).transitive c hc z2 (parent_copy_strict_d hM hC hT h.coords hzLast hMapZ
      ((CopyCoordinates.parent_copy_bad_iff hNotLast).mpr hEnc))
    have hZ2P := (h.nonroot_iff_d hM hC hT hP0 hRootZ hzLast hMapZ hz2n).mpr ⟨p0,hZP,hMapP⟩
    have hPath2 : z2=qf' ∨ Ancestor M C n P0 z2 qf' := by
      rcases hPath with he | hA
      · subst he
        exact Or.inl (parent_copy_unique_d hM hC hT h.coords hMapZ hMapQ)
      · exact Or.inr (h.target_ancestor_d hM hC hT hP0 hA hqfLast hMapZ hMapQ hqf'n)
    refine h.blocker_close_d hM hC hT hF hF' hP0 hF'C hCP hPrefix hPath2 hZ2P ?_
    intro x y hX hY
    exact h.seam_order_d hM hC hT hP0 hLow hRootZ hzLast hLP hZP hVL hVZ hLe hEnc hMapZ hc hz2n hX hY

end

end KP1Y.OneYFinite.TerminalBase
