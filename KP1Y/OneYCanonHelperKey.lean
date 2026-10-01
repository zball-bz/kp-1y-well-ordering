import KP1Y.OneYCanonHelperSetting
import KP1Y.OneYReconstructionOrder

/-! 目标重建网格中的第0行数值比较：共同第0行父项下，图层Key恰等价于底行数值弱序；
逐行父图与Top都相同的两列底值相等；无第0行父项的列底值为1。 -/
namespace KP1Y.OneYFinite.TerminalBase
open YesMetaZFC YesMetaZFC.SetTheory YesMetaZFC.SetTheory.Definitional
open KP1Y.Kuratowski KP1Y.Functions KP1Y.Naturals KP1Y.Bounded KP1Y.Arithmetic
open ReconstructionCanonical Reconstruction MountainReconstruction ReconstructionRecovery
universe u

theorem not_reverse_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {a b : M.Domain} (hb : M.mem b C.omega)
    (hLe : a=b ∨ M.mem a b) : ¬M.mem b a := by
  intro hba
  rcases hLe with he | hab
  · exact SetTheory.KP.mem_irrefl_d (KP1Y.models_weakKP hM) b (he ▸ hba)
  · exact SetTheory.KP.mem_irrefl_d (KP1Y.models_weakKP hM) b
      (((omega_isOrdinal_d hM hC.omega).mem hb).transitive a hab b hba)

theorem le_antisymm_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {a b : M.Domain} (hb : M.mem b C.omega)
    (h1 : a=b ∨ M.mem a b) (h2 : b=a ∨ M.mem b a) : a=b := by
  rcases h1 with he | hab
  · exact he
  · rcases h2 with he | hba
    · exact he.symm
    · exact False.elim (not_reverse_d hM hC hb (Or.inr hab) hba)

theorem same_addend_le_iff_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {Pairs Plus : M.Domain} (hPlus : AdditionTable M C Pairs Plus)
    {a b k x y : M.Domain} (hA : AddAt M Pairs Plus a k x) (hB : AddAt M Pairs Plus b k y) :
    (x=y ∨ M.mem x y) ↔ (a=b ∨ M.mem a b) := by
  have hAB := hA.bounds hM.1 hPlus
  have hBB := hB.bounds hM.1 hPlus
  have hSA := (hPlus.add_iff_sum hM hAB.1 hAB.2.1).mp hA
  have hSB := (hPlus.add_iff_sum hM hBB.1 hBB.2.1).mp hB
  constructor
  · intro hLe
    rcases (omega_isOrdinal_d hM hC.omega).wellOrder.linear.compare a hAB.1 b hBB.1 with he | hlt | hgt
    · exact Or.inl (hM.1.eq_of_same_members a b he)
    · exact Or.inr hlt
    · exact False.elim (not_reverse_d hM hC hBB.2.2 hLe
        (natural_sum_strict_left_d hM hC hBB.1 hAB.1 hAB.2.1 hSB hSA hgt))
  · rintro (he | hlt)
    · subst b
      exact Or.inl (hPlus.add_unique hM.1 hA hB)
    · exact Or.inr (natural_sum_strict_left_d hM hC hAB.1 hBB.1 hAB.2.1 hSA hSB hlt)

theorem depth_eq_of_parent_rows_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {m Q c z a b : M.Domain} (hQ : Forest M C.omega m Q)
    (hRows : ParentRowsEqual M Q c z) (hA : Depth M C m Q c a) (hB : Depth M C m Q z b) : a=b := by
  classical
  by_cases hSome : ∃ p, MemPair M Q c p
  · obtain ⟨p,hCP⟩ := hSome
    have hZP := (hRows p).mp hCP
    obtain ⟨e,hE⟩ := depth_exists_d hM hC hQ (hQ.bounds hM.1 hCP).2
    exact Structure.SuccessorOf.eq hM.1 (depth_parent_successor_d hM hC hQ hCP hA hE)
      (depth_parent_successor_d hM hC hQ hZP hB hE)
  · have hNoC : NoParent M m Q c := fun p _ hp => hSome ⟨p,hp⟩
    have hNoZ : NoParent M m Q z := fun p _ hp => hSome ⟨p,(hRows p).mpr hp⟩
    exact (depth_of_no_parent_d hM hC hQ hNoC hA).trans (depth_of_no_parent_d hM hC hQ hNoZ hB).symm

private theorem one_le_of_zero_mem_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {h : M.Domain} (hh : M.mem h C.omega) (h0 : M.mem C.zero h) :
    C.one=h ∨ M.mem C.one h := by
  have hw := omega_isOrdinal_d hM hC.omega
  apply ordinal_subset_cases_d hM (hw.mem hC.one_nat) (hw.mem hh)
  intro t ht
  rcases (hC.one_succ t).mp ht with h0' | he
  · exact False.elim (hC.zero_empty t h0')
  · exact (hM.1.eq_of_same_members t C.zero he).symm ▸ h0

section
variable {M : SetTheory.Structure.{u}} {C : ExpressionData M.Domain} {T : MatrixArithmetic M.Domain}
  {m V P H level index n OldTop NewTop Bottom : M.Domain} {R : RowStateSpace M.Domain}
  {X Y : CopiedMountain.Data M.Domain} {A : CopyCoordinates.Context M.Domain}

theorem Base.bottom_graph (h : Base M C T m V P H level index n OldTop NewTop Bottom R X Y A) :
    Graph M Bottom Y.width C.omega := h.rebuild.graph

/-- 共同第0行父项下：目标图层Key（自第1行起）等价于底行数值弱序。 -/
theorem Base.key_value_iff_d (hM : M.Models KP1Y.theory) (hC : C.Valid M) (hT : T.Valid M C)
    (h : Base M C T m V P H level index n OldTop NewTop Bottom R X Y A) {P0 : M.Domain}
    (hP0 : MemPair M Y.parents C.zero P0) {c z p tc tz x y : M.Domain}
    (hCP : MemPair M P0 c p) (hZP : MemPair M P0 z p) (hTC : MemPair M NewTop c tc) (hTZ : MemPair M NewTop z tz)
    (hX : MemPair M Bottom c x) (hY : MemPair M Bottom z y) :
    ForestOrder.KeyLE M C Y c z C.one tc tz ↔ (x=y ∨ M.mem x y) := by
  obtain ⟨B,Parents,G,hB,hParents,hG,hBottom⟩ := h.rebuild
  have hD := grid_valid_d hM hC h.target h.newTop.graph hT.add hB hParents
  have hForest := h.target.forest C.zero P0 hP0
  have hc : M.mem c Y.width := (hForest.bounds hM.1 hCP).1
  have hz : M.mem z Y.width := (hForest.bounds hM.1 hZP).1
  have hp : M.mem p Y.width := (hForest.bounds hM.1 hCP).2
  have hLive (a q : M.Domain) (hAQ : MemPair M P0 a q) (ha : M.mem a Y.width) :
      ∃ height, MemPair M Y.heights a height ∧ (C.one=height ∨ M.mem C.one height) := by
    obtain ⟨height,hh,hHeight⟩ := h.target.heights.total a ha
    have h0 : M.mem C.zero height :=
      (h.target.source C.zero a height hHeight).mp ⟨q,(h.target_zero_iff hM hP0 a q).mpr hAQ⟩
    exact ⟨height,hHeight,one_le_of_zero_mem_d hM hC hh h0⟩
  obtain ⟨x1,hX1⟩ := padded_cell_exists_d hM hD hG hC.one_nat hc
  obtain ⟨y1,hY1⟩ := padded_cell_exists_d hM hD hG hC.one_nat hz
  obtain ⟨hcH,hHC,hLiveC⟩ := hLive c p hCP hc
  obtain ⟨hzH,hHZ,hLiveZ⟩ := hLive z p hZP hz
  have hx1 : M.mem C.zero x1 := (hX1.positive_iff_d hM hD hG hHC hTC (h.newTop_positive_d hM hC c tc hTC)).mpr hLiveC
  have hy1 : M.mem C.zero y1 := (hY1.positive_iff_d hM hD hG hHZ hTZ (h.newTop_positive_d hM hC z tz hTZ)).mpr hLiveZ
  have hCommon : ReconstructionOrder.CommonParentsAt M Y C.zero c z :=
    ⟨P0,(h.target.parents.bounds hM.1 hP0).2,hP0,fun q =>
      ⟨fun hq => (hForest.unique c p q hCP hq) ▸ hZP,fun hq => (hForest.unique z p q hZP hq) ▸ hCP⟩⟩
  have hKey := ReconstructionOrder.key_iff_value_le_d hM hC hT.add h.target h.newTop.graph (h.newTop_positive_d hM hC)
    hB hParents hG (base := C.zero)
    (fun _ _ _ _ _ _ _ _ hSucc _ hW hF hQ => h.canonical_d hM hC hT hB hParents hG hW hF hQ hSucc)
    hC.zero_nat (Or.inl rfl) hC.one_succ hCommon hX1 hY1 hx1 hy1 hTC hTZ
  have hCell0 (a v : M.Domain) (hAv : MemPair M Bottom a v) :
      PaddedCell M (grid C Y NewTop T.addPairs T.plus B Parents) G C.zero a v :=
    ⟨hC.zero_nat,(hBottom.graph.bounds hM.1 hAv).1,Or.inl ((hBottom.rows a v).mp hAv)⟩
  obtain ⟨pv,hPV⟩ := padded_cell_exists_d hM hD hG hC.zero_nat hp
  have hParC : Reconstruction.ParentAt M (grid C Y NewTop T.addPairs T.plus B Parents) C.zero c p :=
    (grid_parent_iff_d hM hC h.target hB hParents).mpr ((h.target_zero_iff hM hP0 c p).mpr hCP)
  have hParZ : Reconstruction.ParentAt M (grid C Y NewTop T.addPairs T.plus B Parents) C.zero z p :=
    (grid_parent_iff_d hM hC h.target hB hParents).mpr ((h.target_zero_iff hM hP0 z p).mpr hZP)
  have hSumC := (hCell0 c x hX).parent_sum_d hM hD hG hParC hC.one_succ hX1 hPV
  have hSumZ := (hCell0 z y hY).parent_sum_d hM hD hG hParZ hC.one_succ hY1 hPV
  exact hKey.trans (same_addend_le_iff_d hM hC hT.add hSumC hSumZ).symm

/-- 第0行无父项的列：底值就是新Top读数。 -/
theorem Base.no_parent_top_d (hM : M.Models KP1Y.theory) (hC : C.Valid M) (hT : T.Valid M C)
    (h : Base M C T m V P H level index n OldTop NewTop Bottom R X Y A) {c x t : M.Domain}
    (hNone : ∀ p, ¬CopiedMountain.ParentAt M Y C.zero c p) (hX : MemPair M Bottom c x) (hTC : MemPair M NewTop c t) :
    x=t := by
  obtain ⟨B,Parents,G,hB,hParents,hG,hBottom⟩ := h.rebuild
  have hD := grid_valid_d hM hC h.target h.newTop.graph hT.add hB hParents
  have hc := (hBottom.graph.bounds hM.1 hX).1
  obtain ⟨height,hh,hHeight⟩ := h.target.heights.total c hc
  have hZero : height=C.zero := by
    apply Classical.byContradiction
    intro hne
    obtain ⟨p,hp⟩ := (h.target.source C.zero c height hHeight).mpr ((hC.zero_mem_iff hM hh).mpr hne)
    exact hNone p hp
  subst hZero
  exact ReconstructionOrder.padded_top_value_d hM hD hG ⟨hC.zero_nat,hc,Or.inl ((hBottom.rows c x).mp hX)⟩ hHeight hTC

/-- 第0行无父项的列底值为1（源对应列也是第0行根）。 -/
theorem Base.no_parent_one_d (hM : M.Models KP1Y.theory) (hC : C.Valid M) (hT : T.Valid M C)
    (h : Base M C T m V P H level index n OldTop NewTop Bottom R X Y A) {c x : M.Domain}
    (hNone : ∀ p, ¬CopiedMountain.ParentAt M Y C.zero c p) (hX : MemPair M Bottom c x) : x=C.one := by
  have hcY := (h.bottom_graph.bounds hM.1 hX).1
  obtain ⟨t,_,hTC⟩ := h.newTop.graph.total c hcY
  have hxt := h.no_parent_top_d hM hC hT hNone hX hTC
  subst hxt
  obtain ⟨hcn,src,_,b,_,hDec,hOld⟩ := (h.newTop.rows c x).mp hTC
  obtain ⟨height,hh,hHeight⟩ := h.target.heights.total c hcY
  have hZero : height=C.zero := by
    apply Classical.byContradiction
    intro hne
    obtain ⟨p,hp⟩ := (h.target.source C.zero c height hHeight).mpr ((hC.zero_mem_iff hM hh).mpr hne)
    exact hNone p hp
  subst hZero
  have hXH : MemPair M X.heights src C.zero :=
    (CopiedMountain.Terminal.height_at_decoded_iff_d hM hC hT h.coords hDec).mp ((h.copies.heights c C.zero).mp hHeight).2
  obtain ⟨height',_,hHeight',hValue⟩ := (h.oldTop.rows src x).mp hOld
  have he := h.source.heights.unique src height' C.zero hHeight' hXH
  subst he
  have hV := (h.run.value_initial_iff_d hM).mp hValue
  have hNo : NoParent M m P src := by
    intro p _ hP
    have hPX := (h.source_zero_iff hM src p).mpr hP
    obtain ⟨q,hq⟩ : ∃ q, CopiedMountain.ParentAt M X C.zero src q := ⟨p,hPX⟩
    exact hC.zero_empty C.zero ((h.source.source C.zero src C.zero hXH).mp ⟨q,hq⟩)
  exact h.rooted.rootsOne src x hV hNo

/-- 逐行父图与新Top都相同的两列，目标底值相同。 -/
theorem Base.twin_value_d (hM : M.Models KP1Y.theory) (hC : C.Valid M) (hT : T.Valid M C)
    (h : Base M C T m V P H level index n OldTop NewTop Bottom R X Y A) {c z : M.Domain}
    (hc : M.mem c Y.width) (hz : M.mem z Y.width)
    (hRows : ∀ r, M.mem r C.omega → ∀ p, CopiedMountain.ParentAt M Y r c p ↔ CopiedMountain.ParentAt M Y r z p)
    (hTops : ∀ v, MemPair M NewTop c v ↔ MemPair M NewTop z v) :
    ∀ v, MemPair M Bottom c v ↔ MemPair M Bottom z v := by
  obtain ⟨x,hx,hX⟩ := h.bottom_graph.total c hc
  obtain ⟨y,_,hY⟩ := h.bottom_graph.total z hz
  obtain ⟨t,_,hTC⟩ := h.newTop.graph.total c hc
  have hTZ := (hTops t).mp hTC
  suffices hxy : x=y by
    subst hxy
    intro v
    exact ⟨fun hv => h.bottom_graph.unique c x v hX hv ▸ hY,fun hv => h.bottom_graph.unique z x v hY hv ▸ hX⟩
  classical
  by_cases hSome : ∃ p, CopiedMountain.ParentAt M Y C.zero c p
  · obtain ⟨P0,_,hP0⟩ := h.target.parents.total C.zero hC.zero_nat
    obtain ⟨p,hp⟩ := hSome
    have hCP := (h.target_zero_iff hM hP0 c p).mp hp
    have hZP := (h.target_zero_iff hM hP0 z p).mp ((hRows C.zero hC.zero_nat p).mp hp)
    have hDepth (a b : M.Domain) : ForestOrder.DepthEqFrom M C Y a b C.one →
        ForestOrder.KeyLE M C Y a b C.one t t := fun hEq => Or.inr ⟨hEq,Or.inl rfl⟩
    have hEqFrom (a b : M.Domain) (hAB : ∀ r, M.mem r C.omega → ∀ p, CopiedMountain.ParentAt M Y r a p ↔
        CopiedMountain.ParentAt M Y r b p) : ForestOrder.DepthEqFrom M C Y a b C.one := by
      intro r hr _ da _ db _ hDA hDB
      obtain ⟨Q,_,hQ,hDepthA⟩ := hDA
      obtain ⟨Q',_,hQ',hDepthB⟩ := hDB
      have hQQ := h.target.parents.unique r Q' Q hQ' hQ
      subst Q'
      have hQRows : ParentRowsEqual M Q a b := by
        intro q
        constructor
        · intro hq
          obtain ⟨Q'',_,hQ'',hb⟩ := (hAB r hr q).mp ⟨Q,(h.target.parents.bounds hM.1 hQ).2,hQ,hq⟩
          exact h.target.parents.unique r Q'' Q hQ'' hQ ▸ hb
        · intro hq
          obtain ⟨Q'',_,hQ'',hb⟩ := (hAB r hr q).mpr ⟨Q,(h.target.parents.bounds hM.1 hQ).2,hQ,hq⟩
          exact h.target.parents.unique r Q'' Q hQ'' hQ ▸ hb
      exact depth_eq_of_parent_rows_d hM hC (h.target.forest r Q hQ) hQRows hDepthA hDepthB
    have h1 := (h.key_value_iff_d hM hC hT hP0 hCP hZP hTC hTZ hX hY).mp (hDepth c z (hEqFrom c z hRows))
    have h2 := (h.key_value_iff_d hM hC hT hP0 hZP hCP hTZ hTC hY hX).mp
      (hDepth z c (hEqFrom z c (fun r hr p => (hRows r hr p).symm)))
    exact le_antisymm_d hM hC (h.bottom_graph.bounds hM.1 hY).2 h1 h2
  · have hNoC : ∀ p, ¬CopiedMountain.ParentAt M Y C.zero c p := fun p hp => hSome ⟨p,hp⟩
    have hNoZ : ∀ p, ¬CopiedMountain.ParentAt M Y C.zero z p :=
      fun p hp => hSome ⟨p,(hRows C.zero hC.zero_nat p).mpr hp⟩
    exact (h.no_parent_top_d hM hC hT hNoC hX hTC).trans (h.no_parent_top_d hM hC hT hNoZ hY hTZ).symm

end

end KP1Y.OneYFinite.TerminalBase
