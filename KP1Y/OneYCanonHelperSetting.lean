import KP1Y.OneYExpansionCanonical
import KP1Y.OneYFrameCopy
import KP1Y.OneYLowerValueTransport

/-! Terminal底行(k=K)出口的公共环境：与`ExpansionCanonical.terminal_rebuild_rows_d`完全相同的前提，
打包为一个命题结构；并导出源/目标第0行、前缀值、目标网格的规范逐行选择等基本读数。 -/
namespace KP1Y.OneYFinite.TerminalBase
open YesMetaZFC YesMetaZFC.SetTheory YesMetaZFC.SetTheory.Definitional
open KP1Y.Kuratowski KP1Y.Functions KP1Y.Naturals KP1Y.Bounded KP1Y.Arithmetic
open ReconstructionCanonical Reconstruction MountainReconstruction ReconstructionRecovery
universe u

/-- 公共前提块，字段逐一对应`terminal_rebuild_rows_d`的显式前提。 -/
structure Base (M : SetTheory.Structure.{u}) (C : ExpressionData M.Domain) (T : MatrixArithmetic M.Domain)
    (m V P H level index n OldTop NewTop Bottom : M.Domain) (R : RowStateSpace M.Domain)
    (X Y : CopiedMountain.Data M.Domain) (A : CopyCoordinates.Context M.Domain) : Prop where
  run : RowRun M C m R V P H
  rooted : RootedRow M C m V P
  source : X.Valid M C
  fromRun : CopiedMountain.FromRun M C m R V H X
  oldTop : TopValueGraph M C m R H X.heights OldTop
  coords : A.Valid M C
  lastWidth : M.SuccessorOf m A.last
  bad : RowBadAt M C R H level A.last A.root
  indexNat : M.mem index C.omega
  widthN : CopyCoordinates.Width M C T A index n
  target : Y.Valid M C
  copies : CopiedMountain.Terminal.Copies M C T A X level n Y
  newTop : CopiedTop M C T A OldTop Y.width NewTop
  rebuild : Rebuilds M C T.addPairs T.plus Y NewTop Bottom

section
variable {M : SetTheory.Structure.{u}} {C : ExpressionData M.Domain} {T : MatrixArithmetic M.Domain}
  {m V P H level index n OldTop NewTop Bottom : M.Domain} {R : RowStateSpace M.Domain}
  {X Y : CopiedMountain.Data M.Domain} {A : CopyCoordinates.Context M.Domain}

theorem Base.width_eq (h : Base M C T m V P H level index n OldTop NewTop Bottom R X Y A) : Y.width=n :=
  h.copies.width

theorem Base.active_d (hM : M.Models KP1Y.theory) (hC : C.Valid M)
    (h : Base M C T m V P H level index n OldTop NewTop Bottom R X Y A) :
    CopiedMountain.Terminal.Active M X A level := by
  have hBad' := h.bad
  obtain ⟨W,_,Q,_,hAt,hParent,_⟩ := hBad'
  have hP : CopiedMountain.ParentAt M X level A.last A.root :=
    (h.fromRun.parent_iff hM.1 h.source level A.last A.root).mpr ⟨W,Q,hAt,hParent⟩
  obtain ⟨height,_,hHeight⟩ := h.source.heights.total A.last (hP.bounds hM.1 h.source).2.1
  exact ⟨hP,height,hHeight,(row_bad_height_top_d hM hC h.run h.rooted h.fromRun.heights h.oldTop h.bad hHeight).1⟩

theorem Base.level_nat (hM : M.Models KP1Y.theory) (hC : C.Valid M)
    (h : Base M C T m V P H level index n OldTop NewTop Bottom R X Y A) : M.mem level C.omega :=
  ((h.active_d hM hC).parent.bounds hM.1 h.source).1

theorem Base.m_nat (h : Base M C T m V P H level index n OldTop NewTop Bottom R X Y A) : M.mem m C.omega :=
  h.run.space.width

theorem Base.n_nat (h : Base M C T m V P H level index n OldTop NewTop Bottom R X Y A) : M.mem n C.omega :=
  h.copies.width ▸ h.target.width

theorem Base.last_m (h : Base M C T m V P H level index n OldTop NewTop Bottom R X Y A) : M.mem A.last m :=
  h.lastWidth.predecessor_mem

/-- 源第0行父图恰是给定底行父森林P。 -/
theorem Base.source_zero_iff (hM : M.Models KP1Y.theory)
    (h : Base M C T m V P H level index n OldTop NewTop Bottom R X Y A) (c p : M.Domain) :
    CopiedMountain.ParentAt M X C.zero c p ↔ MemPair M P c p := by
  rw [h.fromRun.parent_iff hM.1 h.source]
  constructor
  · rintro ⟨U,F,hAt,hP⟩
    obtain ⟨_,hF⟩ := h.run.at_unique hM.1 hAt (h.run.initial_row_at_d hM)
    subst hF
    exact hP
  · intro hP
    exact ⟨V,P,h.run.initial_row_at_d hM,hP⟩

/-- 目标第0行父图读取。 -/
theorem Base.target_zero_iff (hM : M.Models KP1Y.theory)
    (h : Base M C T m V P H level index n OldTop NewTop Bottom R X Y A) {P0 : M.Domain}
    (hP0 : MemPair M Y.parents C.zero P0) (c p : M.Domain) :
    CopiedMountain.ParentAt M Y C.zero c p ↔ MemPair M P0 c p := by
  constructor
  · rintro ⟨F,_,hF,hP⟩
    exact h.target.parents.unique C.zero F P0 hF hP0 ▸ hP
  · intro hP
    exact ⟨P0,(h.target.parents.bounds hM.1 hP0).2,hP0,hP⟩

theorem Base.newTop_positive_d (hM : M.Models KP1Y.theory) (hC : C.Valid M)
    (h : Base M C T m V P H level index n OldTop NewTop Bottom R X Y A) :
    ∀ c v, MemPair M NewTop c v → M.mem C.zero v := by
  intro c v hAt
  obtain ⟨_,source,_,_,_,_,hOld⟩ := (h.newTop.rows c v).mp hAt
  obtain ⟨a,_,hVA⟩ := h.run.base.values.total source (h.oldTop.graph.bounds hM.1 hOld).1
  exact h.oldTop.positive_d hM hC h.run h.fromRun.heights hVA (h.rooted.positive source a hVA) hOld

/-- 目标底行的实际运行，第0行父森林就是给定的P0。 -/
theorem Base.bottom_run_d (hM : M.Models KP1Y.theory) (hC : C.Valid M) (hT : T.Valid M C)
    (h : Base M C T m V P H level index n OldTop NewTop Bottom R X Y A) {P0 : M.Domain}
    (hP0 : MemPair M Y.parents C.zero P0) :
    ∃ R' : RowStateSpace M.Domain, ∃ Run, RowRun M C n R' Bottom P0 Run ∧
      CopiedMountain.FromRun M C n R' Bottom Run Y ∧ TopValueGraph M C n R' Run Y.heights NewTop ∧
      (∀ c v, MemPair M Bottom c v → M.mem C.zero v) := by
  obtain ⟨R',P',Run,hRun,hFrom,hTopRun,hPos⟩ := ExpansionCanonical.terminal_rebuild_rows_d hM hC hT h.run h.rooted
    h.source h.fromRun h.oldTop h.coords h.lastWidth h.bad h.indexNat h.widthN h.target h.copies h.newTop h.rebuild
  have hP' : MemPair M Y.parents C.zero P' := (hFrom.parents C.zero P').mpr ⟨Bottom,hRun.initial_row_at_d hM⟩
  have he : P'=P0 := h.target.parents.unique C.zero P' P0 hP' hP0
  subst he
  rw [h.width_eq] at hRun hFrom hTopRun
  exact ⟨R',Run,hRun,hFrom,hTopRun,hPos⟩

theorem Base.bottom_numeric_d (hM : M.Models KP1Y.theory) (hC : C.Valid M) (hT : T.Valid M C)
    (h : Base M C T m V P H level index n OldTop NewTop Bottom R X Y A) {P0 : M.Domain}
    (hP0 : MemPair M Y.parents C.zero P0) :
    NumericRow M C n Bottom P0 ∧ ∀ c v, MemPair M Bottom c v → M.mem C.zero v := by
  obtain ⟨_,_,hRun,_,_,hPos⟩ := h.bottom_run_d hM hC hT hP0
  exact ⟨hRun.base,hPos⟩

theorem Base.nested_d (hM : M.Models KP1Y.theory) (hC : C.Valid M) (hT : T.Valid M C)
    (h : Base M C T m V P H level index n OldTop NewTop Bottom R X Y A) : CopiedMountain.Nested M C Y :=
  h.copies.nested_d hM hC hT h.coords h.source h.target h.run h.fromRun (h.active_d hM hC)

theorem Base.top_bound_d (hM : M.Models KP1Y.theory) (hC : C.Valid M) (hT : T.Valid M C)
    (h : Base M C T m V P H level index n OldTop NewTop Bottom R X Y A) :
    ReconstructionSelection.PseudoTopBound M C Y NewTop :=
  TerminalTopBound.terminal_pseudo_top_bound_d hM hC hT h.coords h.source h.target h.run h.fromRun h.rooted.positive
    h.oldTop (h.active_d hM hC) h.copies h.newTop

theorem Base.blockers_d (hM : M.Models KP1Y.theory) (hC : C.Valid M) (hT : T.Valid M C)
    (h : Base M C T m V P H level index n OldTop NewTop Bottom R X Y A) : DecoratedBlockers M C Y NewTop := by
  obtain ⟨Top',hTop',hBlocker⟩ := TerminalCanonical.row_bad_blocker_exists_d hM hC hT h.run h.rooted h.source h.fromRun
    h.oldTop h.coords h.lastWidth h.bad h.indexNat h.widthN h.target h.copies
  have he := (h.copies.width.symm ▸ hTop').unique hM.1 h.newTop
  subst Top'
  intro r s t F Q c q p hSucc hNext hF hQ hOld hNew hNe
  exact hBlocker r s t c q p Q hSucc hNext ⟨F,(h.target.parents.bounds hM.1 hF).2,hF,hOld⟩
    ⟨Q,(h.target.parents.bounds hM.1 hQ).2,hQ,hNew⟩ hQ hNe

/-- 目标重建网格的每一行都由上一行父森林规范选择得到。 -/
theorem Base.canonical_d (hM : M.Models KP1Y.theory) (hC : C.Valid M) (hT : T.Valid M C)
    (h : Base M C T m V P H level index n OldTop NewTop Bottom R X Y A) {B Parents G : M.Domain}
    (hB : SequenceBound M C Y.width Y.heights B) (hParents : Prefix M Parents Y.parents B Y.forests)
    (hG : Reconstructs M (grid C Y NewTop T.addPairs T.plus B Parents) G)
    {r s W F Q : M.Domain} (hW : RowValues M (grid C Y NewTop T.addPairs T.plus B Parents) G s W)
    (hF : MemPair M Y.parents r F) (hQ : MemPair M Y.parents s Q) (hSucc : M.SuccessorOf s r) :
    Selects true M C Y.width F W Q :=
  structural_reconstruction_selects_d hM hC hT.add h.target h.newTop.graph (h.newTop_positive_d hM hC) hB hParents hG
    (h.nested_d hM hC hT) (h.top_bound_d hM hC hT) (h.blockers_d hM hC hT) hW hF hQ hSucc

theorem Base.last_subset_d (hM : M.Models KP1Y.theory) (hC : C.Valid M) (hT : T.Valid M C)
    (h : Base M C T m V P H level index n OldTop NewTop Bottom R X Y A) : M.MemberSubset A.last n := by
  obtain ⟨_,_,off,hOff,_,hAdd⟩ := h.widthN
  exact sum_base_subset_d hM ((omega_isOrdinal_d hM hC.omega).mem h.coords.last)
    ((hT.add.add_iff_sum hM h.coords.last hOff).mp hAdd)

/-- 源末列以前的目标底行数值与源底行完全相同。 -/
theorem Base.prefix_values_d (hM : M.Models KP1Y.theory) (hC : C.Valid M) (hT : T.Valid M C)
    (h : Base M C T m V P H level index n OldTop NewTop Bottom R X Y A) : RowsAgreeOn M Bottom V A.last := by
  have hw := omega_isOrdinal_d hM hC.omega
  have hOldRebuild := rebuild_original_d hM hC hT.add h.run h.rooted.positive h.source h.fromRun h.oldTop
  have hOldGraph : Graph M OldTop X.width C.omega := h.fromRun.width.symm ▸ h.oldTop.graph
  have hKept : M.MemberSubset A.last Y.width := h.copies.width.symm ▸ h.last_subset_d hM hC hT
  have hOldKept : M.MemberSubset A.last X.width :=
    fun c hc => (hw.mem h.source.width).transitive A.last (h.fromRun.width.symm ▸ h.last_m) c hc
  exact h.rebuild.prefix_d hM hC hT.add h.target h.source h.newTop.graph hOldGraph h.coords.last hKept hOldKept
    (fun c hc v => h.copies.original_heights_d hM hC hT h.coords (h.copies.width ▸ hKept c hc) hc)
    (fun c hc v => h.newTop.prefix_iff_d hM hC hT h.coords (hKept c hc) hc)
    (fun c hc r _ p => h.copies.original_parents_d hM hC h.coords (h.copies.width ▸ hKept c hc) hc) hOldRebuild

/-- 非root副本列的目标第0行父项是源父项的同块ParentCopy像。 -/
theorem Base.nonroot_iff_d (hM : M.Models KP1Y.theory) (hC : C.Valid M) (hT : T.Valid M C)
    (h : Base M C T m V P H level index n OldTop NewTop Bottom R X Y A) {P0 s b c p : M.Domain}
    (hP0 : MemPair M Y.parents C.zero P0) (hs : M.mem A.root s) (hsx : M.mem s A.last)
    (hMap : CopyCoordinates.ParentCopy M C T A b s c) (hc : M.mem c n) :
    MemPair M P0 c p ↔ ∃ q, MemPair M P s q ∧ CopyCoordinates.ParentCopy M C T A b q p := by
  have hNonroot : s≠A.root := fun he => SetTheory.KP.mem_irrefl_d (KP1Y.models_weakKP hM) A.root (he ▸ hs)
  rw [← h.target_zero_iff hM hP0 c p,h.copies.parents C.zero c p,
    CopiedMountain.Terminal.parent_parent_copy_nonroot_d hM hC hT h.coords h.source hsx hNonroot hMap]
  constructor
  · rintro ⟨_,q,_,hq,hMapQ⟩
    exact ⟨q,(h.source_zero_iff hM s q).mp hq,hMapQ⟩
  · rintro ⟨q,hq,hMapQ⟩
    exact ⟨hc,q,hMapQ.1,(h.source_zero_iff hM s q).mpr hq,hMapQ⟩

end

/-- H2：非root副本行0父项（`Base`外部的逐字前提形式）。 -/
theorem terminal_base_nonroot_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
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
    {P0 s b c p : M.Domain} (hP0 : MemPair M Y.parents C.zero P0)
    (hs : M.mem A.root s) (hsx : M.mem s A.last) (hMap : CopyCoordinates.ParentCopy M C T A b s c) (hc : M.mem c n) :
    MemPair M P0 c p ↔ ∃ q, MemPair M P s q ∧ CopyCoordinates.ParentCopy M C T A b q p :=
  (Base.mk hRun hBase hX hFrom hOldTop hA hWidth hBad hIndex hN hY hCopy hTop hRebuild).nonroot_iff_d hM hC hT hP0 hs hsx hMap hc


end KP1Y.OneYFinite.TerminalBase
