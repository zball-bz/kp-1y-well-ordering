import KP1Y.OneYExpansionOrderColumn
import KP1Y.OneYLowerCopy
import KP1Y.OneYTerminalCopy

/-! 单层第一接缝：原层X与实际复制层Y在x=last之前完全一致时，
普通层 Y(x)=X(y)，活动层 Y(x)+1=X(x)，下层把 +1 原样传下。只读本层实际重建网格。 -/
namespace KP1Y.OneYFinite.ExpansionOrder
open YesMetaZFC YesMetaZFC.SetTheory YesMetaZFC.SetTheory.Definitional
open KP1Y.Kuratowski KP1Y.Functions KP1Y.Naturals KP1Y.Bounded KP1Y.Arithmetic
open KP1Y.OneYFinite KP1Y.OneYFinite.CopyCoordinates
universe u

theorem add_zero_iff_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {Pairs Plus a b : M.Domain} (hPlus : AdditionTable M C Pairs Plus)
    (ha : M.mem a C.omega) : AddAt M Pairs Plus a C.zero b ↔ a=b := by
  have hZero := sum_zero_d hM a hC.zero_empty
  constructor
  · intro h
    exact sum_unique_d hM hZero ((hPlus.add_iff_sum hM ha hC.zero_nat).mp h)
  · intro he
    exact (hPlus.add_iff_sum hM ha hC.zero_nat).mpr (he ▸ hZero)

theorem add_one_iff_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {Pairs Plus a b : M.Domain} (hPlus : AdditionTable M C Pairs Plus)
    (ha : M.mem a C.omega) : AddAt M Pairs Plus a C.one b ↔ M.SuccessorOf b a := by
  have hZero := sum_zero_d hM a hC.zero_empty
  constructor
  · intro h
    exact sum_successor_d hM hC.one_succ hZero ((hPlus.add_iff_sum hM ha hC.one_nat).mp h)
  · intro hs
    obtain ⟨c,_,hSum⟩ := natural_sum_exists_d hM hC.omega ha hC.one_nat
    have hc := sum_successor_d hM hC.one_succ hZero hSum
    have hcb := Structure.SuccessorOf.eq hM.1 hc hs
    exact (hPlus.add_iff_sum hM ha hC.one_nat).mpr (hcb ▸ hSum)

/-- 同一层原山形 X 与复制山形 Y：x 之前的列高度、父图、顶部一致，且各自实际重建。 -/
structure LayerPair (M : SetTheory.Structure.{u}) (C : ExpressionData M.Domain) (T : MatrixArithmetic M.Domain)
    (A : CopyCoordinates.Context M.Domain) (X Y : CopiedMountain.Data M.Domain) (TopX TopY FX FY : M.Domain) : Prop where
  orig : X.Valid M C
  copy : Y.Valid M C
  last_orig : M.mem A.last X.width
  last_copy : M.mem A.last Y.width
  heights : ∀c, M.mem c A.last → ∀v, MemPair M Y.heights c v ↔ MemPair M X.heights c v
  parents : ∀c, M.mem c A.last → ∀r p, CopiedMountain.ParentAt M Y r c p ↔ CopiedMountain.ParentAt M X r c p
  top_orig : Graph M TopX X.width C.omega
  top_copy : Graph M TopY Y.width C.omega
  tops : RowsAgreeOn M TopX TopY A.last
  rebuild_orig : MountainReconstruction.Rebuilds M C T.addPairs T.plus X TopX FX
  rebuild_copy : MountainReconstruction.Rebuilds M C T.addPairs T.plus Y TopY FY

theorem LayerPair.grids_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {A : CopyCoordinates.Context M.Domain} (hA : A.Valid M C) {X Y : CopiedMountain.Data M.Domain} {TopX TopY FX FY : M.Domain}
    (h : LayerPair M C T A X Y TopX TopY FX FY) :
    ∃B P H B' P' H', Grid M C T.addPairs T.plus X TopX B P H ∧ Grid M C T.addPairs T.plus Y TopY B' P' H' ∧
      (∀c v, MemPair M FX c v ↔ GCell M C T.addPairs T.plus X TopX B P H c C.zero v) ∧
      (∀c v, MemPair M FY c v ↔ GCell M C T.addPairs T.plus Y TopY B' P' H' c C.zero v) ∧
      ∀p, M.mem p A.last → ∀hp r, MemPair M X.heights p hp → (r=hp ∨ M.mem r hp) → ∀b,
        (GCell M C T.addPairs T.plus X TopX B P H p r b ↔ GCell M C T.addPairs T.plus Y TopY B' P' H' p r b) := by
  obtain ⟨B,P,H,g,hFX⟩ := rebuilds_grid h.rebuild_orig
  obtain ⟨B',P',H',g',hFY⟩ := rebuilds_grid h.rebuild_copy
  have hw := omega_isOrdinal_d hM hC.omega
  refine ⟨B,P,H,B',P',H',g,g',hFX,hFY,?_⟩
  intro p hp hgt r hHeight hr b
  exact g.prefix_cells_d hM hC hT.add h.orig h.copy g' h.top_orig h.top_copy hA.last
    (fun c hc => (hw.mem h.orig.width).transitive A.last h.last_orig c hc)
    (fun c hc => (hw.mem h.copy.width).transitive A.last h.last_copy c hc)
    (fun c hc v => (h.heights c hc v).symm) h.tops (fun c hc r _ q => (h.parents c hc r q).symm) hp hHeight hr

private theorem zero_le_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {a : M.Domain} (ha : M.mem a C.omega) : C.zero=a ∨ M.mem C.zero a := by
  by_cases he : a=C.zero
  · exact .inl he.symm
  · exact .inr ((hC.zero_mem_iff hM ha).mpr he)

/-- 普通复制的第一接缝列x读取原root列的高度与父项（父项都在root左侧，不平移）。 -/
theorem ordinary_seam_column_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {A : CopyCoordinates.Context M.Domain} (hA : A.Valid M C) {X Y : CopiedMountain.Data M.Domain} {n : M.Domain}
    (hCopy : CopiedMountain.Ordinary.Copies M C T A X n Y) (hx : M.mem A.last n) :
    (∀v, MemPair M Y.heights A.last v ↔ MemPair M X.heights A.root v) ∧
      ∀r p, M.mem p A.root → CopiedMountain.ParentAt M X r A.root p → CopiedMountain.ParentAt M Y r A.last p := by
  obtain ⟨next,hNext,hDec⟩ := OrdinaryCoordinates.raw_seam_decoded_d hM hC hT hA hA.last hA.below (first_seam_d hM hC hT hA)
  refine ⟨fun v => (hCopy.heights A.last v).trans ⟨fun h => ?_,fun h => ⟨hx,A.root,hA.root,next,hDec.2.2.1,hDec,h⟩⟩,?_⟩
  · obtain ⟨_,s,_,b,_,hDec',hAt⟩ := h
    exact (hDec'.unique_d hM hC hT hA hDec).1 ▸ hAt
  · intro r p hp hP
    have hpω := (omega_isOrdinal_d hM hC.omega).transitive A.root hA.root p hp
    exact (hCopy.parents r A.last p).mpr ⟨hx,A.root,hA.root,next,hDec.2.2.1,p,hpω,hDec,hP,
      (parent_copy_good_iff hDec.2.2.1 hpω hp).mpr rfl⟩

/-- 普通层：复制层第一接缝列的重建底值等于原root列底值。 -/
theorem LayerPair.ordinary_seam_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {A : CopyCoordinates.Context M.Domain} (hA : A.Valid M C) {X Y : CopiedMountain.Data M.Domain} {TopX TopY FX FY n : M.Domain}
    (h : LayerPair M C T A X Y TopX TopY FX FY) (hCopy : CopiedMountain.Ordinary.Copies M C T A X n Y)
    (hTopSeam : ∀a b, MemPair M TopY A.last a → MemPair M TopX A.root b → a=b) :
    ∀a b, MemPair M FY A.last a → MemPair M FX A.root b → a=b := by
  have hw := omega_isOrdinal_d hM hC.omega
  obtain ⟨B,P,H,B',P',H',g,g',hFX,hFY,hCells⟩ := h.grids_d hM hC hT hA
  have hxn : M.mem A.last n := hCopy.width ▸ h.last_copy
  obtain ⟨hSeamH,hSeamP⟩ := ordinary_seam_column_d hM hC hT hA hCopy hxn
  have hyX : M.mem A.root X.width := (hw.mem h.orig.width).transitive A.last h.last_orig A.root hA.below
  obtain ⟨hgt,hgtω,hHy⟩ := h.orig.heights.total A.root hyX
  have hHx := (hSeamH hgt).mpr hHy
  obtain ⟨ty,_,hTy⟩ := h.top_orig.total A.root hyX
  obtain ⟨tx,txω,hTx⟩ := h.top_copy.total A.last h.last_copy
  have hShift := g.shift_d hM hC hT.add h.orig h.copy g' h.top_orig h.top_copy hHy hHx (.inl rfl) (.inl rfl)
    (zero_le_d hM hC hgtω) hC.zero_nat
    (by
      intro u u' hU hU'
      have hu := g.cell_unique hU (g.cell_top hM.1 h.orig h.top_orig hHy hTy)
      have hu' := g'.cell_unique hU' (g'.cell_top hM.1 h.copy h.top_copy hHx hTx)
      subst u
      subst u'
      exact (add_zero_iff_d hM hC hT.add txω).mpr (hTopSeam tx ty hTx hTy))
    (by
      intro r hr _
      obtain ⟨p,hP⟩ := (h.orig.source r A.root hgt hHy).mpr hr
      have hpy := (hP.bounds hM.1 h.orig).2.2.2
      refine ⟨p,p,hP,hSeamP r p hpy hP,fun b hB => ?_⟩
      obtain ⟨hp,_,hHp⟩ := h.orig.heights.total p (hP.bounds hM.1 h.orig).2.2.1
      exact (hCells p ((hw.mem hA.last).transitive A.root hA.below p hpy) hp r hHp
        (h.orig.endpoint r A.root p hp hP hHp) b).mp hB)
  intro a b hA' hB
  have hab := hShift b a ((hFX A.root b).mp hB) ((hFY A.last a).mp hA')
  exact (add_zero_iff_d hM hC hT.add (h.rebuild_copy.graph.bounds hM.1 hA').2).mp hab

/-- 下层（或任一保留x列几何的层）：顶部差一沿x列原样传到底行。 -/
theorem LayerPair.kept_seam_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {A : CopyCoordinates.Context M.Domain} (hA : A.Valid M C) {X Y : CopiedMountain.Data M.Domain} {TopX TopY FX FY : M.Domain}
    (h : LayerPair M C T A X Y TopX TopY FX FY)
    (hLastH : ∀v, MemPair M Y.heights A.last v ↔ MemPair M X.heights A.last v)
    (hLastP : ∀r p, CopiedMountain.ParentAt M Y r A.last p ↔ CopiedMountain.ParentAt M X r A.last p)
    (hTopSeam : ∀a b, MemPair M TopY A.last a → MemPair M TopX A.last b → M.SuccessorOf b a) :
    ∀a b, MemPair M FY A.last a → MemPair M FX A.last b → M.SuccessorOf b a := by
  have hw := omega_isOrdinal_d hM hC.omega
  obtain ⟨B,P,H,B',P',H',g,g',hFX,hFY,hCells⟩ := h.grids_d hM hC hT hA
  obtain ⟨hgt,hgtω,hHxX⟩ := h.orig.heights.total A.last h.last_orig
  have hHxY := (hLastH hgt).mpr hHxX
  obtain ⟨tX,_,hTX⟩ := h.top_orig.total A.last h.last_orig
  obtain ⟨tY,tYω,hTY⟩ := h.top_copy.total A.last h.last_copy
  have hShift := g.shift_d hM hC hT.add h.orig h.copy g' h.top_orig h.top_copy hHxX hHxY (.inl rfl) (.inl rfl)
    (zero_le_d hM hC hgtω) hC.one_nat
    (by
      intro u u' hU hU'
      have hu := g.cell_unique hU (g.cell_top hM.1 h.orig h.top_orig hHxX hTX)
      have hu' := g'.cell_unique hU' (g'.cell_top hM.1 h.copy h.top_copy hHxY hTY)
      subst u
      subst u'
      exact (add_one_iff_d hM hC hT.add tYω).mpr (hTopSeam tY tX hTY hTX))
    (by
      intro r hr _
      obtain ⟨p,hP⟩ := (h.orig.source r A.last hgt hHxX).mpr hr
      have hpx := (hP.bounds hM.1 h.orig).2.2.2
      refine ⟨p,p,hP,(hLastP r p).mpr hP,fun b hB => ?_⟩
      obtain ⟨hp,_,hHp⟩ := h.orig.heights.total p (hP.bounds hM.1 h.orig).2.2.1
      exact (hCells p hpx hp r hHp (h.orig.endpoint r A.last p hp hP hHp) b).mp hB)
  intro a b hA' hB
  exact (add_one_iff_d hM hC hT.add (h.rebuild_copy.graph.bounds hM.1 hA').2).mp
    (hShift b a ((hFX A.last b).mp hB) ((hFY A.last a).mp hA'))

theorem parent_copy_zero_iff_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {A : CopyCoordinates.Context M.Domain} (hA : A.Valid M C) {p q : M.Domain} (hp : M.mem p C.omega) :
    ParentCopy M C T A C.zero p q ↔ q=p := by
  classical
  by_cases hGood : M.mem p A.root
  · exact parent_copy_good_iff hC.zero_nat hp hGood
  · rw [parent_copy_bad_iff hGood]
    refine ⟨fun h => encode_unique hM.1 hT h (encode_zero_d hM hC hT hA hp),fun he => ?_⟩
    subst q
    exact encode_zero_d hM hC hT hA hp

/-- 活动层接缝列：高行读原root列（不平移），低行保留原x列父项。 -/
theorem terminal_seam_column_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {A : CopyCoordinates.Context M.Domain} (hA : A.Valid M C) {X Y : CopiedMountain.Data M.Domain} (hX : X.Valid M C)
    {level n : M.Domain} (hCopy : CopiedMountain.Terminal.Copies M C T A X level n Y) (hn : M.mem n C.omega) (hx : M.mem A.last n) :
    (∀v, MemPair M Y.heights A.last v ↔ MemPair M X.heights A.root v) ∧
      (∀r p, (level=r ∨ M.mem level r) → (CopiedMountain.ParentAt M Y r A.last p ↔ CopiedMountain.ParentAt M X r A.root p)) ∧
      (∀r p, ¬(level=r ∨ M.mem level r) → (CopiedMountain.ParentAt M Y r A.last p ↔ CopiedMountain.ParentAt M X r A.last p)) := by
  have hRaw := first_seam_d hM hC hT hA
  have hNot : ¬M.mem A.last A.last := SetTheory.KP.mem_irrefl_d (KP1Y.models_weakKP hM) A.last
  refine ⟨fun v => hCopy.seam_heights_d hM hC hT hA hn hx hNot hRaw,
    fun r p hHigh => hCopy.high_seam_parents_d hM hC hT hA hn hx hNot hRaw hHigh,?_⟩
  intro r q hLow
  rw [hCopy.parents r A.last q,CopiedMountain.Terminal.parent_raw_low_iff_d hM hC hT hA hA.last hNot hRaw
    (fun hh => hLow hh.2)]
  constructor
  · rintro ⟨_,p,hpω,hP,hCopyP⟩
    exact ((parent_copy_zero_iff_d hM hC hT hA hpω).mp hCopyP) ▸ hP
  · intro hP
    have hqω := (omega_isOrdinal_d hM hC.omega).transitive X.width hX.width q (hP.bounds hM.1 hX).2.2.1
    exact ⟨hx,q,hqω,hP,(parent_copy_zero_iff_d hM hC hT hA hqω).mpr rfl⟩

/-- 活动层：复制层第一接缝列底值加一等于原x列底值。坏根差一由原x列高度=level+1、
level行父为root、原上层x值为1读出。 -/
theorem LayerPair.terminal_seam_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {A : CopyCoordinates.Context M.Domain} (hA : A.Valid M C) {X Y : CopiedMountain.Data M.Domain} {TopX TopY FX FY level n : M.Domain}
    (h : LayerPair M C T A X Y TopX TopY FX FY) (hCopy : CopiedMountain.Terminal.Copies M C T A X level n Y)
    (hActive : CopiedMountain.Terminal.Active M X A level) (hTopOne : MemPair M TopX A.last C.one)
    (hTopSeam : ∀a b, MemPair M TopY A.last a → MemPair M TopX A.root b → a=b) :
    ∀a b, MemPair M FY A.last a → MemPair M FX A.last b → M.SuccessorOf b a := by
  have hw := omega_isOrdinal_d hM hC.omega
  obtain ⟨B,P,H,B',P',H',g,g',hFX,hFY,hCells⟩ := h.grids_d hM hC hT hA
  have hxn : M.mem A.last n := hCopy.width ▸ h.last_copy
  have hn : M.mem n C.omega := hCopy.width ▸ h.copy.width
  obtain ⟨hSeamH,hHigh,hLow⟩ := terminal_seam_column_d hM hC hT hA h.orig hCopy hn hxn
  have hyX : M.mem A.root X.width := (hw.mem h.orig.width).transitive A.last h.last_orig A.root hA.below
  obtain ⟨hgt,hgtω,hHy⟩ := h.orig.heights.total A.root hyX
  have hHxY := (hSeamH hgt).mpr hHy
  have hdle := hActive.root_height_ge h.orig hHy
  obtain ⟨hx1,hHxX,hx1s⟩ := hActive.lastHeight
  have hdω : M.mem level C.omega := (hActive.parent.bounds hM.1 h.orig).1
  obtain ⟨ty,_,hTy⟩ := h.top_orig.total A.root hyX
  obtain ⟨tx,txω,hTx⟩ := h.top_copy.total A.last h.last_copy
  -- 高段 [level,hgt]：新x列与原root列逐行同值
  have hHighShift := g.shift_d hM hC hT.add h.orig h.copy g' h.top_orig h.top_copy hHy hHxY (.inl rfl) (.inl rfl)
    hdle hC.zero_nat
    (by
      intro u u' hU hU'
      have hu := g.cell_unique hU (g.cell_top hM.1 h.orig h.top_orig hHy hTy)
      have hu' := g'.cell_unique hU' (g'.cell_top hM.1 h.copy h.top_copy hHxY hTx)
      subst u
      subst u'
      exact (add_zero_iff_d hM hC hT.add txω).mpr (hTopSeam tx ty hTx hTy))
    (by
      intro r hr hdr
      obtain ⟨p,hP⟩ := (h.orig.source r A.root hgt hHy).mpr hr
      have hpy := (hP.bounds hM.1 h.orig).2.2.2
      have hrω := hw.transitive hgt hgtω r hr
      refine ⟨p,p,hP,(hHigh r p (ordinal_subset_cases_d hM (hw.mem hdω) (hw.mem hrω) hdr)).mpr hP,fun b hB => ?_⟩
      obtain ⟨hp,_,hHp⟩ := h.orig.heights.total p (hP.bounds hM.1 h.orig).2.2.1
      exact (hCells p ((hw.mem hA.last).transitive A.root hA.below p hpy) hp r hHp
        (h.orig.endpoint r A.root p hp hP hHp) b).mp hB)
  -- 原x列在level行：值 = 1 + 原root列level行值
  obtain ⟨b0,b0ω,hB0⟩ := g.cell_exists_d hM hC h.orig hHy hdle
  obtain ⟨w,wω,hW⟩ := g.cell_exists_d hM hC h.orig hHxX (.inr hx1s.predecessor_mem)
  have hTopCell := g.cell_top hM.1 h.orig h.top_orig hHxX hTopOne
  have hBadAdd := g.parent_equation_d hM hC hT.add h.orig h.top_orig hHxX hActive.parent hx1s hW hTopCell hB0
  have hBadSum := natural_sum_comm_d hM hC hC.one_nat b0ω ((hT.add.add_iff_sum hM hC.one_nat b0ω).mp hBadAdd)
  have hWsucc : M.SuccessorOf w b0 := (add_one_iff_d hM hC hT.add b0ω).mp ((hT.add.add_iff_sum hM b0ω hC.one_nat).mpr hBadSum)
  -- 低段 [0,level]：同为x列，差一下传
  have hLowShift := g.shift_d hM hC hT.add h.orig h.copy g' h.top_orig h.top_copy hHxX hHxY
    (.inr hx1s.predecessor_mem) hdle (zero_le_d hM hC hdω) hC.one_nat
    (by
      intro u u' hU hU'
      have hu := g.cell_unique hU hW
      subst u
      have hu'b := (add_zero_iff_d hM hC hT.add (hU'.bounds hM.1).2).mp (hHighShift b0 u' hB0 hU')
      subst u'
      exact (add_one_iff_d hM hC hT.add b0ω).mpr hWsucc)
    (by
      intro r hr _
      have hrx1 : M.mem r hx1 := (hx1s r).mpr (.inl hr)
      obtain ⟨p,hP⟩ := (h.orig.source r A.last hx1 hHxX).mpr hrx1
      have hpx := (hP.bounds hM.1 h.orig).2.2.2
      have hNotHigh : ¬(level=r ∨ M.mem level r) := by
        rintro (he | hlt)
        · exact SetTheory.KP.mem_irrefl_d (KP1Y.models_weakKP hM) level (he ▸ hr)
        · exact SetTheory.KP.mem_irrefl_d (KP1Y.models_weakKP hM) level ((hw.mem hdω).transitive r hr level hlt)
      refine ⟨p,p,hP,(hLow r p hNotHigh).mpr hP,fun b hB => ?_⟩
      obtain ⟨hp,_,hHp⟩ := h.orig.heights.total p (hP.bounds hM.1 h.orig).2.2.1
      exact (hCells p hpx hp r hHp (h.orig.endpoint r A.last p hp hP hHp) b).mp hB)
  intro a b hA' hB
  exact (add_one_iff_d hM hC hT.add (h.rebuild_copy.graph.bounds hM.1 hA').2).mp
    (hLowShift b a ((hFX A.last b).mp hB) ((hFY A.last a).mp hA'))

end KP1Y.OneYFinite.ExpansionOrder
