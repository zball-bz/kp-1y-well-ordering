import KP1Y.OneYActiveFrameTransport
import KP1Y.OneYNumericDecoratedOrder

/-! 待重建CopiedMountain的图层Key：只使用真实全ω父行图，不假设它已是Numeric RowRun。 -/
namespace KP1Y.OneYFinite.ForestOrder
open YesMetaZFC YesMetaZFC.SetTheory YesMetaZFC.SetTheory.Definitional
open KP1Y.Kuratowski KP1Y.Functions KP1Y.Naturals KP1Y.Bounded KP1Y.Arithmetic
open KP1Y.OneYFinite
universe u

def DepthAt (M : SetTheory.Structure.{u}) (C : ExpressionData M.Domain) (X : CopiedMountain.Data M.Domain) (c r d : M.Domain) : Prop :=
  ∃ Q, M.mem Q X.forests ∧ MemPair M X.parents r Q ∧ Depth M C X.width Q c d

def DepthEqAt (M : SetTheory.Structure.{u}) (C : ExpressionData M.Domain) (X : CopiedMountain.Data M.Domain) (c z r : M.Domain) : Prop :=
  ∀ a, M.mem a C.omega → ∀ b, M.mem b C.omega → DepthAt M C X c r a → DepthAt M C X z r b → a=b

def DepthLtAt (M : SetTheory.Structure.{u}) (C : ExpressionData M.Domain) (X : CopiedMountain.Data M.Domain) (c z r : M.Domain) : Prop :=
  ∃ a, M.mem a C.omega ∧ ∃ b, M.mem b C.omega ∧ DepthAt M C X c r a ∧ DepthAt M C X z r b ∧ M.mem a b

def DepthEqFrom (M : SetTheory.Structure.{u}) (C : ExpressionData M.Domain) (X : CopiedMountain.Data M.Domain) (c z start : M.Domain) : Prop :=
  ∀ r, M.mem r C.omega → start=r ∨ M.mem start r → DepthEqAt M C X c z r

def DepthLtFrom (M : SetTheory.Structure.{u}) (C : ExpressionData M.Domain) (X : CopiedMountain.Data M.Domain) (c z start : M.Domain) : Prop :=
  ∃ r, M.mem r C.omega ∧ (start=r ∨ M.mem start r) ∧
    (∀ q, M.mem q r → start=q ∨ M.mem start q → DepthEqAt M C X c z q) ∧ DepthLtAt M C X c z r

def KeyLE (M : SetTheory.Structure.{u}) (C : ExpressionData M.Domain) (X : CopiedMountain.Data M.Domain) (c z start topC topZ : M.Domain) : Prop :=
  DepthLtFrom M C X c z start ∨ (DepthEqFrom M C X c z start ∧ (topC=topZ ∨ M.mem topC topZ))

theorem depth_at_row_iff {M : SetTheory.Structure.{u}} (he : Extensional M) {C : ExpressionData M.Domain}
    {X : CopiedMountain.Data M.Domain} (hX : X.Valid M C) {r Q : M.Domain} (hQ : MemPair M X.parents r Q) (c d : M.Domain) :
    DepthAt M C X c r d ↔ Depth M C X.width Q c d := by
  constructor
  · rintro ⟨F,_,hF,hDepth⟩
    exact hX.parents.unique r F Q hF hQ ▸ hDepth
  · intro hDepth
    exact ⟨Q,(hX.parents.bounds he hQ).2,hQ,hDepth⟩

theorem from_run_depth_iff_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {m V P H : M.Domain} {R : RowStateSpace M.Domain}
    (hRun : RowRun M C m R V P H) {X : CopiedMountain.Data M.Domain} (hX : X.Valid M C)
    (hFrom : CopiedMountain.FromRun M C m R V H X) (c r d : M.Domain) :
    DepthAt M C X c r d ↔ NumericOrder.DepthAt M C m R H c r d := by
  constructor
  · rintro ⟨Q,_,hQ,hDepth⟩
    obtain ⟨W,hAt⟩ := (hFrom.parents r Q).mp hQ
    exact (NumericOrder.depth_at_iff_d hM hC hRun hAt c d).mpr (hFrom.width ▸ hDepth)
  · rintro ⟨W,_,Q,_,hAt,hDepth⟩
    have hQ := (hFrom.parents r Q).mpr ⟨W,hAt⟩
    exact ⟨Q,(hX.parents.bounds hM.1 hQ).2,hQ,hFrom.width.symm ▸ hDepth⟩

theorem from_run_key_iff_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {m V P H : M.Domain} {R : RowStateSpace M.Domain}
    (hRun : RowRun M C m R V P H) {X : CopiedMountain.Data M.Domain} (hX : X.Valid M C)
    (hFrom : CopiedMountain.FromRun M C m R V H X) (c z start topC topZ : M.Domain) :
    KeyLE M C X c z start topC topZ ↔ NumericOrder.KeyLE M C m R H c z start topC topZ := by
  simp only [KeyLE,DepthLtFrom,DepthEqFrom,DepthLtAt,DepthEqAt,from_run_depth_iff_d hM hC hRun hX hFrom,
    NumericOrder.KeyLE,NumericOrder.DepthLtFrom,NumericOrder.DepthEqFrom,NumericOrder.DepthLtAt,NumericOrder.DepthEqAt]

private theorem offset_map_exists_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {offset : M.Domain} (hOffset : M.mem offset C.omega) :
    ∃ J, ColumnEmbedding M C.omega C.omega J ∧ ∀ r q, MemPair M J r q ↔ AddAt M T.addPairs T.plus offset r q := by
  obtain ⟨J,hJ,hRows⟩ := CopyCoordinates.global_shift_map_exists_d hM hC hT hC.zero_nat hOffset
  refine ⟨J,hJ,?_⟩
  intro r q
  constructor
  · intro hAt
    obtain ⟨hr,⟨hBad,_⟩ | ⟨_,hAdd⟩⟩ := (hRows r q).mp hAt
    · exact False.elim (hC.zero_empty r hBad)
    · exact (hT.add.add_iff_sum hM hOffset hr).mpr
        (natural_sum_comm_d hM hC hr hOffset ((hT.add.add_iff_sum hM hr hOffset).mp hAdd))
  · intro hAdd
    have hr := (hAdd.bounds hM.1 hT.add).2.1
    have hAdd' := (hT.add.add_iff_sum hM hr hOffset).mpr
      (natural_sum_comm_d hM hC hOffset hr ((hT.add.add_iff_sum hM hOffset hr).mp hAdd))
    exact (hRows r q).mpr ⟨hr,Or.inr ⟨hC.zero_empty r,hAdd'⟩⟩

private theorem embedding_order_iff_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {J i j x y : M.Domain}
    (hJ : ColumnEmbedding M C.omega C.omega J) (hI : MemPair M J i x) (hJJ : MemPair M J j y) :
    (x=y ↔ i=j) ∧ (M.mem x y ↔ M.mem i j) := by
  have hw := omega_isOrdinal_d hM hC.omega
  obtain ⟨hi,hx⟩ := hJ.graph.bounds hM.1 hI
  obtain ⟨hj,hy⟩ := hJ.graph.bounds hM.1 hJJ
  have hEq : x=y ↔ i=j := by
    constructor
    · intro he
      rcases hw.wellOrder.linear.compare i hi j hj with hEq | hlt | hgt
      · exact hM.1.eq_of_same_members i j hEq
      · exact False.elim (SetTheory.KP.mem_irrefl_d (KP1Y.models_weakKP hM) y (he ▸ hJ.strict i hi j hj hlt x y hI hJJ))
      · exact False.elim (SetTheory.KP.mem_irrefl_d (KP1Y.models_weakKP hM) y (he ▸ hJ.strict j hj i hi hgt y x hJJ hI))
    · intro he
      subst j
      exact hJ.graph.unique i x y hI hJJ
  refine ⟨hEq,?_,fun hlt => hJ.strict i hi j hj hlt x y hI hJJ⟩
  intro hxy
  rcases hw.wellOrder.linear.compare i hi j hj with he | hlt | hgt
  · have heq := hEq.mpr (hM.1.eq_of_same_members i j he)
    exact False.elim (SetTheory.KP.mem_irrefl_d (KP1Y.models_weakKP hM) y (heq ▸ hxy))
  · exact hlt
  · have hyx := hJ.strict j hj i hi hgt y x hJJ hI
    exact False.elim (SetTheory.KP.mem_irrefl_d (KP1Y.models_weakKP hM) y ((hw.mem hy).transitive x hxy y hyx))

/-- 图层Depth后缀/独立Top与实际矩阵装饰列双向对应；目标图无需是Numeric RowRun。 -/
theorem key_columns_iff_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {X : CopiedMountain.Data M.Domain} {B : FiniteMatrix M.Domain} {offset c z start physical topC topZ : M.Domain}
    (hOffset : M.mem offset C.omega) (hStart : M.mem start C.omega)
    (hShift : AddAt M T.addPairs T.plus offset start physical)
    (hReadC : ∀ r, M.mem r C.omega → ∀ q, AddAt M T.addPairs T.plus offset r q → ∀ d, PaddedEntry M C.zero B q c d ↔ DepthAt M C X c r d)
    (hReadZ : ∀ r, M.mem r C.omega → ∀ q, AddAt M T.addPairs T.plus offset r q → ∀ d, PaddedEntry M C.zero B q z d ↔ DepthAt M C X z r d) :
    KeyLE M C X c z start topC topZ ↔ DecoratedColumnLeFrom M C B B c z physical topC topZ := by
  have hw := omega_isOrdinal_d hM hC.omega
  obtain ⟨J,hJ,hRows⟩ := offset_map_exists_d hM hC hT hOffset
  have hJStart := (hRows start physical).mpr hShift
  have hRange (q : M.Domain) (hq : M.mem q C.omega) (hLe : physical=q ∨ M.mem physical q) :
      ∃ r, M.mem r C.omega ∧ MemPair M J r q ∧ (start=r ∨ M.mem start r) := by
    have hBaseSub := sum_base_subset_d hM (hw.mem hOffset) ((hT.add.add_iff_sum hM hOffset hStart).mp hShift)
    have hOffsetQ : M.MemberSubset offset q := by
      intro x hx
      rcases hLe with he | hlt
      · exact he ▸ hBaseSub x hx
      · exact (hw.mem hq).transitive physical hlt x (hBaseSub x hx)
    obtain ⟨r,hr,hDiff⟩ := truncated_difference_exists_d hM hC hq hOffset
    have hSum := truncated_difference_add_inverse_d hM hC hDiff (ordinal_subset_cases_d hM (hw.mem hOffset) (hw.mem hq) hOffsetQ)
    have hAt := (hRows r q).mpr ((hT.add.add_iff_sum hM hOffset hr).mpr hSum)
    have hOrder := embedding_order_iff_d hM hC hJ hJStart hAt
    exact ⟨r,hr,hAt,hLe.imp hOrder.1.mp hOrder.2.mp⟩
  have hEq (r q : M.Domain) (hAt : MemPair M J r q) : DepthEqAt M C X c z r ↔ ColumnEqAt M C.omega C.zero B B c z q := by
    have hr := (hJ.graph.bounds hM.1 hAt).1
    have hAdd := (hRows r q).mp hAt
    constructor
    · intro hEq x hx y hy hX hY
      exact hEq x hx y hy ((hReadC r hr q hAdd x).mp hX) ((hReadZ r hr q hAdd y).mp hY)
    · intro hEq x hx y hy hX hY
      exact hEq x hx y hy ((hReadC r hr q hAdd x).mpr hX) ((hReadZ r hr q hAdd y).mpr hY)
  have hLt (r q : M.Domain) (hAt : MemPair M J r q) : DepthLtAt M C X c z r ↔ ColumnLtAt M C.omega C.zero B B c z q := by
    have hr := (hJ.graph.bounds hM.1 hAt).1
    have hAdd := (hRows r q).mp hAt
    constructor
    · rintro ⟨x,hx,y,hy,hX,hY,hxy⟩
      exact ⟨x,hx,y,hy,(hReadC r hr q hAdd x).mpr hX,(hReadZ r hr q hAdd y).mpr hY,hxy⟩
    · rintro ⟨x,hx,y,hy,hX,hY,hxy⟩
      exact ⟨x,hx,y,hy,(hReadC r hr q hAdd x).mp hX,(hReadZ r hr q hAdd y).mp hY,hxy⟩
  have hEqFrom : DepthEqFrom M C X c z start ↔ ColumnEqFrom M C.omega C.zero B B c z physical := by
    constructor
    · intro hEqF q hq hPhysicalQ
      obtain ⟨r,hr,hAt,hStartR⟩ := hRange q hq hPhysicalQ
      exact (hEq r q hAt).mp (hEqF r hr hStartR)
    · intro hEqF r hr hStartR
      obtain ⟨q,hq,hAt⟩ := hJ.graph.total r hr
      have hOrder := embedding_order_iff_d hM hC hJ hJStart hAt
      exact (hEq r q hAt).mpr (hEqF q hq (hStartR.imp hOrder.1.mpr hOrder.2.mpr))
  have hLtFrom : DepthLtFrom M C X c z start ↔ ColumnLtFrom M C.omega C.zero B B c z physical := by
    constructor
    · rintro ⟨r,hr,hStartR,hBefore,hLess⟩
      obtain ⟨q,hq,hAt⟩ := hJ.graph.total r hr
      have hOrder := embedding_order_iff_d hM hC hJ hJStart hAt
      refine ⟨q,hq,hStartR.imp hOrder.1.mpr hOrder.2.mpr,?_,(hLt r q hAt).mp hLess⟩
      intro p hp hPhysicalP
      obtain ⟨i,hi,hIP,hStartI⟩ := hRange p (hw.transitive q hq p hp) hPhysicalP
      exact (hEq i p hIP).mp (hBefore i ((embedding_order_iff_d hM hC hJ hIP hAt).2.mp hp) hStartI)
    · rintro ⟨q,hq,hPhysicalQ,hBefore,hLess⟩
      obtain ⟨r,hr,hAt,hStartR⟩ := hRange q hq hPhysicalQ
      refine ⟨r,hr,hStartR,?_,(hLt r q hAt).mpr hLess⟩
      intro i hi hStartI
      obtain ⟨p,hp,hIP⟩ := hJ.graph.total i (hw.transitive r hr i hi)
      have hOrderStart := embedding_order_iff_d hM hC hJ hJStart hIP
      exact (hEq i p hIP).mpr (hBefore p ((embedding_order_iff_d hM hC hJ hIP hAt).2.mpr hi)
        (hStartI.imp hOrderStart.1.mpr hOrderStart.2.mpr))
  exact or_congr hLtFrom (and_congr hEqFrom Iff.rfl)

/-- 原实际数值山形的图层Key与它构造的规范活动帧列双向对应。 -/
theorem source_frame_key_iff_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {m V P H : M.Domain} {R : RowStateSpace M.Domain} (hRun : RowRun M C m R V P H)
    {Frame : ActiveFrame M.Domain} (hFrame : Frame.Valid M C T m P H R) (hCap : FrameValueCap M V Frame.cap)
    {B : FiniteMatrix M.Domain} (hTrim : TrimmedMatrix M C (Frame.raw m) B)
    {X : CopiedMountain.Data M.Domain} (hX : X.Valid M C) (hFrom : CopiedMountain.FromRun M C m R V H X)
    {c z start physical topC topZ : M.Domain} (hc : M.mem c m) (hz : M.mem z m) (hStart : M.mem start C.omega)
    (hShift : AddAt M T.addPairs T.plus Frame.frame.height start physical) :
    KeyLE M C X c z start topC topZ ↔ DecoratedColumnLeFrom M C B B c z physical topC topZ := by
  have hRead (c : M.Domain) (hc : M.mem c m) (r : M.Domain) (hr : M.mem r C.omega) (q : M.Domain)
      (hAdd : AddAt M T.addPairs T.plus Frame.frame.height r q) (d : M.Domain) :
      PaddedEntry M C.zero B q c d ↔ DepthAt M C X c r d := by
    obtain ⟨W,Q,hAt⟩ := hRun.at_exists_d hr
    exact (hFrame.normalized_entry_all_d hM hC hT hRun hCap hTrim hr hAdd hAt hc).trans
      ((from_run_depth_iff_d hM hC hRun hX hFrom c r d).trans (NumericOrder.depth_at_iff_d hM hC hRun hAt c d)).symm
  exact key_columns_iff_d hM hC hT (natural_successor_mem_d hM hC hRun.space.width hFrame.frame.height) hStart hShift (hRead c hc) (hRead z hz)

/-- 实际Terminal复制图的Key与真实展开活动帧列双向对应；不要求目标复制图是Numeric RowRun。 -/
theorem expanded_terminal_key_iff_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {m V P H L : M.Domain} {R : RowStateSpace M.Domain} (hRun : RowRun M C m R V P H)
    {Frame : ActiveFrame M.Domain} (hFrame : Frame.Valid M C T m P H R) (hCap : FrameValueCap M V Frame.cap)
    (hFrameRaw : MatrixParentRun M C m Frame.height Frame.cells Frame.values R.forests Frame.rows L)
    {B D : FiniteMatrix M.Domain} (hTrim : TrimmedMatrix M C (Frame.raw m) B) {BF BR BL DF DR DL : M.Domain}
    (hBRun : MatrixParentRun M C B.width B.height B.cells B.values BF BR BL)
    (hDRun : MatrixParentRun M C D.width D.height D.cells D.values DF DR DL)
    {X Y : CopiedMountain.Data M.Domain} (hX : X.Valid M C) (hFrom : CopiedMountain.FromRun M C m R V H X)
    {A : CopyCoordinates.Context M.Domain} (hA : A.Valid M C) {level active index c z start physical topC topZ : M.Domain}
    (hLevel : M.mem level C.omega) (hActive : AddAt M T.addPairs T.plus Frame.frame.height level active)
    (hContext : MatrixExpansionContext M C B BF BR A.last active A.root)
    (hIndex : M.mem index C.omega) (hExpansion : MatrixExpansion M C B T BF BR index D)
    (hY : Y.Valid M C) (hCopy : CopiedMountain.Terminal.Copies M C T A X level D.width Y)
    (hc : M.mem c D.width) (hz : M.mem z D.width) (hStart : M.mem start C.omega)
    (hShift : AddAt M T.addPairs T.plus Frame.frame.height start physical) :
    KeyLE M C Y c z start topC topZ ↔ DecoratedColumnLeFrom M C D D c z physical topC topZ := by
  have hRead (c : M.Domain) (hc : M.mem c D.width) (r : M.Domain) (hr : M.mem r C.omega) (q : M.Domain)
      (hAdd : AddAt M T.addPairs T.plus Frame.frame.height r q) (d : M.Domain) :
      PaddedEntry M C.zero D q c d ↔ DepthAt M C Y c r d := by
    obtain ⟨Q,_,hQ⟩ := hY.parents.total r hr
    exact (ActiveFrameTransport.expanded_terminal_depth_d hM hC hT hRun hFrame hCap hFrameRaw hTrim hBRun hDRun hX hFrom hA
      hLevel hActive hContext hIndex hExpansion hY hCopy hQ hAdd hc).trans (depth_at_row_iff hM.1 hY hQ c d).symm
  exact key_columns_iff_d hM hC hT (natural_successor_mem_d hM hC hRun.space.width hFrame.frame.height) hStart hShift (hRead c hc) (hRead z hz)

private theorem previous_rows_equal_from_numeric_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {m V P H L : M.Domain} {R : RowStateSpace M.Domain} (hRun : RowRun M C m R V P H)
    {Frame : ActiveFrame M.Domain} (hFrame : Frame.Valid M C T m P H R) (hCap : FrameValueCap M V Frame.cap)
    (hFrameRaw : MatrixParentRun M C m Frame.height Frame.cells Frame.values R.forests Frame.rows L)
    {B : FiniteMatrix M.Domain} (hTrim : TrimmedMatrix M C (Frame.raw m) B) {BF BR BL : M.Domain}
    (hBRun : MatrixParentRun M C B.width B.height B.cells B.values BF BR BL)
    {u start physical U F c z : M.Domain} (hu : M.mem u C.omega) (hs : M.SuccessorOf start u)
    (hShift : AddAt M T.addPairs T.plus Frame.frame.height start physical)
    (hAt : RowAt M R.states H u U F) (hc : M.mem c m) (hz : M.mem z m) (hSame : ParentRowsEqual M F c z) :
    PreviousRowsEqual M C B.height BF BR BL physical c z := by
  have hOffset := natural_successor_mem_d hM hC hRun.space.width hFrame.frame.height
  have hStart := natural_successor_mem_d hM hC hu hs
  obtain ⟨lower,hLower,hAdd⟩ := hT.add.add_exists_d hM hC hOffset hu
  have hPhysicalSucc := sum_successor_d hM hs ((hT.add.add_iff_sum hM hOffset hu).mp hAdd)
    ((hT.add.add_iff_sum hM hOffset hStart).mp hShift)
  intro Q hPrevious
  rcases hPrevious with ⟨he,_⟩ | ⟨j,_,hSucc,_,hQ⟩
  · exact False.elim (hC.zero_empty lower (he ▸ hPhysicalSucc.predecessor_mem))
  · have hj := Structure.SuccessorOf.predecessor_eq hM.1 ((omega_isOrdinal_d hM hC.omega).mem hLower) hPhysicalSucc hSucc
    subst j
    have hColumn (s p : M.Domain) (hs : M.mem s m) : MemPair M Q s p ↔ MemPair M F s p := by
      have hToMatrix : MemPair M Q s p ↔ MatrixParentAt M BF BR lower s p := by
        constructor
        · exact fun hp => ⟨Q,(hBRun.graph.bounds hM.1 hQ).2,hQ,hp⟩
        · rintro ⟨Q',_,hQ',hParent⟩
          exact hBRun.graph.unique lower Q' Q hQ' hQ ▸ hParent
      exact hToMatrix.trans (hFrame.normalized_parent_all_d hM hC hT hRun hCap hFrameRaw hTrim hBRun hu hAdd hAt hs)
    exact fun p => (hColumn c p hc).trans ((hSame p).trans (hColumn z p hz).symm)

private theorem copy_in_count {M : SetTheory.Structure.{u}} {index count copy : M.Domain}
    (hCount : M.SuccessorOf count index) (hCopy : copy=index ∨ M.mem copy index) : M.mem copy count :=
  hCopy.elim (fun he => he ▸ hCount.predecessor_mem) (fun hlt => (hCount copy).mpr (Or.inl hlt))

private theorem raw_copy_bound_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {A : CopyCoordinates.Context M.Domain} (hA : A.Valid M C) {B Raw : FiniteMatrix M.Domain}
    {BF BR active index count total copy source child : M.Domain}
    (hRaw : RawMatrixExpansion M C B T BF BR A.last active A.root index count A.length total Raw)
    (hIndex : M.mem index C.omega) (hCopy : M.mem copy count) (hRoot : M.mem A.root source) (hSource : M.mem source A.last)
    (hMap : CopyCoordinates.ParentCopy M C T A copy source child) : M.mem child Raw.width := by
  obtain ⟨slot,hSlot,_,hPos⟩ := MatrixCopy.parent_copy_bad_position_d hM hC hT hA (Or.inr hRoot) hSource hMap
  exact copy_position_bounded_d hM hC hT.add hT.mul hA.root (hA.length_nat hM.1) (natural_successor_mem_d hM hC hIndex hRaw.copies)
    hRaw.product hRaw.width hCopy hSlot hPos

private theorem trim_column_eq_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {A B : FiniteMatrix M.Domain} (hA : A.Valid M C.omega)
    (hTrim : TrimmedMatrix M C A B) (c start : M.Domain) : ColumnEqFrom M C.omega C.zero B A c c start := by
  intro r _ _ x _ y _ hX hY
  exact hA.padded_unique hM.1 ((hTrim.padded_iff_d hM hC hA r c x).mp hX) hY

/-- 实际共同父行下，图层Key随同一副本运输，并返回真实复制Top读数。 -/
theorem copied_key_le_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {m V P H L : M.Domain} {R : RowStateSpace M.Domain} (hRun : RowRun M C m R V P H)
    {Frame : ActiveFrame M.Domain} (hFrame : Frame.Valid M C T m P H R) (hCap : FrameValueCap M V Frame.cap)
    (hFrameRaw : MatrixParentRun M C m Frame.height Frame.cells Frame.values R.forests Frame.rows L)
    {B D : FiniteMatrix M.Domain} (hTrim : TrimmedMatrix M C (Frame.raw m) B) {BF BR BL DF DR DL : M.Domain}
    (hBRun : MatrixParentRun M C B.width B.height B.cells B.values BF BR BL)
    (hDRun : MatrixParentRun M C D.width D.height D.cells D.values DF DR DL)
    {X Y : CopiedMountain.Data M.Domain} (hX : X.Valid M C) (hFrom : CopiedMountain.FromRun M C m R V H X)
    {A : CopyCoordinates.Context M.Domain} (hA : A.Valid M C) {level active index copy u start U F c z child target Top NewTop topC topZ : M.Domain}
    (hLevel : M.mem level C.omega) (hActive : AddAt M T.addPairs T.plus Frame.frame.height level active)
    (hContext : MatrixExpansionContext M C B BF BR A.last active A.root)
    (hIndex : M.mem index C.omega) (hExpansion : MatrixExpansion M C B T BF BR index D)
    (hY : Y.Valid M C) (hCopies : CopiedMountain.Terminal.Copies M C T A X level D.width Y)
    (hTop : Graph M Top B.width C.omega) (hCopiedTop : CopiedTop M C T A Top D.width NewTop)
    (hTopC : MemPair M Top c topC) (hTopZ : MemPair M Top z topZ)
    (hu : M.mem u C.omega) (hs : M.SuccessorOf start u) (hAt : RowAt M R.states H u U F)
    (hSame : ParentRowsEqual M F c z) (hc : M.mem c A.last) (hz : M.mem z A.last)
    (hRootC : M.mem A.root c) (hRootZ : M.mem A.root z)
    (hCopy : copy=index ∨ M.mem copy index)
    (hMapC : CopyCoordinates.ParentCopy M C T A copy c child) (hMapZ : CopyCoordinates.ParentCopy M C T A copy z target)
    (hKey : KeyLE M C X c z start topC topZ) :
    MemPair M NewTop child topC ∧ MemPair M NewTop target topZ ∧ KeyLE M C Y child target start topC topZ := by
  have hw := omega_isOrdinal_d hM hC.omega
  have hWidth : B.width=m := hTrim.width
  have hLastB := hContext.width_successor.predecessor_mem
  have hcB := (hw.mem hTrim.matrix.width).transitive A.last hLastB c hc
  have hzB := (hw.mem hTrim.matrix.width).transitive A.last hLastB z hz
  have hRootB := (hw.mem hTrim.matrix.width).transitive A.last hLastB A.root hA.below
  have hOffset := natural_successor_mem_d hM hC hRun.space.width hFrame.frame.height
  have hStart := natural_successor_mem_d hM hC hu hs
  obtain ⟨physical,_,hShift⟩ := hT.add.add_exists_d hM hC hOffset hStart
  have hOld := (source_frame_key_iff_d hM hC hT hRun hFrame hCap hTrim hX hFrom (hWidth ▸ hcB) (hWidth ▸ hzB) hStart hShift).mp hKey
  have hPrevious := previous_rows_equal_from_numeric_d hM hC hT hRun hFrame hCap hFrameRaw hTrim hBRun hu hs hShift hAt
    (hWidth ▸ hcB) (hWidth ▸ hzB) hSame
  obtain ⟨count,len,total,Raw,hRaw,hOutTrim⟩ := hExpansion.raw_from_context_d hM hC hTrim.matrix hT hBRun hContext hIndex
  have hLen := truncated_difference_unique_d hM hC hRaw.difference hA.difference
  subst len
  have hCopyCount := copy_in_count hRaw.copies hCopy
  have hChildRaw := raw_copy_bound_d hM hC hT hA hRaw hIndex hCopyCount hRootC hc hMapC
  have hTargetRaw := raw_copy_bound_d hM hC hT hA hRaw hIndex hCopyCount hRootZ hz hMapZ
  have hChild : M.mem child D.width := hOutTrim.width.symm ▸ hChildRaw
  have hTarget : M.mem target D.width := hOutTrim.width.symm ▸ hTargetRaw
  have hNewTopC := (hCopiedTop.parent_copy_iff_d hM hC hT hA hc hChild hMapC).mpr hTopC
  have hNewTopZ := (hCopiedTop.parent_copy_iff_d hM hC hT hA hz hTarget hMapZ).mpr hTopZ
  have hLift := decorated_lift_realized_of_common_previous_d hM hC hTrim.matrix hRaw.matrix hRaw.matrix hT
    (U := ⟨BF,BR,A.last,active,A.root,copy⟩) hBRun hcB hzB hRootC hRootZ hLastB hRootB hMapC.2.1 hPrevious
    hRaw.height hRaw.height hChildRaw hTargetRaw
    (fun r d => hRaw.parent_copy_entry_iff_d hM hC hTrim.matrix hT hA hLastB hIndex hCopyCount hc hMapC)
    (fun r d => hRaw.parent_copy_entry_iff_d hM hC hTrim.matrix hT hA hLastB hIndex hCopyCount hz hMapZ) hOld
  have hNorm := decorated_eq_transport_d hM hC hRaw.matrix hOutTrim.matrix hOutTrim.matrix (hTop.bounds hM.1 hTopZ).2
    (trim_column_eq_d hM hC hRaw.matrix hOutTrim child physical) (trim_column_eq_d hM hC hRaw.matrix hOutTrim target physical) hLift
  exact ⟨hNewTopC,hNewTopZ,(expanded_terminal_key_iff_d hM hC hT hRun hFrame hCap hFrameRaw hTrim hBRun hDRun hX hFrom hA
    hLevel hActive hContext hIndex hExpansion hY hCopies hChild hTarget hStart hShift).mpr hNorm⟩

/-- 低行seam的图层Key比较：左侧采用实际复制Top读数，严格ghost比较不对它附加条件。 -/
theorem seam_key_le_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {m V P H L : M.Domain} {R : RowStateSpace M.Domain} (hRun : RowRun M C m R V P H)
    {Frame : ActiveFrame M.Domain} (hFrame : Frame.Valid M C T m P H R) (hCap : FrameValueCap M V Frame.cap)
    (hFrameRaw : MatrixParentRun M C m Frame.height Frame.cells Frame.values R.forests Frame.rows L)
    {B D : FiniteMatrix M.Domain} (hTrim : TrimmedMatrix M C (Frame.raw m) B) {BF BR BL DF DR DL : M.Domain}
    (hBRun : MatrixParentRun M C B.width B.height B.cells B.values BF BR BL)
    (hDRun : MatrixParentRun M C D.width D.height D.cells D.values DF DR DL)
    {X Y : CopiedMountain.Data M.Domain} (hX : X.Valid M C) (hFrom : CopiedMountain.FromRun M C m R V H X)
    {A : CopyCoordinates.Context M.Domain} (hA : A.Valid M C) {level active index copy next u start U F z seam target Top NewTop topLast topZ : M.Domain}
    (hLevel : M.mem level C.omega) (hActive : AddAt M T.addPairs T.plus Frame.frame.height level active)
    (hContext : MatrixExpansionContext M C B BF BR A.last active A.root)
    (hIndex : M.mem index C.omega) (hExpansion : MatrixExpansion M C B T BF BR index D)
    (hY : Y.Valid M C) (hCopies : CopiedMountain.Terminal.Copies M C T A X level D.width Y)
    (hTop : Graph M Top B.width C.omega) (hCopiedTop : CopiedTop M C T A Top D.width NewTop)
    (_hTopLast : MemPair M Top A.last topLast) (hTopZ : MemPair M Top z topZ)
    (hu : M.mem u C.omega) (hLow : M.mem u level) (hs : M.SuccessorOf start u) (hAt : RowAt M R.states H u U F)
    (hSame : ParentRowsEqual M F A.last z) (hz : M.mem z A.last) (hRootZ : M.mem A.root z)
    (hNext : M.SuccessorOf next copy) (hNextBound : next=index ∨ M.mem next index)
    (hEncode : CopyCoordinates.Encode M C T A A.last copy seam) (hMapZ : CopyCoordinates.ParentCopy M C T A copy z target)
    (hKey : KeyLE M C X A.last z start topLast topZ) :
    ∃ topSeam, M.mem topSeam C.omega ∧ MemPair M NewTop seam topSeam ∧ MemPair M NewTop target topZ ∧
      KeyLE M C Y seam target start topSeam topZ := by
  have hw := omega_isOrdinal_d hM hC.omega
  have hWidth : B.width=m := hTrim.width
  have hLastB := hContext.width_successor.predecessor_mem
  have hzB := (hw.mem hTrim.matrix.width).transitive A.last hLastB z hz
  have hRootB := (hw.mem hTrim.matrix.width).transitive A.last hLastB A.root hA.below
  have hOffset := natural_successor_mem_d hM hC hRun.space.width hFrame.frame.height
  have hStart := natural_successor_mem_d hM hC hu hs
  obtain ⟨physical,_,hShift⟩ := hT.add.add_exists_d hM hC hOffset hStart
  obtain ⟨lower,_,hLowerAdd⟩ := hT.add.add_exists_d hM hC hOffset hu
  have hPhysicalSucc := sum_successor_d hM hs ((hT.add.add_iff_sum hM hOffset hu).mp hLowerAdd)
    ((hT.add.add_iff_sum hM hOffset hStart).mp hShift)
  have hLowPhysical := sum_strict_right_d hM (hw.mem hOffset) ((hT.add.add_iff_sum hM hOffset hu).mp hLowerAdd)
    ((hT.add.add_iff_sum hM hOffset hLevel).mp hActive) hLow
  have hOld := (source_frame_key_iff_d hM hC hT hRun hFrame hCap hTrim hX hFrom (hWidth ▸ hLastB) (hWidth ▸ hzB) hStart hShift).mp hKey
  have hPrevious := previous_rows_equal_from_numeric_d hM hC hT hRun hFrame hCap hFrameRaw hTrim hBRun hu hs hShift hAt
    (hWidth ▸ hLastB) (hWidth ▸ hzB) hSame
  obtain ⟨count,len,total,Raw,hRaw,hOutTrim⟩ := hExpansion.raw_from_context_d hM hC hTrim.matrix hT hBRun hContext hIndex
  have hLen := truncated_difference_unique_d hM hC hRaw.difference hA.difference
  subst len
  have hNextCount := copy_in_count hRaw.copies hNextBound
  have hCountNat := natural_successor_mem_d hM hC hIndex hRaw.copies
  have hCopyCount := (hw.mem hCountNat).transitive next hNextCount copy hNext.predecessor_mem
  have hCopyNat := hEncode.2.1
  obtain ⟨next',_,hs',hSeamPos⟩ := CopyCoordinates.encode_seam_bms_d hM hC hT hA hEncode
  have hNextEq := Structure.SuccessorOf.eq hM.1 hs' hNext
  subst next'
  have hSeamRaw := copy_position_bounded_d hM hC hT.add hT.mul hA.root (hA.length_nat hM.1) hCountNat hRaw.product hRaw.width
    hNextCount (hA.length_positive_d hM hC) hSeamPos
  have hTargetRaw := raw_copy_bound_d hM hC hT hA hRaw hIndex hCopyCount hRootZ hz hMapZ
  have hSeam : M.mem seam D.width := hOutTrim.width.symm ▸ hSeamRaw
  have hTarget : M.mem target D.width := hOutTrim.width.symm ▸ hTargetRaw
  obtain ⟨topSeam,hTopSeamNat,hNewTopSeam⟩ := hCopiedTop.graph.total seam hSeam
  have hNewTopZ := (hCopiedTop.parent_copy_iff_d hM hC hT hA hz hTarget hMapZ).mpr hTopZ
  let Lift : MatrixLiftParameters M.Domain := ⟨BF,BR,A.last,active,A.root,copy⟩
  obtain ⟨Ghost,hGhost⟩ := ghost_column_exists_d hM hC hTrim.matrix hT (U := Lift) hLastB hRootB hCopyNat
  have hLift := decorated_lift_realized_of_common_previous_d hM hC hTrim.matrix hGhost.matrix hRaw.matrix hT (U := Lift)
    hBRun hLastB hzB hA.below hRootZ hLastB hRootB hCopyNat hPrevious hGhost.height hRaw.height (hGhost.column_bound hC) hTargetRaw
    hGhost.entries (fun r d => hRaw.parent_copy_entry_iff_d hM hC hTrim.matrix hT hA hLastB hIndex hCopyCount hz hMapZ) hOld
  have hStrict := newroot_suffix_lt_ghost_d hM hC hTrim.matrix hT hBRun hContext hRaw hIndex hCopyNat hNext hNextBound hSeamPos
    hGhost hLowPhysical hPhysicalSucc
  have hStrictTarget := column_lt_le_trans_d hM hC hRaw.matrix hGhost.matrix hRaw.matrix hStrict hLift.forget
  have hNorm := decorated_eq_transport_d hM hC hRaw.matrix hOutTrim.matrix hOutTrim.matrix (hTop.bounds hM.1 hTopZ).2
    (trim_column_eq_d hM hC hRaw.matrix hOutTrim seam physical) (trim_column_eq_d hM hC hRaw.matrix hOutTrim target physical)
    (show DecoratedColumnLeFrom M C Raw Raw seam target physical topSeam topZ from Or.inl hStrictTarget)
  exact ⟨topSeam,hTopSeamNat,hNewTopSeam,hNewTopZ,
    (expanded_terminal_key_iff_d hM hC hT hRun hFrame hCap hFrameRaw hTrim hBRun hDRun hX hFrom hA
      hLevel hActive hContext hIndex hExpansion hY hCopies hSeam hTarget hStart hShift).mpr hNorm⟩

/-! 图层Key的字面有界公式，供后续对象归纳和内模型绝对性直接消费。 -/
def depthAtFormula {n : Nat} (C : ExpressionData (Project.Term n)) (X : CopiedMountain.Data (Project.Term n))
    (c r d : Project.Term n) : Project.Formula 1 n :=
  Project.Formula.existsMem X.forests (.conj (memPairFormula X.parents.weaken r.weaken (.bound 0))
    (depthFormula C.weaken X.width.weaken (.bound 0) c.weaken d.weaken))

theorem depthAtFormula_delta0 {n : Nat} (C : ExpressionData (Project.Term n)) (X : CopiedMountain.Data (Project.Term n))
    (c r d : Project.Term n) : (depthAtFormula C X c r d).IsDelta0 :=
  .existsMem _ (.conj (memPairFormula_delta0 _ _ _) (depthFormula_delta0 _ _ _ _ _))

theorem depthAtFormula_freeClosed {n : Nat} {C : ExpressionData (Project.Term n)} (hC : C.Closed)
    {X : CopiedMountain.Data (Project.Term n)} (hX : X.Closed) (c r d : Project.Term n)
    (hc : c.freeSupport=[]) (hr : r.freeSupport=[]) (hd : d.freeSupport=[]) : (depthAtFormula C X c r d).FreeClosed := by
  have hDepth := depthFormula_freeClosed hC.weaken X.width.weaken (.bound 0) c.weaken d.weaken
    (by simpa using hX.width) rfl (by simpa using hc) (by simpa using hd)
  simp [depthAtFormula,Project.Formula.existsMem,Project.Formula.forallMem,Definitional.Formula.FreeClosed,
    memPairFormula,codeFormula,pairFormula,hX.forests,hX.parents,hr,hDepth]

theorem depthAtFormula_iff {M : SetTheory.Structure.{u}} (he : Extensional M) {n : Nat} (e : Env M n)
    (C : ExpressionData (Project.Term n)) (X : CopiedMountain.Data (Project.Term n)) (c r d : Project.Term n) :
    Project.Formula.satisfies e (depthAtFormula C X c r d) ↔ DepthAt M (C.eval e) (X.eval e) (c.eval e) (r.eval e) (d.eval e) := by
  simp only [depthAtFormula,DepthAt,Project.Formula.satisfies_existsMem_iff,Project.Formula.satisfies_conj_iff,
    memPairFormula_iff he,depthFormula_iff he,ExpressionData.eval_weaken,Term.eval_weaken]
  rfl

def depthEqAtFormula {n : Nat} (C : ExpressionData (Project.Term n)) (X : CopiedMountain.Data (Project.Term n))
    (c z r : Project.Term n) : Project.Formula 1 n :=
  Project.Formula.forallMem C.omega (Project.Formula.forallMem C.omega.weaken
    (.imp (.conj (depthAtFormula C.weaken.weaken X.weaken.weaken c.weaken.weaken r.weaken.weaken (.bound 1))
      (depthAtFormula C.weaken.weaken X.weaken.weaken z.weaken.weaken r.weaken.weaken (.bound 0)))
      (Project.Formula.extensionalEq (.bound 1) (.bound 0))))

def depthLtAtFormula {n : Nat} (C : ExpressionData (Project.Term n)) (X : CopiedMountain.Data (Project.Term n))
    (c z r : Project.Term n) : Project.Formula 1 n :=
  Project.Formula.existsMem C.omega (Project.Formula.existsMem C.omega.weaken
    (.conj (depthAtFormula C.weaken.weaken X.weaken.weaken c.weaken.weaken r.weaken.weaken (.bound 1))
      (.conj (depthAtFormula C.weaken.weaken X.weaken.weaken z.weaken.weaken r.weaken.weaken (.bound 0)) (.mem (.bound 1) (.bound 0)))))

private theorem depthAtPair_freeClosed {n : Nat} {C : ExpressionData (Project.Term n)} (hC : C.Closed)
    {X : CopiedMountain.Data (Project.Term n)} (hX : X.Closed) (c z r : Project.Term n)
    (hc : c.freeSupport=[]) (hz : z.freeSupport=[]) (hr : r.freeSupport=[]) :
    (depthEqAtFormula C X c z r).FreeClosed ∧ (depthLtAtFormula C X c z r).FreeClosed := by
  have hL := depthAtFormula_freeClosed hC.weaken.weaken hX.weaken.weaken c.weaken.weaken r.weaken.weaken (.bound 1)
    (by simpa using hc) (by simpa using hr) rfl
  have hR := depthAtFormula_freeClosed hC.weaken.weaken hX.weaken.weaken z.weaken.weaken r.weaken.weaken (.bound 0)
    (by simpa using hz) (by simpa using hr) rfl
  constructor <;> simp [depthEqAtFormula,depthLtAtFormula,Project.Formula.forallMem,Project.Formula.existsMem,
    Definitional.Formula.FreeClosed,hC.omega,hL,hR]

theorem depthEqAtFormula_iff {M : SetTheory.Structure.{u}} (he : Extensional M) {n : Nat} (e : Env M n)
    (C : ExpressionData (Project.Term n)) (X : CopiedMountain.Data (Project.Term n)) (c z r : Project.Term n) :
    Project.Formula.satisfies e (depthEqAtFormula C X c z r) ↔ DepthEqAt M (C.eval e) (X.eval e) (c.eval e) (z.eval e) (r.eval e) := by
  simp only [depthEqAtFormula,DepthEqAt,Project.Formula.satisfies_forallMem_iff,Project.Formula.satisfies_imp_iff,
    Project.Formula.satisfies_conj_iff,depthAtFormula_iff he,Project.Formula.satisfies_extensionalEq_iff_eq he,
    ExpressionData.eval_weaken,CopiedMountain.Data.eval_weaken,Term.eval_weaken,and_imp]
  rfl

theorem depthLtAtFormula_iff {M : SetTheory.Structure.{u}} (he : Extensional M) {n : Nat} (e : Env M n)
    (C : ExpressionData (Project.Term n)) (X : CopiedMountain.Data (Project.Term n)) (c z r : Project.Term n) :
    Project.Formula.satisfies e (depthLtAtFormula C X c z r) ↔ DepthLtAt M (C.eval e) (X.eval e) (c.eval e) (z.eval e) (r.eval e) := by
  simp only [depthLtAtFormula,DepthLtAt,Project.Formula.satisfies_existsMem_iff,Project.Formula.satisfies_conj_iff,
    depthAtFormula_iff he,Project.Formula.satisfies_mem_iff,ExpressionData.eval_weaken,CopiedMountain.Data.eval_weaken,Term.eval_weaken]
  rfl

def depthEqFromFormula {n : Nat} (C : ExpressionData (Project.Term n)) (X : CopiedMountain.Data (Project.Term n))
    (c z start : Project.Term n) : Project.Formula 1 n :=
  Project.Formula.forallMem C.omega (.imp (.disj (Project.Formula.extensionalEq start.weaken (.bound 0)) (.mem start.weaken (.bound 0)))
    (depthEqAtFormula C.weaken X.weaken c.weaken z.weaken (.bound 0)))

def depthLtFromFormula {n : Nat} (C : ExpressionData (Project.Term n)) (X : CopiedMountain.Data (Project.Term n))
    (c z start : Project.Term n) : Project.Formula 1 n :=
  Project.Formula.existsMem C.omega (.conj (.disj (Project.Formula.extensionalEq start.weaken (.bound 0)) (.mem start.weaken (.bound 0)))
    (.conj (Project.Formula.forallMem (.bound 0)
      (.imp (.disj (Project.Formula.extensionalEq start.weaken.weaken (.bound 0)) (.mem start.weaken.weaken (.bound 0)))
        (depthEqAtFormula C.weaken.weaken X.weaken.weaken c.weaken.weaken z.weaken.weaken (.bound 0))))
      (depthLtAtFormula C.weaken X.weaken c.weaken z.weaken (.bound 0))))

def keyLEFormula {n : Nat} (C : ExpressionData (Project.Term n)) (X : CopiedMountain.Data (Project.Term n))
    (c z start topC topZ : Project.Term n) : Project.Formula 1 n :=
  .disj (depthLtFromFormula C X c z start) (.conj (depthEqFromFormula C X c z start)
    (.disj (Project.Formula.extensionalEq topC topZ) (.mem topC topZ)))

theorem keyLEFormula_delta0 {n : Nat} (C : ExpressionData (Project.Term n)) (X : CopiedMountain.Data (Project.Term n))
    (c z start topC topZ : Project.Term n) : (keyLEFormula C X c z start topC topZ).IsDelta0 := by
  have hEqAny {d : Nat} (C : ExpressionData (Project.Term d)) (X : CopiedMountain.Data (Project.Term d)) (c z r : Project.Term d) :
      (depthEqAtFormula C X c z r).IsDelta0 := .forallMem _ (.forallMem _ (.imp
        (.conj (depthAtFormula_delta0 _ _ _ _ _) (depthAtFormula_delta0 _ _ _ _ _)) (.atom _ _ _)))
  have hLtAny {d : Nat} (C : ExpressionData (Project.Term d)) (X : CopiedMountain.Data (Project.Term d)) (c z r : Project.Term d) :
      (depthLtAtFormula C X c z r).IsDelta0 := .existsMem _ (.existsMem _ (.conj (depthAtFormula_delta0 _ _ _ _ _)
        (.conj (depthAtFormula_delta0 _ _ _ _ _) (.mem _ _))))
  exact .disj (.existsMem _ (.conj (.disj (.atom _ _ _) (.mem _ _)) (.conj (.forallMem _ (.imp
    (.disj (.atom _ _ _) (.mem _ _)) (hEqAny _ _ _ _ _))) (hLtAny _ _ _ _ _))))
    (.conj (.forallMem _ (.imp (.disj (.atom _ _ _) (.mem _ _)) (hEqAny _ _ _ _ _))) (.disj (.atom _ _ _) (.mem _ _)))

theorem keyLEFormula_freeClosed {n : Nat} {C : ExpressionData (Project.Term n)} (hC : C.Closed)
    {X : CopiedMountain.Data (Project.Term n)} (hX : X.Closed) (c z start topC topZ : Project.Term n)
    (hc : c.freeSupport=[]) (hz : z.freeSupport=[]) (hs : start.freeSupport=[]) (htc : topC.freeSupport=[]) (htz : topZ.freeSupport=[]) :
    (keyLEFormula C X c z start topC topZ).FreeClosed := by
  have hRow := depthAtPair_freeClosed hC.weaken hX.weaken c.weaken z.weaken (.bound 0) (by simpa using hc) (by simpa using hz) rfl
  have hEarlier := depthAtPair_freeClosed hC.weaken.weaken hX.weaken.weaken c.weaken.weaken z.weaken.weaken (.bound 0)
    (by simpa using hc) (by simpa using hz) rfl
  simp [keyLEFormula,depthEqFromFormula,depthLtFromFormula,Project.Formula.forallMem,Project.Formula.existsMem,
    Definitional.Formula.FreeClosed,hC.omega,hs,htc,htz,hRow.1,hRow.2,hEarlier.1]

theorem keyLEFormula_iff {M : SetTheory.Structure.{u}} (he : Extensional M) {n : Nat} (e : Env M n)
    (C : ExpressionData (Project.Term n)) (X : CopiedMountain.Data (Project.Term n)) (c z start topC topZ : Project.Term n) :
    Project.Formula.satisfies e (keyLEFormula C X c z start topC topZ) ↔
      KeyLE M (C.eval e) (X.eval e) (c.eval e) (z.eval e) (start.eval e) (topC.eval e) (topZ.eval e) := by
  simp only [keyLEFormula,KeyLE,depthEqFromFormula,DepthEqFrom,depthLtFromFormula,DepthLtFrom,
    Project.Formula.satisfies_disj_iff,Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_forallMem_iff,
    Project.Formula.satisfies_existsMem_iff,Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_extensionalEq_iff_eq he,
    Project.Formula.satisfies_mem_iff,depthEqAtFormula_iff he,depthLtAtFormula_iff he,
    ExpressionData.eval_weaken,CopiedMountain.Data.eval_weaken,Term.eval_weaken]
  rfl

end KP1Y.OneYFinite.ForestOrder
