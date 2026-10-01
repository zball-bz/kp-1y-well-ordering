import KP1Y.OneYSparseDepth
import KP1Y.OneYMatrixNormalization
import KP1Y.OneYSelectionBlocker
import KP1Y.OneYBadRoot

/-! 实际数值山形上方的有限活动帧。矩阵值是父森林的Depth；
原数值山形的top值始终作为独立的最后比较坐标。
-/
namespace KP1Y.OneYFinite
open YesMetaZFC YesMetaZFC.SetTheory YesMetaZFC.SetTheory.Definitional
open KP1Y.Kuratowski KP1Y.Functions KP1Y.Naturals KP1Y.Bounded KP1Y.Arithmetic
universe u

private theorem sum_tail_index_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {offset cap height r : M.Domain} (hOffset : M.mem offset C.omega) (hCap : M.mem cap C.omega)
    (hSum : AddAt M T.addPairs T.plus offset cap height) (hr : M.mem r height) (hNot : ¬M.mem r offset) :
    ∃ j, M.mem j cap ∧ AddAt M T.addPairs T.plus offset j r := by
  have hw := omega_isOrdinal_d hM hC.omega
  have hHeight := (hSum.bounds hM.1 hT.add).2.2
  have hrNat := hw.transitive height hHeight r hr
  have hLe : offset=r ∨ M.mem offset r := by
    rcases hw.wellOrder.linear.compare offset hOffset r hrNat with he | hlt | hgt
    · exact Or.inl (hM.1.eq_of_same_members offset r he)
    · exact Or.inr hlt
    · exact False.elim (hNot hgt)
  obtain ⟨j,hj,hDiff⟩ := truncated_difference_exists_d hM hC hrNat hOffset
  have hJR := truncated_difference_add_inverse_d hM hC hDiff hLe
  have hSum' := (hT.add.add_iff_sum hM hOffset hCap).mp hSum
  have hJCap : M.mem j cap := by
    rcases hw.wellOrder.linear.compare j hj cap hCap with he | hlt | hgt
    · have heq := hM.1.eq_of_same_members j cap he
      subst j
      have hrEq := sum_unique_d hM hJR hSum'
      exact False.elim (SetTheory.KP.mem_irrefl_d (KP1Y.models_weakKP hM) height (hrEq ▸ hr))
    · exact hlt
    · have hHeightR := sum_strict_right_d hM (hw.mem hOffset) hSum' hJR hgt
      exact False.elim (SetTheory.KP.mem_irrefl_d (KP1Y.models_weakKP hM) r ((hw.mem hrNat).transitive height hHeightR r hr))
  exact ⟨j,hJCap,(hT.add.add_iff_sum hM hOffset hj).mpr hJR⟩

private theorem add_not_below_base_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {offset j r : M.Domain} (hOffset : M.mem offset C.omega) (hj : M.mem j C.omega)
    (hAdd : AddAt M T.addPairs T.plus offset j r) : ¬M.mem r offset := by
  intro hr
  exact SetTheory.KP.mem_irrefl_d (KP1Y.models_weakKP hM) r
    (sum_base_subset_d hM ((omega_isOrdinal_d hM hC.omega).mem hOffset) ((hT.add.add_iff_sum hM hOffset hj).mp hAdd) r hr)

def ActiveFrameRow (M : SetTheory.Structure.{u}) (Pairs Plus FrameRows Values States H offset cap r Q : M.Domain) : Prop :=
  MemPair M FrameRows r Q ∨ ∃ j, M.mem j cap ∧ AddAt M Pairs Plus offset j r ∧
    ∃ W, M.mem W Values ∧ RowAt M States H j W Q

private def activeRowEnv {M : SetTheory.Structure.{u}} (Pairs Plus FrameRows Values States H offset cap : M.Domain) : Env M 8 :=
  (((((((oneEnv Pairs).push Plus).push FrameRows).push H).push Values).push States).push offset).push cap

private def activeRowSchema : Project.Delta0BinarySchema 8 where
  body := .disj (memPairFormula (.bound 7) (.bound 1) (.bound 0))
    (Project.Formula.existsMem (.bound 2) (.conj (addAtFormula (.bound 10) (.bound 9) (.bound 4) (.bound 0) (.bound 2))
      (Project.Formula.existsMem (.bound 6) (rowAtFormula (.bound 6) (.bound 8) (.bound 1) (.bound 0) (.bound 2)))))
  freeClosed := by
    simp [addAtFormula,rowAtFormula,memPairFormula,codeFormula,pairFormula,Project.Formula.existsMem,
      Project.Formula.forallMem,Definitional.Formula.FreeClosed]
  delta0 := .disj (memPairFormula_delta0 _ _ _) (.existsMem _ (.conj (addAtFormula_delta0 _ _ _ _ _)
    (.existsMem _ (rowAtFormula_delta0 _ _ _ _ _))))

private theorem activeRowSchema_iff {M : SetTheory.Structure.{u}} (he : Extensional M)
    (Pairs Plus FrameRows Values States H offset cap r Q : M.Domain) :
    Project.Formula.satisfies (((activeRowEnv Pairs Plus FrameRows Values States H offset cap).push r).push Q) activeRowSchema.body ↔
      ActiveFrameRow M Pairs Plus FrameRows Values States H offset cap r Q := by
  simp only [activeRowSchema,ActiveFrameRow,Project.Formula.satisfies_disj_iff,memPairFormula_iff he,
    Project.Formula.satisfies_existsMem_iff,Project.Formula.satisfies_conj_iff,addAtFormula_iff he,rowAtFormula_iff he]
  rfl

/-- 实际拼接整个width+1行森林帧及cap行数值父森林，值域复用真实RowStateSpace的森林集合。 -/
theorem active_frame_row_graph_exists_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {m V P H cap height : M.Domain} {R : RowStateSpace M.Domain} (hRun : RowRun M C m R V P H)
    {Frame : ForestFrameMatrix M.Domain} (hFrame : Frame.Valid M C m P) (hCap : M.mem cap C.omega)
    (hSum : AddAt M T.addPairs T.plus Frame.height cap height) :
    ∃ Rows, Graph M Rows height R.forests ∧ ∀ r Q,
      MemPair M Rows r Q ↔ ActiveFrameRow M T.addPairs T.plus Frame.rows R.values R.states H Frame.height cap r Q := by
  have hw := omega_isOrdinal_d hM hC.omega
  have hOffset := natural_successor_mem_d hM hC hRun.base.forest.width hFrame.height
  have hHeight := (hSum.bounds hM.1 hT.add).2.2
  obtain ⟨Rows,hSupport,hRaw⟩ := relation_comprehension_d hM activeRowSchema
    (activeRowEnv T.addPairs T.plus Frame.rows R.values R.states H Frame.height cap) height R.forests
  have hBounds (r Q : M.Domain) (hAt : ActiveFrameRow M T.addPairs T.plus Frame.rows R.values R.states H Frame.height cap r Q) :
      M.mem r height ∧ M.mem Q R.forests := by
    rcases hAt with hFrameAt | ⟨j,hj,hAdd,W,_,hAt⟩
    · exact ⟨sum_base_subset_d hM (hw.mem hOffset) ((hT.add.add_iff_sum hM hOffset hCap).mp hSum) r
        (hFrame.rows.bounds hM.1 hFrameAt).1,(hRun.space.forests Q).mpr (hFrame.row_forest hFrameAt)⟩
    · have hjNat := hw.transitive cap hCap j hj
      exact ⟨sum_strict_right_d hM (hw.mem hOffset) ((hT.add.add_iff_sum hM hOffset hjNat).mp hAdd)
        ((hT.add.add_iff_sum hM hOffset hCap).mp hSum) hj,(hRun.space.forests Q).mpr (hRun.at_numeric_d hM hC hAt).forest⟩
  have hRows (r Q : M.Domain) : MemPair M Rows r Q ↔ ActiveFrameRow M T.addPairs T.plus Frame.rows R.values R.states H Frame.height cap r Q := by
    rw [hRaw r Q,activeRowSchema_iff hM.1]
    exact ⟨fun h => h.2.2,fun h => ⟨(hBounds r Q h).1,(hBounds r Q h).2,h⟩⟩
  refine ⟨Rows,⟨hSupport,?_,?_⟩,hRows⟩
  · intro r hr
    classical
    by_cases hFrameR : M.mem r Frame.height
    · obtain ⟨Q,_,hQ⟩ := hFrame.rows.total r hFrameR
      have hAt : ActiveFrameRow M T.addPairs T.plus Frame.rows R.values R.states H Frame.height cap r Q := Or.inl hQ
      exact ⟨Q,(hBounds r Q hAt).2,(hRows r Q).mpr hAt⟩
    · obtain ⟨j,hj,hAdd⟩ := sum_tail_index_d hM hC hT hOffset hCap hSum hr hFrameR
      obtain ⟨W,Q,hAt⟩ := hRun.at_exists_d (hw.transitive cap hCap j hj)
      have hRow := hRun.at_numeric_d hM hC hAt
      exact ⟨Q,(hRun.space.forests Q).mpr hRow.forest,(hRows r Q).mpr (Or.inr ⟨j,hj,hAdd,W,(hRun.space.values W).mpr hRow.values,hAt⟩)⟩
  · intro r Q Q' hQ hQ'
    rcases (hRows r Q).mp hQ with hFrameQ | ⟨j,hj,hAdd,W,_,hAt⟩ <;>
      rcases (hRows r Q').mp hQ' with hFrameQ' | ⟨j',hj',hAdd',W',_,hAt'⟩
    · exact hFrame.rows.unique r Q Q' hFrameQ hFrameQ'
    · exact False.elim (add_not_below_base_d hM hC hT hOffset (hw.transitive cap hCap j' hj') hAdd' (hFrame.rows.bounds hM.1 hFrameQ).1)
    · exact False.elim (add_not_below_base_d hM hC hT hOffset (hw.transitive cap hCap j hj) hAdd (hFrame.rows.bounds hM.1 hFrameQ').1)
    · have hJ := natural_sum_cancel_left_d hM hC hOffset (hw.transitive cap hCap j hj) (hw.transitive cap hCap j' hj')
        ((hT.add.add_iff_sum hM hOffset (hw.transitive cap hCap j hj)).mp hAdd)
        ((hT.add.add_iff_sum hM hOffset (hw.transitive cap hCap j' hj')).mp hAdd')
      subst j'
      exact (hRun.at_unique hM.1 hAt hAt').2

structure ActiveFrame (α : Type u) where
  frame : ForestFrameMatrix α
  cap : α
  height : α
  rows : α
  cells : α
  values : α

def ActiveFrame.raw {α : Type u} (A : ActiveFrame α) (m : α) : FiniteMatrix α := ⟨A.height,m,A.cells,A.values⟩

structure ActiveFrame.Valid (M : SetTheory.Structure.{u}) (C : ExpressionData M.Domain) (T : MatrixArithmetic M.Domain)
    (m P H : M.Domain) (R : RowStateSpace M.Domain) (A : ActiveFrame M.Domain) : Prop where
  frame : A.frame.Valid M C m P
  cap : M.mem A.cap C.omega
  height : M.mem A.height C.omega
  height_sum : AddAt M T.addPairs T.plus A.frame.height A.cap A.height
  rows : Graph M A.rows A.height R.forests
  row_meaning : ∀ r Q, MemPair M A.rows r Q ↔ ActiveFrameRow M T.addPairs T.plus A.frame.rows R.values R.states H A.frame.height A.cap r Q
  cells : IsProduct M A.cells A.height m
  values : Graph M A.values A.cells C.omega
  entries : ∀ r, M.mem r A.height → ∀ c, M.mem c m → ∀ Q, MemPair M A.rows r Q → ∀ key, Codes M key r c →
    ∀ d, MemPair M A.values key d ↔ Depth M C m Q c d

theorem active_frame_raw_exists_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {m V P H cap : M.Domain} {R : RowStateSpace M.Domain} (hRun : RowRun M C m R V P H) (hCap : M.mem cap C.omega) :
    ∃ A : ActiveFrame M.Domain, A.cap=cap ∧ A.Valid M C T m P H R := by
  obtain ⟨Frame,hFrame⟩ := forest_frame_matrix_exists_d hM hC hRun.base.forest
  have hOffset := natural_successor_mem_d hM hC hRun.base.forest.width hFrame.height
  obtain ⟨height,hHeight,hSum⟩ := hT.add.add_exists_d hM hC hOffset hCap
  obtain ⟨Rows,hRows,hMeaning⟩ := active_frame_row_graph_exists_d hM hC hT hRun hFrame hCap hSum
  obtain ⟨Cells,Values,hCells,hValues,hEntries⟩ := depth_matrix_exists_d hM hC hRows
    (fun r Q hAt => (hRun.space.forests Q).mp (hRows.bounds hM.1 hAt).2)
  exact ⟨⟨Frame,cap,height,Rows,Cells,Values⟩,rfl,hFrame,hCap,hHeight,hSum,hRows,hMeaning,hCells,hValues,hEntries⟩

theorem ActiveFrame.Valid.raw_valid {M : SetTheory.Structure.{u}} {C : ExpressionData M.Domain} {T : MatrixArithmetic M.Domain}
    {m P H : M.Domain} {R : RowStateSpace M.Domain} {A : ActiveFrame M.Domain} (hR : R.Valid M C m) (h : A.Valid M C T m P H R) :
    (A.raw m).Valid M C.omega := ⟨h.height,hR.width,h.cells,h.values⟩

theorem ActiveFrame.Valid.frame_row_iff_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {m V P H : M.Domain} {R : RowStateSpace M.Domain} (hRun : RowRun M C m R V P H)
    {A : ActiveFrame M.Domain} (h : A.Valid M C T m P H R) {r Q : M.Domain} (hr : M.mem r A.frame.height) :
    MemPair M A.rows r Q ↔ MemPair M A.frame.rows r Q := by
  rw [h.row_meaning]
  constructor
  · rintro (hAt | ⟨j,hj,hAdd,_,_,_⟩)
    · exact hAt
    · exact False.elim (add_not_below_base_d hM hC hT (natural_successor_mem_d hM hC hRun.space.width h.frame.height)
        ((omega_isOrdinal_d hM hC.omega).transitive A.cap h.cap j hj) hAdd hr)
  · exact Or.inl

theorem ActiveFrame.Valid.numeric_row_iff_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {m V P H : M.Domain} {R : RowStateSpace M.Domain} (hRun : RowRun M C m R V P H)
    {A : ActiveFrame M.Domain} (h : A.Valid M C T m P H R) {j r Q : M.Domain}
    (hj : M.mem j A.cap) (hAdd : AddAt M T.addPairs T.plus A.frame.height j r) :
    MemPair M A.rows r Q ↔ ∃ W, M.mem W R.values ∧ RowAt M R.states H j W Q := by
  have hw := omega_isOrdinal_d hM hC.omega
  have hOffset := natural_successor_mem_d hM hC hRun.space.width h.frame.height
  have hjNat := hw.transitive A.cap h.cap j hj
  rw [h.row_meaning]
  constructor
  · rintro (hAt | ⟨j',hj',hAdd',W,hW,hAt⟩)
    · exact False.elim (add_not_below_base_d hM hC hT hOffset hjNat hAdd (h.frame.rows.bounds hM.1 hAt).1)
    · have hJ := natural_sum_cancel_left_d hM hC hOffset (hw.transitive A.cap h.cap j' hj') hjNat
        ((hT.add.add_iff_sum hM hOffset (hw.transitive A.cap h.cap j' hj')).mp hAdd') ((hT.add.add_iff_sum hM hOffset hjNat).mp hAdd)
      subst j'
      exact ⟨W,hW,hAt⟩
  · rintro ⟨W,hW,hAt⟩
    exact Or.inr ⟨j,hj,hAdd,W,hW,hAt⟩

theorem ActiveFrame.Valid.entry_depth_iff_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} {T : MatrixArithmetic M.Domain} {m P H : M.Domain} {R : RowStateSpace M.Domain}
    (hR : R.Valid M C m) {A : ActiveFrame M.Domain} (h : A.Valid M C T m P H R) {r Q : M.Domain}
    (hAt : MemPair M A.rows r Q) (c d : M.Domain) : MatrixEntry M (A.raw m) r c d ↔ Depth M C m Q c d := by
  have hr := (h.rows.bounds hM.1 hAt).1
  constructor
  · intro hEntry
    have hc := (hEntry.bounds hM.1 (h.raw_valid hR)).2.1
    obtain ⟨key,_,hCode,hValue⟩ := hEntry
    exact (h.entries r hr c hc Q hAt key hCode d).mp hValue
  · intro hDepth
    have hc := hDepth.column_bound hM.1
    obtain ⟨key,hCode⟩ := codes_total hM r c
    exact ⟨key,(h.cells key).mpr ⟨r,hr,c,hc,hCode⟩,hCode,(h.entries r hr c hc Q hAt key hCode d).mpr hDepth⟩

private theorem add_index_successor_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {offset i j r s : M.Domain} (hOffset : M.mem offset C.omega) (hi : M.mem i C.omega) (hj : M.mem j C.omega)
    (hR : AddAt M T.addPairs T.plus offset i r) (hS : AddAt M T.addPairs T.plus offset j s) (hs : M.SuccessorOf s r) :
    M.SuccessorOf j i := by
  obtain ⟨next,hNext,hNextNat⟩ := hC.omega.1.2 i hi
  obtain ⟨s',_,hAdd⟩ := hT.add.add_exists_d hM hC hOffset hNextNat
  have hSucc := natural_sum_left_successor_d hM hC hOffset hNext
    (natural_sum_comm_d hM hC hOffset hi ((hT.add.add_iff_sum hM hOffset hi).mp hR))
    (natural_sum_comm_d hM hC hOffset hNextNat ((hT.add.add_iff_sum hM hOffset hNextNat).mp hAdd))
  have hEq := Structure.SuccessorOf.eq hM.1 hSucc hs
  subst s'
  have hNextJ := natural_sum_cancel_left_d hM hC hOffset hNextNat hj
    ((hT.add.add_iff_sum hM hOffset hNextNat).mp hAdd) ((hT.add.add_iff_sum hM hOffset hj).mp hS)
  exact hNextJ ▸ hNext

/-- 真正的BM4父算法恢复拼接帧中的每个父森林，不把此恢复写入帧定义。 -/
theorem ActiveFrame.Valid.parent_run_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {m V P H : M.Domain} {R : RowStateSpace M.Domain} (hRun : RowRun M C m R V P H)
    {A : ActiveFrame M.Domain} (h : A.Valid M C T m P H R) :
    ∃ L, MatrixParentRun M C m A.height A.cells A.values R.forests A.rows L := by
  have hw := omega_isOrdinal_d hM hC.omega
  have hRaw := h.raw_valid hRun.space
  have hOffset := natural_successor_mem_d hM hC hRun.space.width h.frame.height
  have hZeroOffset : M.mem C.zero A.frame.height := (hC.zero_mem_iff hM hOffset).mpr
    (fun he => hC.zero_empty m (he ▸ h.frame.height.predecessor_mem))
  obtain ⟨L,hL⟩ := linear_forest_exists_d hM hC.omega hRun.space.width
  refine ⟨L,h.height,hL,h.rows,?_,?_,?_,?_⟩
  · intro r Q hAt
    exact (hRun.space.forests Q).mp (h.rows.bounds hM.1 hAt).2
  · exact fun r hr => hRaw.row_view_d hM hr
  · intro Q D hAt hD
    have hFrameAt := (h.frame_row_iff_d hM hC hT hRun hZeroOffset).mp hAt
    obtain ⟨W,hW⟩ := h.frame.row_values_exist_d hM hC hZeroOffset
    have hOld := h.frame.initial_selection_d hM hC hRun.base.forest hL hFrameAt hW
    exact hOld.depth_selection_d hM hC hD.graph (fun c d =>
      (matrix_row_view_entry_iff_d hM hRaw (h.rows.bounds hM.1 hAt).1 hD c d).trans (h.entry_depth_iff_d hM hRun.space hAt c d))
  · intro r s Q Q' D hs hAt hAt' hD
    have hDepth (c d : M.Domain) := (matrix_row_view_entry_iff_d hM hRaw (h.rows.bounds hM.1 hAt').1 hD c d).trans
      (h.entry_depth_iff_d hM hRun.space hAt' c d)
    have hrNat := hw.transitive A.height h.height r (h.rows.bounds hM.1 hAt).1
    rcases (h.row_meaning r Q).mp hAt with hFrameR | ⟨i,hi,hAddR,U,_,hNumericR⟩ <;>
      rcases (h.row_meaning s Q').mp hAt' with hFrameS | ⟨j,hj,hAddS,W,_,hNumericS⟩
    · exact h.frame.successive_selection_d hM hC hRun.base.forest hs hFrameR hFrameS hD.graph hDepth
    · have hjNat := hw.transitive A.cap h.cap j hj
      have hNotS := add_not_below_base_d hM hC hT hOffset hjNat hAddS
      have hrEq : r=m := by
        rcases (h.frame.height r).mp (h.frame.rows.bounds hM.1 hFrameR).1 with hrm | he
        · exact False.elim (hNotS ((natural_successor_lt_iff hM hC hRun.space.width hrNat h.frame.height hs).mpr hrm))
        · exact hM.1.eq_of_same_members r m he
      subst r
      have hsEq := Structure.SuccessorOf.eq hM.1 hs h.frame.height
      subst s
      have hjZero := natural_sum_cancel_left_d hM hC hOffset hjNat hC.zero_nat
        ((hT.add.add_iff_sum hM hOffset hjNat).mp hAddS) (sum_zero_d hM A.frame.height hC.zero_empty)
      subst j
      have hBaseQ := h.frame.terminal_parent_d hM hC hRun.base.forest hFrameR
      have hBaseQ' := (hRun.at_unique hM.1 (hRun.initial_row_at_d hM) hNumericS).2
      subst Q
      subst Q'
      exact depth_selects_self_d hM hC hRun.base.forest hD.graph hDepth
    · have hNotR := add_not_below_base_d hM hC hT hOffset (hw.transitive A.cap h.cap i hi) hAddR
      exact False.elim (hNotR ((hw.mem hOffset).transitive s (h.frame.rows.bounds hM.1 hFrameS).1 r hs.predecessor_mem))
    · exact hRun.next_depth_selection_d hM hC
        (add_index_successor_d hM hC hT hOffset (hw.transitive A.cap h.cap i hi) (hw.transitive A.cap h.cap j hj) hAddR hAddS hs)
        hNumericR hNumericS hD.graph hDepth

theorem ActiveFrame.Valid.depth_regular_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} {m P H : M.Domain} {R : RowStateSpace M.Domain}
    (hR : R.Valid M C m) {A : ActiveFrame M.Domain} (h : A.Valid M C T m P H R) :
    MatrixDepthRegular M C (A.raw m) R.forests A.rows := by
  intro r _ Q hQMem hAt c _ d _ hEntry
  have hQ := (hR.forests Q).mp hQMem
  have hD := (h.entry_depth_iff_d hM hR hAt c d).mp hEntry
  refine ⟨fun hn => depth_of_no_parent_d hM hC hQ hn hD,?_⟩
  intro p _ hParent e _ hEntryP
  exact depth_parent_successor_d hM hC hQ hParent hD ((h.entry_depth_iff_d hM hR hAt p e).mp hEntryP)

/-- 从真实数值山形构造规范化活动帧及其真实父运行。 -/
theorem active_frame_exists_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {m V P H cap : M.Domain} {R : RowStateSpace M.Domain} (hRun : RowRun M C m R V P H) (hCap : M.mem cap C.omega) :
    ∃ A : ActiveFrame M.Domain, ∃ B : FiniteMatrix M.Domain, ∃ L OtherForests Other OtherL,
      A.cap=cap ∧ A.Valid M C T m P H R ∧ TrimmedMatrix M C (A.raw m) B ∧ NormalizedMatrix M C B ∧
      MatrixParentRun M C m A.height A.cells A.values R.forests A.rows L ∧
      MatrixParentRun M C B.width B.height B.cells B.values OtherForests Other OtherL ∧ MatrixDepthRegular M C B OtherForests Other := by
  obtain ⟨A,hCapEq,hA⟩ := active_frame_raw_exists_d hM hC hT hRun hCap
  obtain ⟨L,hParent⟩ := hA.parent_run_d hM hC hT hRun
  obtain ⟨B,hB⟩ := trim_matrix_exists_d hM hC (hA.raw_valid hRun.space)
  obtain ⟨OtherForests,Other,OtherL,hOther⟩ := matrix_parent_run_exists_d hM hC hB.matrix
  exact ⟨A,B,L,OtherForests,Other,OtherL,hCapEq,hA,hB,hB.normalized,hParent,hOther,
    hB.depth_regular_d hM hC (hA.raw_valid hRun.space) hParent hOther (hA.depth_regular_d hM hC hRun.space)⟩

def MatrixParentAt (M : SetTheory.Structure.{u}) (Forests Rows r c p : M.Domain) : Prop :=
  ∃ Q, M.mem Q Forests ∧ MemPair M Rows r Q ∧ MemPair M Q c p

def matrixParentAtFormula {n : Nat} (Forests Rows r c p : Project.Term n) : Project.Formula 1 n :=
  Project.Formula.existsMem Forests (.conj (memPairFormula Rows.weaken r.weaken (.bound 0))
    (memPairFormula (.bound 0) c.weaken p.weaken))

theorem matrixParentAtFormula_delta0 {n : Nat} (Forests Rows r c p : Project.Term n) :
    (matrixParentAtFormula Forests Rows r c p).IsDelta0 := .existsMem _ (.conj (memPairFormula_delta0 _ _ _) (memPairFormula_delta0 _ _ _))

theorem matrixParentAtFormula_iff {M : SetTheory.Structure.{u}} (he : Extensional M) {n : Nat} (e : Env M n)
    (Forests Rows r c p : Project.Term n) : Project.Formula.satisfies e (matrixParentAtFormula Forests Rows r c p) ↔
      MatrixParentAt M (Forests.eval e) (Rows.eval e) (r.eval e) (c.eval e) (p.eval e) := by
  simp only [matrixParentAtFormula,MatrixParentAt,Project.Formula.satisfies_existsMem_iff,
    Project.Formula.satisfies_conj_iff,memPairFormula_iff he,Term.eval_weaken]
  rfl

def FrameValueCap (M : SetTheory.Structure.{u}) (V cap : M.Domain) : Prop :=
  ∀ c a, MemPair M V c a → a=cap ∨ M.mem a cap

private theorem numeric_no_parent_of_bound_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {m V P H : M.Domain} {R : RowStateSpace M.Domain}
    (hRun : RowRun M C m R V P H) {j W Q c a : M.Domain} (hj : M.mem j C.omega)
    (hAt : RowAt M R.states H j W Q) (hOriginal : MemPair M V c a) (hNot : ¬M.mem j a) : NoParent M m Q c := by
  have hRow := hRun.at_numeric_d hM hC hAt
  obtain ⟨v,_,hV⟩ := hRow.values.total c (hRun.base.values.bounds hM.1 hOriginal).1
  have hValue : RowValue M R.states R.values R.forests H j c v :=
    ⟨W,(hRun.space.values W).mpr hRow.values,Q,(hRun.space.forests Q).mpr hRow.forest,hAt,hV⟩
  have hZero := hRun.value_zero_of_bound_d hM hC hj hValue hOriginal hNot
  intro p hp hParent
  obtain ⟨b,_,hB⟩ := hRow.values.total p hp
  exact hC.zero_empty b (hZero ▸ (hRow.parentValues c p b v hParent hB hV).2)

private theorem ActiveFrame.Valid.numeric_above_cap_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {m V P H : M.Domain} {R : RowStateSpace M.Domain} (hRun : RowRun M C m R V P H)
    {A : ActiveFrame M.Domain} (h : A.Valid M C T m P H R) {j r : M.Domain}
    (hj : M.mem j C.omega) (hAdd : AddAt M T.addPairs T.plus A.frame.height j r) (hOutside : ¬M.mem j A.cap) : ¬M.mem r A.height := by
  have hw := omega_isOrdinal_d hM hC.omega
  have hOffset := natural_successor_mem_d hM hC hRun.space.width h.frame.height
  intro hr
  obtain ⟨i,hi,hI⟩ := sum_tail_index_d hM hC hT hOffset h.cap h.height_sum hr (add_not_below_base_d hM hC hT hOffset hj hAdd)
  have he := natural_sum_cancel_left_d hM hC hOffset (hw.transitive A.cap h.cap i hi) hj
    ((hT.add.add_iff_sum hM hOffset (hw.transitive A.cap h.cap i hi)).mp hI) ((hT.add.add_iff_sum hM hOffset hj).mp hAdd)
  exact hOutside (he ▸ hi)

/-- 数值部分对全部内部j的读值规格；超出cap的行由数值预算证明Depth=0。 -/
theorem ActiveFrame.Valid.numeric_entry_all_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {m V P H : M.Domain} {R : RowStateSpace M.Domain} (hRun : RowRun M C m R V P H)
    {A : ActiveFrame M.Domain} (h : A.Valid M C T m P H R) (hCap : FrameValueCap M V A.cap)
    {j r W Q c d : M.Domain} (hj : M.mem j C.omega) (hAdd : AddAt M T.addPairs T.plus A.frame.height j r)
    (hAt : RowAt M R.states H j W Q) (hc : M.mem c m) :
    PaddedEntry M C.zero (A.raw m) r c d ↔ Depth M C m Q c d := by
  have hw := omega_isOrdinal_d hM hC.omega
  have hRow := hRun.at_numeric_d hM hC hAt
  classical
  by_cases hjCap : M.mem j A.cap
  · have hJoined := (h.numeric_row_iff_d hM hC hT hRun hjCap hAdd).mpr ⟨W,(hRun.space.values W).mpr hRow.values,hAt⟩
    have hr := (h.rows.bounds hM.1 hJoined).1
    have hPads : PaddedEntry M C.zero (A.raw m) r c d ↔ MatrixEntry M (A.raw m) r c d := by
      simp only [PaddedEntry,ActiveFrame.raw,hr,hc,not_true_eq_false,false_and,or_false]
    exact hPads.trans (h.entry_depth_iff_d hM hRun.space hJoined c d)
  · have hrOut := h.numeric_above_cap_d hM hC hT hRun hj hAdd hjCap
    obtain ⟨a,_,hOriginal⟩ := hRun.base.values.total c hc
    have hjA : ¬M.mem j a := by
      intro hja
      rcases hCap c a hOriginal with he | hlt
      · exact hjCap (he ▸ hja)
      · exact hjCap ((hw.mem h.cap).transitive a hlt j hja)
    have hNone := numeric_no_parent_of_bound_d hM hC hRun hj hAt hOriginal hjA
    obtain ⟨e,hDepth⟩ := depth_exists_d hM hC hRow.forest hc
    have heZero := depth_of_no_parent_d hM hC hRow.forest hNone hDepth
    have hDepthZero : Depth M C m Q c C.zero := heZero ▸ hDepth
    constructor
    · rintro (hEntry | ⟨_,he⟩)
      · exact False.elim (hrOut (hEntry.bounds hM.1 (h.raw_valid hRun.space)).1)
      · exact he.symm ▸ hDepthZero
    · intro hDepth
      exact Or.inr ⟨Or.inl hrOut,depth_of_no_parent_d hM hC hRow.forest hNone hDepth⟩

/-- 全部内部j的父关系规格：有限Rows域外无行，且真实数值山形同样无父。 -/
theorem ActiveFrame.Valid.numeric_parent_all_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {m V P H : M.Domain} {R : RowStateSpace M.Domain} (hRun : RowRun M C m R V P H)
    {A : ActiveFrame M.Domain} (h : A.Valid M C T m P H R) (hCap : FrameValueCap M V A.cap)
    {j r W Q c p : M.Domain} (hj : M.mem j C.omega) (hAdd : AddAt M T.addPairs T.plus A.frame.height j r)
    (hAt : RowAt M R.states H j W Q) (hc : M.mem c m) :
    MatrixParentAt M R.forests A.rows r c p ↔ MemPair M Q c p := by
  have hw := omega_isOrdinal_d hM hC.omega
  have hRow := hRun.at_numeric_d hM hC hAt
  classical
  by_cases hjCap : M.mem j A.cap
  · have hJoined := (h.numeric_row_iff_d hM hC hT hRun hjCap hAdd).mpr ⟨W,(hRun.space.values W).mpr hRow.values,hAt⟩
    constructor
    · rintro ⟨Q',_,hQ',hParent⟩
      exact h.rows.unique r Q' Q hQ' hJoined ▸ hParent
    · intro hParent
      exact ⟨Q,(hRun.space.forests Q).mpr hRow.forest,hJoined,hParent⟩
  · have hrOut := h.numeric_above_cap_d hM hC hT hRun hj hAdd hjCap
    obtain ⟨a,_,hOriginal⟩ := hRun.base.values.total c hc
    have hjA : ¬M.mem j a := by
      intro hja
      rcases hCap c a hOriginal with he | hlt
      · exact hjCap (he ▸ hja)
      · exact hjCap ((hw.mem h.cap).transitive a hlt j hja)
    apply iff_of_false
    · rintro ⟨_,_,hAt,_⟩
      exact hrOut (h.rows.bounds hM.1 hAt).1
    · intro hParent
      exact numeric_no_parent_of_bound_d hM hC hRun hj hAt hOriginal hjA p (hRow.forest.bounds hM.1 hParent).2 hParent

/-- trim前后用有限Rows查找的父关系全域一致；被删旧行的无父性已证明。 -/
theorem TrimmedMatrix.parent_at_iff_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {A B : FiniteMatrix M.Domain} (hA : A.Valid M C.omega)
    {Forests Rows L OtherForests Other OtherL : M.Domain}
    (hRun : MatrixParentRun M C A.width A.height A.cells A.values Forests Rows L)
    (h : TrimmedMatrix M C A B) (hOther : MatrixParentRun M C B.width B.height B.cells B.values OtherForests Other OtherL)
    (r c p : M.Domain) : MatrixParentAt M OtherForests Other r c p ↔ MatrixParentAt M Forests Rows r c p := by
  constructor
  · rintro ⟨Q,_,hQ,hParent⟩
    have hr := (hOther.graph.bounds hM.1 hQ).1
    obtain ⟨P,hPMem,hP⟩ := hRun.graph.total r (h.trim.below r hr)
    have he := h.parent_rows_d hM hC hA hRun hOther r P Q hP hQ
    exact ⟨P,hPMem,hP,he.symm ▸ hParent⟩
  · rintro ⟨P,_,hP,hParent⟩
    classical
    by_cases hr : M.mem r B.height
    · obtain ⟨Q,hQMem,hQ⟩ := hOther.graph.total r hr
      have he := h.parent_rows_d hM hC hA hRun hOther r P Q hP hQ
      exact ⟨Q,hQMem,hQ,he ▸ hParent⟩
    · exact False.elim (h.tail_parent_empty_d hM hC hA hRun hP hr c p ((hRun.forests r P hP).bounds hM.1 hParent).2 hParent)

theorem ActiveFrame.Valid.normalized_entry_all_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {m V P H : M.Domain} {R : RowStateSpace M.Domain} (hRun : RowRun M C m R V P H)
    {A : ActiveFrame M.Domain} (h : A.Valid M C T m P H R) (hCap : FrameValueCap M V A.cap)
    {B : FiniteMatrix M.Domain} (hTrim : TrimmedMatrix M C (A.raw m) B)
    {j r W Q c d : M.Domain} (hj : M.mem j C.omega) (hAdd : AddAt M T.addPairs T.plus A.frame.height j r)
    (hAt : RowAt M R.states H j W Q) (hc : M.mem c m) :
    PaddedEntry M C.zero B r c d ↔ Depth M C m Q c d :=
  (hTrim.padded_iff_d hM hC (h.raw_valid hRun.space) r c d).trans (h.numeric_entry_all_d hM hC hT hRun hCap hj hAdd hAt hc)

theorem ActiveFrame.Valid.normalized_parent_all_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {m V P H L : M.Domain} {R : RowStateSpace M.Domain} (hRun : RowRun M C m R V P H)
    {A : ActiveFrame M.Domain} (h : A.Valid M C T m P H R) (hCap : FrameValueCap M V A.cap)
    (hRaw : MatrixParentRun M C m A.height A.cells A.values R.forests A.rows L)
    {B : FiniteMatrix M.Domain} (hTrim : TrimmedMatrix M C (A.raw m) B) {OtherForests Other OtherL : M.Domain}
    (hOther : MatrixParentRun M C B.width B.height B.cells B.values OtherForests Other OtherL)
    {j r W Q c p : M.Domain} (hj : M.mem j C.omega) (hAdd : AddAt M T.addPairs T.plus A.frame.height j r)
    (hAt : RowAt M R.states H j W Q) (hc : M.mem c m) :
    MatrixParentAt M OtherForests Other r c p ↔ MemPair M Q c p :=
  (hTrim.parent_at_iff_d hM hC (h.raw_valid hRun.space) hRaw hOther r c p).trans
    (h.numeric_parent_all_d hM hC hT hRun hCap hj hAdd hAt hc)

/-- 帧容量也由真实有限值图的内部上界构造，不要求预先提供合适cap。 -/
theorem active_frame_bounded_exists_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {m V P H : M.Domain} {R : RowStateSpace M.Domain} (hRun : RowRun M C m R V P H) :
    ∃ A : ActiveFrame M.Domain, ∃ B : FiniteMatrix M.Domain, ∃ L OtherForests Other OtherL,
      A.Valid M C T m P H R ∧ FrameValueCap M V A.cap ∧ TrimmedMatrix M C (A.raw m) B ∧ NormalizedMatrix M C B ∧
      MatrixParentRun M C m A.height A.cells A.values R.forests A.rows L ∧
      MatrixParentRun M C B.width B.height B.cells B.values OtherForests Other OtherL ∧ MatrixDepthRegular M C B OtherForests Other := by
  obtain ⟨cap,hCap,hBound⟩ := finite_natural_range_bounded_d hM hC.omega hRun.space.width hRun.base.values
  obtain ⟨A,B,L,OtherForests,Other,OtherL,hCapEq,hA,hTrim,hNorm,hRaw,hOther,hI⟩ := active_frame_exists_d hM hC hT hRun hCap
  have hCapA : FrameValueCap M V A.cap := hCapEq.symm ▸ (show FrameValueCap M V cap from fun c a hAt => Or.inr (hBound c a hAt))
  exact ⟨A,B,L,OtherForests,Other,OtherL,hA,hCapA,hTrim,hNorm,hRaw,hOther,hI⟩

/-- 真实高度证书强制BM4最大活动行恰为offset+d；不是额外指定该搜索结果。 -/
theorem ActiveFrame.Valid.maximal_parent_row_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {m V P H L : M.Domain} {R : RowStateSpace M.Domain} (hRun : RowRun M C m R V P H)
    {A : ActiveFrame M.Domain} (h : A.Valid M C T m P H R) (hCap : FrameValueCap M V A.cap)
    (hRaw : MatrixParentRun M C m A.height A.cells A.values R.forests A.rows L)
    {B : FiniteMatrix M.Domain} (hTrim : TrimmedMatrix M C (A.raw m) B) {OtherForests Other OtherL : M.Domain}
    (hOther : MatrixParentRun M C B.width B.height B.cells B.values OtherForests Other OtherL)
    {last root d height active a W Q : M.Domain} (hWidth : M.SuccessorOf m last)
    (hOriginal : MemPair M V last a) (hPositive : M.mem C.zero a) (hHeight : HeightAt M C R V H last height)
    (hSuccessor : M.SuccessorOf height d) (hAt : RowAt M R.states H d W Q) (hParent : MemPair M Q last root)
    (hAdd : AddAt M T.addPairs T.plus A.frame.height d active) :
    MaximalParentRow M B.height OtherForests Other B.width last active := by
  have hw := omega_isOrdinal_d hM hC.omega
  have hd := (hAdd.bounds hM.1 hT.add).2.1
  have hActiveNat := (hAdd.bounds hM.1 hT.add).2.2
  have hOffset := natural_successor_mem_d hM hC hRun.space.width h.frame.height
  have hNewParent := (h.normalized_parent_all_d hM hC hT hRun hCap hRaw hTrim hOther hd hAdd hAt hWidth.predecessor_mem).mpr hParent
  obtain ⟨PActive,hPAMem,hPA,hActiveParent⟩ := hNewParent
  have hActiveBound := (hOther.graph.bounds hM.1 hPA).1
  refine Or.inr ⟨hActiveBound,⟨PActive,hPAMem,hPA,root,(hOther.forests active PActive hPA).bounds hM.1 hActiveParent |>.2,hActiveParent⟩,?_⟩
  intro r hr hActive
  have hrNat := hw.transitive B.height hTrim.matrix.height r hr
  rcases hw.wellOrder.linear.compare r hrNat active hActiveNat with he | hlt | hgt
  · exact Or.inl (hM.1.eq_of_same_members r active he)
  · exact Or.inr hlt
  · have hNotFrame : ¬M.mem r A.frame.height := by
      intro hRFrame
      have hRActive := sum_base_subset_d hM (hw.mem hOffset) ((hT.add.add_iff_sum hM hOffset hd).mp hAdd) r hRFrame
      exact SetTheory.KP.mem_irrefl_d (KP1Y.models_weakKP hM) r ((hw.mem hrNat).transitive active hgt r hRActive)
    obtain ⟨j,hj,hJR⟩ := sum_tail_index_d hM hC hT hOffset h.cap h.height_sum (hTrim.trim.below r hr) hNotFrame
    have hjNat := hw.transitive A.cap h.cap j hj
    have hdj : M.mem d j := by
      rcases hw.wellOrder.linear.compare j hjNat d hd with he | hlt | hgt'
      · have hJEq := hM.1.eq_of_same_members j d he
        subst j
        have hREq := hT.add.add_unique hM.1 hJR hAdd
        exact False.elim (SetTheory.KP.mem_irrefl_d (KP1Y.models_weakKP hM) active (hREq ▸ hgt))
      · have hRActive := sum_strict_right_d hM (hw.mem hOffset) ((hT.add.add_iff_sum hM hOffset hjNat).mp hJR)
          ((hT.add.add_iff_sum hM hOffset hd).mp hAdd) hlt
        exact False.elim (SetTheory.KP.mem_irrefl_d (KP1Y.models_weakKP hM) r ((hw.mem hrNat).transitive active hgt r hRActive))
      · exact hgt'
    obtain ⟨U,F,hJ⟩ := hRun.at_exists_d hjNat
    obtain ⟨Q',hQMem,hQAt,p,_,hQP⟩ := hActive
    have hJP := (h.normalized_parent_all_d hM hC hT hRun hCap hRaw hTrim hOther hjNat hJR hJ hWidth.predecessor_mem).mp
      ⟨Q',hQMem,hQAt,hQP⟩
    have hjHeight := (hRun.parent_iff_lt_height_d hM hC hJ hOriginal hPositive hHeight).mp ⟨p,hJP⟩
    rcases (hSuccessor j).mp hjHeight with hjd | he
    · exact False.elim (SetTheory.KP.mem_irrefl_d (KP1Y.models_weakKP hM) j ((hw.mem hjNat).transitive d hdj j hjd))
    · have hJEq := hM.1.eq_of_same_members j d he
      exact False.elim (SetTheory.KP.mem_irrefl_d (KP1Y.models_weakKP hM) d (hJEq ▸ hdj))

/-- 数值山形的实际终止层给出规范矩阵上的真实展开Context，last/root及活动行均精确。 -/
theorem ActiveFrame.Valid.terminal_context_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {m V P H L : M.Domain} {R : RowStateSpace M.Domain} (hRun : RowRun M C m R V P H)
    {A : ActiveFrame M.Domain} (h : A.Valid M C T m P H R) (hCap : FrameValueCap M V A.cap)
    (hRaw : MatrixParentRun M C m A.height A.cells A.values R.forests A.rows L)
    {B : FiniteMatrix M.Domain} (hTrim : TrimmedMatrix M C (A.raw m) B) {OtherForests Other OtherL : M.Domain}
    (hOther : MatrixParentRun M C B.width B.height B.cells B.values OtherForests Other OtherL)
    {last root d height active a W Q : M.Domain} (hWidth : M.SuccessorOf m last)
    (hOriginal : MemPair M V last a) (hPositive : M.mem C.zero a) (hHeight : HeightAt M C R V H last height)
    (hSuccessor : M.SuccessorOf height d) (hAt : RowAt M R.states H d W Q) (hParent : MemPair M Q last root)
    (hAdd : AddAt M T.addPairs T.plus A.frame.height d active) :
    MatrixExpansionContext M C B OtherForests Other last active root := by
  have hMax := h.maximal_parent_row_d hM hC hT hRun hCap hRaw hTrim hOther hWidth hOriginal hPositive hHeight hSuccessor hAt hParent hAdd
  obtain ⟨PActive,hPAMem,hPA,hParent'⟩ := (h.normalized_parent_all_d hM hC hT hRun hCap hRaw hTrim hOther
    (hAdd.bounds hM.1 hT.add).2.1 hAdd hAt hWidth.predecessor_mem).mpr hParent
  exact ⟨hTrim.width.symm ▸ hWidth,hMax,(hOther.graph.bounds hM.1 hPA).1,PActive,hPAMem,hPA,hParent'⟩

/-- 差一坏根直接生成活动帧、独立top图和正确的BM4展开Context。
cap、帧、规范化矩阵、高度图、top图及活动行地址均由实际对象构造。
-/
theorem row_bad_active_frame_exists_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {m V P H d last root : M.Domain} {R : RowStateSpace M.Domain}
    (hRun : RowRun M C m R V P H) (hBase : RootedRow M C m V P) (hWidth : M.SuccessorOf m last)
    (hBad : RowBadAt M C R H d last root) :
    ∃ A : ActiveFrame M.Domain, ∃ B : FiniteMatrix M.Domain, ∃ L OtherForests Other OtherL Heights Top active,
      A.Valid M C T m P H R ∧ FrameValueCap M V A.cap ∧ TrimmedMatrix M C (A.raw m) B ∧ NormalizedMatrix M C B ∧
      MatrixParentRun M C m A.height A.cells A.values R.forests A.rows L ∧
      MatrixParentRun M C B.width B.height B.cells B.values OtherForests Other OtherL ∧ MatrixDepthRegular M C B OtherForests Other ∧
      HeightGraph M C m R V H Heights ∧ TopValueGraph M C m R H Heights Top ∧ MemPair M Top last C.one ∧
      AddAt M T.addPairs T.plus A.frame.height d active ∧ MatrixExpansionContext M C B OtherForests Other last active root := by
  obtain ⟨A,B,L,OtherForests,Other,OtherL,hA,hCap,hTrim,hNorm,hRaw,hOther,hI⟩ := active_frame_bounded_exists_d hM hC hT hRun
  obtain ⟨Heights,Top,hHeights,hTop⟩ := mountain_height_top_exists_d hM hC hRun
  obtain ⟨height,_,hHeight⟩ := hHeights.graph.total last hWidth.predecessor_mem
  obtain ⟨hHeightSucc,hTopOne⟩ := row_bad_height_top_d hM hC hRun hBase hHeights hTop hBad hHeight
  obtain ⟨W,_,Q,_,hAt,hParent,_⟩ := hBad
  have hd : M.mem d C.omega := by
    obtain ⟨_,_,hD,_⟩ := hAt
    exact (hRun.graph.bounds hM.1 hD).1
  have hOffset := natural_successor_mem_d hM hC hRun.space.width hA.frame.height
  obtain ⟨active,_,hAdd⟩ := hT.add.add_exists_d hM hC hOffset hd
  obtain ⟨a,_,hOriginal⟩ := hRun.base.values.total last hWidth.predecessor_mem
  have hContext := hA.terminal_context_d hM hC hT hRun hCap hRaw hTrim hOther hWidth hOriginal (hBase.positive last a hOriginal)
    ((hHeights.rows last height).mp hHeight).2 hHeightSucc hAt hParent hAdd
  exact ⟨A,B,L,OtherForests,Other,OtherL,Heights,Top,active,hA,hCap,hTrim,hNorm,hRaw,hOther,hI,hHeights,hTop,hTopOne,hAdd,hContext⟩

end KP1Y.OneYFinite
