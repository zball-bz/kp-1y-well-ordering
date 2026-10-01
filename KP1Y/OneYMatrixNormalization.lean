import KP1Y.OneYFiniteBlocker

/-! 实际 BM4 的 trimZeroRows 与退化删除分支。保留行域之外只主张补零读值，
不伪造父运行在有限 Rows 域外的额外行。
-/
namespace KP1Y.OneYFinite
open YesMetaZFC YesMetaZFC.SetTheory YesMetaZFC.SetTheory.Definitional
open KP1Y.Kuratowski KP1Y.Functions KP1Y.Naturals KP1Y.Bounded
universe u

def ActiveValueRow (M : SetTheory.Structure.{u}) (C : ExpressionData M.Domain) (A : FiniteMatrix M.Domain) (r : M.Domain) : Prop :=
  ∃ c, M.mem c A.width ∧ ∃ d, M.mem d C.omega ∧ MatrixEntry M A r c d ∧ d≠C.zero

private def activeValueEnv {M : SetTheory.Structure.{u}} (C : ExpressionData M.Domain) (A : FiniteMatrix M.Domain) : Env M 6 :=
  (((((oneEnv C.zero).push C.omega).push A.height).push A.width).push A.cells).push A.values

private def activeValueSchema : Project.Delta0UnarySchema 6 where
  body := Project.Formula.existsMem (.bound 3) (Project.Formula.existsMem (.bound 6)
    (.conj (matrixEntryFormula ⟨.bound 6,.bound 5,.bound 4,.bound 3⟩ (.bound 2) (.bound 1) (.bound 0))
      (.neg (Project.Formula.extensionalEq (.bound 0) (.bound 8)))))
  freeClosed := by
    simp [matrixEntryFormula,memPairFormula,codeFormula,pairFormula,Project.Formula.existsMem,
      Project.Formula.forallMem,Definitional.Formula.FreeClosed]
  delta0 := .existsMem _ (.existsMem _ (.conj (matrixEntryFormula_delta0 _ _ _ _) (.neg (.atom _ _ _))))

private theorem activeValueSchema_iff {M : SetTheory.Structure.{u}} (he : Extensional M)
    (C : ExpressionData M.Domain) (A : FiniteMatrix M.Domain) (r : M.Domain) :
    Project.Formula.satisfies ((activeValueEnv C A).push r) activeValueSchema.body ↔ ActiveValueRow M C A r := by
  simp only [activeValueSchema,ActiveValueRow,Project.Formula.satisfies_existsMem_iff,
    Project.Formula.satisfies_conj_iff,matrixEntryFormula_iff he,Project.Formula.satisfies_neg_iff,
    Project.Formula.satisfies_extensionalEq_iff_eq he]
  rfl

/-- 真实支撑高度：其上全部值0，且非零高度的最后保留行确有非零值。 -/
structure TrimHeight (M : SetTheory.Structure.{u}) (C : ExpressionData M.Domain) (A : FiniteMatrix M.Domain) (height : M.Domain) : Prop where
  natural : M.mem height C.omega
  below : M.MemberSubset height A.height
  zero_above : ∀ r, M.mem r A.height → ¬M.mem r height → ∀ c, M.mem c A.width → ∀ d, MatrixEntry M A r c d → d=C.zero
  top : height=C.zero ∨ ∃ p, M.SuccessorOf height p ∧ ActiveValueRow M C A p

/-- Δ0分离全部非零行，然后内部最大值搜索确定真正的trimHeight。 -/
theorem trim_height_exists_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {A : FiniteMatrix M.Domain} (hA : A.Valid M C.omega) :
    ∃ height, TrimHeight M C A height := by
  obtain ⟨Active,hActive⟩ := SetTheory.KP.separation_exists_d (KP1Y.models_weakKP hM) activeValueSchema (activeValueEnv C A) A.height
  have hRows (r : M.Domain) : M.mem r Active ↔ M.mem r A.height ∧ ActiveValueRow M C A r := by
    simpa only [activeValueSchema_iff hM.1] using hActive r
  obtain ⟨last,_,hSearch⟩ := bounded_search_exists_d (A := Active) hM hC.omega hA.height
  rcases hSearch with ⟨_,hNone⟩ | ⟨hLast,hLastActive,hMax⟩
  · refine ⟨C.zero,hC.zero_nat,fun x hx => False.elim (hC.zero_empty x hx),?_,Or.inl rfl⟩
    intro r hr _ c hc d hEntry
    apply Classical.byContradiction
    intro hNot
    exact hNone r hr ((hRows r).mpr ⟨hr,c,hc,d,(hEntry.bounds hM.1 hA).2.2,hEntry,hNot⟩)
  · have hw := omega_isOrdinal_d hM hC.omega
    have hLastNat := hw.transitive A.height hA.height last hLast
    obtain ⟨height,hs,hHeight⟩ := hC.omega.1.2 last hLastNat
    refine ⟨height,hHeight,?_,?_,Or.inr ⟨last,hs,((hRows last).mp hLastActive).2⟩⟩
    · intro x hx
      rcases (hs x).mp hx with hxl | he
      · exact (hw.mem hA.height).transitive last hLast x hxl
      · exact (hM.1.eq_of_same_members x last he).symm ▸ hLast
    · intro r hr hOutside c hc d hEntry
      apply Classical.byContradiction
      intro hNot
      have hRActive := (hRows r).mpr ⟨hr,c,hc,d,(hEntry.bounds hM.1 hA).2.2,hEntry,hNot⟩
      rcases hMax r hr hRActive with he | hlt
      · exact hOutside (he.symm ▸ hs.predecessor_mem)
      · exact hOutside ((hs r).mpr (Or.inl hlt))

theorem TrimHeight.active_below {M : SetTheory.Structure.{u}} (he : Extensional M)
    {C : ExpressionData M.Domain} {A : FiniteMatrix M.Domain} (hA : A.Valid M C.omega) {height r : M.Domain}
    (h : TrimHeight M C A height) (hActive : ActiveValueRow M C A r) : M.mem r height := by
  obtain ⟨c,hc,d,_,hEntry,hNonzero⟩ := hActive
  apply Classical.byContradiction
  intro hNot
  exact hNonzero (h.zero_above r (hEntry.bounds he hA).1 hNot c hc d hEntry)

theorem TrimHeight.unique_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {A : FiniteMatrix M.Domain} (hA : A.Valid M C.omega) {h k : M.Domain}
    (hH : TrimHeight M C A h) (hK : TrimHeight M C A k) : h=k := by
  have sub {h k : M.Domain} (hH : TrimHeight M C A h) (hK : TrimHeight M C A k) : M.MemberSubset h k := by
    intro x hx
    rcases hH.top with he | ⟨p,hs,hActive⟩
    · exact False.elim (hC.zero_empty x (he ▸ hx))
    · have hp := hK.active_below hM.1 hA hActive
      rcases (hs x).mp hx with hxp | he
      · exact ((omega_isOrdinal_d hM hC.omega).mem hK.natural).transitive p hp x hxp
      · exact (hM.1.eq_of_same_members x p he).symm ▸ hp
  exact hM.1.eq_of_same_members h k (fun x => ⟨sub hH hK x,sub hK hH x⟩)

theorem TrimHeight.width_zero_d {M : SetTheory.Structure.{u}}
    {C : ExpressionData M.Domain} (hC : C.Valid M) {A : FiniteMatrix M.Domain} {height : M.Domain}
    (h : TrimHeight M C A height) (hWidth : A.width=C.zero) : height=C.zero := by
  rcases h.top with he | ⟨_,_,c,hc,_,_,_,_⟩
  · exact he
  · exact False.elim (hC.zero_empty c (hWidth ▸ hc))

/-- 沿内部行高限制实际矩阵图。 -/
theorem FiniteMatrix.Valid.height_prefix_exists_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {w : M.Domain} {A : FiniteMatrix M.Domain} (hA : A.Valid M w) {height : M.Domain}
    (hHeight : M.mem height w) (hSub : M.MemberSubset height A.height) :
    ∃ B, B.Valid M w ∧ B.height=height ∧ B.width=A.width ∧
      ∀ r c d, MatrixEntry M B r c d ↔ M.mem r height ∧ MatrixEntry M A r c d := by
  obtain ⟨Cells,hCells⟩ := product_exists hM height A.width
  have hCellsSub : M.MemberSubset Cells A.cells := by
    intro key hk
    obtain ⟨r,hr,c,hc,hCode⟩ := (hCells key).mp hk
    exact (hA.cells key).mpr ⟨r,hSub r hr,c,hc,hCode⟩
  obtain ⟨Values,hValues,hRows⟩ := restrict_graph_d hM hA.values hCellsSub
  let B : FiniteMatrix M.Domain := ⟨height,A.width,Cells,Values⟩
  refine ⟨B,⟨hHeight,hA.width,hCells,hValues⟩,rfl,rfl,?_⟩
  intro r c d
  constructor
  · rintro ⟨key,hk,hCode,hAt⟩
    obtain ⟨r',hr,c',_,hCode'⟩ := (hCells key).mp hk
    obtain ⟨hrr,hcc⟩ := codes_injective hM.1 hCode' hCode
    subst r'
    subst c'
    exact ⟨hr,key,hCellsSub key hk,hCode,((hRows key d).mp hAt).2⟩
  · rintro ⟨hr,key,hk,hCode,hAt⟩
    obtain ⟨r',_,c',hc,hCode'⟩ := (hA.cells key).mp hk
    obtain ⟨hrr,hcc⟩ := codes_injective hM.1 hCode' hCode
    subst r'
    subst c'
    have hk' := (hCells key).mpr ⟨r,hr,c,hc,hCode⟩
    exact ⟨key,hk',hCode,(hRows key d).mpr ⟨hk',hAt⟩⟩

structure TrimmedMatrix (M : SetTheory.Structure.{u}) (C : ExpressionData M.Domain) (A B : FiniteMatrix M.Domain) : Prop where
  matrix : B.Valid M C.omega
  trim : TrimHeight M C A B.height
  width : B.width=A.width
  entries : ∀ r c d, MatrixEntry M B r c d ↔ M.mem r B.height ∧ MatrixEntry M A r c d

theorem trim_matrix_exists_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {A : FiniteMatrix M.Domain} (hA : A.Valid M C.omega) :
    ∃ B, TrimmedMatrix M C A B := by
  obtain ⟨height,hHeight⟩ := trim_height_exists_d hM hC hA
  obtain ⟨B,hB,hBH,hBW,hEntries⟩ := hA.height_prefix_exists_d hM hHeight.natural hHeight.below
  exact ⟨B,hB,hBH.symm ▸ hHeight,hBW,fun r c d => hBH.symm ▸ hEntries r c d⟩

/-- 删除全零尾行后，全部内部行/列的补零读值完全一致。 -/
theorem TrimmedMatrix.padded_iff_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (_hC : C.Valid M) {A B : FiniteMatrix M.Domain} (hA : A.Valid M C.omega)
    (h : TrimmedMatrix M C A B) (r c d : M.Domain) : PaddedEntry M C.zero B r c d ↔ PaddedEntry M C.zero A r c d := by
  classical
  constructor
  · rintro (hEntry | ⟨hOutside,he⟩)
    · exact Or.inl ((h.entries r c d).mp hEntry).2
    · subst d
      by_cases hr : M.mem r A.height
      · by_cases hc : M.mem c A.width
        · have hrB : ¬M.mem r B.height := hOutside.elim id (fun hn => False.elim (hn (h.width.symm ▸ hc)))
          obtain ⟨e,_,hEntry⟩ := hA.entry_total_d hM hr hc
          have he := h.trim.zero_above r hr hrB c hc e hEntry
          exact Or.inl (he ▸ hEntry)
        · exact Or.inr ⟨Or.inr hc,rfl⟩
      · exact Or.inr ⟨Or.inl hr,rfl⟩
  · rintro (hEntry | ⟨hOutside,he⟩)
    · by_cases hr : M.mem r B.height
      · exact Or.inl ((h.entries r c d).mpr ⟨hr,hEntry⟩)
      · exact Or.inr ⟨Or.inl hr,h.trim.zero_above r (hEntry.bounds hM.1 hA).1 hr c (hEntry.bounds hM.1 hA).2.1 d hEntry⟩
    · exact Or.inr ⟨hOutside.elim (fun hn => Or.inl (fun hr => hn (h.trim.below r hr)))
        (fun hn => Or.inr (fun hc => hn (h.width ▸ hc))),he⟩

def NormalizedMatrix (M : SetTheory.Structure.{u}) (C : ExpressionData M.Domain) (A : FiniteMatrix M.Domain) : Prop :=
  A.height=C.zero ∨ ∃ r, M.SuccessorOf A.height r ∧ ActiveValueRow M C A r

theorem TrimmedMatrix.normalized {M : SetTheory.Structure.{u}}
    {C : ExpressionData M.Domain} {A B : FiniteMatrix M.Domain} (h : TrimmedMatrix M C A B) : NormalizedMatrix M C B := by
  rcases h.trim.top with he | ⟨r,hs,c,hc,d,hd,hEntry,hNot⟩
  · exact Or.inl he
  · exact Or.inr ⟨r,hs,c,h.width.symm ▸ hc,d,hd,(h.entries r c d).mpr ⟨hs.predecessor_mem,hEntry⟩,hNot⟩

/-- 保留行上的实际父图相等；比较只作用于两张有限Rows图共同的域。 -/
theorem TrimmedMatrix.parent_rows_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {A B : FiniteMatrix M.Domain} (hA : A.Valid M C.omega)
    {Forests Rows L OtherForests Other OtherL : M.Domain}
    (hRun : MatrixParentRun M C A.width A.height A.cells A.values Forests Rows L)
    (h : TrimmedMatrix M C A B)
    (hOther : MatrixParentRun M C B.width B.height B.cells B.values OtherForests Other OtherL) :
    ∀ r P Q, MemPair M Rows r P → MemPair M Other r Q → P=Q := by
  have hRows := matrix_parent_common_prefix_d hM hC hA h.matrix hRun hOther hA.width (fun _ hx => hx)
    (fun c hc => h.width.symm ▸ hc) (by
      intro r c d _ hr _
      exact ((h.entries r c d).trans ⟨And.right,fun he => ⟨hr,he⟩⟩).symm)
  intro r P Q hP hQ
  have hPF := hRun.forests r P hP
  have hQF : Forest M C.omega A.width Q := h.width ▸ hOther.forests r Q hQ
  apply hPF.ext hM.1 hQF
  intro c p
  classical
  by_cases hc : M.mem c A.width
  · exact hRows r P Q hP hQ c hc p
  · exact iff_of_false (fun hp => hc (hPF.bounds hM.1 hp).1) (fun hp => hc (hQF.bounds hM.1 hp).1)

/-- 被删除的每一旧行确实没有父边；新有限Rows域外不需要添加伪行。 -/
theorem TrimmedMatrix.tail_parent_empty_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {A B : FiniteMatrix M.Domain} (hA : A.Valid M C.omega)
    {Forests Rows L r P : M.Domain} (hRun : MatrixParentRun M C A.width A.height A.cells A.values Forests Rows L)
    (h : TrimmedMatrix M C A B) (hP : MemPair M Rows r P) (hOutside : ¬M.mem r B.height) :
    ∀ c, NoParent M A.width P c := by
  have hr := (hRun.graph.bounds hM.1 hP).1
  obtain ⟨V,hV⟩ := hRun.values_exist r hr
  obtain ⟨F,hSel⟩ := hRun.selection_at_d hM hC hP hV
  intro c p _ hParent
  obtain ⟨x,_,y,_,_,hY,hxy,_⟩ := hSel.parent_values hParent
  have hZero := h.trim.zero_above r hr hOutside c (hSel.forest.bounds hM.1 hParent).1 y
    ((matrix_row_view_entry_iff_d hM hA hr hV c y).mp hY)
  exact hC.zero_empty x (hZero ▸ hxy)

theorem TrimmedMatrix.depth_regular_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {A B : FiniteMatrix M.Domain} (hA : A.Valid M C.omega)
    {Forests Rows L OtherForests Other OtherL : M.Domain}
    (hRun : MatrixParentRun M C A.width A.height A.cells A.values Forests Rows L)
    (h : TrimmedMatrix M C A B) (hOther : MatrixParentRun M C B.width B.height B.cells B.values OtherForests Other OtherL)
    (hI : MatrixDepthRegular M C A Forests Rows) : MatrixDepthRegular M C B OtherForests Other := by
  intro r hr Q _ hQ c hc d hd hEntry
  obtain ⟨P,hPMem,hP⟩ := hRun.graph.total r (h.trim.below r hr)
  have hEq := h.parent_rows_d hM hC hA hRun hOther r P Q hP hQ
  subst Q
  have hOld := hI r (h.trim.below r hr) P hPMem hP c (h.width ▸ hc) d hd ((h.entries r c d).mp hEntry).2
  refine ⟨?_,?_⟩
  · intro hNone
    exact hOld.1 (fun p hp => hNone p (h.width.symm ▸ hp))
  · intro p hp hParent e he hEntryP
    exact hOld.2 p (h.width ▸ hp) hParent e he ((h.entries r p e).mp hEntryP).2

theorem TrimmedMatrix.aboveS_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {A B : FiniteMatrix M.Domain} (hA : A.Valid M C.omega)
    {Forests Rows L OtherForests Other OtherL base : M.Domain}
    (hRun : MatrixParentRun M C A.width A.height A.cells A.values Forests Rows L)
    (h : TrimmedMatrix M C A B) (hOther : MatrixParentRun M C B.width B.height B.cells B.values OtherForests Other OtherL)
    (hS : AboveS M C A Forests Rows L base) : AboveS M C B OtherForests Other OtherL base := by
  intro r hr hBase F hPrevious Q _ hQ start hStartNat hStart
  obtain ⟨P,hPMem,hP⟩ := hRun.graph.total r (h.trim.below r hr)
  have hEq := h.parent_rows_d hM hC hA hRun hOther r P Q hP hQ
  subst Q
  have hOldPrevious : PreviousMatrixForest M C A.height Forests Rows L r F := by
    rcases hPrevious with ⟨hz,hF⟩ | ⟨j,hj,hs,_,hF⟩
    · have hNewLinear : LinearForest M C.omega A.width OtherL := h.width ▸ hOther.linear
      have hLEq := linear_forest_unique hM.1 hRun.linear hNewLinear
      exact Or.inl ⟨hz,hF.trans hLEq.symm⟩
    · obtain ⟨P0,hP0Mem,hP0⟩ := hRun.graph.total j (h.trim.below j hj)
      have hP0F := h.parent_rows_d hM hC hA hRun hOther j P0 F hP0 hF
      exact Or.inr ⟨j,h.trim.below j hj,hs,hP0F ▸ hP0Mem,hP0F ▸ hP0⟩
  have hOldS := hS r (h.trim.below r hr) hBase F hOldPrevious P hPMem hP start hStartNat hStart
  intro c hc q hq p hp hPrev hCur hNe
  obtain ⟨z,hz,hPath,hZParent,hLe⟩ := hOldS c (h.width ▸ hc) q (h.width ▸ hq) p (h.width ▸ hp) hPrev hCur hNe
  refine ⟨z,h.width.symm ▸ hz,hPath.imp id (fun ha => h.width.symm ▸ ha),hZParent,?_⟩
  exact (column_le_from_congr (fun r d => (h.padded_iff_d hM hC hA r c d).symm)
    (fun r d => (h.padded_iff_d hM hC hA r z d).symm)).mp hLe

/-- 实际构造归一化矩阵及其父运行，并保持I与同一边界以上S。 -/
theorem relative_structural_trim_exists_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {A : FiniteMatrix M.Domain} (hA : A.Valid M C.omega)
    {Forests Rows L base : M.Domain} (hRun : MatrixParentRun M C A.width A.height A.cells A.values Forests Rows L)
    (hI : MatrixDepthRegular M C A Forests Rows) (hS : AboveS M C A Forests Rows L base) :
    ∃ B OtherForests Other OtherL, TrimmedMatrix M C A B ∧ NormalizedMatrix M C B ∧
      MatrixParentRun M C B.width B.height B.cells B.values OtherForests Other OtherL ∧
      MatrixDepthRegular M C B OtherForests Other ∧ AboveS M C B OtherForests Other OtherL base := by
  obtain ⟨B,hB⟩ := trim_matrix_exists_d hM hC hA
  obtain ⟨OtherForests,Other,OtherL,hOther⟩ := matrix_parent_run_exists_d hM hC hB.matrix
  exact ⟨B,OtherForests,Other,OtherL,hB,hB.normalized,hOther,
    hB.depth_regular_d hM hC hA hRun hOther hI,hB.aboveS_d hM hC hA hRun hOther hS⟩

theorem FiniteMatrix.Valid.ext_entries_d {M : SetTheory.Structure.{u}} (he : Extensional M)
    {w : M.Domain} {A B : FiniteMatrix M.Domain} (hA : A.Valid M w) (hB : B.Valid M w)
    (hHeight : A.height=B.height) (hWidth : A.width=B.width)
    (hEntries : ∀ r c d, MatrixEntry M A r c d ↔ MatrixEntry M B r c d) : A=B := by
  cases A with | mk ah aw ac av =>
    cases B with | mk bh bw bc bv =>
      dsimp at hHeight hWidth
      subst bh
      subst bw
      have hCells : ac=bc := he.eq_of_same_members ac bc (fun key => (hA.cells key).trans (hB.cells key).symm)
      subst bc
      have hValues : av=bv := hA.values.ext he hB.values (by
        intro key hk d
        obtain ⟨r,_,c,_,hCode⟩ := (hA.cells key).mp hk
        constructor
        · intro hAt
          obtain ⟨key',_,hCode',hAt'⟩ := (hEntries r c d).mp ⟨key,hk,hCode,hAt⟩
          exact codes_unique he hCode' hCode ▸ hAt'
        · intro hAt
          obtain ⟨key',_,hCode',hAt'⟩ := (hEntries r c d).mpr ⟨key,hk,hCode,hAt⟩
          exact codes_unique he hCode' hCode ▸ hAt')
      subst bv
      rfl

theorem TrimmedMatrix.unique_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {A B D : FiniteMatrix M.Domain} (hA : A.Valid M C.omega)
    (hB : TrimmedMatrix M C A B) (hD : TrimmedMatrix M C A D) : B=D := by
  have hHeight := hB.trim.unique_d hM hC hA hD.trim
  exact hB.matrix.ext_entries_d hM.1 hD.matrix hHeight (hB.width.trans hD.width.symm)
    (fun r c d => by rw [hB.entries,hD.entries,hHeight])

/-- expandRaw 的三个可达分支。搜索成功但读不到父项的源码fallback由真实搜索规格排除。 -/
def RawMatrixStep (M : SetTheory.Structure.{u}) (C : ExpressionData M.Domain) (A : FiniteMatrix M.Domain)
    (T : MatrixArithmetic M.Domain) (Forests Rows index : M.Domain) (R : FiniteMatrix M.Domain) : Prop :=
  (A.width=C.zero ∧ R.height=C.zero ∧ R.width=C.zero) ∨
    ∃ last, M.SuccessorOf A.width last ∧
      (((∀ r, M.mem r A.height → ¬ActiveParentRow M Forests Rows A.width last r) ∧
        R.height=A.height ∧ R.width=last ∧ ∀ r c d, MatrixEntry M R r c d ↔ M.mem c last ∧ MatrixEntry M A r c d) ∨
        ∃ maximal root count len total, MatrixExpansionContext M C A Forests Rows last maximal root ∧
          RawMatrixExpansion M C A T Forests Rows last maximal root index count len total R)

/-- 完整实际矩阵展开，先执行真实raw分支，再删除全部全零尾行。 -/
def MatrixExpansion (M : SetTheory.Structure.{u}) (C : ExpressionData M.Domain) (A : FiniteMatrix M.Domain)
    (T : MatrixArithmetic M.Domain) (Forests Rows index : M.Domain) (B : FiniteMatrix M.Domain) : Prop :=
  ∃ R, R.Valid M C.omega ∧ RawMatrixStep M C A T Forests Rows index R ∧ TrimmedMatrix M C R B

theorem matrix_raw_step_exists_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {A : FiniteMatrix M.Domain} (hA : A.Valid M C.omega)
    {T : MatrixArithmetic M.Domain} (hT : T.Valid M C) {Forests Rows L index : M.Domain}
    (hRun : MatrixParentRun M C A.width A.height A.cells A.values Forests Rows L) (hIndex : M.mem index C.omega) :
    ∃ R, R.Valid M C.omega ∧ RawMatrixStep M C A T Forests Rows index R := by
  have hw := omega_isOrdinal_d hM hC.omega
  rcases natural_cases hM hC.omega hA.width with hEmpty | ⟨last,hLastNat,hWidth⟩
  · have hWidth := hM.1.eq_of_same_members A.width C.zero (fun t => iff_of_false (hEmpty t) (hC.zero_empty t))
    obtain ⟨R,hR,hRH,hRW,_⟩ := hA.height_prefix_exists_d hM hC.zero_nat (fun t ht => False.elim (hC.zero_empty t ht))
    exact ⟨R,hR,Or.inl ⟨hWidth,hRH,hRW.trans hWidth⟩⟩
  · obtain ⟨maximal,_,hMax⟩ := maximal_parent_row_exists_d hM hC.omega hA.height Forests Rows A.width last
    rcases hMax with ⟨_,hNone⟩ | ⟨hRow,hActive,hGreatest⟩
    · have hSub := (hw.mem hA.width).transitive last hWidth.predecessor_mem
      obtain ⟨R,hR,hRH,hRW,hEntries⟩ := hA.prefix_exists_d hM hLastNat hSub
      refine ⟨R,hR,Or.inr ⟨last,hWidth,Or.inl ⟨hNone,hRH,hRW,?_⟩⟩⟩
      intro r c d
      constructor
      · intro hEntry
        have hc : M.mem c last := hRW ▸ (hEntry.bounds hM.1 hR).2.1
        exact ⟨hc,(hEntries r c d hc).mp hEntry⟩
      · rintro ⟨hc,hEntry⟩
        exact (hEntries r c d hc).mpr hEntry
    · have hSuccess : maximal≠A.height := fun he => SetTheory.KP.mem_irrefl_d (KP1Y.models_weakKP hM) A.height (he ▸ hRow)
      obtain ⟨root,hContext⟩ := matrix_expansion_context_exists hWidth (Or.inr ⟨hRow,hActive,hGreatest⟩) hSuccess
      obtain ⟨count,len,total,R,hRaw⟩ := matrix_expand_raw_context_d hM hC hA hT hRun hContext hIndex
      exact ⟨R,hRaw.matrix,Or.inr ⟨last,hWidth,Or.inr ⟨maximal,root,count,len,total,hContext,hRaw⟩⟩⟩

theorem matrix_expansion_exists_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {A : FiniteMatrix M.Domain} (hA : A.Valid M C.omega)
    {T : MatrixArithmetic M.Domain} (hT : T.Valid M C) {Forests Rows L index : M.Domain}
    (hRun : MatrixParentRun M C A.width A.height A.cells A.values Forests Rows L) (hIndex : M.mem index C.omega) :
    ∃ B, MatrixExpansion M C A T Forests Rows index B := by
  obtain ⟨R,hR,hRaw⟩ := matrix_raw_step_exists_d hM hC hA hT hRun hIndex
  obtain ⟨B,hB⟩ := trim_matrix_exists_d hM hC hR
  exact ⟨B,R,hR,hRaw,hB⟩

theorem MatrixExpansion.matrix {M : SetTheory.Structure.{u}} {C : ExpressionData M.Domain} {A B : FiniteMatrix M.Domain}
    {T : MatrixArithmetic M.Domain} {Forests Rows index : M.Domain} (h : MatrixExpansion M C A T Forests Rows index B) : B.Valid M C.omega := by
  obtain ⟨_,_,_,hTrim⟩ := h
  exact hTrim.matrix

theorem MatrixExpansion.normalized {M : SetTheory.Structure.{u}} {C : ExpressionData M.Domain} {A B : FiniteMatrix M.Domain}
    {T : MatrixArithmetic M.Domain} {Forests Rows index : M.Domain} (h : MatrixExpansion M C A T Forests Rows index B) : NormalizedMatrix M C B := by
  obtain ⟨_,_,_,hTrim⟩ := h
  exact hTrim.normalized

theorem RawMatrixStep.relative_structural_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {A R : FiniteMatrix M.Domain} (hA : A.Valid M C.omega)
    {T : MatrixArithmetic M.Domain} (hT : T.Valid M C) {Forests Rows L RawForests RawRows RawL index base : M.Domain}
    (hRun : MatrixParentRun M C A.width A.height A.cells A.values Forests Rows L)
    (hR : R.Valid M C.omega) (hRaw : RawMatrixStep M C A T Forests Rows index R)
    (hRawRun : MatrixParentRun M C R.width R.height R.cells R.values RawForests RawRows RawL)
    (hIndex : M.mem index C.omega) (hI : MatrixDepthRegular M C A Forests Rows) (hS : AboveS M C A Forests Rows L base) :
    MatrixDepthRegular M C R RawForests RawRows ∧ AboveS M C R RawForests RawRows RawL base := by
  rcases hRaw with ⟨_,hHeight,_⟩ | ⟨last,hWidth,hCase⟩
  · exact ⟨fun r hr => False.elim (hC.zero_empty r (hHeight ▸ hr)),fun r hr => False.elim (hC.zero_empty r (hHeight ▸ hr))⟩
  · rcases hCase with ⟨_,hHeight,hRW,hEntries⟩ | ⟨maximal,root,count,len,total,hContext,hExp⟩
    · have hSub : M.MemberSubset R.width A.width := by
        intro c hc
        exact ((omega_isOrdinal_d hM hC.omega).mem hA.width).transitive last hWidth.predecessor_mem c (hRW ▸ hc)
      have hEntry (r c d : M.Domain) (hc : M.mem c R.width) : MatrixEntry M R r c d ↔ MatrixEntry M A r c d :=
        (hEntries r c d).trans ⟨And.right,fun h => ⟨hRW ▸ hc,h⟩⟩
      have hParents := matrix_parent_common_prefix_d hM hC hA hR hRun hRawRun hR.width hSub (fun _ hc => hc)
        (fun r c d _ _ hc => (hEntry r c d hc).symm)
      exact ⟨depth_regular_prefix_d hM hC hR hRun hHeight hSub hParents hEntry hI,
        aboveS_prefix_d hM hC hR hRun hRawRun hHeight hSub hParents hEntry hS⟩
    · obtain ⟨first,hFirst,_⟩ := hC.omega.1.2 root hExp.difference.2.1
      let X : CopyCoordinates.Context M.Domain := ⟨last,root,len,first⟩
      have hX : X.Valid M C := ⟨hExp.difference.1,hExp.difference.2.1,hContext.root_lt_last hRun,hExp.difference,hFirst⟩
      exact ⟨hExp.depth_regular_d hM hC hA hT hX hRun hContext hRawRun hIndex hI,
        hExp.aboveS_d hM hC hA hT hX hRun hContext hRawRun hIndex hS⟩

/-- 完整expand保持I与同一base以上S；包括空宽度、无活动父行、非退化复制和最后裁剪。 -/
theorem MatrixExpansion.relative_structural_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {A B : FiniteMatrix M.Domain} (hA : A.Valid M C.omega)
    {T : MatrixArithmetic M.Domain} (hT : T.Valid M C) {Forests Rows L OtherForests Other OtherL index base : M.Domain}
    (hRun : MatrixParentRun M C A.width A.height A.cells A.values Forests Rows L)
    (h : MatrixExpansion M C A T Forests Rows index B)
    (hOther : MatrixParentRun M C B.width B.height B.cells B.values OtherForests Other OtherL)
    (hIndex : M.mem index C.omega) (hI : MatrixDepthRegular M C A Forests Rows) (hS : AboveS M C A Forests Rows L base) :
    MatrixDepthRegular M C B OtherForests Other ∧ AboveS M C B OtherForests Other OtherL base := by
  obtain ⟨R,hR,hRaw,hTrim⟩ := h
  obtain ⟨RawForests,RawRows,RawL,hRawRun⟩ := matrix_parent_run_exists_d hM hC hR
  obtain ⟨hRI,hRS⟩ := hRaw.relative_structural_d hM hC hA hT hRun hR hRawRun hIndex hI hS
  exact ⟨hTrim.depth_regular_d hM hC hR hRawRun hOther hRI,hTrim.aboveS_d hM hC hR hRawRun hOther hRS⟩

/-- 完整实际expand及其实际父运行存在，同时满足规范性和相对结构保持。 -/
theorem matrix_expansion_structural_exists_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {A : FiniteMatrix M.Domain} (hA : A.Valid M C.omega)
    {T : MatrixArithmetic M.Domain} (hT : T.Valid M C) {Forests Rows L index base : M.Domain}
    (hRun : MatrixParentRun M C A.width A.height A.cells A.values Forests Rows L) (hIndex : M.mem index C.omega)
    (hI : MatrixDepthRegular M C A Forests Rows) (hS : AboveS M C A Forests Rows L base) :
    ∃ B OtherForests Other OtherL, MatrixExpansion M C A T Forests Rows index B ∧ NormalizedMatrix M C B ∧
      MatrixParentRun M C B.width B.height B.cells B.values OtherForests Other OtherL ∧
      MatrixDepthRegular M C B OtherForests Other ∧ AboveS M C B OtherForests Other OtherL base := by
  obtain ⟨B,hB⟩ := matrix_expansion_exists_d hM hC hA hT hRun hIndex
  obtain ⟨OtherForests,Other,OtherL,hOther⟩ := matrix_parent_run_exists_d hM hC hB.matrix
  obtain ⟨hBI,hBS⟩ := hB.relative_structural_d hM hC hA hT hRun hOther hIndex hI hS
  exact ⟨B,OtherForests,Other,OtherL,hB,hB.normalized,hOther,hBI,hBS⟩

theorem MatrixExpansion.empty_width_d {M : SetTheory.Structure.{u}} (_hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {A B : FiniteMatrix M.Domain} {T : MatrixArithmetic M.Domain}
    {Forests Rows index : M.Domain} (h : MatrixExpansion M C A T Forests Rows index B) (hWidth : A.width=C.zero) :
    B.height=C.zero ∧ B.width=C.zero := by
  obtain ⟨R,_,hRaw,hTrim⟩ := h
  have hRW : R.width=C.zero := by
    rcases hRaw with ⟨_,_,hRW⟩ | ⟨last,hs,_⟩
    · exact hRW
    · exact False.elim (hC.zero_empty last (hWidth ▸ hs.predecessor_mem))
  exact ⟨hTrim.trim.width_zero_d hC hRW,hTrim.width.trans hRW⟩

/-- 同一实际raw复制参数的数值矩阵唯一，包含内部复制次数、差和乘积见证的唯一性。 -/
theorem RawMatrixExpansion.unique_matrix_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {A B D : FiniteMatrix M.Domain} {T : MatrixArithmetic M.Domain}
    {Forests Rows last maximal root index count len total count' len' total' : M.Domain}
    (hB : RawMatrixExpansion M C A T Forests Rows last maximal root index count len total B)
    (hD : RawMatrixExpansion M C A T Forests Rows last maximal root index count' len' total' D) : B=D := by
  have hCount := Structure.SuccessorOf.eq hM.1 hB.copies hD.copies
  subst count'
  have hLen := truncated_difference_unique_d hM hC hB.difference hD.difference
  subst len'
  have hTotal := KP1Y.Arithmetic.product_unique_d hM hB.product hD.product
  subst total'
  have hWidth := KP1Y.Arithmetic.sum_unique_d hM hB.width hD.width
  exact hB.matrix.ext_entries_d hM.1 hD.matrix (hB.height.trans hD.height.symm) hWidth
    (fun r c d => by rw [hB.entries,hD.entries,hWidth])

private theorem no_active_context_false {M : SetTheory.Structure.{u}}
    {C : ExpressionData M.Domain} {A : FiniteMatrix M.Domain} {Forests Rows L last maximal root : M.Domain}
    (he : Extensional M) (hRun : MatrixParentRun M C A.width A.height A.cells A.values Forests Rows L)
    (hNone : ∀ r, M.mem r A.height → ¬ActiveParentRow M Forests Rows A.width last r)
    (hContext : MatrixExpansionContext M C A Forests Rows last maximal root) : False := by
  obtain ⟨P,hPMem,hP,hParent⟩ := hContext.parent
  exact hNone maximal hContext.row ⟨P,hPMem,hP,root,(hRun.forests maximal P hP).bounds he hParent |>.2,hParent⟩

theorem RawMatrixStep.unique_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {A R S : FiniteMatrix M.Domain} (hA : A.Valid M C.omega)
    {T : MatrixArithmetic M.Domain} {Forests Rows L index : M.Domain}
    (hRun : MatrixParentRun M C A.width A.height A.cells A.values Forests Rows L)
    (hR : R.Valid M C.omega) (hS : S.Valid M C.omega)
    (hRawR : RawMatrixStep M C A T Forests Rows index R) (hRawS : RawMatrixStep M C A T Forests Rows index S) : R=S := by
  rcases hRawR with ⟨hA0,hRH,hRW⟩ | ⟨last,hWidth,hCase⟩
  · rcases hRawS with ⟨_,hSH,hSW⟩ | ⟨last',hWidth',_⟩
    · exact hR.ext_entries_d hM.1 hS (hRH.trans hSH.symm) (hRW.trans hSW.symm)
        (fun r _ _ => iff_of_false (fun h => hC.zero_empty r (hRH ▸ (h.bounds hM.1 hR).1))
          (fun h => hC.zero_empty r (hSH ▸ (h.bounds hM.1 hS).1)))
    · exact False.elim (hC.zero_empty last' (hA0 ▸ hWidth'.predecessor_mem))
  · rcases hRawS with ⟨hA0,_,_⟩ | ⟨last',hWidth',hCase'⟩
    · exact False.elim (hC.zero_empty last (hA0 ▸ hWidth.predecessor_mem))
    · have hw := omega_isOrdinal_d hM hC.omega
      have hLastNat := hw.transitive A.width hA.width last hWidth.predecessor_mem
      have hLast := Structure.SuccessorOf.predecessor_eq hM.1 (hw.mem hLastNat) hWidth hWidth'
      subst last'
      rcases hCase with ⟨hNone,hRH,hRW,hRE⟩ | ⟨maximal,root,count,len,total,hContext,hRaw⟩ <;>
        rcases hCase' with ⟨hNone',hSH,hSW,hSE⟩ | ⟨maximal',root',count',len',total',hContext',hRaw'⟩
      · exact hR.ext_entries_d hM.1 hS (hRH.trans hSH.symm) (hRW.trans hSW.symm) (fun r c d => (hRE r c d).trans (hSE r c d).symm)
      · exact False.elim (no_active_context_false hM.1 hRun hNone hContext')
      · exact False.elim (no_active_context_false hM.1 hRun hNone' hContext)
      · have hMax := maximal_parent_row_unique_d hM (hw.mem hA.height) hContext.maximality hContext'.maximality
        subst maximal'
        have hRoot := hContext.unique_root hRun hContext'
        subst root'
        exact hRaw.unique_matrix_d hM hC hRaw'

theorem MatrixExpansion.unique_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {A B D : FiniteMatrix M.Domain} (hA : A.Valid M C.omega)
    {T : MatrixArithmetic M.Domain} {Forests Rows L index : M.Domain}
    (hRun : MatrixParentRun M C A.width A.height A.cells A.values Forests Rows L)
    (hB : MatrixExpansion M C A T Forests Rows index B) (hD : MatrixExpansion M C A T Forests Rows index D) : B=D := by
  obtain ⟨R,hR,hRawR,hTrimB⟩ := hB
  obtain ⟨S,hS,hRawS,hTrimD⟩ := hD
  have hRS := hRawR.unique_d hM hC hA hRun hR hS hRawS
  subst S
  exact hTrimB.unique_d hM hC hR hTrimD

end KP1Y.OneYFinite
