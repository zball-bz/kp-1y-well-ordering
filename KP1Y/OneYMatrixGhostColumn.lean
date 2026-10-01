import KP1Y.OneYMatrixLiftOrder

/-! 实际单列虚拟末列，以及低行新根后缀严格小于前块虚拟末列。 -/
namespace KP1Y.OneYFinite
open YesMetaZFC YesMetaZFC.SetTheory YesMetaZFC.SetTheory.Definitional
open KP1Y.Kuratowski KP1Y.Functions KP1Y.Naturals KP1Y.Bounded
universe u

private def singleColumnSchema : Project.Delta0BinarySchema 3 where
  body := Project.Formula.existsMem (.bound 4) (Project.Formula.existsMem (.bound 4)
    (.conj (codeFormula (.bound 3) (.bound 1) (.bound 0)) (memPairFormula (.bound 4) (.bound 1) (.bound 2))))
  freeClosed := by
    simp [codeFormula,pairFormula,memPairFormula,Project.Formula.existsMem,Project.Formula.forallMem,Definitional.Formula.FreeClosed]
  delta0 := .existsMem _ (.existsMem _ (.conj (codeFormula_delta0 _ _ _) (memPairFormula_delta0 _ _ _)))

/-- 将内部有限height→ω图实现为宽度恰为1的实际矩阵。 -/
theorem single_column_matrix_exists_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {height V : M.Domain} (hHeight : M.mem height C.omega)
    (hV : Graph M V height C.omega) :
    ∃ G : FiniteMatrix M.Domain, G.Valid M C.omega ∧ G.height=height ∧ G.width=C.one ∧
      ∀ r y, MatrixEntry M G r C.zero y ↔ MemPair M V r y := by
  obtain ⟨Cells,hCells⟩ := product_exists hM height C.one
  let env := ((oneEnv height).push C.one).push V
  have hφ (key y : M.Domain) : Project.Formula.satisfies ((env.push key).push y) singleColumnSchema.body ↔
      ∃ r, M.mem r height ∧ ∃ c, M.mem c C.one ∧ Codes M key r c ∧ MemPair M V r y := by
    simp only [singleColumnSchema,Project.Formula.satisfies_existsMem_iff,Project.Formula.satisfies_conj_iff,
      codeFormula_iff hM.1,memPairFormula_iff hM.1]
    rfl
  obtain ⟨Values,hSupport,hRaw⟩ := relation_comprehension_d hM singleColumnSchema env Cells C.omega
  have hRows (key y : M.Domain) : MemPair M Values key y ↔
      ∃ r, M.mem r height ∧ ∃ c, M.mem c C.one ∧ Codes M key r c ∧ MemPair M V r y := by
    rw [hRaw key y,hφ]
    constructor
    · exact fun h => h.2.2
    · rintro ⟨r,hr,c,hc,hCode,hAt⟩
      exact ⟨(hCells key).mpr ⟨r,hr,c,hc,hCode⟩,(hV.bounds hM.1 hAt).2,r,hr,c,hc,hCode,hAt⟩
  have hValues : Graph M Values Cells C.omega := by
    refine ⟨hSupport,?_,?_⟩
    · intro key hk
      obtain ⟨r,hr,c,hc,hCode⟩ := (hCells key).mp hk
      obtain ⟨y,hy,hAt⟩ := hV.total r hr
      exact ⟨y,hy,(hRows key y).mpr ⟨r,hr,c,hc,hCode,hAt⟩⟩
    · intro key y z hy hz
      obtain ⟨r,_,c,_,hCode,hY⟩ := (hRows key y).mp hy
      obtain ⟨s,_,d,_,hCode',hZ⟩ := (hRows key z).mp hz
      obtain ⟨hrs,_⟩ := codes_injective hM.1 hCode hCode'
      subst s
      exact hV.unique r y z hY hZ
  let G : FiniteMatrix M.Domain := ⟨height,C.one,Cells,Values⟩
  refine ⟨G,⟨hHeight,hC.one_nat,hCells,hValues⟩,rfl,rfl,?_⟩
  intro r y
  constructor
  · rintro ⟨key,_,hCode,hAt⟩
    obtain ⟨s,_,c,_,hCode',hVAt⟩ := (hRows key y).mp hAt
    obtain ⟨hrs,_⟩ := codes_injective hM.1 hCode hCode'
    exact hrs.symm ▸ hVAt
  · intro hAt
    obtain ⟨key,hCode⟩ := codes_total hM r C.zero
    have hr := (hV.bounds hM.1 hAt).1
    have hz := hC.one_succ.predecessor_mem
    exact ⟨key,(hCells key).mpr ⟨r,hr,C.zero,hz,hCode⟩,hCode,
      (hRows key y).mpr ⟨r,hr,C.zero,hz,hCode,hAt⟩⟩

structure GhostColumn (M : SetTheory.Structure.{u}) (C : ExpressionData M.Domain)
    (A : FiniteMatrix M.Domain) (T : MatrixArithmetic M.Domain) (U : MatrixLiftParameters M.Domain)
    (G : FiniteMatrix M.Domain) : Prop where
  matrix : G.Valid M C.omega
  height : G.height=A.height
  width : G.width=C.one
  entries : ∀ r y, MatrixEntry M G r C.zero y ↔
    LiftedEntry M C A T U.forests U.rows U.last U.maximal U.root U.copy U.last r y

theorem ghost_column_exists_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {A : FiniteMatrix M.Domain} (hA : A.Valid M C.omega)
    {T : MatrixArithmetic M.Domain} (hT : T.Valid M C) {U : MatrixLiftParameters M.Domain}
    (hLast : M.mem U.last A.width) (hRoot : M.mem U.root A.width) (hCopy : M.mem U.copy C.omega) :
    ∃ G, GhostColumn M C A T U G := by
  obtain ⟨V,hV⟩ := lifted_column_graph_exists_d hM hC hA hT hLast hRoot hLast hCopy
  obtain ⟨G,hG,hHeight,hWidth,hEntries⟩ := single_column_matrix_exists_d hM hC hA.height hV.graph
  exact ⟨G,hG,hHeight,hWidth,fun r y => (hEntries r y).trans (hV.entries r y)⟩

theorem GhostColumn.column_bound {M : SetTheory.Structure.{u}} {C : ExpressionData M.Domain} (hC : C.Valid M)
    {A G : FiniteMatrix M.Domain} {T : MatrixArithmetic M.Domain} {U : MatrixLiftParameters M.Domain}
    (hG : GhostColumn M C A T U G) : M.mem C.zero G.width :=
  hG.width.symm ▸ hC.one_succ.predecessor_mem

theorem GhostColumn.padded_iff {M : SetTheory.Structure.{u}} (he : Extensional M)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {A G : FiniteMatrix M.Domain}
    {T : MatrixArithmetic M.Domain} {U : MatrixLiftParameters M.Domain} (hG : GhostColumn M C A T U G) (r y : M.Domain) :
    PaddedEntry M C.zero G r C.zero y ↔ PaddedLiftedEntry M C A T U U.last r y :=
  padded_matrix_iff_lifted_d he hG.matrix hG.height (hG.column_bound hC) hG.entries r y

/-- 所有较低后缀行相等，在最大活动行首次严格分离；结论是实际矩阵列的ColumnLtFrom。 -/
theorem newroot_suffix_lt_ghost_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {A B G : FiniteMatrix M.Domain} (hA : A.Valid M C.omega)
    {T : MatrixArithmetic M.Domain} (hT : T.Valid M C) {U : MatrixLiftParameters M.Domain}
    {Linear index count length total next target r start : M.Domain}
    (hRun : MatrixParentRun M C A.width A.height A.cells A.values U.forests U.rows Linear)
    (hContext : MatrixExpansionContext M C A U.forests U.rows U.last U.maximal U.root)
    (hRaw : RawMatrixExpansion M C A T U.forests U.rows U.last U.maximal U.root index count length total B)
    (hIndex : M.mem index C.omega) (hCopy : M.mem U.copy C.omega) (hNext : M.SuccessorOf next U.copy)
    (hNextBound : next=index ∨ M.mem next index)
    (hPos : CopyPosition M C.omega T.addPairs T.plus T.mulPairs T.times U.root length next C.zero target)
    (hG : GhostColumn M C A T U G) (hLow : M.mem r U.maximal) (hStart : M.SuccessorOf start r) :
    ColumnLtFrom M C.omega C.zero B G target C.zero start := by
  have hw := omega_isOrdinal_d hM hC.omega
  have hLast := hContext.width_successor.predecessor_mem
  have hRootLast := hContext.root_lt_last hRun
  have hRoot := (hw.mem hA.width).transitive U.last hLast U.root hRootLast
  have hRootNat := hw.transitive A.width hA.width U.root hRoot
  have hNextNat := natural_successor_mem_d hM hC hCopy hNext
  have hLengthPos := (truncated_difference_positive_iff_d hM hC hRaw.difference).mpr hRootLast
  have hRootZero := (hT.add.add_iff_sum hM hRootNat hC.zero_nat).mpr (KP1Y.Arithmetic.sum_zero_d hM U.root hC.zero_empty)
  have hRead (q y : M.Domain) : MatrixEntry M B q target y ↔
      LiftedEntry M C A T U.forests U.rows U.last U.maximal U.root next U.root q y :=
    hRaw.copied_entry_iff_d hM hC hA hT hLast hRootLast hIndex hNextBound hLengthPos hRootZero hPos
  obtain ⟨x,hx,hX⟩ := lifted_entry_exists_d hM hC hA hT hLast hRoot hNextNat hRoot hContext.row
  have hBX := (hRead U.maximal x).mpr hX
  have hTarget := (hBX.bounds hM.1 hRaw.matrix).2.1
  have hMaxNat := hw.transitive A.height hA.height U.maximal hContext.row
  have hrNat := hw.transitive U.maximal hMaxNat r hLow
  have hStartSub : M.MemberSubset start U.maximal := by
    intro z hz
    rcases (hStart z).mp hz with hzr | he
    · exact (hw.mem hMaxNat).transitive r hLow z hzr
    · exact (hM.1.eq_of_same_members z r he).symm ▸ hLow
  have hStartMax := ordinal_subset_cases_d hM
    (hw.mem (natural_successor_mem_d hM hC hrNat hStart)) (hw.mem hMaxNat) hStartSub
  refine ⟨U.maximal,hMaxNat,hStartMax,?_,?_⟩
  · intro q hq _ a _ b _ hBa hGb
    have hqH := (hw.mem hA.height).transitive U.maximal hContext.row q hq
    have hBa' : LiftedEntry M C A T U.forests U.rows U.last U.maximal U.root next U.root q a := by
      rcases hBa with hBa | ⟨hOutside,_⟩
      · exact (hRead q a).mp hBa
      · exact False.elim (hOutside.elim (fun hn => hn (hRaw.height.symm ▸ hqH)) (fun hn => hn hTarget))
    have hGb' : LiftedEntry M C A T U.forests U.rows U.last U.maximal U.root U.copy U.last q b := by
      rcases hGb with hGb | ⟨hOutside,_⟩
      · exact (hG.entries q b).mp hGb
      · exact False.elim (hOutside.elim (fun hn => hn (hG.height.symm ▸ hqH)) (fun hn => hn (hG.column_bound hC)))
    exact hContext.lifted_root_succ_eq_last_d hM hC hA hT hRun hq hCopy hNext hBa' hGb'
  · obtain ⟨y,hy,hGY⟩ := hG.matrix.entry_total_d hM (hG.height.symm ▸ hContext.row) (hG.column_bound hC)
    exact ⟨x,hx,y,hy,Or.inl hBX,Or.inl hGY,
      hContext.lifted_root_lt_last_at_d hM hC hA hRun hX ((hG.entries U.maximal y).mp hGY)⟩

end KP1Y.OneYFinite
