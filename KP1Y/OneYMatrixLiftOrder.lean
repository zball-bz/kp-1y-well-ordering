import KP1Y.OneYMatrixStructuralDefs
import KP1Y.OneYMatrixExpansionFacts
import KP1Y.OneYSelectionDepth
import KP1Y.OneYDepthValues

/-! 同一复制块中的完整列后缀保序。所有行号、列号与复制次数均取模型内部ω。
共同候选链与相等原值直接决定相等选择父行；首差处的上升标志单调。
补零行与可作为比较列的原末列均保留，不截短后缀结论。
-/
namespace KP1Y.OneYFinite
open YesMetaZFC YesMetaZFC.SetTheory YesMetaZFC.SetTheory.Definitional
open KP1Y.Kuratowski KP1Y.Functions KP1Y.Naturals KP1Y.Bounded
universe u

def ParentRowsEqual (M : SetTheory.Structure.{u}) (P c d : M.Domain) : Prop :=
  ∀ p, MemPair M P c p ↔ MemPair M P d p

def parentRowsEqualFormula {n : Nat} (P c d : Project.Term n) : Project.Formula 1 n :=
  .forallE (.iff (memPairFormula P.weaken c.weaken (.bound 0)) (memPairFormula P.weaken d.weaken (.bound 0)))

theorem parentRowsEqualFormula_iff {M : SetTheory.Structure.{u}} (he : Extensional M)
    {n : Nat} (env : Env M n) (P c d : Project.Term n) :
    Project.Formula.satisfies env (parentRowsEqualFormula P c d) ↔
      ParentRowsEqual M (P.eval env) (c.eval env) (d.eval env) := by
  simp only [parentRowsEqualFormula,ParentRowsEqual,Project.Formula.satisfies_forall_iff,
    Project.Formula.satisfies_iff_iff,memPairFormula_iff he,Term.eval_weaken]
  rfl

def previousMatrixForestFormula {n : Nat} (z height Forests Rows L r P : Project.Term n) : Project.Formula 1 n :=
  .disj (.conj (Project.Formula.extensionalEq r z) (Project.Formula.extensionalEq P L))
    (Project.Formula.existsMem height (.conj (successorFormula r.weaken (.bound 0))
      (.conj (.mem P.weaken Forests.weaken) (memPairFormula Rows.weaken (.bound 0) P.weaken))))

theorem previousMatrixForestFormula_iff {M : SetTheory.Structure.{u}} (he : Extensional M)
    {n : Nat} (env : Env M n) (C : ExpressionData (Project.Term n)) (height Forests Rows L r P : Project.Term n) :
    Project.Formula.satisfies env (previousMatrixForestFormula C.zero height Forests Rows L r P) ↔
      PreviousMatrixForest M (C.eval env) (height.eval env) (Forests.eval env) (Rows.eval env)
        (L.eval env) (r.eval env) (P.eval env) := by
  simp only [previousMatrixForestFormula,PreviousMatrixForest,Project.Formula.satisfies_disj_iff,
    Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_extensionalEq_iff_eq he,
    Project.Formula.satisfies_existsMem_iff,Project.Formula.satisfies_mem_iff,successorFormula_iff he,
    memPairFormula_iff he,Term.eval_weaken]
  rfl

theorem MatrixParentRun.selects_previous_d {M : SetTheory.Structure.{u}}
    {C : ExpressionData M.Domain} {m height Cells Values Forests Rows L r P Q V : M.Domain}
    (h : MatrixParentRun M C m height Cells Values Forests Rows L)
    (hPrev : PreviousMatrixForest M C height Forests Rows L r P)
    (hQ : MemPair M Rows r Q) (hV : MatrixRowValues M C.omega m Cells Values r V) :
    Selects false M C m P V Q := by
  rcases hPrev with ⟨hr,hP⟩ | ⟨j,_,hSucc,_,hP⟩
  · subst r
    subst P
    exact h.initial Q V hQ hV
  · exact h.step j r P Q V hSucc hP hQ hV

theorem MatrixParentRun.previous_exists_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {m height Cells Values Forests Rows L r : M.Domain}
    (h : MatrixParentRun M C m height Cells Values Forests Rows L) (hr : M.mem r height) :
    ∃ P, PreviousMatrixForest M C height Forests Rows L r P := by
  have hw := omega_isOrdinal_d hM hC.omega
  rcases natural_cases hM hC.omega (hw.transitive height h.height_nat r hr) with hz | ⟨j,_,hs⟩
  · have he := hM.1.eq_of_same_members r C.zero (fun x => iff_of_false (hz x) (hC.zero_empty x))
    exact ⟨L,Or.inl ⟨he,rfl⟩⟩
  · have hj := (hw.mem h.height_nat).transitive r hr j hs.predecessor_mem
    obtain ⟨P,hPF,hP⟩ := h.graph.total j hj
    exact ⟨P,Or.inr ⟨j,hj,hs,hPF,hP⟩⟩

/-- 条件I的实际局部方程确实给出父路径深度。 -/
theorem matrix_depth_regular_entry_iff_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {A : FiniteMatrix M.Domain} (hA : A.Valid M C.omega)
    {Forests Rows L r P : M.Domain}
    (h : MatrixParentRun M C A.width A.height A.cells A.values Forests Rows L)
    (hI : MatrixDepthRegular M C A Forests Rows) (hP : MemPair M Rows r P) (c d : M.Domain) :
    MatrixEntry M A r c d ↔ Depth M C A.width P c d := by
  have hr := (h.graph.bounds hM.1 hP).1
  obtain ⟨V,hV⟩ := h.values_exist r hr
  have hVP := matrix_row_view_entry_iff_d hM hA hr hV
  have hEq : DepthValueEquations M C A.width P V := by
    intro c v hAt
    have hc := (hV.graph.bounds hM.1 hAt).1
    have hv := (hV.graph.bounds hM.1 hAt).2
    have hRow := hI r hr P (h.graph.bounds hM.1 hP).2 hP c hc v hv ((hVP c v).mp hAt)
    refine ⟨hRow.1,?_⟩
    intro p w hcp hAtp
    exact hRow.2 p (hV.graph.bounds hM.1 hAtp).1 hcp w (hV.graph.bounds hM.1 hAtp).2 ((hVP p w).mp hAtp)
  exact (hVP c d).symm.trans (depth_values_iff_d hM hC (h.forests r P hP) hV.graph hEq c d)

/-- 这里可直接用相等数值，因而比原条件I下的出口更一般。 -/
theorem matrix_parent_equal_of_previous_equal_entry_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {A : FiniteMatrix M.Domain} (hA : A.Valid M C.omega)
    {Forests Rows L r P Q c d x : M.Domain}
    (h : MatrixParentRun M C A.width A.height A.cells A.values Forests Rows L)
    (hPrev : PreviousMatrixForest M C A.height Forests Rows L r P) (hQ : MemPair M Rows r Q)
    (hSame : ParentRowsEqual M P c d) (hX : MatrixEntry M A r c x) (hY : MatrixEntry M A r d x) :
    ParentRowsEqual M Q c d := by
  have hr := (h.graph.bounds hM.1 hQ).1
  obtain ⟨V,hV⟩ := h.values_exist r hr
  have hS := h.selects_previous_d hPrev hQ hV
  exact hS.parent_rows_eq_of_common_chain_value_d hM
    (ancestor_iff_of_parent_rows_eq_d hM hC hS.inherited hSame)
    ((matrix_row_view_entry_iff_d hM hA hr hV c x).mpr hX)
    ((matrix_row_view_entry_iff_d hM hA hr hV d x).mpr hY)

theorem matrix_ascending_equal_of_parent_equal_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {m height Cells Values Forests Rows L r Q maximal root c d : M.Domain}
    (h : MatrixParentRun M C m height Cells Values Forests Rows L) (hQ : MemPair M Rows r Q)
    (hc : M.mem root c) (hd : M.mem root d) (hSame : ParentRowsEqual M Q c d) :
    Ascending M C m Forests Rows maximal root c r ↔ Ascending M C m Forests Rows maximal root d r := by
  have hAnc := ancestor_iff_of_parent_rows_eq_d hM hC (h.forests r Q hQ) hSame root
  have convert (source : M.Domain) (hRoot : M.mem root source) :
      Ascending M C m Forests Rows maximal root source r ↔ M.mem r maximal ∧ Ancestor M C m Q root source := by
    constructor
    · rintro ⟨hr,hSource | ⟨P,_,hP,hA⟩⟩
      · exact False.elim (SetTheory.KP.mem_irrefl_d (KP1Y.models_weakKP hM) root (hSource ▸ hRoot))
      · have he := h.graph.unique r P Q hP hQ
        exact ⟨hr,he ▸ hA⟩
    · rintro ⟨hr,hA⟩
      exact ⟨hr,Or.inr ⟨Q,(h.graph.bounds hM.1 hQ).2,hQ,hA⟩⟩
  rw [convert c hc,convert d hd,hAnc]

theorem matrix_ascending_mono_of_previous_equal_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {A : FiniteMatrix M.Domain} (hA : A.Valid M C.omega)
    {Forests Rows L r P Q maximal root c d x y : M.Domain}
    (h : MatrixParentRun M C A.width A.height A.cells A.values Forests Rows L)
    (hPrev : PreviousMatrixForest M C A.height Forests Rows L r P) (hQ : MemPair M Rows r Q)
    (hc : M.mem root c) (hSame : ParentRowsEqual M P c d)
    (hX : MatrixEntry M A r c x) (hY : MatrixEntry M A r d y) (hXY : x=y ∨ M.mem x y)
    (hAsc : Ascending M C A.width Forests Rows maximal root c r) :
    Ascending M C A.width Forests Rows maximal root d r := by
  have hr := (h.graph.bounds hM.1 hQ).1
  obtain ⟨V,hV⟩ := h.values_exist r hr
  have hS := h.selects_previous_d hPrev hQ hV
  have hAnc : Ancestor M C A.width Q root c := by
    rcases hAsc.2 with he | ⟨R,_,hR,hA⟩
    · exact False.elim (SetTheory.KP.mem_irrefl_d (KP1Y.models_weakKP hM) root (he ▸ hc))
    · exact (h.graph.unique r R Q hR hQ) ▸ hA
  exact ⟨hAsc.1,Or.inr ⟨Q,(h.graph.bounds hM.1 hQ).2,hQ,
    hS.ancestor_mono_of_common_chain_d hM hC
      (ancestor_iff_of_parent_rows_eq_d hM hC hS.inherited hSame)
      ((matrix_row_view_entry_iff_d hM hA hr hV c x).mpr hX)
      ((matrix_row_view_entry_iff_d hM hA hr hV d y).mpr hY) hXY hAnc⟩⟩

def PreviousRowsEqual (M : SetTheory.Structure.{u}) (C : ExpressionData M.Domain)
    (height Forests Rows L r c d : M.Domain) : Prop :=
  ∀ P, PreviousMatrixForest M C height Forests Rows L r P → ParentRowsEqual M P c d

private def equalRowsEnv {M : SetTheory.Structure.{u}} (C : ExpressionData M.Domain)
    (A : FiniteMatrix M.Domain) (Forests Rows L c d start : M.Domain) : Env M 15 :=
  ((((((((((((((oneEnv C.omega).push C.zero).push C.one).push C.sequences).push C.expressions).push A.width).push A.height).push A.cells).push A.values).push Forests).push Rows).push L).push c).push d).push start

private def equalRowsSchema : Project.UnarySchema 15 where
  body := .forallE (.imp
    (previousMatrixForestFormula (.bound 15) (.bound 10) (.bound 7) (.bound 6) (.bound 5) (.bound 1) (.bound 0))
    (.imp (.disj (Project.Formula.extensionalEq (.bound 2) (.bound 1)) (.mem (.bound 2) (.bound 1)))
      (.imp (Project.Formula.forallMem (.bound 1) (.imp
        (.disj (Project.Formula.extensionalEq (.bound 3) (.bound 0)) (.mem (.bound 3) (.bound 0)))
        (columnEqAtFormula (.bound 17) (.bound 16) ⟨.bound 11,.bound 12,.bound 10,.bound 9⟩
          ⟨.bound 11,.bound 12,.bound 10,.bound 9⟩ (.bound 5) (.bound 4) (.bound 0))))
        (parentRowsEqualFormula (.bound 0) (.bound 4) (.bound 3)))))
  freeClosed := by
    simp [previousMatrixForestFormula,parentRowsEqualFormula,columnEqAtFormula,paddedEntryFormula,matrixEntryFormula,
      memPairFormula,codeFormula,pairFormula,successorFormula,Project.Formula.forallMem,Project.Formula.existsMem,
      FiniteMatrix.weaken,FiniteMatrix.map,Definitional.Formula.FreeClosed]

private theorem equalRowsSchema_iff {M : SetTheory.Structure.{u}} (he : Extensional M)
    (C : ExpressionData M.Domain) (A : FiniteMatrix M.Domain) (Forests Rows L c d start r : M.Domain) :
    Project.Formula.satisfies ((equalRowsEnv C A Forests Rows L c d start).push r) equalRowsSchema.body ↔
      ∀ P, PreviousMatrixForest M C A.height Forests Rows L r P → (start=r ∨ M.mem start r) →
        (∀ q, M.mem q r → (start=q ∨ M.mem start q) → ColumnEqAt M C.omega C.zero A A c d q) → ParentRowsEqual M P c d := by
  simp only [equalRowsSchema,previousMatrixForestFormula,PreviousMatrixForest,
    Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_imp_iff,
    Project.Formula.satisfies_disj_iff,Project.Formula.satisfies_extensionalEq_iff_eq he,
    Project.Formula.satisfies_mem_iff,Project.Formula.satisfies_forallMem_iff,
    Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_existsMem_iff,successorFormula_iff he,
    memPairFormula_iff he,Term.eval_weaken,columnEqAtFormula_iff he,parentRowsEqualFormula_iff he]
  rfl

/-- 明确的对象行归纳；不用宿主count次迭代。 -/
theorem matrix_previous_equal_of_equal_rows_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {A : FiniteMatrix M.Domain} (hA : A.Valid M C.omega)
    {Forests Rows L c d start r : M.Domain}
    (h : MatrixParentRun M C A.width A.height A.cells A.values Forests Rows L)
    (hc : M.mem c A.width) (hd : M.mem d A.width) (hr : M.mem r C.omega)
    (hStart : PreviousRowsEqual M C A.height Forests Rows L start c d)
    (hLe : start=r ∨ M.mem start r)
    (hEarlier : ∀ q, M.mem q r → (start=q ∨ M.mem start q) → ColumnEqAt M C.omega C.zero A A c d q) :
    PreviousRowsEqual M C A.height Forests Rows L r c d := by
  have hw := omega_isOrdinal_d hM hC.omega
  have hAll := natural_induction_d hM equalRowsSchema (equalRowsEnv C A Forests Rows L c d start) hC.omega
    (by
      intro z hz
      apply (equalRowsSchema_iff hM.1 C A Forests Rows L c d start z).mpr
      intro P hP hsz _
      rcases hsz with he | hs
      · exact hStart P (he.symm ▸ hP)
      · exact False.elim (hz start hs))
    (by
      intro j hj ih r hs
      apply (equalRowsSchema_iff hM.1 C A Forests Rows L c d start r).mpr
      intro P hP hsr hEq
      rcases hsr with he | hsr
      · exact hStart P (he.symm ▸ hP)
      · have hStartJ : start=j ∨ M.mem start j := by
          rcases (hs start).mp hsr with hsj | he
          · exact Or.inr hsj
          · exact Or.inl (hM.1.eq_of_same_members start j he)
        rcases hP with ⟨hrz,_⟩ | ⟨k,hk,hks,_,hAt⟩
        · exact False.elim (hC.zero_empty j (hrz ▸ hs.predecessor_mem))
        · have hjk := Structure.SuccessorOf.predecessor_eq hM.1 (hw.mem hj) hs hks
          subst k
          obtain ⟨Q,hQPrev⟩ := h.previous_exists_d hM hC hk
          have hCommon := (equalRowsSchema_iff hM.1 C A Forests Rows L c d start j).mp ih Q hQPrev hStartJ
            (fun q hq hsq => hEq q ((hs q).mpr (Or.inl hq)) hsq)
          obtain ⟨x,hx,hX⟩ := hA.entry_total_d hM hk hc
          obtain ⟨y,hy,hY⟩ := hA.entry_total_d hM hk hd
          have hxy := hEq j hs.predecessor_mem hStartJ x hx y hy (Or.inl hX) (Or.inl hY)
          subst y
          exact matrix_parent_equal_of_previous_equal_entry_d hM hC hA h hQPrev hAt hCommon hX hY)
  intro P hP
  exact (equalRowsSchema_iff hM.1 C A Forests Rows L c d start r).mp (hAll r hr) P hP hLe hEarlier

/-! 复制加量的逐项比较，以及包含补零行的完整列视图。 -/

structure MatrixLiftParameters (α : Type u) where
  forests : α
  rows : α
  last : α
  maximal : α
  root : α
  copy : α

def PaddedLiftedEntry (M : SetTheory.Structure.{u}) (C : ExpressionData M.Domain)
    (A : FiniteMatrix M.Domain) (T : MatrixArithmetic M.Domain) (U : MatrixLiftParameters M.Domain)
    (source r y : M.Domain) : Prop :=
  (M.mem r A.height ∧ LiftedEntry M C A T U.forests U.rows U.last U.maximal U.root U.copy source r y) ∨
    (¬M.mem r A.height ∧ y=C.zero)

theorem padded_lifted_entry_exists_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {A : FiniteMatrix M.Domain} (hA : A.Valid M C.omega)
    {T : MatrixArithmetic M.Domain} (hT : T.Valid M C) {U : MatrixLiftParameters M.Domain}
    (hLast : M.mem U.last A.width) (hRoot : M.mem U.root A.width) (hCopy : M.mem U.copy C.omega)
    {source : M.Domain} (hSource : M.mem source A.width) (r : M.Domain) :
    ∃ y, M.mem y C.omega ∧ PaddedLiftedEntry M C A T U source r y := by
  classical
  by_cases hr : M.mem r A.height
  · obtain ⟨y,hy,hY⟩ := lifted_entry_exists_d hM hC hA hT hLast hRoot hCopy hSource hr
    exact ⟨y,hy,Or.inl ⟨hr,hY⟩⟩
  · exact ⟨C.zero,hC.zero_nat,Or.inr ⟨hr,rfl⟩⟩

theorem padded_lifted_entry_unique_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} {A : FiniteMatrix M.Domain} (hA : A.Valid M C.omega)
    {T : MatrixArithmetic M.Domain} (hT : T.Valid M C) {U : MatrixLiftParameters M.Domain} {source r x y : M.Domain}
    (hX : PaddedLiftedEntry M C A T U source r x) (hY : PaddedLiftedEntry M C A T U source r y) : x=y := by
  rcases hX with ⟨hr,hX⟩ | ⟨hr,hX⟩ <;> rcases hY with ⟨hr',hY⟩ | ⟨hr',hY⟩
  · exact lifted_entry_unique_d hM hA hT hX hY
  · exact False.elim (hr' hr)
  · exact False.elim (hr hr')
  · exact hX.trans hY.symm

theorem lifted_values_equal_of_flags_equal_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} {A : FiniteMatrix M.Domain} (hA : A.Valid M C.omega)
    {T : MatrixArithmetic M.Domain} (hT : T.Valid M C) {U : MatrixLiftParameters M.Domain} {c d r a x y : M.Domain}
    (hAEntry : MatrixEntry M A r c a) (hBEntry : MatrixEntry M A r d a)
    (hFlags : Ascending M C A.width U.forests U.rows U.maximal U.root c r ↔
      Ascending M C A.width U.forests U.rows U.maximal U.root d r)
    (hX : LiftedEntry M C A T U.forests U.rows U.last U.maximal U.root U.copy c r x)
    (hY : LiftedEntry M C A T U.forests U.rows U.last U.maximal U.root U.copy d r y) : x=y := by
  obtain ⟨a',_,hA',hX⟩ := hX
  obtain ⟨b',_,hB',hY⟩ := hY
  have ha := hA.entry_unique hM.1 hA' hAEntry
  have hb := hA.entry_unique hM.1 hB' hBEntry
  subst a'
  subst b'
  rcases hX with ⟨hFlag,e,_,t,_,hE,hMul,hPlus⟩ | ⟨hFlag,hX⟩ <;>
    rcases hY with ⟨hFlag',f,_,v,_,hF,hMul',hPlus'⟩ | ⟨hFlag',hY⟩
  · have hef := row_increment_unique_d hM hA hT.diff hE hF
    subst f
    have htv := hT.mul.mul_unique hM.1 hMul hMul'
    subst v
    exact hT.add.add_unique hM.1 hPlus hPlus'
  · exact False.elim (hFlag' (hFlags.mp hFlag))
  · exact False.elim (hFlag (hFlags.mpr hFlag'))
  · exact hX.trans hY.symm

theorem lifted_values_lt_of_flags_mono_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {A : FiniteMatrix M.Domain} (hA : A.Valid M C.omega)
    {T : MatrixArithmetic M.Domain} (hT : T.Valid M C) {U : MatrixLiftParameters M.Domain} {c d r a b x y : M.Domain}
    (hAEntry : MatrixEntry M A r c a) (hBEntry : MatrixEntry M A r d b) (hab : M.mem a b)
    (hFlags : Ascending M C A.width U.forests U.rows U.maximal U.root c r →
      Ascending M C A.width U.forests U.rows U.maximal U.root d r)
    (hX : LiftedEntry M C A T U.forests U.rows U.last U.maximal U.root U.copy c r x)
    (hY : LiftedEntry M C A T U.forests U.rows U.last U.maximal U.root U.copy d r y) : M.mem x y := by
  obtain ⟨a',ha',hA',hX⟩ := hX
  obtain ⟨b',hb',hB',hY⟩ := hY
  have ha := hA.entry_unique hM.1 hA' hAEntry
  have hb := hA.entry_unique hM.1 hB' hBEntry
  subst a'
  subst b'
  rcases hX with ⟨hFlag,e,_,t,ht,hE,hMul,hPlus⟩ | ⟨_,hX⟩ <;>
    rcases hY with ⟨hFlag',f,_,v,hv,hF,hMul',hPlus'⟩ | ⟨hFlag',hY⟩
  · have hef := row_increment_unique_d hM hA hT.diff hE hF
    subst f
    have htv := hT.mul.mul_unique hM.1 hMul hMul'
    subst v
    exact natural_sum_strict_left_d hM hC ha' hb' ht
      ((hT.add.add_iff_sum hM ha' ht).mp hPlus) ((hT.add.add_iff_sum hM hb' ht).mp hPlus') hab
  · exact False.elim (hFlag' (hFlags hFlag))
  · subst x
    exact KP1Y.Arithmetic.sum_base_subset_d hM ((omega_isOrdinal_d hM hC.omega).mem hb')
      ((hT.add.add_iff_sum hM hb' hv).mp hPlus') a hab
  · exact hX.symm ▸ hY.symm ▸ hab

def LiftedColumnEqAt (M : SetTheory.Structure.{u}) (C : ExpressionData M.Domain)
    (A : FiniteMatrix M.Domain) (T : MatrixArithmetic M.Domain) (U : MatrixLiftParameters M.Domain) (c d r : M.Domain) : Prop :=
  ∀ x, M.mem x C.omega → ∀ y, M.mem y C.omega →
    PaddedLiftedEntry M C A T U c r x → PaddedLiftedEntry M C A T U d r y → x=y

def LiftedColumnLtAt (M : SetTheory.Structure.{u}) (C : ExpressionData M.Domain)
    (A : FiniteMatrix M.Domain) (T : MatrixArithmetic M.Domain) (U : MatrixLiftParameters M.Domain) (c d r : M.Domain) : Prop :=
  ∃ x, M.mem x C.omega ∧ ∃ y, M.mem y C.omega ∧
    PaddedLiftedEntry M C A T U c r x ∧ PaddedLiftedEntry M C A T U d r y ∧ M.mem x y

def LiftedColumnEqFrom (M : SetTheory.Structure.{u}) (C : ExpressionData M.Domain)
    (A : FiniteMatrix M.Domain) (T : MatrixArithmetic M.Domain) (U : MatrixLiftParameters M.Domain) (c d start : M.Domain) : Prop :=
  ∀ r, M.mem r C.omega → (start=r ∨ M.mem start r) → LiftedColumnEqAt M C A T U c d r

def LiftedColumnLtFrom (M : SetTheory.Structure.{u}) (C : ExpressionData M.Domain)
    (A : FiniteMatrix M.Domain) (T : MatrixArithmetic M.Domain) (U : MatrixLiftParameters M.Domain) (c d start : M.Domain) : Prop :=
  ∃ r, M.mem r C.omega ∧ (start=r ∨ M.mem start r) ∧
    (∀ q, M.mem q r → (start=q ∨ M.mem start q) → LiftedColumnEqAt M C A T U c d q) ∧
    LiftedColumnLtAt M C A T U c d r

def LiftedColumnLeFrom (M : SetTheory.Structure.{u}) (C : ExpressionData M.Domain)
    (A : FiniteMatrix M.Domain) (T : MatrixArithmetic M.Domain) (U : MatrixLiftParameters M.Domain) (c d start : M.Domain) : Prop :=
  LiftedColumnEqFrom M C A T U c d start ∨ LiftedColumnLtFrom M C A T U c d start

theorem lifted_equal_at_of_equal_earlier_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {A : FiniteMatrix M.Domain} (hA : A.Valid M C.omega)
    {T : MatrixArithmetic M.Domain} (hT : T.Valid M C) {U : MatrixLiftParameters M.Domain} {L c d start r : M.Domain}
    (h : MatrixParentRun M C A.width A.height A.cells A.values U.forests U.rows L)
    (hc : M.mem c A.width) (hd : M.mem d A.width) (hRootC : M.mem U.root c) (hRootD : M.mem U.root d)
    (hStart : PreviousRowsEqual M C A.height U.forests U.rows L start c d)
    (hr : M.mem r C.omega) (hLe : start=r ∨ M.mem start r)
    (hEarlier : ∀ q, M.mem q r → (start=q ∨ M.mem start q) → ColumnEqAt M C.omega C.zero A A c d q)
    (hAt : ColumnEqAt M C.omega C.zero A A c d r) : LiftedColumnEqAt M C A T U c d r := by
  intro x _ y _ hX hY
  rcases hX with ⟨hrH,hX⟩ | ⟨hrH,hX⟩ <;> rcases hY with ⟨hrH',hY⟩ | ⟨hrH',hY⟩
  · obtain ⟨P,hPrev⟩ := h.previous_exists_d hM hC hrH
    obtain ⟨Q,_,hQ⟩ := h.graph.total r hrH
    have hCommon := matrix_previous_equal_of_equal_rows_d hM hC hA h hc hd hr hStart hLe hEarlier P hPrev
    obtain ⟨a,ha,hAEntry⟩ := hA.entry_total_d hM hrH hc
    obtain ⟨b,hb,hBEntry⟩ := hA.entry_total_d hM hrH hd
    have hab := hAt a ha b hb (Or.inl hAEntry) (Or.inl hBEntry)
    subst b
    have hCurrent := matrix_parent_equal_of_previous_equal_entry_d hM hC hA h hPrev hQ hCommon hAEntry hBEntry
    exact lifted_values_equal_of_flags_equal_d hM hA hT hAEntry hBEntry
      (matrix_ascending_equal_of_parent_equal_d hM hC h hQ hRootC hRootD hCurrent) hX hY
  · exact False.elim (hrH' hrH)
  · exact False.elim (hrH hrH')
  · exact hX.trans hY.symm

theorem lifted_suffix_eq_of_common_previous_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {A : FiniteMatrix M.Domain} (hA : A.Valid M C.omega)
    {T : MatrixArithmetic M.Domain} (hT : T.Valid M C) {U : MatrixLiftParameters M.Domain} {L c d start : M.Domain}
    (h : MatrixParentRun M C A.width A.height A.cells A.values U.forests U.rows L)
    (hc : M.mem c A.width) (hd : M.mem d A.width) (hRootC : M.mem U.root c) (hRootD : M.mem U.root d)
    (hStart : PreviousRowsEqual M C A.height U.forests U.rows L start c d)
    (hEq : ColumnEqFrom M C.omega C.zero A A c d start) : LiftedColumnEqFrom M C A T U c d start := by
  intro r hr hLe
  exact lifted_equal_at_of_equal_earlier_d hM hC hA hT h hc hd hRootC hRootD hStart hr hLe
    (fun q hq hsq => hEq q ((omega_isOrdinal_d hM hC.omega).transitive r hr q hq) hsq) (hEq r hr hLe)

theorem lifted_suffix_lt_of_common_previous_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {A : FiniteMatrix M.Domain} (hA : A.Valid M C.omega)
    {T : MatrixArithmetic M.Domain} (hT : T.Valid M C) {U : MatrixLiftParameters M.Domain} {L c d start : M.Domain}
    (h : MatrixParentRun M C A.width A.height A.cells A.values U.forests U.rows L)
    (hc : M.mem c A.width) (hd : M.mem d A.width) (hRootC : M.mem U.root c) (hRootD : M.mem U.root d)
    (hLast : M.mem U.last A.width) (hRoot : M.mem U.root A.width) (hCopy : M.mem U.copy C.omega)
    (hStart : PreviousRowsEqual M C A.height U.forests U.rows L start c d)
    (hLt : ColumnLtFrom M C.omega C.zero A A c d start) : LiftedColumnLtFrom M C A T U c d start := by
  obtain ⟨r,hr,hLe,hEarlier,a,ha,b,hb,hAEntry,hBEntry,hab⟩ := hLt
  have hw := omega_isOrdinal_d hM hC.omega
  have hrH : M.mem r A.height := by
    classical
    apply Classical.byContradiction
    intro hn
    have haz := hA.padded_unique hM.1 hAEntry (Or.inr ⟨Or.inl hn,rfl⟩ : PaddedEntry M C.zero A r c C.zero)
    have hbz := hA.padded_unique hM.1 hBEntry (Or.inr ⟨Or.inl hn,rfl⟩ : PaddedEntry M C.zero A r d C.zero)
    subst a
    subst b
    exact hC.zero_empty C.zero hab
  have hA' : MatrixEntry M A r c a := by
    rcases hAEntry with hAEntry | ⟨hn,_⟩
    · exact hAEntry
    · exact False.elim (hn.elim (fun hh => hh hrH) (fun hh => hh hc))
  have hB' : MatrixEntry M A r d b := by
    rcases hBEntry with hBEntry | ⟨hn,_⟩
    · exact hBEntry
    · exact False.elim (hn.elim (fun hh => hh hrH) (fun hh => hh hd))
  refine ⟨r,hr,hLe,?_,?_⟩
  · intro q hqr hsq
    exact lifted_equal_at_of_equal_earlier_d hM hC hA hT h hc hd hRootC hRootD hStart
      (hw.transitive r hr q hqr) hsq
      (fun j hj hsj => hEarlier j ((hw.mem hr).transitive q hqr j hj) hsj) (hEarlier q hqr hsq)
  · obtain ⟨P,hPrev⟩ := h.previous_exists_d hM hC hrH
    obtain ⟨Q,_,hQ⟩ := h.graph.total r hrH
    have hCommon := matrix_previous_equal_of_equal_rows_d hM hC hA h hc hd hr hStart hLe hEarlier P hPrev
    obtain ⟨x,hx,hX⟩ := lifted_entry_exists_d hM hC hA hT hLast hRoot hCopy hc hrH
    obtain ⟨y,hy,hY⟩ := lifted_entry_exists_d hM hC hA hT hLast hRoot hCopy hd hrH
    refine ⟨x,hx,y,hy,Or.inl ⟨hrH,hX⟩,Or.inl ⟨hrH,hY⟩,?_⟩
    exact lifted_values_lt_of_flags_mono_d hM hC hA hT hA' hB' hab
      (matrix_ascending_mono_of_previous_equal_d hM hC hA h hPrev hQ hRootC hCommon hA' hB' (Or.inr hab)) hX hY

theorem lifted_suffix_le_of_common_previous_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {A : FiniteMatrix M.Domain} (hA : A.Valid M C.omega)
    {T : MatrixArithmetic M.Domain} (hT : T.Valid M C) {U : MatrixLiftParameters M.Domain} {L c d start : M.Domain}
    (h : MatrixParentRun M C A.width A.height A.cells A.values U.forests U.rows L)
    (hc : M.mem c A.width) (hd : M.mem d A.width) (hRootC : M.mem U.root c) (hRootD : M.mem U.root d)
    (hLast : M.mem U.last A.width) (hRoot : M.mem U.root A.width) (hCopy : M.mem U.copy C.omega)
    (hStart : PreviousRowsEqual M C A.height U.forests U.rows L start c d)
    (hLe : ColumnLeFrom M C.omega C.zero A A c d start) : LiftedColumnLeFrom M C A T U c d start := by
  rcases hLe with hEq | hLt
  · exact Or.inl (lifted_suffix_eq_of_common_previous_d hM hC hA hT h hc hd hRootC hRootD hStart hEq)
  · exact Or.inr (lifted_suffix_lt_of_common_previous_d hM hC hA hT h hc hd hRootC hRootD hLast hRoot hCopy hStart hLt)

theorem previous_rows_equal_of_common_current_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {m height Cells Values Forests Rows L r start Q c d : M.Domain}
    (h : MatrixParentRun M C m height Cells Values Forests Rows L) (hQ : MemPair M Rows r Q)
    (hSucc : M.SuccessorOf start r) (hSame : ParentRowsEqual M Q c d) :
    PreviousRowsEqual M C height Forests Rows L start c d := by
  intro P hP
  rcases hP with ⟨hz,_⟩ | ⟨j,_,hs,_,hAt⟩
  · exact False.elim (hC.zero_empty r (hz ▸ hSucc.predecessor_mem))
  · have hr := (omega_isOrdinal_d hM hC.omega).transitive height h.height_nat r (h.graph.bounds hM.1 hQ).1
    have he := Structure.SuccessorOf.predecessor_eq hM.1 ((omega_isOrdinal_d hM hC.omega).mem hr) hSucc hs
    subst j
    exact (h.graph.unique r Q P hQ hAt) ▸ hSame

theorem lifted_suffix_le_of_common_parent_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {A : FiniteMatrix M.Domain} (hA : A.Valid M C.omega)
    {T : MatrixArithmetic M.Domain} (hT : T.Valid M C) {U : MatrixLiftParameters M.Domain} {L Q c d r start : M.Domain}
    (h : MatrixParentRun M C A.width A.height A.cells A.values U.forests U.rows L)
    (hc : M.mem c A.width) (hd : M.mem d A.width) (hRootC : M.mem U.root c) (hRootD : M.mem U.root d)
    (hLast : M.mem U.last A.width) (hRoot : M.mem U.root A.width) (hCopy : M.mem U.copy C.omega)
    (hQ : MemPair M U.rows r Q) (hSucc : M.SuccessorOf start r) (hSame : ParentRowsEqual M Q c d)
    (hLe : ColumnLeFrom M C.omega C.zero A A c d start) : LiftedColumnLeFrom M C A T U c d start :=
  lifted_suffix_le_of_common_previous_d hM hC hA hT h hc hd hRootC hRootD hLast hRoot hCopy
    (previous_rows_equal_of_common_current_d hM hC h hQ hSucc hSame) hLe

/-! 实际有限列图及矩阵读取桥，避免仅把提升列当作未实现的函数。 -/

structure LiftedColumnGraph (M : SetTheory.Structure.{u}) (C : ExpressionData M.Domain)
    (A : FiniteMatrix M.Domain) (T : MatrixArithmetic M.Domain) (U : MatrixLiftParameters M.Domain)
    (source V : M.Domain) : Prop where
  graph : Graph M V A.height C.omega
  entries : ∀ r y, MemPair M V r y ↔ LiftedEntry M C A T U.forests U.rows U.last U.maximal U.root U.copy source r y

theorem lifted_column_graph_exists_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {A : FiniteMatrix M.Domain} (hA : A.Valid M C.omega)
    {T : MatrixArithmetic M.Domain} (hT : T.Valid M C) {U : MatrixLiftParameters M.Domain}
    {source : M.Domain} (hLast : M.mem U.last A.width) (hRoot : M.mem U.root A.width)
    (hSource : M.mem source A.width) (hCopy : M.mem U.copy C.omega) :
    ∃ V, LiftedColumnGraph M C A T U source V := by
  obtain ⟨Base,Inc,Flags,V,_,_,hV,hBase,hInc,hFlags,hRows⟩ :=
    lifted_column_exists_d hM hC hA hT.diff hT.add hT.mul hLast hRoot hSource hCopy
  refine ⟨V,hV,?_⟩
  intro r y
  rw [hRows r y]
  constructor
  · rintro ⟨a,ha,hAEntry,hCase⟩
    have hA' := (hBase r a).mp hAEntry
    refine ⟨a,ha,hA',?_⟩
    rcases hCase with ⟨hFlag,d,hd,t,ht,hI,hMul,hAdd⟩ | ⟨hFlag,hy⟩
    · exact Or.inl ⟨((hFlags r).mp hFlag).2,d,hd,t,ht,(hInc r d).mp hI,hMul,hAdd⟩
    · exact Or.inr ⟨fun hAsc => hFlag ((hFlags r).mpr ⟨(hA'.bounds hM.1 hA).1,hAsc⟩),hy⟩
  · rintro ⟨a,ha,hAEntry,hCase⟩
    refine ⟨a,ha,(hBase r a).mpr hAEntry,?_⟩
    rcases hCase with ⟨hFlag,d,hd,t,ht,hI,hMul,hAdd⟩ | ⟨hFlag,hy⟩
    · exact Or.inl ⟨(hFlags r).mpr ⟨(hAEntry.bounds hM.1 hA).1,hFlag⟩,d,hd,t,ht,(hInc r d).mpr hI,hMul,hAdd⟩
    · exact Or.inr ⟨fun hr => hFlag ((hFlags r).mp hr).2,hy⟩

theorem LiftedColumnGraph.unique {M : SetTheory.Structure.{u}} (he : Extensional M)
    {C : ExpressionData M.Domain} {A : FiniteMatrix M.Domain} {T : MatrixArithmetic M.Domain}
    {U : MatrixLiftParameters M.Domain} {source V W : M.Domain}
    (hV : LiftedColumnGraph M C A T U source V) (hW : LiftedColumnGraph M C A T U source W) : V=W :=
  hV.graph.ext he hW.graph (fun r _ y => (hV.entries r y).trans (hW.entries r y).symm)

def PaddedColumnValue (M : SetTheory.Structure.{u}) (z height V r y : M.Domain) : Prop :=
  MemPair M V r y ∨ (¬M.mem r height ∧ y=z)

theorem LiftedColumnGraph.padded_iff {M : SetTheory.Structure.{u}} (he : Extensional M)
    {C : ExpressionData M.Domain} {A : FiniteMatrix M.Domain} {T : MatrixArithmetic M.Domain}
    {U : MatrixLiftParameters M.Domain} {source V : M.Domain}
    (hV : LiftedColumnGraph M C A T U source V) (r y : M.Domain) :
    PaddedColumnValue M C.zero A.height V r y ↔ PaddedLiftedEntry M C A T U source r y := by
  constructor
  · rintro (hAt | hOutside)
    · exact Or.inl ⟨(hV.graph.bounds he hAt).1,(hV.entries r y).mp hAt⟩
    · exact Or.inr hOutside
  · rintro (⟨_,hAt⟩ | hOutside)
    · exact Or.inl ((hV.entries r y).mpr hAt)
    · exact Or.inr hOutside

theorem padded_matrix_iff_lifted_d {M : SetTheory.Structure.{u}} (he : Extensional M)
    {C : ExpressionData M.Domain} {A B : FiniteMatrix M.Domain} (hB : B.Valid M C.omega)
    {T : MatrixArithmetic M.Domain} {U : MatrixLiftParameters M.Domain} {source target : M.Domain}
    (hHeight : B.height=A.height) (hTarget : M.mem target B.width)
    (hEntries : ∀ r y, MatrixEntry M B r target y ↔
      LiftedEntry M C A T U.forests U.rows U.last U.maximal U.root U.copy source r y) (r y : M.Domain) :
    PaddedEntry M C.zero B r target y ↔ PaddedLiftedEntry M C A T U source r y := by
  constructor
  · rintro (hAt | ⟨hOutside,hy⟩)
    · exact Or.inl ⟨hHeight ▸ (hAt.bounds he hB).1,(hEntries r y).mp hAt⟩
    · rcases hOutside with hr | ht
      · exact Or.inr ⟨fun hrA => hr (hHeight.symm ▸ hrA),hy⟩
      · exact False.elim (ht hTarget)
  · rintro (⟨_,hAt⟩ | ⟨hOutside,hy⟩)
    · exact Or.inl ((hEntries r y).mpr hAt)
    · exact Or.inr ⟨Or.inl (fun hrB => hOutside (hHeight ▸ hrB)),hy⟩

/-- 同一个提升公式的任意两个实际矩阵列读取，继承已证明的完整后缀次序。
该接口允许两列位于不同矩阵，例如额外构造的虚拟末列。 -/
theorem lifted_suffix_le_realized_d {M : SetTheory.Structure.{u}} (he : Extensional M)
    {C : ExpressionData M.Domain} {A B D : FiniteMatrix M.Domain}
    (hB : B.Valid M C.omega) (hD : D.Valid M C.omega)
    {T : MatrixArithmetic M.Domain} {U : MatrixLiftParameters M.Domain} {c d x y start : M.Domain}
    (hBH : B.height=A.height) (hDH : D.height=A.height) (hx : M.mem x B.width) (hy : M.mem y D.width)
    (hX : ∀ r v, MatrixEntry M B r x v ↔ LiftedEntry M C A T U.forests U.rows U.last U.maximal U.root U.copy c r v)
    (hY : ∀ r v, MatrixEntry M D r y v ↔ LiftedEntry M C A T U.forests U.rows U.last U.maximal U.root U.copy d r v)
    (hLe : LiftedColumnLeFrom M C A T U c d start) : ColumnLeFrom M C.omega C.zero B D x y start := by
  have xiff := padded_matrix_iff_lifted_d he hB hBH hx hX
  have yiff := padded_matrix_iff_lifted_d he hD hDH hy hY
  have convert (r : M.Domain) (hEq : LiftedColumnEqAt M C A T U c d r) : ColumnEqAt M C.omega C.zero B D x y r := by
    intro a ha b hb hA hB
    exact hEq a ha b hb ((xiff r a).mp hA) ((yiff r b).mp hB)
  rcases hLe with hEq | ⟨r,hr,hStart,hEarlier,a,ha,b,hb,hA,hB,hab⟩
  · exact Or.inl (fun r hr hStart => convert r (hEq r hr hStart))
  · exact Or.inr ⟨r,hr,hStart,fun q hq hsq => convert q (hEarlier q hq hsq),
      a,ha,b,hb,(xiff r a).mpr hA,(yiff r b).mpr hB,hab⟩

end KP1Y.OneYFinite
