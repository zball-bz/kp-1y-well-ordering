import KP1Y.OneYFrameMatrix
import KP1Y.OneYNaturalAdditionTable
import KP1Y.OneYNaturalMultiplication
import KP1Y.OneYNaturalMultiplicationLaws
import KP1Y.OneYNaturalDifferenceAddition

/-! BM4 有限矩阵的实际对象编码、数值行、列前缀及最大活动父行搜索。
矩阵复制的数值加量在此模块继续装配；不把复制父图或结构保持作为公理。
-/
namespace KP1Y.OneYFinite
open YesMetaZFC YesMetaZFC.SetTheory YesMetaZFC.SetTheory.Definitional
open KP1Y.Kuratowski KP1Y.Functions KP1Y.Naturals KP1Y.Bounded
universe u v

structure FiniteMatrix (α : Type u) where
  height : α
  width : α
  cells : α
  values : α

def FiniteMatrix.map {α : Type u} {β : Type v} (A : FiniteMatrix α) (f : α → β) : FiniteMatrix β :=
  ⟨f A.height,f A.width,f A.cells,f A.values⟩

def FiniteMatrix.eval {M : SetTheory.Structure.{u}} {d : Nat} (A : FiniteMatrix (Project.Term d)) (env : Env M d) : FiniteMatrix M.Domain :=
  A.map (fun t => t.eval env)

def FiniteMatrix.weaken {d : Nat} (A : FiniteMatrix (Project.Term d)) : FiniteMatrix (Project.Term (d+1)) := A.map (fun t => t.weaken)

theorem FiniteMatrix.eval_weaken {M : SetTheory.Structure.{u}} {d : Nat}
    (A : FiniteMatrix (Project.Term d)) (env : Env M d) (x : M.Domain) : A.weaken.eval (env.push x)=A.eval env := by
  cases A
  simp [FiniteMatrix.map,FiniteMatrix.weaken,FiniteMatrix.eval,Term.eval_weaken]

structure FiniteMatrix.Valid (M : SetTheory.Structure.{u}) (w : M.Domain) (A : FiniteMatrix M.Domain) : Prop where
  height : M.mem A.height w
  width : M.mem A.width w
  cells : IsProduct M A.cells A.height A.width
  values : Graph M A.values A.cells w

def MatrixEntry (M : SetTheory.Structure.{u}) (A : FiniteMatrix M.Domain) (r c d : M.Domain) : Prop :=
  ∃ key, M.mem key A.cells ∧ Codes M key r c ∧ MemPair M A.values key d

def matrixEntryFormula {d : Nat} (A : FiniteMatrix (Project.Term d)) (r c x : Project.Term d) : Project.Formula 1 d :=
  Project.Formula.existsMem A.cells (.conj (codeFormula (.bound 0) r.weaken c.weaken)
    (memPairFormula A.values.weaken (.bound 0) x.weaken))

theorem matrixEntryFormula_delta0 {d : Nat} (A : FiniteMatrix (Project.Term d)) (r c x : Project.Term d) :
    (matrixEntryFormula A r c x).IsDelta0 := .existsMem _ (.conj (codeFormula_delta0 _ _ _) (memPairFormula_delta0 _ _ _))

theorem matrixEntryFormula_iff {M : SetTheory.Structure.{u}} (he : Extensional M) {d : Nat}
    (env : Env M d) (A : FiniteMatrix (Project.Term d)) (r c x : Project.Term d) :
    Project.Formula.satisfies env (matrixEntryFormula A r c x) ↔ MatrixEntry M (A.eval env) (r.eval env) (c.eval env) (x.eval env) := by
  simp only [matrixEntryFormula,MatrixEntry,Project.Formula.satisfies_existsMem_iff,
    Project.Formula.satisfies_conj_iff,codeFormula_iff he,memPairFormula_iff he,Term.eval_weaken]
  rfl

theorem MatrixEntry.bounds {M : SetTheory.Structure.{u}} (he : Extensional M)
    {w : M.Domain} {A : FiniteMatrix M.Domain} (hA : A.Valid M w) {r c d : M.Domain} (h : MatrixEntry M A r c d) :
    M.mem r A.height ∧ M.mem c A.width ∧ M.mem d w := by
  obtain ⟨key,hk,hCode,hAt⟩ := h
  obtain ⟨r',hr,c',hc,hCode'⟩ := (hA.cells key).mp hk
  obtain ⟨hrr,hcc⟩ := codes_injective he hCode hCode'
  subst r'
  subst c'
  exact ⟨hr,hc,(hA.values.bounds he hAt).2⟩

theorem FiniteMatrix.Valid.entry_total_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {w : M.Domain} {A : FiniteMatrix M.Domain} (hA : A.Valid M w) {r c : M.Domain}
    (hr : M.mem r A.height) (hc : M.mem c A.width) : ∃ d, M.mem d w ∧ MatrixEntry M A r c d := by
  obtain ⟨key,hCode⟩ := codes_total hM r c
  have hk := (hA.cells key).mpr ⟨r,hr,c,hc,hCode⟩
  obtain ⟨d,hd,hAt⟩ := hA.values.total key hk
  exact ⟨d,hd,key,hk,hCode,hAt⟩

theorem FiniteMatrix.Valid.entry_unique {M : SetTheory.Structure.{u}} (he : Extensional M)
    {w : M.Domain} {A : FiniteMatrix M.Domain} (hA : A.Valid M w) {r c d e : M.Domain}
    (hd : MatrixEntry M A r c d) (he' : MatrixEntry M A r c e) : d=e := by
  obtain ⟨key,_,hCode,hAt⟩ := hd
  obtain ⟨key',_,hCode',hAt'⟩ := he'
  have hKeys := codes_unique he hCode hCode'
  subst key'
  exact hA.values.unique key d e hAt hAt'

private def rowValueSchema : Project.Delta0BinarySchema 3 where
  body := Project.Formula.existsMem (.bound 4)
    (.conj (codeFormula (.bound 0) (.bound 3) (.bound 2)) (memPairFormula (.bound 4) (.bound 0) (.bound 1)))
  freeClosed := by
    simp [codeFormula,pairFormula,memPairFormula,Project.Formula.existsMem,Project.Formula.forallMem,Definitional.Formula.FreeClosed]
  delta0 := .existsMem _ (.conj (codeFormula_delta0 _ _ _) (memPairFormula_delta0 _ _ _))

theorem FiniteMatrix.Valid.row_values_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {w : M.Domain} {A : FiniteMatrix M.Domain} (hA : A.Valid M w) {r : M.Domain} (hr : M.mem r A.height) :
    ∃ V, Graph M V A.width w ∧ ∀ c d, MemPair M V c d ↔ MatrixEntry M A r c d := by
  let env := ((oneEnv A.cells).push A.values).push r
  have hφ (c d : M.Domain) : Project.Formula.satisfies ((env.push c).push d) rowValueSchema.body ↔ MatrixEntry M A r c d := by
    simp only [rowValueSchema,Project.Formula.satisfies_existsMem_iff,Project.Formula.satisfies_conj_iff,
      codeFormula_iff hM.1,memPairFormula_iff hM.1]
    rfl
  obtain ⟨V,hSupport,hRaw⟩ := relation_comprehension_d hM rowValueSchema env A.width w
  have hRows (c d : M.Domain) : MemPair M V c d ↔ MatrixEntry M A r c d := by
    rw [hRaw c d,hφ]
    exact ⟨fun h => h.2.2,fun h => ⟨(h.bounds hM.1 hA).2.1,(h.bounds hM.1 hA).2.2,h⟩⟩
  refine ⟨V,⟨hSupport,?_,?_⟩,hRows⟩
  · intro c hc
    obtain ⟨d,hd,hEntry⟩ := hA.entry_total_d hM hr hc
    exact ⟨d,hd,(hRows c d).mpr hEntry⟩
  · intro c d e hd he
    exact hA.entry_unique hM.1 ((hRows c d).mp hd) ((hRows c e).mp he)

theorem FiniteMatrix.Valid.row_view_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {w : M.Domain} {A : FiniteMatrix M.Domain} (hA : A.Valid M w) {r : M.Domain} (hr : M.mem r A.height) :
    ∃ V, MatrixRowValues M w A.width A.cells A.values r V := by
  obtain ⟨V,hV,hRows⟩ := hA.row_values_d hM hr
  refine ⟨V,hV,?_⟩
  intro c _ key hk hCode d _
  constructor
  · intro hAt
    exact (hRows c d).mpr ⟨key,hk,hCode,hAt⟩
  · intro hAt
    obtain ⟨key',_,hCode',hAt'⟩ := (hRows c d).mp hAt
    exact codes_unique hM.1 hCode' hCode ▸ hAt'

theorem FiniteMatrix.Valid.row_view_unique_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {w : M.Domain} {A : FiniteMatrix M.Domain} (hA : A.Valid M w) {r V W : M.Domain} (hr : M.mem r A.height)
    (hV : MatrixRowValues M w A.width A.cells A.values r V) (hW : MatrixRowValues M w A.width A.cells A.values r W) : V=W := by
  classical
  apply hV.graph.ext hM.1 hW.graph
  intro c hc d
  by_cases hd : M.mem d w
  · obtain ⟨key,hCode⟩ := codes_total hM r c
    have hk := (hA.cells key).mpr ⟨r,hr,c,hc,hCode⟩
    exact (hV.entries c hc key hk hCode d hd).symm.trans (hW.entries c hc key hk hCode d hd)
  · exact iff_of_false (fun h => hd (hV.graph.bounds hM.1 h).2) (fun h => hd (hW.graph.bounds hM.1 h).2)

/-- 列前缀取实际地址子集及值图限制；行高不改变。 -/
theorem FiniteMatrix.Valid.prefix_exists_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {w : M.Domain} {A : FiniteMatrix M.Domain} (hA : A.Valid M w) {n : M.Domain}
    (hn : M.mem n w) (hSub : M.MemberSubset n A.width) :
    ∃ B, B.Valid M w ∧ B.height=A.height ∧ B.width=n ∧ ∀ r c d, M.mem c n →
      (MatrixEntry M B r c d ↔ MatrixEntry M A r c d) := by
  obtain ⟨Cells,hCells⟩ := product_exists hM A.height n
  have hKeysSub : M.MemberSubset Cells A.cells := by
    intro key hk
    obtain ⟨r,hr,c,hc,hCode⟩ := (hCells key).mp hk
    exact (hA.cells key).mpr ⟨r,hr,c,hSub c hc,hCode⟩
  obtain ⟨Values,hValues,hRows⟩ := restrict_graph_d hM hA.values hKeysSub
  let B : FiniteMatrix M.Domain := ⟨A.height,n,Cells,Values⟩
  refine ⟨B,⟨hA.height,hn,hCells,hValues⟩,rfl,rfl,?_⟩
  intro r c d hc
  constructor
  · rintro ⟨key,hk,hCode,hAt⟩
    exact ⟨key,hKeysSub key hk,hCode,((hRows key d).mp hAt).2⟩
  · rintro hEntry
    have hr := (hEntry.bounds hM.1 hA).1
    obtain ⟨key,_,hCode,hAt⟩ := hEntry
    have hk := (hCells key).mpr ⟨r,hr,c,hc,hCode⟩
    exact ⟨key,hk,hCode,(hRows key d).mpr ⟨hk,hAt⟩⟩

def ActiveParentRow (M : SetTheory.Structure.{u}) (Forests Rows width last r : M.Domain) : Prop :=
  ∃ P, M.mem P Forests ∧ MemPair M Rows r P ∧ ∃ p, M.mem p width ∧ MemPair M P last p

private def activeParentSchema : Project.Delta0UnarySchema 4 where
  body := Project.Formula.existsMem (.bound 4) (.conj (memPairFormula (.bound 4) (.bound 1) (.bound 0))
    (Project.Formula.existsMem (.bound 3) (memPairFormula (.bound 1) (.bound 3) (.bound 0))))
  freeClosed := by
    simp [memPairFormula,codeFormula,pairFormula,Project.Formula.existsMem,Project.Formula.forallMem,Definitional.Formula.FreeClosed]
  delta0 := .existsMem _ (.conj (memPairFormula_delta0 _ _ _) (.existsMem _ (memPairFormula_delta0 _ _ _)))

private def activeParentEnv {M : SetTheory.Structure.{u}} (Forests Rows width last : M.Domain) : Env M 4 :=
  (((oneEnv Forests).push Rows).push width).push last

private theorem activeParentSchema_iff {M : SetTheory.Structure.{u}} (he : Extensional M)
    (Forests Rows width last r : M.Domain) :
    Project.Formula.satisfies ((activeParentEnv Forests Rows width last).push r) activeParentSchema.body ↔
      ActiveParentRow M Forests Rows width last r := by
  simp only [activeParentSchema,Project.Formula.satisfies_existsMem_iff,Project.Formula.satisfies_conj_iff,memPairFormula_iff he]
  rfl

/-- height 哨兵表示无活动行，否则得到实际最大活动行；成功结果0不会与失败混同。 -/
def MaximalParentRow (M : SetTheory.Structure.{u}) (height Forests Rows width last result : M.Domain) : Prop :=
  (result=height ∧ ∀ r, M.mem r height → ¬ActiveParentRow M Forests Rows width last r) ∨
    (M.mem result height ∧ ActiveParentRow M Forests Rows width last result ∧
      ∀ r, M.mem r height → ActiveParentRow M Forests Rows width last r → r=result ∨ M.mem r result)

theorem maximal_parent_row_exists_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {w height : M.Domain} (hw : M.IsOmega w) (hHeight : M.mem height w) (Forests Rows width last : M.Domain) :
    ∃ result, M.mem result w ∧ MaximalParentRow M height Forests Rows width last result := by
  obtain ⟨A,hA⟩ := SetTheory.KP.separation_exists_d (KP1Y.models_weakKP hM) activeParentSchema
    (activeParentEnv Forests Rows width last) height
  have hRows (r : M.Domain) : M.mem r A ↔ M.mem r height ∧ ActiveParentRow M Forests Rows width last r := by
    simpa only [activeParentSchema_iff hM.1] using hA r
  obtain ⟨result,hResult,hSearch⟩ := bounded_search_exists_d (A := A) hM hw hHeight
  refine ⟨result,hResult,?_⟩
  rcases hSearch with ⟨he,hNone⟩ | ⟨hr,hAct,hMax⟩
  · exact Or.inl ⟨he,fun r hr hAct => hNone r hr ((hRows r).mpr ⟨hr,hAct⟩)⟩
  · exact Or.inr ⟨hr,((hRows result).mp hAct).2,fun r hr hAct => hMax r hr ((hRows r).mpr ⟨hr,hAct⟩)⟩

theorem maximal_parent_row_unique_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {height Forests Rows width last r s : M.Domain} (hHeight : M.IsOrdinal height)
    (hr : MaximalParentRow M height Forests Rows width last r)
    (hs : MaximalParentRow M height Forests Rows width last s) : r=s := by
  rcases hr with ⟨he,hNone⟩ | ⟨hr,hAct,hMax⟩ <;> rcases hs with ⟨he',hNone'⟩ | ⟨hs,hAct',hMax'⟩
  · exact he.trans he'.symm
  · exact False.elim (hNone s hs hAct')
  · exact False.elim (hNone' r hr hAct)
  · rcases hMax s hs hAct' with he | hsr
    · exact he.symm
    · rcases hMax' r hr hAct with he | hrs
      · exact he
      · exact False.elim (SetTheory.KP.mem_irrefl_d (KP1Y.models_weakKP hM) r
          ((hHeight.mem hr).transitive s hsr r hrs))

def PaddedEntry (M : SetTheory.Structure.{u}) (z : M.Domain) (A : FiniteMatrix M.Domain) (r c d : M.Domain) : Prop :=
  MatrixEntry M A r c d ∨ ((¬M.mem r A.height ∨ ¬M.mem c A.width) ∧ d=z)

def paddedEntryFormula {d : Nat} (z : Project.Term d) (A : FiniteMatrix (Project.Term d)) (r c x : Project.Term d) : Project.Formula 1 d :=
  .disj (matrixEntryFormula A r c x) (.conj (.disj (.neg (.mem r A.height)) (.neg (.mem c A.width)))
    (Project.Formula.extensionalEq x z))

theorem paddedEntryFormula_delta0 {d : Nat} (z : Project.Term d) (A : FiniteMatrix (Project.Term d)) (r c x : Project.Term d) :
    (paddedEntryFormula z A r c x).IsDelta0 := .disj (matrixEntryFormula_delta0 _ _ _ _)
      (.conj (.disj (.neg (.mem _ _)) (.neg (.mem _ _))) (.atom _ _ _))

theorem paddedEntryFormula_iff {M : SetTheory.Structure.{u}} (he : Extensional M) {d : Nat}
    (env : Env M d) (z : Project.Term d) (A : FiniteMatrix (Project.Term d)) (r c x : Project.Term d) :
    Project.Formula.satisfies env (paddedEntryFormula z A r c x) ↔
      PaddedEntry M (z.eval env) (A.eval env) (r.eval env) (c.eval env) (x.eval env) := by
  simp only [paddedEntryFormula,PaddedEntry,Project.Formula.satisfies_disj_iff,Project.Formula.satisfies_conj_iff,
    Project.Formula.satisfies_neg_iff,Project.Formula.satisfies_mem_iff,
    Project.Formula.satisfies_extensionalEq_iff_eq he,matrixEntryFormula_iff he]
  rfl

theorem FiniteMatrix.Valid.padded_total_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {A : FiniteMatrix M.Domain} (hA : A.Valid M C.omega)
    (r c : M.Domain) : ∃ d, M.mem d C.omega ∧ PaddedEntry M C.zero A r c d := by
  classical
  by_cases hr : M.mem r A.height
  · by_cases hc : M.mem c A.width
    · obtain ⟨d,hd,hEntry⟩ := hA.entry_total_d hM hr hc
      exact ⟨d,hd,Or.inl hEntry⟩
    · exact ⟨C.zero,hC.zero_nat,Or.inr ⟨Or.inr hc,rfl⟩⟩
  · exact ⟨C.zero,hC.zero_nat,Or.inr ⟨Or.inl hr,rfl⟩⟩

theorem FiniteMatrix.Valid.padded_unique {M : SetTheory.Structure.{u}} (he : Extensional M)
    {w z : M.Domain} {A : FiniteMatrix M.Domain} (hA : A.Valid M w) {r c d e : M.Domain}
    (hd : PaddedEntry M z A r c d) (he' : PaddedEntry M z A r c e) : d=e := by
  rcases hd with hd | ⟨hOutside,hd⟩ <;> rcases he' with he' | ⟨hOutside',he'⟩
  · exact hA.entry_unique he hd he'
  · exact False.elim (hOutside'.elim (fun h => h (hd.bounds he hA).1) (fun h => h (hd.bounds he hA).2.1))
  · exact False.elim (hOutside.elim (fun h => h (he'.bounds he hA).1) (fun h => h (he'.bounds he hA).2.1))
  · exact hd.trans he'.symm

theorem PaddedEntry.natural {M : SetTheory.Structure.{u}} (he : Extensional M)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {A : FiniteMatrix M.Domain} (hA : A.Valid M C.omega)
    {r c d : M.Domain} (h : PaddedEntry M C.zero A r c d) : M.mem d C.omega := by
  rcases h with h | ⟨_,heq⟩
  · exact (h.bounds he hA).2.2
  · exact heq ▸ hC.zero_nat

theorem padded_entry_prefix_iff {M : SetTheory.Structure.{u}}
    {z : M.Domain} {A B : FiniteMatrix M.Domain}
    (hHeight : B.height=A.height) (hSub : M.MemberSubset B.width A.width)
    (hEntries : ∀ r c d, M.mem c B.width → (MatrixEntry M B r c d ↔ MatrixEntry M A r c d))
    {r c d : M.Domain} (hc : M.mem c B.width) : PaddedEntry M z B r c d ↔ PaddedEntry M z A r c d := by
  have hOld := hSub c hc
  simp only [PaddedEntry,hHeight,hEntries r c d hc,hc,hOld,not_true_eq_false,or_false]

structure MatrixExpansionContext (M : SetTheory.Structure.{u}) (C : ExpressionData M.Domain)
    (A : FiniteMatrix M.Domain) (Forests Rows last maximal root : M.Domain) : Prop where
  width_successor : M.SuccessorOf A.width last
  maximality : MaximalParentRow M A.height Forests Rows A.width last maximal
  row : M.mem maximal A.height
  parent : ∃ P, M.mem P Forests ∧ MemPair M Rows maximal P ∧ MemPair M P last root

/-- 最大父行搜索成功时，从真实父图唯一恢复复制根；尚未假设任何复制保持结论。 -/
theorem matrix_expansion_context_exists {M : SetTheory.Structure.{u}}
    {C : ExpressionData M.Domain} {A : FiniteMatrix M.Domain} {Forests Rows last maximal : M.Domain}
    (hLast : M.SuccessorOf A.width last) (hMax : MaximalParentRow M A.height Forests Rows A.width last maximal)
    (hSuccess : maximal≠A.height) : ∃ root, MatrixExpansionContext M C A Forests Rows last maximal root := by
  rcases hMax with ⟨he,_⟩ | ⟨hm,hActive,hGreatest⟩
  · exact False.elim (hSuccess he)
  · obtain ⟨P,hP,hAt,root,hRoot,hParent⟩ := hActive
    exact ⟨root,hLast,Or.inr ⟨hm,⟨P,hP,hAt,root,hRoot,hParent⟩,hGreatest⟩,
      hm,P,hP,hAt,hParent⟩

theorem MatrixExpansionContext.root_lt_last {M : SetTheory.Structure.{u}}
    {C : ExpressionData M.Domain} {A : FiniteMatrix M.Domain} {Forests Rows L last maximal root : M.Domain}
    (hRun : MatrixParentRun M C A.width A.height A.cells A.values Forests Rows L)
    (h : MatrixExpansionContext M C A Forests Rows last maximal root) : M.mem root last := by
  obtain ⟨P,_,hAt,hParent⟩ := h.parent
  exact (hRun.forests maximal P hAt).left last root hParent

theorem MatrixExpansionContext.unique_root {M : SetTheory.Structure.{u}}
    {C : ExpressionData M.Domain} {A : FiniteMatrix M.Domain} {Forests Rows L last maximal root root' : M.Domain}
    (hRun : MatrixParentRun M C A.width A.height A.cells A.values Forests Rows L)
    (h : MatrixExpansionContext M C A Forests Rows last maximal root)
    (h' : MatrixExpansionContext M C A Forests Rows last maximal root') : root=root' := by
  obtain ⟨P,_,hAt,hParent⟩ := h.parent
  obtain ⟨Q,_,hAt',hParent'⟩ := h'.parent
  have hPQ := hRun.graph.unique maximal P Q hAt hAt'
  subst Q
  exact (hRun.forests maximal P hAt).unique last root root' hParent hParent'

/-- BM4 行加量是原末列值减去复制根列值的实际截断差。 -/
def RowIncrement (M : SetTheory.Structure.{u}) (w : M.Domain) (A : FiniteMatrix M.Domain)
    (Pairs Diff last root r d : M.Domain) : Prop :=
  ∃ x, M.mem x w ∧ ∃ y, M.mem y w ∧ ∃ key, M.mem key Pairs ∧ Codes M key x y ∧
    MatrixEntry M A r last x ∧ MatrixEntry M A r root y ∧ MemPair M Diff key d

private def rowIncrementEnv {M : SetTheory.Structure.{u}} (w : M.Domain) (A : FiniteMatrix M.Domain)
    (Pairs Diff last root : M.Domain) : Env M 9 :=
  ((((((((oneEnv w).push A.height).push A.width).push A.cells).push A.values).push Pairs).push Diff).push last).push root

private def rowIncrementSchema : Project.Delta0BinarySchema 9 where
  body := Project.Formula.existsMem (.bound 10) (Project.Formula.existsMem (.bound 11)
    (Project.Formula.existsMem (.bound 7) (.conj (codeFormula (.bound 0) (.bound 2) (.bound 1))
      (.conj (matrixEntryFormula ⟨.bound 12,.bound 11,.bound 10,.bound 9⟩ (.bound 4) (.bound 6) (.bound 2))
        (.conj (matrixEntryFormula ⟨.bound 12,.bound 11,.bound 10,.bound 9⟩ (.bound 4) (.bound 5) (.bound 1))
          (memPairFormula (.bound 7) (.bound 0) (.bound 3)))))))
  freeClosed := by
    simp [matrixEntryFormula,codeFormula,pairFormula,memPairFormula,Project.Formula.existsMem,
      Project.Formula.forallMem,Definitional.Formula.FreeClosed]
  delta0 := .existsMem _ (.existsMem _ (.existsMem _ (.conj (codeFormula_delta0 _ _ _)
    (.conj (matrixEntryFormula_delta0 _ _ _ _) (.conj (matrixEntryFormula_delta0 _ _ _ _) (memPairFormula_delta0 _ _ _))))))

private theorem rowIncrementSchema_iff {M : SetTheory.Structure.{u}} (he : Extensional M) (w : M.Domain)
    (A : FiniteMatrix M.Domain) (Pairs Diff last root r d : M.Domain) :
    Project.Formula.satisfies (((rowIncrementEnv w A Pairs Diff last root).push r).push d) rowIncrementSchema.body ↔
      RowIncrement M w A Pairs Diff last root r d := by
  simp only [rowIncrementSchema,Project.Formula.satisfies_existsMem_iff,Project.Formula.satisfies_conj_iff,
    codeFormula_iff he,matrixEntryFormula_iff he,memPairFormula_iff he]
  rfl

theorem row_increment_unique_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} {A : FiniteMatrix M.Domain} (hA : A.Valid M C.omega)
    {Pairs Diff last root r d e : M.Domain} (hDiff : DifferenceTable M C Pairs Diff)
    (hd : RowIncrement M C.omega A Pairs Diff last root r d)
    (he : RowIncrement M C.omega A Pairs Diff last root r e) : d=e := by
  obtain ⟨x,_,y,_,key,_,hCode,hLast,hRoot,hAt⟩ := hd
  obtain ⟨x',_,y',_,key',_,hCode',hLast',hRoot',hAt'⟩ := he
  have hxx := hA.entry_unique hM.1 hLast hLast'
  have hyy := hA.entry_unique hM.1 hRoot hRoot'
  subst x'
  subst y'
  have hKeys := codes_unique hM.1 hCode hCode'
  subst key'
  exact hDiff.graph.unique key d e hAt hAt'

theorem row_increment_graph_exists_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} {A : FiniteMatrix M.Domain} (hA : A.Valid M C.omega)
    {Pairs Diff last root : M.Domain} (hDiff : DifferenceTable M C Pairs Diff)
    (hLast : M.mem last A.width) (hRoot : M.mem root A.width) :
    ∃ Inc, Graph M Inc A.height C.omega ∧ ∀ r d, MemPair M Inc r d ↔ RowIncrement M C.omega A Pairs Diff last root r d := by
  let env := rowIncrementEnv C.omega A Pairs Diff last root
  obtain ⟨Inc,hSupport,hRaw⟩ := relation_comprehension_d hM rowIncrementSchema env A.height C.omega
  have hRows (r d : M.Domain) : MemPair M Inc r d ↔ RowIncrement M C.omega A Pairs Diff last root r d := by
    have hRaw' := (hRaw r d).trans (and_congr Iff.rfl (and_congr Iff.rfl
      (rowIncrementSchema_iff hM.1 C.omega A Pairs Diff last root r d)))
    refine hRaw'.trans ⟨fun h => h.2.2,?_⟩
    intro h
    obtain ⟨x,hx,y,hy,key,hk,hCode,hLast,hRoot,hAt⟩ := h
    exact ⟨(hLast.bounds hM.1 hA).1,(hDiff.graph.bounds hM.1 hAt).2,x,hx,y,hy,key,hk,hCode,hLast,hRoot,hAt⟩
  refine ⟨Inc,⟨hSupport,?_,?_⟩,hRows⟩
  · intro r hr
    obtain ⟨x,hx,hL⟩ := hA.entry_total_d hM hr hLast
    obtain ⟨y,hy,hR⟩ := hA.entry_total_d hM hr hRoot
    obtain ⟨key,hCode⟩ := codes_total hM x y
    have hk := (hDiff.pairs key).mpr ⟨x,hx,y,hy,hCode⟩
    obtain ⟨d,hd,hAt⟩ := hDiff.graph.total key hk
    exact ⟨d,hd,(hRows r d).mpr ⟨x,hx,y,hy,key,hk,hCode,hL,hR,hAt⟩⟩
  · intro r d e hd he
    exact row_increment_unique_d hM hA hDiff ((hRows r d).mp hd) ((hRows r e).mp he)

def Ascending (M : SetTheory.Structure.{u}) (C : ExpressionData M.Domain)
    (width Forests Rows maximal root source r : M.Domain) : Prop :=
  M.mem r maximal ∧ (source=root ∨ ∃ P, M.mem P Forests ∧ MemPair M Rows r P ∧ Ancestor M C width P root source)

def ascendingFormula {d : Nat} (C : ExpressionData (Project.Term d))
    (width Forests Rows maximal root source r : Project.Term d) : Project.Formula 1 d :=
  .conj (.mem r maximal) (.disj (Project.Formula.extensionalEq source root) (Project.Formula.existsMem Forests
    (.conj (memPairFormula Rows.weaken r.weaken (.bound 0))
      (ancestorFormula C.weaken width.weaken (.bound 0) root.weaken source.weaken))))

theorem ascendingFormula_delta0 {d : Nat} (C : ExpressionData (Project.Term d))
    (width Forests Rows maximal root source r : Project.Term d) :
    (ascendingFormula C width Forests Rows maximal root source r).IsDelta0 :=
  .conj (.mem _ _) (.disj (.atom _ _ _) (.existsMem _ (.conj (memPairFormula_delta0 _ _ _) (ancestorFormula_delta0 _ _ _ _ _))))

theorem ascendingFormula_iff {M : SetTheory.Structure.{u}} (he : Extensional M) {d : Nat} (env : Env M d)
    (C : ExpressionData (Project.Term d)) (width Forests Rows maximal root source r : Project.Term d) :
    Project.Formula.satisfies env (ascendingFormula C width Forests Rows maximal root source r) ↔
      Ascending M (C.eval env) (width.eval env) (Forests.eval env) (Rows.eval env)
        (maximal.eval env) (root.eval env) (source.eval env) (r.eval env) := by
  simp only [ascendingFormula,Ascending,Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_mem_iff,
    Project.Formula.satisfies_disj_iff,Project.Formula.satisfies_extensionalEq_iff_eq he,Project.Formula.satisfies_existsMem_iff,
    memPairFormula_iff he,ancestorFormula_iff he,ExpressionData.eval_weaken,Term.eval_weaken]
  rfl

private def ascendingEnv {M : SetTheory.Structure.{u}} (C : ExpressionData M.Domain)
    (width Forests Rows maximal root source : M.Domain) : Env M 11 :=
  ((((((((((oneEnv C.omega).push C.zero).push C.one).push C.sequences).push C.expressions).push width).push Forests).push Rows).push maximal).push root).push source

private def ascendingSchema : Project.Delta0UnarySchema 11 where
  body := ascendingFormula ⟨.bound 11,.bound 10,.bound 9,.bound 8,.bound 7⟩
    (.bound 6) (.bound 5) (.bound 4) (.bound 3) (.bound 2) (.bound 1) (.bound 0)
  freeClosed := by
    have hAnc := ancestorFormula_freeClosed
      (show (⟨.bound 12,.bound 11,.bound 10,.bound 9,.bound 8⟩ : ExpressionData (Project.Term 13)).Closed from ⟨rfl,rfl,rfl,rfl,rfl⟩)
      (.bound 7) (.bound 0) (.bound 3) (.bound 2) rfl rfl rfl rfl
    simp [ascendingFormula,ExpressionData.weaken,ExpressionData.map,memPairFormula,codeFormula,pairFormula,
      Project.Formula.existsMem,Project.Formula.forallMem,Definitional.Formula.FreeClosed]
    exact hAnc
  delta0 := ascendingFormula_delta0 _ _ _ _ _ _ _ _

theorem ascending_rows_exists_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    (C : ExpressionData M.Domain) (height width Forests Rows maximal root source : M.Domain) :
    ∃ Flags, ∀ r, M.mem r Flags ↔ M.mem r height ∧ Ascending M C width Forests Rows maximal root source r := by
  let env := ascendingEnv C width Forests Rows maximal root source
  have hφ (r : M.Domain) : Project.Formula.satisfies (env.push r) ascendingSchema.body ↔
      Ascending M C width Forests Rows maximal root source r := by
    simp only [ascendingSchema,ascendingFormula_iff hM.1]
    rfl
  obtain ⟨Flags,hFlags⟩ := SetTheory.KP.separation_exists_d (KP1Y.models_weakKP hM) ascendingSchema env height
  exact ⟨Flags,fun r => by simpa only [hφ] using hFlags r⟩

private def columnValueSchema : Project.Delta0BinarySchema 3 where
  body := Project.Formula.existsMem (.bound 4)
    (.conj (codeFormula (.bound 0) (.bound 2) (.bound 3)) (memPairFormula (.bound 4) (.bound 0) (.bound 1)))
  freeClosed := by
    simp [codeFormula,pairFormula,memPairFormula,Project.Formula.existsMem,Project.Formula.forallMem,Definitional.Formula.FreeClosed]
  delta0 := .existsMem _ (.conj (codeFormula_delta0 _ _ _) (memPairFormula_delta0 _ _ _))

theorem FiniteMatrix.Valid.column_values_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {w : M.Domain} {A : FiniteMatrix M.Domain} (hA : A.Valid M w) {c : M.Domain} (hc : M.mem c A.width) :
    ∃ V, Graph M V A.height w ∧ ∀ r d, MemPair M V r d ↔ MatrixEntry M A r c d := by
  let env := ((oneEnv A.cells).push A.values).push c
  have hφ (r d : M.Domain) : Project.Formula.satisfies ((env.push r).push d) columnValueSchema.body ↔ MatrixEntry M A r c d := by
    simp only [columnValueSchema,Project.Formula.satisfies_existsMem_iff,Project.Formula.satisfies_conj_iff,
      codeFormula_iff hM.1,memPairFormula_iff hM.1]
    rfl
  obtain ⟨V,hSupport,hRaw⟩ := relation_comprehension_d hM columnValueSchema env A.height w
  have hRows (r d : M.Domain) : MemPair M V r d ↔ MatrixEntry M A r c d := by
    rw [hRaw r d,hφ]
    exact ⟨fun h => h.2.2,fun h => ⟨(h.bounds hM.1 hA).1,(h.bounds hM.1 hA).2.2,h⟩⟩
  refine ⟨V,⟨hSupport,?_,?_⟩,hRows⟩
  · intro r hr
    obtain ⟨d,hd,hEntry⟩ := hA.entry_total_d hM hr hc
    exact ⟨d,hd,(hRows r d).mpr hEntry⟩
  · intro r d e hd he
    exact hA.entry_unique hM.1 ((hRows r d).mp hd) ((hRows r e).mp he)

def LiftedRow (M : SetTheory.Structure.{u}) (w Base Inc Flags copy AddPairs Plus MulPairs Times r y : M.Domain) : Prop :=
  ∃ a, M.mem a w ∧ MemPair M Base r a ∧
    ((M.mem r Flags ∧ ∃ d, M.mem d w ∧ ∃ t, M.mem t w ∧ MemPair M Inc r d ∧
      MulAt M MulPairs Times copy d t ∧ AddAt M AddPairs Plus a t y) ∨ (¬M.mem r Flags ∧ y=a))

private def liftedRowEnv {M : SetTheory.Structure.{u}} (w Base Inc Flags copy AddPairs Plus MulPairs Times : M.Domain) : Env M 9 :=
  ((((((((oneEnv w).push Base).push Inc).push Flags).push copy).push AddPairs).push Plus).push MulPairs).push Times

private def liftedRowSchema : Project.Delta0BinarySchema 9 where
  body := Project.Formula.existsMem (.bound 10) (.conj (memPairFormula (.bound 10) (.bound 2) (.bound 0))
    (.disj (.conj (.mem (.bound 2) (.bound 8)) (Project.Formula.existsMem (.bound 11)
      (Project.Formula.existsMem (.bound 12) (.conj (memPairFormula (.bound 11) (.bound 4) (.bound 1))
        (.conj (mulAtFormula (.bound 6) (.bound 5) (.bound 9) (.bound 1) (.bound 0))
          (addAtFormula (.bound 8) (.bound 7) (.bound 2) (.bound 0) (.bound 3)))))))
      (.conj (.neg (.mem (.bound 2) (.bound 8))) (Project.Formula.extensionalEq (.bound 1) (.bound 0)))))
  freeClosed := by
    simp [mulAtFormula,addAtFormula,codeFormula,pairFormula,memPairFormula,Project.Formula.existsMem,
      Project.Formula.forallMem,Definitional.Formula.FreeClosed]
  delta0 := .existsMem _ (.conj (memPairFormula_delta0 _ _ _) (.disj (.conj (.mem _ _)
    (.existsMem _ (.existsMem _ (.conj (memPairFormula_delta0 _ _ _)
      (.conj (mulAtFormula_delta0 _ _ _ _ _) (addAtFormula_delta0 _ _ _ _ _))))))
      (.conj (.neg (.mem _ _)) (.atom _ _ _))))

private theorem liftedRowSchema_iff {M : SetTheory.Structure.{u}} (he : Extensional M)
    (w Base Inc Flags copy AddPairs Plus MulPairs Times r y : M.Domain) :
    Project.Formula.satisfies (((liftedRowEnv w Base Inc Flags copy AddPairs Plus MulPairs Times).push r).push y) liftedRowSchema.body ↔
      LiftedRow M w Base Inc Flags copy AddPairs Plus MulPairs Times r y := by
  simp only [liftedRowSchema,Project.Formula.satisfies_existsMem_iff,Project.Formula.satisfies_conj_iff,
    Project.Formula.satisfies_disj_iff,Project.Formula.satisfies_neg_iff,Project.Formula.satisfies_mem_iff,
    Project.Formula.satisfies_extensionalEq_iff_eq he,mulAtFormula_iff he,addAtFormula_iff he,memPairFormula_iff he]
  rfl

theorem lifted_row_unique {M : SetTheory.Structure.{u}} (he : Extensional M)
    {C : ExpressionData M.Domain} {height Base Inc Flags copy AddPairs Plus MulPairs Times r y z : M.Domain}
    (hBase : Graph M Base height C.omega) (hInc : Graph M Inc height C.omega)
    (hAdd : AdditionTable M C AddPairs Plus) (hMul : MultiplicationTable M C MulPairs Times)
    (hy : LiftedRow M C.omega Base Inc Flags copy AddPairs Plus MulPairs Times r y)
    (hz : LiftedRow M C.omega Base Inc Flags copy AddPairs Plus MulPairs Times r z) : y=z := by
  obtain ⟨a,_,hRa,hY⟩ := hy
  obtain ⟨b,_,hRb,hZ⟩ := hz
  have hab := hBase.unique r a b hRa hRb
  subst b
  rcases hY with ⟨hFlag,d,_,t,_,hRd,hMulD,hAddY⟩ | ⟨hFlag,hY⟩ <;>
    rcases hZ with ⟨hFlag',e,_,u,_,hRe,hMulE,hAddZ⟩ | ⟨hFlag',hZ⟩
  · have hde := hInc.unique r d e hRd hRe
    subst e
    have htu := hMul.mul_unique he hMulD hMulE
    subst u
    exact hAdd.add_unique he hAddY hAddZ
  · exact False.elim (hFlag' hFlag)
  · exact False.elim (hFlag hFlag')
  · exact hY.trans hZ.symm

/-- 精确构造原值 + (ascending ? copy×增量 : 0) 的实际列值图。 -/
theorem lifted_values_exists_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {height Base Inc Flags copy AddPairs Plus MulPairs Times : M.Domain}
    (hBase : Graph M Base height C.omega) (hInc : Graph M Inc height C.omega) (hCopy : M.mem copy C.omega)
    (hAdd : AdditionTable M C AddPairs Plus) (hMul : MultiplicationTable M C MulPairs Times) :
    ∃ V, Graph M V height C.omega ∧ ∀ r y, MemPair M V r y ↔ LiftedRow M C.omega Base Inc Flags copy AddPairs Plus MulPairs Times r y := by
  let env := liftedRowEnv C.omega Base Inc Flags copy AddPairs Plus MulPairs Times
  obtain ⟨V,hSupport,hRaw⟩ := relation_comprehension_d hM liftedRowSchema env height C.omega
  have hRows (r y : M.Domain) : MemPair M V r y ↔ LiftedRow M C.omega Base Inc Flags copy AddPairs Plus MulPairs Times r y := by
    rw [hRaw r y,liftedRowSchema_iff hM.1]
    refine ⟨fun h => h.2.2,?_⟩
    intro h
    obtain ⟨a,ha,hRa,hCase⟩ := h
    have hy : M.mem y C.omega := by
      rcases hCase with ⟨_,_,_,_,_,_,_,hSum⟩ | ⟨_,he⟩
      · exact (hSum.bounds hM.1 hAdd).2.2
      · exact he ▸ ha
    exact ⟨(hBase.bounds hM.1 hRa).1,hy,a,ha,hRa,hCase⟩
  refine ⟨V,⟨hSupport,?_,?_⟩,hRows⟩
  · intro r hr
    obtain ⟨a,ha,hRa⟩ := hBase.total r hr
    classical
    by_cases hFlag : M.mem r Flags
    · obtain ⟨d,hd,hRd⟩ := hInc.total r hr
      obtain ⟨t,ht,hTimes⟩ := hMul.mul_exists_d hM hC hCopy hd
      obtain ⟨y,hy,hPlus⟩ := hAdd.add_exists_d hM hC ha ht
      exact ⟨y,hy,(hRows r y).mpr ⟨a,ha,hRa,Or.inl ⟨hFlag,d,hd,t,ht,hRd,hTimes,hPlus⟩⟩⟩
    · exact ⟨a,ha,(hRows r a).mpr ⟨a,ha,hRa,Or.inr ⟨hFlag,rfl⟩⟩⟩
  · intro r y z hy hz
    exact lifted_row_unique hM.1 hBase hInc hAdd hMul ((hRows r y).mp hy) ((hRows r z).mp hz)

theorem lifted_row_unflagged_iff {M : SetTheory.Structure.{u}} {w Base Inc Flags copy AddPairs Plus MulPairs Times r y : M.Domain}
    (hNot : ¬M.mem r Flags) :
    LiftedRow M w Base Inc Flags copy AddPairs Plus MulPairs Times r y ↔ M.mem y w ∧ MemPair M Base r y := by
  constructor
  · rintro ⟨a,ha,hRa,hCase⟩
    rcases hCase with ⟨hFlag,_⟩ | ⟨_,hy⟩
    · exact False.elim (hNot hFlag)
    · exact hy ▸ ⟨ha,hRa⟩
  · rintro ⟨hy,hRy⟩
    exact ⟨y,hy,hRy,Or.inr ⟨hNot,rfl⟩⟩

theorem lifted_column_exists_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {A : FiniteMatrix M.Domain} (hA : A.Valid M C.omega)
    {DiffPairs Diff AddPairs Plus MulPairs Times Forests Rows last maximal root copy source : M.Domain}
    (hDiff : DifferenceTable M C DiffPairs Diff) (hAdd : AdditionTable M C AddPairs Plus)
    (hMul : MultiplicationTable M C MulPairs Times) (hLast : M.mem last A.width) (hRoot : M.mem root A.width)
    (hSource : M.mem source A.width) (hCopy : M.mem copy C.omega) :
    ∃ Base Inc Flags V, Graph M Base A.height C.omega ∧ Graph M Inc A.height C.omega ∧ Graph M V A.height C.omega ∧
      (∀ r d, MemPair M Base r d ↔ MatrixEntry M A r source d) ∧
      (∀ r d, MemPair M Inc r d ↔ RowIncrement M C.omega A DiffPairs Diff last root r d) ∧
      (∀ r, M.mem r Flags ↔ M.mem r A.height ∧ Ascending M C A.width Forests Rows maximal root source r) ∧
      ∀ r d, MemPair M V r d ↔ LiftedRow M C.omega Base Inc Flags copy AddPairs Plus MulPairs Times r d := by
  obtain ⟨Base,hBase,hBaseRows⟩ := hA.column_values_d hM hSource
  obtain ⟨Inc,hInc,hIncRows⟩ := row_increment_graph_exists_d hM hA hDiff hLast hRoot
  obtain ⟨Flags,hFlags⟩ := ascending_rows_exists_d hM C A.height A.width Forests Rows maximal root source
  obtain ⟨V,hV,hRows⟩ := lifted_values_exists_d hM hC hBase hInc hCopy hAdd hMul
  exact ⟨Base,Inc,Flags,V,hBase,hInc,hV,hBaseRows,hIncRows,hFlags,hRows⟩

private def repeatedBlocksSchema : Project.UnarySchema 2 where
  body := Project.Formula.forallMem (.bound 2) (Project.Formula.forallMem (.bound 0)
    (.imp (mulFormula (.bound 3) (.bound 2) (.bound 1))
      (Project.Formula.existsMem (.bound 2) (Project.Formula.existsMem (.bound 4)
        (Project.Formula.existsMem (.bound 6) (.conj (mulFormula (.bound 6) (.bound 2) (.bound 0))
          (sumFormula (.bound 0) (.bound 1) (.bound 3))))))))
  freeClosed := by
    have hP := mulFormula_freeClosed (n := 5) (.bound 3) (.bound 2) (.bound 1) rfl rfl rfl
    have hB := mulFormula_freeClosed (n := 8) (.bound 6) (.bound 2) (.bound 0) rfl rfl rfl
    have hS := sumFormula_freeClosed (n := 8) (.bound 0) (.bound 1) (.bound 3) rfl rfl rfl
    simp [Project.Formula.forallMem,Project.Formula.existsMem,Definitional.Formula.FreeClosed,hP,hB,hS]

private theorem repeatedBlocksSchema_iff {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    (w L count : M.Domain) : Project.Formula.satisfies (((oneEnv w).push L).push count) repeatedBlocksSchema.body ↔
      ∀ total, M.mem total w → ∀ q, M.mem q total → KP1Y.Arithmetic.Product M L count total →
        ∃ copy, M.mem copy count ∧ ∃ slot, M.mem slot L ∧ ∃ offset, M.mem offset w ∧
          KP1Y.Arithmetic.Product M L copy offset ∧ KP1Y.Arithmetic.Sum M offset slot q := by
  simp only [repeatedBlocksSchema,Project.Formula.satisfies_forallMem_iff,Project.Formula.satisfies_imp_iff,
    Project.Formula.satisfies_existsMem_iff,Project.Formula.satisfies_conj_iff,mulFormula_iff hM,sumFormula_iff hM]
  rfl

/-- 每个内部重复块区间的地址都有 copy/slot 分解，使用对象归纳而不调用外部除法。 -/
theorem repeated_block_coverage_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {L count total q : M.Domain}
    (hL : M.mem L C.omega) (hCount : M.mem count C.omega)
    (hTotal : KP1Y.Arithmetic.Product M L count total) (hq : M.mem q total) :
    ∃ copy, M.mem copy count ∧ ∃ slot, M.mem slot L ∧ ∃ offset, M.mem offset C.omega ∧
      KP1Y.Arithmetic.Product M L copy offset ∧ KP1Y.Arithmetic.Sum M offset slot q := by
  have hw := omega_isOrdinal_d hM hC.omega
  have hAll := natural_induction_d hM repeatedBlocksSchema ((oneEnv C.omega).push L) hC.omega
    (fun zero hEmpty => (repeatedBlocksSchema_iff hM C.omega L zero).mpr (by
      intro total _ q hq hProd
      exact False.elim (hProd.zero_value_d hM hEmpty q hq)))
    (fun count hCount ih next hs => (repeatedBlocksSchema_iff hM C.omega L next).mpr (by
      intro total hTotalNat q hq hProd
      obtain ⟨old,hOldNat,hOld⟩ := natural_product_exists_d hM hC hL hCount
      have hSum := KP1Y.Arithmetic.product_successor_d hM hs hOld hProd
      classical
      by_cases hqOld : M.mem q old
      · obtain ⟨copy,hCopy,slot,hLocal,offset,hOffset,hTimes,hAdd⟩ :=
          (repeatedBlocksSchema_iff hM C.omega L count).mp ih old hOldNat q hqOld hOld
        exact ⟨copy,(hs copy).mpr (Or.inl hCopy),slot,hLocal,offset,hOffset,hTimes,hAdd⟩
      · have hqNat := hw.transitive total hTotalNat q hq
        have hOldLe : old=q ∨ M.mem old q := by
          rcases hw.wellOrder.linear.compare old hOldNat q hqNat with he | hlt | hgt
          · exact Or.inl (hM.1.eq_of_same_members old q he)
          · exact Or.inr hlt
          · exact False.elim (hqOld hgt)
        obtain ⟨slot,hLocalNat,hDiff⟩ := truncated_difference_exists_d hM hC hqNat hOldNat
        have hLocalSum := truncated_difference_add_inverse_d hM hC hDiff hOldLe
        have hLocal : M.mem slot L := by
          rcases hw.wellOrder.linear.compare slot hLocalNat L hL with he | hlt | hgt
          · have heq := hM.1.eq_of_same_members slot L he
            subst slot
            have hqTotal := KP1Y.Arithmetic.sum_unique_d hM hLocalSum hSum
            exact False.elim (SetTheory.KP.mem_irrefl_d (KP1Y.models_weakKP hM) total (hqTotal ▸ hq))
          · exact hlt
          · have hTotalQ := KP1Y.Arithmetic.sum_strict_right_d hM (hw.mem hOldNat) hSum hLocalSum hgt
            exact False.elim (SetTheory.KP.mem_irrefl_d (KP1Y.models_weakKP hM) q ((hw.mem hqNat).transitive total hTotalQ q hq))
        exact ⟨count,hs.predecessor_mem,slot,hLocal,old,hOldNat,hOld,hLocalSum⟩))
  exact (repeatedBlocksSchema_iff hM C.omega L count).mp (hAll count hCount) total
    (natural_product_closed_d hM hC hL hCount hTotal) q hq hTotal

def ShiftColumn (M : SetTheory.Structure.{u}) (AddPairs Plus root offset c x : M.Domain) : Prop :=
  (M.mem c root ∧ x=c) ∨ (¬M.mem c root ∧ AddAt M AddPairs Plus c offset x)

private def shiftColumnSchema : Project.Delta0BinarySchema 4 where
  body := .disj (.conj (.mem (.bound 1) (.bound 3)) (Project.Formula.extensionalEq (.bound 0) (.bound 1)))
    (.conj (.neg (.mem (.bound 1) (.bound 3))) (addAtFormula (.bound 5) (.bound 4) (.bound 1) (.bound 2) (.bound 0)))
  freeClosed := by
    simp [addAtFormula,codeFormula,pairFormula,memPairFormula,Project.Formula.existsMem,Project.Formula.forallMem,Definitional.Formula.FreeClosed]
  delta0 := .disj (.conj (.mem _ _) (.atom _ _ _)) (.conj (.neg (.mem _ _)) (addAtFormula_delta0 _ _ _ _ _))

private theorem shiftColumnSchema_iff {M : SetTheory.Structure.{u}} (he : Extensional M)
    (AddPairs Plus root offset c x : M.Domain) :
    Project.Formula.satisfies ((((((oneEnv AddPairs).push Plus).push root).push offset).push c).push x) shiftColumnSchema.body ↔
      ShiftColumn M AddPairs Plus root offset c x := by
  simp only [shiftColumnSchema,ShiftColumn,Project.Formula.satisfies_disj_iff,Project.Formula.satisfies_conj_iff,
    Project.Formula.satisfies_mem_iff,Project.Formula.satisfies_neg_iff,Project.Formula.satisfies_extensionalEq_iff_eq he,addAtFormula_iff he]
  rfl

/-- copyColumn 的真实有限图：好部固定，坏部平移 copy×L，且严格保序。 -/
theorem copy_column_map_exists_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {m root copy L AddPairs Plus MulPairs Times : M.Domain}
    (hm : M.mem m C.omega) (hRoot : M.mem root C.omega) (hCopy : M.mem copy C.omega) (hL : M.mem L C.omega)
    (hAdd : AdditionTable M C AddPairs Plus) (hMul : MultiplicationTable M C MulPairs Times) :
    ∃ offset J, M.mem offset C.omega ∧ MulAt M MulPairs Times copy L offset ∧ ColumnEmbedding M m C.omega J ∧
      ∀ c x, MemPair M J c x ↔ M.mem c m ∧ ShiftColumn M AddPairs Plus root offset c x := by
  obtain ⟨offset,hOffset,hTimes⟩ := hMul.mul_exists_d hM hC hCopy hL
  let env := (((oneEnv AddPairs).push Plus).push root).push offset
  have hw := omega_isOrdinal_d hM hC.omega
  obtain ⟨J,hSupport,hRaw⟩ := relation_comprehension_d hM shiftColumnSchema env m C.omega
  have hRows (c x : M.Domain) : MemPair M J c x ↔ M.mem c m ∧ ShiftColumn M AddPairs Plus root offset c x := by
    rw [hRaw c x,shiftColumnSchema_iff hM.1]
    refine ⟨fun h => ⟨h.1,h.2.2⟩,fun h => ⟨h.1,?_,h.2⟩⟩
    rcases h.2 with ⟨_,he⟩ | ⟨_,hPlus⟩
    · exact he ▸ hw.transitive m hm c h.1
    · exact (hPlus.bounds hM.1 hAdd).2.2
  have hGraph : Graph M J m C.omega := by
    refine ⟨hSupport,?_,?_⟩
    · intro c hc
      classical
      by_cases hGood : M.mem c root
      · exact ⟨c,hw.transitive m hm c hc,(hRows c c).mpr ⟨hc,Or.inl ⟨hGood,rfl⟩⟩⟩
      · obtain ⟨x,hx,hPlus⟩ := hAdd.add_exists_d hM hC (hw.transitive m hm c hc) hOffset
        exact ⟨x,hx,(hRows c x).mpr ⟨hc,Or.inr ⟨hGood,hPlus⟩⟩⟩
    · intro c x y hx hy
      rcases ((hRows c x).mp hx).2 with ⟨hGood,hx⟩ | ⟨hGood,hx⟩ <;>
        rcases ((hRows c y).mp hy).2 with ⟨hGood',hy⟩ | ⟨hGood',hy⟩
      · exact hx.trans hy.symm
      · exact False.elim (hGood' hGood)
      · exact False.elim (hGood hGood')
      · exact hAdd.add_unique hM.1 hx hy
  refine ⟨offset,J,hOffset,hTimes,⟨hGraph,?_⟩,hRows⟩
  intro a ha c hc hac x y hax hcy
  have haNat := hw.transitive m hm a ha
  have hcNat := hw.transitive m hm c hc
  rcases ((hRows a x).mp hax).2 with ⟨hGood,hx⟩ | ⟨hGood,hx⟩ <;>
    rcases ((hRows c y).mp hcy).2 with ⟨hGood',hy⟩ | ⟨hGood',hy⟩
  · exact hx.symm ▸ hy.symm ▸ hac
  · subst x
    exact KP1Y.Arithmetic.sum_base_subset_d hM (hw.mem hcNat) ((hAdd.add_iff_sum hM hcNat hOffset).mp hy) a hac
  · exact False.elim (hGood ((hw.mem hRoot).transitive c hGood' a hac))
  · exact natural_sum_strict_left_d hM hC haNat hcNat hOffset
      ((hAdd.add_iff_sum hM haNat hOffset).mp hx) ((hAdd.add_iff_sum hM hcNat hOffset).mp hy) hac

/-- 第0副本不提升任何条目，即使该行具有 ascending 标志。 -/
theorem lifted_row_zero_iff_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {height Base Inc Flags AddPairs Plus MulPairs Times r y : M.Domain}
    (hBase : Graph M Base height C.omega) (hInc : Graph M Inc height C.omega)
    (hAdd : AdditionTable M C AddPairs Plus) (hMul : MultiplicationTable M C MulPairs Times) :
    LiftedRow M C.omega Base Inc Flags C.zero AddPairs Plus MulPairs Times r y ↔ MemPair M Base r y := by
  classical
  constructor
  · rintro ⟨a,ha,hRa,hCase⟩
    rcases hCase with ⟨_,d,hd,t,_,_,hTimes,hPlus⟩ | ⟨_,he⟩
    · have ht0 := natural_product_zero_left_d hM hC hd ((hMul.mul_iff_product hM hC.zero_nat hd).mp hTimes)
      subst t
      have hya := ((hAdd.add_iff_sum hM ha hC.zero_nat).mp hPlus).zero_value_d hM hC.zero_empty
      exact hya.symm ▸ hRa
    · exact he ▸ hRa
  · intro hRy
    have hy := (hBase.bounds hM.1 hRy).2
    by_cases hFlag : M.mem r Flags
    · obtain ⟨d,hd,hRd⟩ := hInc.total r (hBase.bounds hM.1 hRy).1
      obtain ⟨t,_,hTimes⟩ := hMul.mul_exists_d hM hC hC.zero_nat hd
      have ht0 := natural_product_zero_left_d hM hC hd ((hMul.mul_iff_product hM hC.zero_nat hd).mp hTimes)
      subst t
      have hPlus := (hAdd.add_iff_sum hM hy hC.zero_nat).mpr (KP1Y.Arithmetic.sum_zero_d hM y hC.zero_empty)
      exact ⟨y,hy,hRy,Or.inl ⟨hFlag,d,hd,C.zero,hC.zero_nat,hRd,hTimes,hPlus⟩⟩
    · exact ⟨y,hy,hRy,Or.inr ⟨hFlag,rfl⟩⟩

def CopyPosition (M : SetTheory.Structure.{u}) (w AddPairs Plus MulPairs Times root L copy slot target : M.Domain) : Prop :=
  ∃ offset, M.mem offset w ∧ ∃ start, M.mem start w ∧ MulAt M MulPairs Times copy L offset ∧
    AddAt M AddPairs Plus root offset start ∧ AddAt M AddPairs Plus start slot target

def copyPositionFormula {d : Nat} (w AddPairs Plus MulPairs Times root L copy slot target : Project.Term d) : Project.Formula 1 d :=
  Project.Formula.existsMem w (Project.Formula.existsMem w.weaken
    (.conj (mulAtFormula MulPairs.weaken.weaken Times.weaken.weaken copy.weaken.weaken L.weaken.weaken (.bound 1))
      (.conj (addAtFormula AddPairs.weaken.weaken Plus.weaken.weaken root.weaken.weaken (.bound 1) (.bound 0))
        (addAtFormula AddPairs.weaken.weaken Plus.weaken.weaken (.bound 0) slot.weaken.weaken target.weaken.weaken))))

theorem copyPositionFormula_delta0 {d : Nat} (w AddPairs Plus MulPairs Times root L copy slot target : Project.Term d) :
    (copyPositionFormula w AddPairs Plus MulPairs Times root L copy slot target).IsDelta0 :=
  .existsMem _ (.existsMem _ (.conj (mulAtFormula_delta0 _ _ _ _ _)
    (.conj (addAtFormula_delta0 _ _ _ _ _) (addAtFormula_delta0 _ _ _ _ _))))

theorem copyPositionFormula_iff {M : SetTheory.Structure.{u}} (he : Extensional M) {d : Nat} (env : Env M d)
    (w AddPairs Plus MulPairs Times root L copy slot target : Project.Term d) :
    Project.Formula.satisfies env (copyPositionFormula w AddPairs Plus MulPairs Times root L copy slot target) ↔
      CopyPosition M (w.eval env) (AddPairs.eval env) (Plus.eval env) (MulPairs.eval env) (Times.eval env)
        (root.eval env) (L.eval env) (copy.eval env) (slot.eval env) (target.eval env) := by
  simp only [copyPositionFormula,CopyPosition,Project.Formula.satisfies_existsMem_iff,Project.Formula.satisfies_conj_iff,
    mulAtFormula_iff he,addAtFormula_iff he,Term.eval_weaken]
  rfl

theorem copy_position_exists_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {AddPairs Plus MulPairs Times root L copy slot : M.Domain}
    (hAdd : AdditionTable M C AddPairs Plus) (hMul : MultiplicationTable M C MulPairs Times)
    (hRoot : M.mem root C.omega) (hL : M.mem L C.omega) (hCopy : M.mem copy C.omega) (hSlot : M.mem slot C.omega) :
    ∃ target, M.mem target C.omega ∧ CopyPosition M C.omega AddPairs Plus MulPairs Times root L copy slot target := by
  obtain ⟨offset,hOffset,hProduct⟩ := hMul.mul_exists_d hM hC hCopy hL
  obtain ⟨start,hStart,hStartAdd⟩ := hAdd.add_exists_d hM hC hRoot hOffset
  obtain ⟨target,hTarget,hTargetAdd⟩ := hAdd.add_exists_d hM hC hStart hSlot
  exact ⟨target,hTarget,offset,hOffset,start,hStart,hProduct,hStartAdd,hTargetAdd⟩

theorem copy_position_unique {M : SetTheory.Structure.{u}} (he : Extensional M)
    {C : ExpressionData M.Domain} {AddPairs Plus MulPairs Times root L copy slot x y : M.Domain}
    (hAdd : AdditionTable M C AddPairs Plus) (hMul : MultiplicationTable M C MulPairs Times)
    (hx : CopyPosition M C.omega AddPairs Plus MulPairs Times root L copy slot x)
    (hy : CopyPosition M C.omega AddPairs Plus MulPairs Times root L copy slot y) : x=y := by
  obtain ⟨off,_,start,_,hMulX,hStartX,hX⟩ := hx
  obtain ⟨off',_,start',_,hMulY,hStartY,hY⟩ := hy
  have hOff := hMul.mul_unique he hMulX hMulY
  subst off'
  have hStart := hAdd.add_unique he hStartX hStartY
  subst start'
  exact hAdd.add_unique he hX hY

/-- 复制块覆盖整个坏部区间，乘法顺序为原实现的 copy×L。 -/
theorem copy_interval_coverage_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {AddPairs Plus MulPairs Times root L count total width target : M.Domain}
    (hAdd : AdditionTable M C AddPairs Plus) (hMul : MultiplicationTable M C MulPairs Times)
    (hRoot : M.mem root C.omega) (hL : M.mem L C.omega) (hCount : M.mem count C.omega)
    (hTotal : KP1Y.Arithmetic.Product M count L total) (hWidth : KP1Y.Arithmetic.Sum M root total width)
    (hTarget : M.mem target width) (hAfter : root=target ∨ M.mem root target) :
    ∃ copy, M.mem copy count ∧ ∃ slot, M.mem slot L ∧
      CopyPosition M C.omega AddPairs Plus MulPairs Times root L copy slot target := by
  have hw := omega_isOrdinal_d hM hC.omega
  have hTotalNat := natural_product_closed_d hM hC hCount hL hTotal
  have hWidthNat := natural_sum_closed_d hM hC.omega hRoot hTotalNat hWidth
  have hTargetNat := hw.transitive width hWidthNat target hTarget
  obtain ⟨q,hq,hDiff⟩ := truncated_difference_exists_d hM hC hTargetNat hRoot
  have hRootQ := truncated_difference_add_inverse_d hM hC hDiff hAfter
  have hqTotal : M.mem q total := by
    rcases hw.wellOrder.linear.compare q hq total hTotalNat with he | hlt | hgt
    · have heq := hM.1.eq_of_same_members q total he
      subst q
      have hEq := KP1Y.Arithmetic.sum_unique_d hM hRootQ hWidth
      exact False.elim (SetTheory.KP.mem_irrefl_d (KP1Y.models_weakKP hM) width (hEq ▸ hTarget))
    · exact hlt
    · have hRev := KP1Y.Arithmetic.sum_strict_right_d hM (hw.mem hRoot) hWidth hRootQ hgt
      exact False.elim (SetTheory.KP.mem_irrefl_d (KP1Y.models_weakKP hM) target ((hw.mem hTargetNat).transitive width hRev target hTarget))
  obtain ⟨copy,hCopy,slot,hSlot,offset,hOffset,hBlock,hBlockSum⟩ := repeated_block_coverage_d hM hC hL hCount
    (natural_product_comm_d hM hC hCount hL hTotal) hqTotal
  have hCopyNat := hw.transitive count hCount copy hCopy
  have hSlotNat := hw.transitive L hL slot hSlot
  have hBlock' := natural_product_comm_d hM hC hL hCopyNat hBlock
  obtain ⟨start,hStart,hStartAdd⟩ := hAdd.add_exists_d hM hC hRoot hOffset
  obtain ⟨y,_,hY⟩ := hAdd.add_exists_d hM hC hStart hSlotNat
  have hYEq := natural_sum_assoc_d hM hC hOffset hSlotNat
    ((hAdd.add_iff_sum hM hRoot hOffset).mp hStartAdd) ((hAdd.add_iff_sum hM hStart hSlotNat).mp hY) hBlockSum hRootQ
  subst y
  exact ⟨copy,hCopy,slot,hSlot,offset,hOffset,start,hStart,(hMul.mul_iff_product hM hCopyNat hL).mpr hBlock',hStartAdd,hY⟩

private theorem copy_position_relative_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {AddPairs Plus MulPairs Times root L copy slot target : M.Domain}
    (hAdd : AdditionTable M C AddPairs Plus) (hMul : MultiplicationTable M C MulPairs Times)
    (hRoot : M.mem root C.omega) (hL : M.mem L C.omega) (hCopy : M.mem copy C.omega) (hSlot : M.mem slot C.omega)
    (hPos : CopyPosition M C.omega AddPairs Plus MulPairs Times root L copy slot target) :
    ∃ q, M.mem q C.omega ∧ ∃ offset, M.mem offset C.omega ∧ KP1Y.Arithmetic.Product M copy L offset ∧
      KP1Y.Arithmetic.Sum M offset slot q ∧ KP1Y.Arithmetic.Sum M root q target := by
  obtain ⟨offset,hOffset,start,hStart,hTimes,hRootOff,hStartSlot⟩ := hPos
  obtain ⟨q,hq,hQ⟩ := natural_sum_exists_d hM hC.omega hOffset hSlot
  obtain ⟨t,_,hT⟩ := natural_sum_exists_d hM hC.omega hRoot hq
  have hTargetT := natural_sum_assoc_d hM hC hOffset hSlot
    ((hAdd.add_iff_sum hM hRoot hOffset).mp hRootOff) ((hAdd.add_iff_sum hM hStart hSlot).mp hStartSlot) hQ hT
  subst t
  exact ⟨q,hq,offset,hOffset,(hMul.mul_iff_product hM hCopy hL).mp hTimes,hQ,hT⟩

private theorem earlier_block_position_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {a b L offA offB slotA slotB qA qB : M.Domain}
    (ha : M.mem a C.omega) (hb : M.mem b C.omega) (hL : M.mem L C.omega) (hab : M.mem a b)
    (hSlot : M.mem slotA L) (hA : KP1Y.Arithmetic.Product M a L offA) (hB : KP1Y.Arithmetic.Product M b L offB)
    (hQA : KP1Y.Arithmetic.Sum M offA slotA qA) (hQB : KP1Y.Arithmetic.Sum M offB slotB qB) : M.mem qA qB := by
  have hw := omega_isOrdinal_d hM hC.omega
  obtain ⟨next,hNext,hNextNat⟩ := hC.omega.1.2 a ha
  obtain ⟨offNext,_,hProdNext⟩ := natural_product_exists_d hM hC hNextNat hL
  have hSum := natural_product_left_successor_d hM hC ha hL hNext hA hProdNext
  have hNextSub : M.MemberSubset next b := by
    intro x hx
    rcases (hNext x).mp hx with hx | he
    · exact (hw.mem hb).transitive a hab x hx
    · exact (hM.1.eq_of_same_members x a he) ▸ hab
  have hProductSub := natural_product_mono_left_d hM hC hNextNat hb hL hProdNext hB hNextSub
  have hQAOff := KP1Y.Arithmetic.sum_strict_right_d hM (hA.isOrdinal_d hM) hQA hSum hSlot
  exact KP1Y.Arithmetic.sum_base_subset_d hM (hB.isOrdinal_d hM) hQB qA (hProductSub qA hQAOff)

theorem copy_position_bounded_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {AddPairs Plus MulPairs Times root L count total width copy slot target : M.Domain}
    (hAdd : AdditionTable M C AddPairs Plus) (hMul : MultiplicationTable M C MulPairs Times)
    (hRoot : M.mem root C.omega) (hL : M.mem L C.omega) (hCount : M.mem count C.omega)
    (hTotal : KP1Y.Arithmetic.Product M count L total) (hWidth : KP1Y.Arithmetic.Sum M root total width)
    (hCopy : M.mem copy count) (hSlot : M.mem slot L)
    (hPos : CopyPosition M C.omega AddPairs Plus MulPairs Times root L copy slot target) : M.mem target width := by
  have hw := omega_isOrdinal_d hM hC.omega
  have hCopyNat := hw.transitive count hCount copy hCopy
  have hSlotNat := hw.transitive L hL slot hSlot
  obtain ⟨q,_,offset,_,hOffset,hQ,hRootQ⟩ := copy_position_relative_d hM hC hAdd hMul hRoot hL hCopyNat hSlotNat hPos
  have hqTotal := earlier_block_position_d hM hC hCopyNat hCount hL hCopy hSlot hOffset hTotal hQ
    (KP1Y.Arithmetic.sum_zero_d hM total hC.zero_empty)
  exact KP1Y.Arithmetic.sum_strict_right_d hM (hw.mem hRoot) hRootQ hWidth hqTotal

theorem copy_position_injective_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {AddPairs Plus MulPairs Times root L copy copy' slot slot' target : M.Domain}
    (hAdd : AdditionTable M C AddPairs Plus) (hMul : MultiplicationTable M C MulPairs Times)
    (hRoot : M.mem root C.omega) (hL : M.mem L C.omega) (hCopy : M.mem copy C.omega) (hCopy' : M.mem copy' C.omega)
    (hSlot : M.mem slot L) (hSlot' : M.mem slot' L)
    (hPos : CopyPosition M C.omega AddPairs Plus MulPairs Times root L copy slot target)
    (hPos' : CopyPosition M C.omega AddPairs Plus MulPairs Times root L copy' slot' target) : copy=copy' ∧ slot=slot' := by
  have hw := omega_isOrdinal_d hM hC.omega
  have hSlotNat := hw.transitive L hL slot hSlot
  have hSlotNat' := hw.transitive L hL slot' hSlot'
  obtain ⟨q,hq,offset,hOffset,hProduct,hSum,hRootQ⟩ := copy_position_relative_d hM hC hAdd hMul hRoot hL hCopy hSlotNat hPos
  obtain ⟨q',hq',offset',hOffset',hProduct',hSum',hRootQ'⟩ := copy_position_relative_d hM hC hAdd hMul hRoot hL hCopy' hSlotNat' hPos'
  have hqq' := natural_sum_cancel_left_d hM hC hRoot hq hq' hRootQ hRootQ'
  subst q'
  rcases hw.wellOrder.linear.compare copy hCopy copy' hCopy' with he | hLess | hGreater
  · have hCopies := hM.1.eq_of_same_members copy copy' he
    subst copy'
    have hOffsets := KP1Y.Arithmetic.product_unique_d hM hProduct hProduct'
    subst offset'
    exact ⟨rfl,natural_sum_cancel_left_d hM hC hOffset hSlotNat hSlotNat' hSum hSum'⟩
  · exact False.elim (SetTheory.KP.mem_irrefl_d (KP1Y.models_weakKP hM) q
      (earlier_block_position_d hM hC hCopy hCopy' hL hLess hSlot hProduct hProduct' hSum hSum'))
  · exact False.elim (SetTheory.KP.mem_irrefl_d (KP1Y.models_weakKP hM) q
      (earlier_block_position_d hM hC hCopy' hCopy hL hGreater hSlot' hProduct' hProduct hSum' hSum))

structure MatrixArithmetic (α : Type u) where
  addPairs : α
  plus : α
  mulPairs : α
  times : α
  diffPairs : α
  difference : α

def MatrixArithmetic.map {α : Type u} {β : Type v} (T : MatrixArithmetic α) (f : α → β) : MatrixArithmetic β :=
  ⟨f T.addPairs,f T.plus,f T.mulPairs,f T.times,f T.diffPairs,f T.difference⟩

def MatrixArithmetic.eval {M : SetTheory.Structure.{u}} {d : Nat} (T : MatrixArithmetic (Project.Term d)) (env : Env M d) : MatrixArithmetic M.Domain :=
  T.map (fun t => t.eval env)

def MatrixArithmetic.weaken {d : Nat} (T : MatrixArithmetic (Project.Term d)) : MatrixArithmetic (Project.Term (d+1)) := T.map (fun t => t.weaken)

theorem MatrixArithmetic.eval_weaken {M : SetTheory.Structure.{u}} {d : Nat}
    (T : MatrixArithmetic (Project.Term d)) (env : Env M d) (x : M.Domain) : T.weaken.eval (env.push x)=T.eval env := by
  cases T
  simp [MatrixArithmetic.map,MatrixArithmetic.eval,MatrixArithmetic.weaken,Term.eval_weaken]

structure MatrixArithmetic.Valid (M : SetTheory.Structure.{u}) (C : ExpressionData M.Domain) (T : MatrixArithmetic M.Domain) : Prop where
  add : AdditionTable M C T.addPairs T.plus
  mul : MultiplicationTable M C T.mulPairs T.times
  diff : DifferenceTable M C T.diffPairs T.difference

theorem matrix_arithmetic_exists_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) : ∃ T, MatrixArithmetic.Valid M C T := by
  obtain ⟨AP,Plus,hAdd⟩ := addition_table_exists_d hM hC
  obtain ⟨MP,Times,hMul⟩ := multiplication_table_exists_d hM hC
  obtain ⟨DP,Diff,hDiff⟩ := difference_table_exists_d hM hC
  exact ⟨⟨AP,Plus,MP,Times,DP,Diff⟩,hAdd,hMul,hDiff⟩

def rowIncrementFormula {d : Nat} (w : Project.Term d) (A : FiniteMatrix (Project.Term d))
    (Pairs Diff last root r value : Project.Term d) : Project.Formula 1 d :=
  Project.Formula.existsMem w (Project.Formula.existsMem w.weaken (Project.Formula.existsMem Pairs.weaken.weaken
    (.conj (codeFormula (.bound 0) (.bound 2) (.bound 1))
      (.conj (matrixEntryFormula A.weaken.weaken.weaken r.weaken.weaken.weaken last.weaken.weaken.weaken (.bound 2))
        (.conj (matrixEntryFormula A.weaken.weaken.weaken r.weaken.weaken.weaken root.weaken.weaken.weaken (.bound 1))
          (memPairFormula Diff.weaken.weaken.weaken (.bound 0) value.weaken.weaken.weaken))))))

theorem rowIncrementFormula_delta0 {d : Nat} (w : Project.Term d) (A : FiniteMatrix (Project.Term d))
    (Pairs Diff last root r value : Project.Term d) : (rowIncrementFormula w A Pairs Diff last root r value).IsDelta0 :=
  .existsMem _ (.existsMem _ (.existsMem _ (.conj (codeFormula_delta0 _ _ _)
    (.conj (matrixEntryFormula_delta0 _ _ _ _) (.conj (matrixEntryFormula_delta0 _ _ _ _) (memPairFormula_delta0 _ _ _))))))

theorem rowIncrementFormula_iff {M : SetTheory.Structure.{u}} (he : Extensional M) {d : Nat} (env : Env M d)
    (w : Project.Term d) (A : FiniteMatrix (Project.Term d)) (Pairs Diff last root r value : Project.Term d) :
    Project.Formula.satisfies env (rowIncrementFormula w A Pairs Diff last root r value) ↔
      RowIncrement M (w.eval env) (A.eval env) (Pairs.eval env) (Diff.eval env) (last.eval env) (root.eval env) (r.eval env) (value.eval env) := by
  simp only [rowIncrementFormula,RowIncrement,Project.Formula.satisfies_existsMem_iff,Project.Formula.satisfies_conj_iff,
    codeFormula_iff he,matrixEntryFormula_iff he,memPairFormula_iff he,FiniteMatrix.eval_weaken,Term.eval_weaken]
  rfl

def LiftedEntry (M : SetTheory.Structure.{u}) (C : ExpressionData M.Domain) (A : FiniteMatrix M.Domain)
    (T : MatrixArithmetic M.Domain) (Forests Rows last maximal root copy source r y : M.Domain) : Prop :=
  ∃ a, M.mem a C.omega ∧ MatrixEntry M A r source a ∧
    ((Ascending M C A.width Forests Rows maximal root source r ∧ ∃ d, M.mem d C.omega ∧ ∃ t, M.mem t C.omega ∧
      RowIncrement M C.omega A T.diffPairs T.difference last root r d ∧ MulAt M T.mulPairs T.times copy d t ∧ AddAt M T.addPairs T.plus a t y) ∨
      (¬Ascending M C A.width Forests Rows maximal root source r ∧ y=a))

theorem lifted_entry_exists_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {A : FiniteMatrix M.Domain} (hA : A.Valid M C.omega)
    {T : MatrixArithmetic M.Domain} (hT : T.Valid M C) {Forests Rows last maximal root copy source r : M.Domain}
    (hLast : M.mem last A.width) (hRoot : M.mem root A.width) (hCopy : M.mem copy C.omega)
    (hSource : M.mem source A.width) (hr : M.mem r A.height) :
    ∃ y, M.mem y C.omega ∧ LiftedEntry M C A T Forests Rows last maximal root copy source r y := by
  obtain ⟨a,ha,hAEntry⟩ := hA.entry_total_d hM hr hSource
  classical
  by_cases hFlag : Ascending M C A.width Forests Rows maximal root source r
  · obtain ⟨Inc,hInc,hIncRows⟩ := row_increment_graph_exists_d hM hA hT.diff hLast hRoot
    obtain ⟨d,hd,hRd⟩ := hInc.total r hr
    obtain ⟨t,ht,hTimes⟩ := hT.mul.mul_exists_d hM hC hCopy hd
    obtain ⟨y,hy,hPlus⟩ := hT.add.add_exists_d hM hC ha ht
    exact ⟨y,hy,a,ha,hAEntry,Or.inl ⟨hFlag,d,hd,t,ht,(hIncRows r d).mp hRd,hTimes,hPlus⟩⟩
  · exact ⟨a,ha,a,ha,hAEntry,Or.inr ⟨hFlag,rfl⟩⟩

theorem lifted_entry_unique_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} {A : FiniteMatrix M.Domain} (hA : A.Valid M C.omega)
    {T : MatrixArithmetic M.Domain} (hT : T.Valid M C) {Forests Rows last maximal root copy source r y z : M.Domain}
    (hy : LiftedEntry M C A T Forests Rows last maximal root copy source r y)
    (hz : LiftedEntry M C A T Forests Rows last maximal root copy source r z) : y=z := by
  obtain ⟨a,_,hRa,hY⟩ := hy
  obtain ⟨b,_,hRb,hZ⟩ := hz
  have hab := hA.entry_unique hM.1 hRa hRb
  subst b
  rcases hY with ⟨hFlag,d,_,t,_,hRd,hMulD,hAddY⟩ | ⟨hFlag,hY⟩ <;>
    rcases hZ with ⟨hFlag',e,_,u,_,hRe,hMulE,hAddZ⟩ | ⟨hFlag',hZ⟩
  · have hde := row_increment_unique_d hM hA hT.diff hRd hRe
    subst e
    have htu := hT.mul.mul_unique hM.1 hMulD hMulE
    subst u
    exact hT.add.add_unique hM.1 hAddY hAddZ
  · exact False.elim (hFlag' hFlag)
  · exact False.elim (hFlag hFlag')
  · exact hY.trans hZ.symm

def liftedEntryFormula {d : Nat} (C : ExpressionData (Project.Term d)) (A : FiniteMatrix (Project.Term d))
    (T : MatrixArithmetic (Project.Term d)) (Forests Rows last maximal root copy source r y : Project.Term d) : Project.Formula 1 d :=
  Project.Formula.existsMem C.omega (.conj (matrixEntryFormula A.weaken r.weaken source.weaken (.bound 0))
    (.disj (.conj (ascendingFormula C.weaken A.width.weaken Forests.weaken Rows.weaken maximal.weaken root.weaken source.weaken r.weaken)
      (Project.Formula.existsMem C.omega.weaken (Project.Formula.existsMem C.omega.weaken.weaken
        (.conj (rowIncrementFormula C.omega.weaken.weaken.weaken A.weaken.weaken.weaken
          T.diffPairs.weaken.weaken.weaken T.difference.weaken.weaken.weaken last.weaken.weaken.weaken root.weaken.weaken.weaken r.weaken.weaken.weaken (.bound 1))
          (.conj (mulAtFormula T.mulPairs.weaken.weaken.weaken T.times.weaken.weaken.weaken copy.weaken.weaken.weaken (.bound 1) (.bound 0))
            (addAtFormula T.addPairs.weaken.weaken.weaken T.plus.weaken.weaken.weaken (.bound 2) (.bound 0) y.weaken.weaken.weaken))))))
      (.conj (.neg (ascendingFormula C.weaken A.width.weaken Forests.weaken Rows.weaken maximal.weaken root.weaken source.weaken r.weaken))
        (Project.Formula.extensionalEq y.weaken (.bound 0)))))

theorem liftedEntryFormula_delta0 {d : Nat} (C : ExpressionData (Project.Term d)) (A : FiniteMatrix (Project.Term d))
    (T : MatrixArithmetic (Project.Term d)) (Forests Rows last maximal root copy source r y : Project.Term d) :
    (liftedEntryFormula C A T Forests Rows last maximal root copy source r y).IsDelta0 :=
  .existsMem _ (.conj (matrixEntryFormula_delta0 _ _ _ _) (.disj (.conj (ascendingFormula_delta0 _ _ _ _ _ _ _ _)
    (.existsMem _ (.existsMem _ (.conj (rowIncrementFormula_delta0 _ _ _ _ _ _ _ _)
      (.conj (mulAtFormula_delta0 _ _ _ _ _) (addAtFormula_delta0 _ _ _ _ _))))))
    (.conj (.neg (ascendingFormula_delta0 _ _ _ _ _ _ _ _)) (.atom _ _ _))))

theorem liftedEntryFormula_iff {M : SetTheory.Structure.{u}} (he : Extensional M) {d : Nat} (env : Env M d)
    (C : ExpressionData (Project.Term d)) (A : FiniteMatrix (Project.Term d)) (T : MatrixArithmetic (Project.Term d))
    (Forests Rows last maximal root copy source r y : Project.Term d) :
    Project.Formula.satisfies env (liftedEntryFormula C A T Forests Rows last maximal root copy source r y) ↔
      LiftedEntry M (C.eval env) (A.eval env) (T.eval env) (Forests.eval env) (Rows.eval env) (last.eval env)
        (maximal.eval env) (root.eval env) (copy.eval env) (source.eval env) (r.eval env) (y.eval env) := by
  simp only [liftedEntryFormula,LiftedEntry,Project.Formula.satisfies_existsMem_iff,Project.Formula.satisfies_conj_iff,
    Project.Formula.satisfies_disj_iff,Project.Formula.satisfies_neg_iff,Project.Formula.satisfies_extensionalEq_iff_eq he,
    matrixEntryFormula_iff he,ascendingFormula_iff he,rowIncrementFormula_iff he,mulAtFormula_iff he,addAtFormula_iff he,
    ExpressionData.eval_weaken,FiniteMatrix.eval_weaken,Term.eval_weaken]
  rfl

theorem LiftedEntry.value_natural {M : SetTheory.Structure.{u}} (he : Extensional M)
    {C : ExpressionData M.Domain} {A : FiniteMatrix M.Domain} {T : MatrixArithmetic M.Domain}
    (hT : T.Valid M C) {Forests Rows last maximal root copy source r y : M.Domain}
    (h : LiftedEntry M C A T Forests Rows last maximal root copy source r y) : M.mem y C.omega := by
  obtain ⟨a,ha,_,hCase⟩ := h
  rcases hCase with ⟨_,_,_,_,_,_,_,hPlus⟩ | ⟨_,hy⟩
  · exact (hPlus.bounds he hT.add).2.2
  · exact hy ▸ ha

def RawExpandedEntry (M : SetTheory.Structure.{u}) (C : ExpressionData M.Domain) (A : FiniteMatrix M.Domain)
    (T : MatrixArithmetic M.Domain) (Forests Rows last maximal root L count r c y : M.Domain) : Prop :=
  (M.mem c root ∧ MatrixEntry M A r c y) ∨ (¬M.mem c root ∧ ∃ copy, M.mem copy count ∧ ∃ slot, M.mem slot L ∧
    ∃ source, M.mem source A.width ∧ AddAt M T.addPairs T.plus root slot source ∧
      CopyPosition M C.omega T.addPairs T.plus T.mulPairs T.times root L copy slot c ∧
      LiftedEntry M C A T Forests Rows last maximal root copy source r y)

def rawExpandedEntryFormula {d : Nat} (C : ExpressionData (Project.Term d)) (A : FiniteMatrix (Project.Term d))
    (T : MatrixArithmetic (Project.Term d)) (Forests Rows last maximal root L count r c y : Project.Term d) : Project.Formula 1 d :=
  .disj (.conj (.mem c root) (matrixEntryFormula A r c y)) (.conj (.neg (.mem c root))
    (Project.Formula.existsMem count (Project.Formula.existsMem L.weaken (Project.Formula.existsMem A.width.weaken.weaken
      (.conj (addAtFormula T.addPairs.weaken.weaken.weaken T.plus.weaken.weaken.weaken root.weaken.weaken.weaken (.bound 1) (.bound 0))
        (.conj (copyPositionFormula C.omega.weaken.weaken.weaken T.addPairs.weaken.weaken.weaken T.plus.weaken.weaken.weaken
          T.mulPairs.weaken.weaken.weaken T.times.weaken.weaken.weaken root.weaken.weaken.weaken L.weaken.weaken.weaken (.bound 2) (.bound 1) c.weaken.weaken.weaken)
          (liftedEntryFormula C.weaken.weaken.weaken A.weaken.weaken.weaken T.weaken.weaken.weaken
            Forests.weaken.weaken.weaken Rows.weaken.weaken.weaken last.weaken.weaken.weaken maximal.weaken.weaken.weaken
            root.weaken.weaken.weaken (.bound 2) (.bound 0) r.weaken.weaken.weaken y.weaken.weaken.weaken)))))))

theorem rawExpandedEntryFormula_delta0 {d : Nat} (C : ExpressionData (Project.Term d)) (A : FiniteMatrix (Project.Term d))
    (T : MatrixArithmetic (Project.Term d)) (Forests Rows last maximal root L count r c y : Project.Term d) :
    (rawExpandedEntryFormula C A T Forests Rows last maximal root L count r c y).IsDelta0 :=
  .disj (.conj (.mem _ _) (matrixEntryFormula_delta0 _ _ _ _)) (.conj (.neg (.mem _ _))
    (.existsMem _ (.existsMem _ (.existsMem _ (.conj (addAtFormula_delta0 _ _ _ _ _)
      (.conj (copyPositionFormula_delta0 _ _ _ _ _ _ _ _ _ _) (liftedEntryFormula_delta0 _ _ _ _ _ _ _ _ _ _ _ _)))))))

theorem rawExpandedEntryFormula_iff {M : SetTheory.Structure.{u}} (he : Extensional M) {d : Nat} (env : Env M d)
    (C : ExpressionData (Project.Term d)) (A : FiniteMatrix (Project.Term d)) (T : MatrixArithmetic (Project.Term d))
    (Forests Rows last maximal root L count r c y : Project.Term d) :
    Project.Formula.satisfies env (rawExpandedEntryFormula C A T Forests Rows last maximal root L count r c y) ↔
      RawExpandedEntry M (C.eval env) (A.eval env) (T.eval env) (Forests.eval env) (Rows.eval env) (last.eval env)
        (maximal.eval env) (root.eval env) (L.eval env) (count.eval env) (r.eval env) (c.eval env) (y.eval env) := by
  simp only [rawExpandedEntryFormula,RawExpandedEntry,Project.Formula.satisfies_existsMem_iff,
    Project.Formula.satisfies_disj_iff,Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_mem_iff,
    Project.Formula.satisfies_neg_iff,matrixEntryFormula_iff he,addAtFormula_iff he,copyPositionFormula_iff he,
    liftedEntryFormula_iff he,ExpressionData.eval_weaken,FiniteMatrix.eval_weaken,MatrixArithmetic.eval_weaken,Term.eval_weaken]
  rfl

theorem raw_expanded_entry_unique_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {A : FiniteMatrix M.Domain} (hA : A.Valid M C.omega)
    {T : MatrixArithmetic M.Domain} (hT : T.Valid M C) {Forests Rows last maximal root L count r c y z : M.Domain}
    (hRoot : M.mem root C.omega) (hL : M.mem L C.omega) (hCount : M.mem count C.omega)
    (hy : RawExpandedEntry M C A T Forests Rows last maximal root L count r c y)
    (hz : RawExpandedEntry M C A T Forests Rows last maximal root L count r c z) : y=z := by
  rcases hy with ⟨hGood,hy⟩ | ⟨hGood,i,hi,j,hj,s,_,hSource,hPos,hLift⟩ <;>
    rcases hz with ⟨hGood',hz⟩ | ⟨hGood',i',hi',j',hj',s',_,hSource',hPos',hLift'⟩
  · exact hA.entry_unique hM.1 hy hz
  · exact False.elim (hGood' hGood)
  · exact False.elim (hGood hGood')
  · have hw := omega_isOrdinal_d hM hC.omega
    obtain ⟨hCopies,hSlots⟩ := copy_position_injective_d hM hC hT.add hT.mul hRoot hL
      (hw.transitive count hCount i hi) (hw.transitive count hCount i' hi') hj hj' hPos hPos'
    subst i'
    subst j'
    have hSources := hT.add.add_unique hM.1 hSource hSource'
    subst s'
    exact lifted_entry_unique_d hM hA hT hLift hLift'

theorem raw_expanded_entry_exists_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {A : FiniteMatrix M.Domain} (hA : A.Valid M C.omega)
    {T : MatrixArithmetic M.Domain} (hT : T.Valid M C) {Forests Rows last maximal root L count total width r c : M.Domain}
    (hLast : M.mem last A.width) (hRoot : M.mem root A.width) (hL : M.mem L C.omega) (hCount : M.mem count C.omega)
    (hRootL : KP1Y.Arithmetic.Sum M root L last) (hTotal : KP1Y.Arithmetic.Product M count L total)
    (hWidth : KP1Y.Arithmetic.Sum M root total width) (hr : M.mem r A.height) (hc : M.mem c width) :
    ∃ y, M.mem y C.omega ∧ RawExpandedEntry M C A T Forests Rows last maximal root L count r c y := by
  have hw := omega_isOrdinal_d hM hC.omega
  have hRootNat := hw.transitive A.width hA.width root hRoot
  classical
  by_cases hGood : M.mem c root
  · obtain ⟨y,hy,hEntry⟩ := hA.entry_total_d hM hr ((hw.mem hA.width).transitive root hRoot c hGood)
    exact ⟨y,hy,Or.inl ⟨hGood,hEntry⟩⟩
  · have hTotalNat := natural_product_closed_d hM hC hCount hL hTotal
    have hWidthNat := natural_sum_closed_d hM hC.omega hRootNat hTotalNat hWidth
    have hcNat := hw.transitive width hWidthNat c hc
    have hRootLe : root=c ∨ M.mem root c := by
      rcases hw.wellOrder.linear.compare root hRootNat c hcNat with he | hlt | hgt
      · exact Or.inl (hM.1.eq_of_same_members root c he)
      · exact Or.inr hlt
      · exact False.elim (hGood hgt)
    obtain ⟨copy,hCopy,slot,hSlot,hPos⟩ := copy_interval_coverage_d hM hC hT.add hT.mul hRootNat hL hCount hTotal hWidth hc hRootLe
    have hCopyNat := hw.transitive count hCount copy hCopy
    have hSlotNat := hw.transitive L hL slot hSlot
    obtain ⟨source,_,hSource⟩ := hT.add.add_exists_d hM hC hRootNat hSlotNat
    have hSourceLast := KP1Y.Arithmetic.sum_strict_right_d hM (hw.mem hRootNat)
      ((hT.add.add_iff_sum hM hRootNat hSlotNat).mp hSource) hRootL hSlot
    have hSourceBound := (hw.mem hA.width).transitive last hLast source hSourceLast
    obtain ⟨y,hy,hLift⟩ := lifted_entry_exists_d hM hC hA hT hLast hRoot hCopyNat hSourceBound hr
    exact ⟨y,hy,Or.inr ⟨hGood,copy,hCopy,slot,hSlot,source,hSourceBound,hSource,hPos,hLift⟩⟩

private def rawValueEnv {M : SetTheory.Structure.{u}} (C : ExpressionData M.Domain) (A : FiniteMatrix M.Domain)
    (T : MatrixArithmetic M.Domain) (Forests Rows last maximal root L count : M.Domain) : Env M 22 where
  bound i := match i.val with
    | 0 => C.omega | 1 => C.zero | 2 => C.one | 3 => C.sequences | 4 => C.expressions
    | 5 => A.height | 6 => A.width | 7 => A.cells | 8 => A.values
    | 9 => T.addPairs | 10 => T.plus | 11 => T.mulPairs | 12 => T.times | 13 => T.diffPairs | 14 => T.difference
    | 15 => Forests | 16 => Rows | 17 => last | 18 => maximal | 19 => root | 20 => L | _ => count
  free _ := C.zero

private def rawValueSchema : Project.Delta0BinarySchema 22 where
  body := Project.Formula.existsMem (.bound 7) (Project.Formula.existsMem (.bound 3)
    (.conj (codeFormula (.bound 3) (.bound 1) (.bound 0))
      (rawExpandedEntryFormula ⟨.bound 4,.bound 5,.bound 6,.bound 7,.bound 8⟩
        ⟨.bound 9,.bound 10,.bound 11,.bound 12⟩ ⟨.bound 13,.bound 14,.bound 15,.bound 16,.bound 17,.bound 18⟩
        (.bound 19) (.bound 20) (.bound 21) (.bound 22) (.bound 23) (.bound 24) (.bound 25) (.bound 1) (.bound 0) (.bound 2))))
  freeClosed := by
    simp [rawExpandedEntryFormula,liftedEntryFormula,rowIncrementFormula,ascendingFormula,ancestorFormula,parentPathFormula,
      ExpressionData.weaken,ExpressionData.map,FiniteMatrix.weaken,FiniteMatrix.map,MatrixArithmetic.weaken,MatrixArithmetic.map,
      matrixEntryFormula,copyPositionFormula,mulAtFormula,addAtFormula,successorFormula,graphFormula,
      memPairFormula,codeFormula,pairFormula,Project.Formula.forallMem,Project.Formula.existsMem,Definitional.Formula.FreeClosed]
  delta0 := .existsMem _ (.existsMem _ (.conj (codeFormula_delta0 _ _ _) (rawExpandedEntryFormula_delta0 _ _ _ _ _ _ _ _ _ _ _ _ _)))

private theorem rawValueSchema_iff {M : SetTheory.Structure.{u}} (he : Extensional M)
    (C : ExpressionData M.Domain) (A : FiniteMatrix M.Domain) (T : MatrixArithmetic M.Domain)
    (Forests Rows last maximal root L count key y : M.Domain) :
    Project.Formula.satisfies (((rawValueEnv C A T Forests Rows last maximal root L count).push key).push y) rawValueSchema.body ↔
      ∃ r, M.mem r A.height ∧ ∃ c, M.mem c C.omega ∧ Codes M key r c ∧ RawExpandedEntry M C A T Forests Rows last maximal root L count r c y := by
  simp only [rawValueSchema,Project.Formula.satisfies_existsMem_iff,Project.Formula.satisfies_conj_iff,
    codeFormula_iff he,rawExpandedEntryFormula_iff he]
  rfl

theorem raw_expansion_matrix_exists_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {A : FiniteMatrix M.Domain} (hA : A.Valid M C.omega)
    {T : MatrixArithmetic M.Domain} (hT : T.Valid M C) {Forests Rows last maximal root L count total width : M.Domain}
    (hLast : M.mem last A.width) (hRoot : M.mem root A.width) (hL : M.mem L C.omega) (hCount : M.mem count C.omega)
    (hRootL : KP1Y.Arithmetic.Sum M root L last) (hTotal : KP1Y.Arithmetic.Product M count L total)
    (hWidth : KP1Y.Arithmetic.Sum M root total width) :
    ∃ B, B.Valid M C.omega ∧ B.height=A.height ∧ B.width=width ∧ ∀ r c y,
      MatrixEntry M B r c y ↔ M.mem r A.height ∧ M.mem c width ∧ RawExpandedEntry M C A T Forests Rows last maximal root L count r c y := by
  have hw := omega_isOrdinal_d hM hC.omega
  have hRootNat := hw.transitive A.width hA.width root hRoot
  have hTotalNat := natural_product_closed_d hM hC hCount hL hTotal
  have hWidthNat := natural_sum_closed_d hM hC.omega hRootNat hTotalNat hWidth
  have hValueNat (r c y : M.Domain) (h : RawExpandedEntry M C A T Forests Rows last maximal root L count r c y) : M.mem y C.omega := by
    rcases h with ⟨_,hEntry⟩ | ⟨_,_,_,_,_,_,_,_,_,hLift⟩
    · exact (hEntry.bounds hM.1 hA).2.2
    · exact hLift.value_natural hM.1 hT
  obtain ⟨Cells,hCells⟩ := product_exists hM A.height width
  let env := rawValueEnv C A T Forests Rows last maximal root L count
  obtain ⟨Values,hSupport,hRaw⟩ := relation_comprehension_d hM rawValueSchema env Cells C.omega
  have hRows (key y : M.Domain) : MemPair M Values key y ↔ M.mem key Cells ∧ M.mem y C.omega ∧
      ∃ r, M.mem r A.height ∧ ∃ c, M.mem c C.omega ∧ Codes M key r c ∧ RawExpandedEntry M C A T Forests Rows last maximal root L count r c y :=
    (hRaw key y).trans (and_congr Iff.rfl (and_congr Iff.rfl (rawValueSchema_iff hM.1 C A T Forests Rows last maximal root L count key y)))
  have hValues : Graph M Values Cells C.omega := by
    refine ⟨hSupport,?_,?_⟩
    · intro key hk
      obtain ⟨r,hr,c,hc,hCode⟩ := (hCells key).mp hk
      obtain ⟨y,hy,hEntry⟩ := raw_expanded_entry_exists_d hM hC hA hT hLast hRoot hL hCount hRootL hTotal hWidth hr hc
      exact ⟨y,hy,(hRows key y).mpr ⟨hk,hy,r,hr,c,hw.transitive width hWidthNat c hc,hCode,hEntry⟩⟩
    · intro key y z hy hz
      obtain ⟨_,_,r,_,c,_,hCode,hY⟩ := (hRows key y).mp hy
      obtain ⟨_,_,r',_,c',_,hCode',hZ⟩ := (hRows key z).mp hz
      obtain ⟨hrr,hcc⟩ := codes_injective hM.1 hCode hCode'
      subst r'
      subst c'
      exact raw_expanded_entry_unique_d hM hC hA hT hRootNat hL hCount hY hZ
  let B : FiniteMatrix M.Domain := ⟨A.height,width,Cells,Values⟩
  have hB : B.Valid M C.omega := ⟨hA.height,hWidthNat,hCells,hValues⟩
  refine ⟨B,hB,rfl,rfl,?_⟩
  intro r c y
  constructor
  · intro hEntry
    have hBounds := hEntry.bounds hM.1 hB
    obtain ⟨key,_,hCode,hAt⟩ := hEntry
    obtain ⟨_,_,r',_,c',_,hCode',hY⟩ := (hRows key y).mp hAt
    obtain ⟨hrr,hcc⟩ := codes_injective hM.1 hCode hCode'
    subst r'
    subst c'
    exact ⟨hBounds.1,hBounds.2.1,hY⟩
  · rintro ⟨hr,hc,hEntry⟩
    obtain ⟨key,hCode⟩ := codes_total hM r c
    have hk := (hCells key).mpr ⟨r,hr,c,hc,hCode⟩
    exact ⟨key,hk,hCode,(hRows key y).mpr ⟨hk,hValueNat r c y hEntry,r,hr,c,hw.transitive width hWidthNat c hc,hCode,hEntry⟩⟩

structure RawMatrixExpansion (M : SetTheory.Structure.{u}) (C : ExpressionData M.Domain)
    (A : FiniteMatrix M.Domain) (T : MatrixArithmetic M.Domain)
    (Forests Rows last maximal root index count L total : M.Domain) (B : FiniteMatrix M.Domain) : Prop where
  copies : M.SuccessorOf count index
  difference : TruncatedDifference M C.omega C.zero last root L
  product : KP1Y.Arithmetic.Product M count L total
  width : KP1Y.Arithmetic.Sum M root total B.width
  matrix : B.Valid M C.omega
  height : B.height=A.height
  entries : ∀ r c y, MatrixEntry M B r c y ↔ M.mem r A.height ∧ M.mem c B.width ∧
    RawExpandedEntry M C A T Forests Rows last maximal root L count r c y

/-- 给定实际成功的最大父行搜索，真实构造未裁剪的整个非退化 BM4 展开。 -/
theorem matrix_expand_raw_context_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {A : FiniteMatrix M.Domain} (hA : A.Valid M C.omega)
    {T : MatrixArithmetic M.Domain} (hT : T.Valid M C) {Forests Rows Linear last maximal root index : M.Domain}
    (hRun : MatrixParentRun M C A.width A.height A.cells A.values Forests Rows Linear)
    (hContext : MatrixExpansionContext M C A Forests Rows last maximal root) (hIndex : M.mem index C.omega) :
    ∃ count L total B, RawMatrixExpansion M C A T Forests Rows last maximal root index count L total B := by
  have hw := omega_isOrdinal_d hM hC.omega
  have hLast := hContext.width_successor.predecessor_mem
  have hRootLast := hContext.root_lt_last hRun
  have hRoot := (hw.mem hA.width).transitive last hLast root hRootLast
  have hLastNat := hw.transitive A.width hA.width last hLast
  have hRootNat := hw.transitive A.width hA.width root hRoot
  obtain ⟨count,hCount,hCountNat⟩ := hC.omega.1.2 index hIndex
  obtain ⟨L,hL,hDiff⟩ := truncated_difference_exists_d hM hC hLastNat hRootNat
  have hRootL := truncated_difference_add_inverse_d hM hC hDiff (Or.inr hRootLast)
  obtain ⟨total,hTotalNat,hProduct⟩ := natural_product_exists_d hM hC hCountNat hL
  obtain ⟨width,_,hWidth⟩ := natural_sum_exists_d hM hC.omega hRootNat hTotalNat
  obtain ⟨B,hB,hHeight,hBWidth,hEntries⟩ := raw_expansion_matrix_exists_d hM hC hA hT hLast hRoot hL hCountNat hRootL hProduct hWidth
  exact ⟨count,L,total,B,hCount,hDiff,hProduct,hBWidth ▸ hWidth,hB,hHeight,
    fun r c y => (hEntries r c y).trans (and_congr Iff.rfl (and_congr (congrArg (M.mem c) hBWidth).to_iff.symm Iff.rfl))⟩

end KP1Y.OneYFinite
