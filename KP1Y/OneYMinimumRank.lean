import KP1Y.OneYDiagramMinimumRank
import KP1Y.OneYExpressionDiagramGraph

/-! 全部合法表达式的实际最小表示秩函数。图形算法和逐图最小化均由已证工厂提供。 -/
namespace KP1Y.OneYRank
open YesMetaZFC YesMetaZFC.SetTheory YesMetaZFC.SetTheory.Definitional
open KP1Y.Kuratowski KP1Y.Functions KP1Y.Naturals KP1Y.Bounded KP1Y.Cardinal
open KP1Y.Reflection KP1Y.ReflectionModel KP1Y.OneYFinite KP1Y.OneYFinite.ExpressionDiagram
universe u

def ExpressionMinimum (M : SetTheory.Structure.{u}) (E : ExpressionData M.Domain) (T : MatrixArithmetic M.Domain)
    (C : ArticleData M.Domain) (s a : M.Domain) : Prop :=
  ∃ m, M.mem m E.omega ∧ ∃ A, M.mem A C.reflection.edgeLists ∧
    ExpressionGraph M E T C.reflection s m A ∧ DiagramMinimum M C m A a

theorem ExpressionMinimum.source_mem {M : SetTheory.Structure.{u}} {E : ExpressionData M.Domain} (hE : E.Valid M)
    {T : MatrixArithmetic M.Domain} {C : ArticleData M.Domain} {s a : M.Domain}
    (h : ExpressionMinimum M E T C s a) : M.mem s E.expressions := by
  obtain ⟨m,hm,_,_,hGraph,_⟩ := h
  exact (hE.expressions s).mpr ⟨m,hm,hGraph.1⟩

theorem ExpressionMinimum.unique_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {E : ExpressionData M.Domain} (hE : E.Valid M) {T : MatrixArithmetic M.Domain}
    {C : ArticleData M.Domain} (hC : C.Valid M) {s a b : M.Domain}
    (h : ExpressionMinimum M E T C s a) (h' : ExpressionMinimum M E T C s b) : a=b := by
  obtain ⟨m,_,A,_,hGraph,hMin⟩ := h
  obtain ⟨n,_,B,_,hGraph',hMin'⟩ := h'
  obtain ⟨hm,hA⟩ := hGraph.unique_d hM hE hGraph'
  subst n
  subst B
  exact hMin.unique_d hM hC hMin'

theorem ExpressionMinimum.in_top_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {E : ExpressionData M.Domain} {T : MatrixArithmetic M.Domain} {C : ArticleData M.Domain} (hC : C.Valid M)
    (hκ : UncountableOrdinal M C.reflection.omega C.top) {s a : M.Domain}
    (h : ExpressionMinimum M E T C s a) : M.mem a C.top := by
  obtain ⟨_,_,_,_,_,hMin⟩ := h
  exact hMin.in_top_d hM hC hκ

theorem expression_minimum_exists_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {E : ExpressionData M.Domain} (hE : E.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M E)
    {C : ArticleData M.Domain} (hC : C.Valid M) (hκ : UncountableOrdinal M C.reflection.omega C.top)
    (hOmega : C.reflection.omega=E.omega) {s : M.Domain} (hs : M.mem s E.expressions) :
    ∃ a, M.mem a C.top ∧ ExpressionMinimum M E T C s a := by
  obtain ⟨m,hm,hLegal⟩ := (hE.expressions s).mp hs
  obtain ⟨A,hA⟩ := expression_graph_exists_d hM hE hT C.reflection hLegal
  have hDiagram := hA.diagram_d hM hE hT hC.reflection hOmega
  obtain ⟨S,hS⟩ := article_structure_exists_d hM hC
  obtain ⟨a,ha,hMin⟩ := diagram_minimum_exists_d hM hC hS hκ hDiagram
  exact ⟨a,ha,m,hm,A,hDiagram.2.1,hA,hMin⟩

private def BoundedExpressionMinimum (M : SetTheory.Structure.{u}) (E : ExpressionData M.Domain)
    (C : ArticleData M.Domain) (GraphA s a : M.Domain) : Prop :=
  ∃ m, M.mem m E.omega ∧ ∃ A, M.mem A C.reflection.edgeLists ∧
    LegalAt M E.omega E.zero E.one s m ∧ MemPair M GraphA s A ∧ DiagramMinimum M C m A a

private def minimumEnv {M : SetTheory.Structure.{u}} (E : ExpressionData M.Domain)
    (C : ArticleData M.Domain) (GraphA : M.Domain) : Env M 28 :=
  ((((articleEnv C).push E.omega).push E.zero).push E.one).push GraphA

private abbrev rankArticle30 : ArticleData (Project.Term 30) :=
  articleTerms.weaken.weaken.weaken.weaken.weaken.weaken

private def minimumSchema : Project.Delta0BinarySchema 28 where
  body := Project.Formula.existsMem (.bound 5) (Project.Formula.existsMem rankArticle30.weaken.reflection.edgeLists
    (.conj (legalAtFormula (.bound 7) (.bound 6) (.bound 5) (.bound 3) (.bound 1))
      (.conj (memPairFormula (.bound 4) (.bound 3) (.bound 0))
        (diagramMinimumFormula rankArticle30.weaken.weaken (.bound 1) (.bound 0) (.bound 2)))))
  freeClosed := by
    have hC : rankArticle30.Closed := articleTerms_closed.weaken.weaken.weaken.weaken.weaken.weaken
    have hLegal := legalAtFormula_freeClosed (n := 32) (.bound 7) (.bound 6) (.bound 5) (.bound 3) (.bound 1) rfl rfl rfl rfl rfl
    have hMin := diagramMinimumFormula_freeClosed hC.weaken.weaken (.bound 1) (.bound 0) (.bound 2) rfl rfl rfl
    simp [Project.Formula.existsMem,Definitional.Formula.FreeClosed,memPairFormula,codeFormula,pairFormula,
      Project.Formula.forallMem,hC.weaken.reflection.edgeLists,hLegal,hMin]
  delta0 := .existsMem _ (.existsMem _ (.conj (legalAtFormula_delta0 _ _ _ _ _)
    (.conj (memPairFormula_delta0 _ _ _) (diagramMinimumFormula_delta0 _ _ _ _))))

private theorem minimumSchema_iff {M : SetTheory.Structure.{u}} (he : Extensional M)
    (E : ExpressionData M.Domain) (C : ArticleData M.Domain) (GraphA s a : M.Domain) :
    Project.Formula.satisfies (((minimumEnv E C GraphA).push s).push a) minimumSchema.body ↔
      BoundedExpressionMinimum M E C GraphA s a := by
  simp only [minimumSchema,BoundedExpressionMinimum,Project.Formula.satisfies_existsMem_iff,
    Project.Formula.satisfies_conj_iff,legalAtFormula_iff he,memPairFormula_iff he,diagramMinimumFormula_iff he,
    ArticleData.eval_weaken]
  rfl

structure MinimumRank (M : SetTheory.Structure.{u}) (E : ExpressionData M.Domain) (T : MatrixArithmetic M.Domain)
    (C : ArticleData M.Domain) (μ : M.Domain) : Prop where
  graph : Graph M μ E.expressions C.top
  rows : ∀ s a, MemPair M μ s a ↔ ExpressionMinimum M E T C s a

/-- 在实际规范图函数上以有界分离构造μ。该辅助入口的算法图前提由下方总工厂消除。 -/
theorem minimum_rank_from_graph_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {E : ExpressionData M.Domain} (hE : E.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M E)
    {C : ArticleData M.Domain} (hC : C.Valid M) (hκ : UncountableOrdinal M C.reflection.omega C.top)
    (hOmega : C.reflection.omega=E.omega) {GraphA : M.Domain}
    (hRows : ∀ s A, MemPair M GraphA s A ↔ ∃ m, M.mem m E.omega ∧ ExpressionGraph M E T C.reflection s m A) :
    ∃ μ, MinimumRank M E T C μ := by
  have hMeaning (s a : M.Domain) : BoundedExpressionMinimum M E C GraphA s a ↔ ExpressionMinimum M E T C s a := by
    constructor
    · rintro ⟨m,hm,A,hA,hLegal,hAt,hMin⟩
      obtain ⟨hGraph,_⟩ := expression_diagram_graph_width_d hM hE hT hC.reflection hOmega hRows hAt hLegal
      exact ⟨m,hm,A,hA,hGraph,hMin⟩
    · rintro ⟨m,hm,A,hA,hGraph,hMin⟩
      exact ⟨m,hm,A,hA,hGraph.1,(hRows s A).mpr ⟨m,hm,hGraph⟩,hMin⟩
  obtain ⟨μ,hSupport,hRaw⟩ := relation_comprehension_d hM minimumSchema (minimumEnv E C GraphA) E.expressions C.top
  have hμRows (s a : M.Domain) : MemPair M μ s a ↔ ExpressionMinimum M E T C s a := by
    rw [hRaw s a,minimumSchema_iff hM.1,hMeaning s a]
    exact ⟨fun h => h.2.2,fun h => ⟨h.source_mem hE,h.in_top_d hM hC hκ,h⟩⟩
  refine ⟨μ,⟨hSupport,?_,?_⟩,hμRows⟩
  · intro s hs
    obtain ⟨a,ha,hMin⟩ := expression_minimum_exists_d hM hE hT hC hκ hOmega hs
    exact ⟨a,ha,(hμRows s a).mpr hMin⟩
  · intro s a b hA hB
    exact ((hμRows s a).mp hA).unique_d hM hE hC ((hμRows s b).mp hB)

/-- 完整实际E→μ工厂：没有秩、逐表达式表示或算法总性假设。 -/
theorem minimum_rank_exists_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {E : ExpressionData M.Domain} (hE : E.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M E)
    {C : ArticleData M.Domain} (hC : C.Valid M) (hκ : UncountableOrdinal M C.reflection.omega C.top)
    (hOmega : C.reflection.omega=E.omega) : ∃ μ, MinimumRank M E T C μ := by
  obtain ⟨GraphA,_,hRows⟩ := expression_diagram_graph_exists_d hM hE hT hC.reflection hOmega
  exact minimum_rank_from_graph_d hM hE hT hC hκ hOmega hRows

theorem MinimumRank.unique {M : SetTheory.Structure.{u}} (he : Extensional M)
    {E : ExpressionData M.Domain} {T : MatrixArithmetic M.Domain} {C : ArticleData M.Domain} {μ ν : M.Domain}
    (hμ : MinimumRank M E T C μ) (hν : MinimumRank M E T C ν) : μ=ν :=
  hμ.graph.ext he hν.graph (fun s _ a => (hμ.rows s a).trans (hν.rows s a).symm)

theorem expression_article_zero_eq {M : SetTheory.Structure.{u}} (he : Extensional M)
    {E : ExpressionData M.Domain} (hE : E.Valid M) {C : ArticleData M.Domain} (hC : C.Valid M) : E.zero=C.numbers 0 :=
  he.eq_of_same_members E.zero (C.numbers 0) (fun x => iff_of_false (hE.zero_empty x) (hC.numerals.zero_empty x))

theorem legal_zero_length_iff_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {E : ExpressionData M.Domain} (hE : E.Valid M) {s m : M.Domain}
    (hLegal : LegalAt M E.omega E.zero E.one s m) : m=E.zero ↔ s=E.zero := by
  constructor
  · intro hm
    subst m
    exact hLegal.1.2.ext hM.1 (empty_legal_d hE).1.2 (fun i hi => False.elim (hE.zero_empty i hi))
  · intro hs
    subst s
    exact legal_length_unique hM.1 hLegal (empty_legal_d hE)

theorem ExpressionMinimum.empty_value_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {E : ExpressionData M.Domain} (hE : E.Valid M) {T : MatrixArithmetic M.Domain}
    {C : ArticleData M.Domain} (hC : C.Valid M) {a : M.Domain}
    (h : ExpressionMinimum M E T C E.zero a) : a=E.zero := by
  obtain ⟨m,_,_,_,hGraph,hMin⟩ := h
  have hm := legal_length_unique hM.1 hGraph.1 (empty_legal_d hE)
  exact (hMin.empty_value hC (hm.trans (expression_article_zero_eq hM.1 hE hC))).trans
    (expression_article_zero_eq hM.1 hE hC).symm

theorem MinimumRank.empty_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {E : ExpressionData M.Domain} (hE : E.Valid M) {T : MatrixArithmetic M.Domain}
    {C : ArticleData M.Domain} (hC : C.Valid M) {μ : M.Domain} (hμ : MinimumRank M E T C μ) :
    MemPair M μ E.zero E.zero := by
  obtain ⟨a,_,hAt⟩ := hμ.graph.total E.zero (empty_expression_d hE)
  exact ((hμ.rows E.zero a).mp hAt).empty_value_d hM hE hC ▸ hAt

theorem ExpressionMinimum.nonempty_above_omega_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {E : ExpressionData M.Domain} (hE : E.Valid M) {T : MatrixArithmetic M.Domain}
    {C : ArticleData M.Domain} (hC : C.Valid M) {s a : M.Domain}
    (h : ExpressionMinimum M E T C s a) (hs : s≠E.zero) : M.mem C.reflection.omega a := by
  obtain ⟨m,_,_,_,hGraph,hMin⟩ := h
  apply hMin.nonempty_above_omega_d hM hC
  intro hm
  have hm0 : m=E.zero := hm.trans (expression_article_zero_eq hM.1 hE hC).symm
  exact hs ((legal_zero_length_iff_d hM hE hGraph.1).mp hm0)

theorem MinimumRank.nonempty_positive_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {E : ExpressionData M.Domain} (hE : E.Valid M) {T : MatrixArithmetic M.Domain}
    {C : ArticleData M.Domain} (hC : C.Valid M) (hOmega : C.reflection.omega=E.omega)
    {μ s a : M.Domain} (hμ : MinimumRank M E T C μ) (hAt : MemPair M μ s a) (hs : s≠E.zero) : M.mem E.zero a := by
  have hAbove := ((hμ.rows s a).mp hAt).nonempty_above_omega_d hM hE hC hs
  exact (hC.top.mem (hμ.graph.bounds hM.1 hAt).2).transitive C.reflection.omega hAbove E.zero (hOmega.symm ▸ hE.zero_nat)

theorem MinimumRank.realized_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {E : ExpressionData M.Domain} {T : MatrixArithmetic M.Domain} {C : ArticleData M.Domain} (hC : C.Valid M)
    {μ s a : M.Domain} (hμ : MinimumRank M E T C μ) (hAt : MemPair M μ s a) :
    ∃ m A f, ExpressionGraph M E T C.reflection s m A ∧ M.mem f C.reflection.labels ∧
      Representation M C.reflection C.table m A f ∧ Below M C.reflection m f C.top ∧ LastValue M (C.numbers 0) m f a := by
  obtain ⟨m,_,A,_,hGraph,hMin⟩ := (hμ.rows s a).mp hAt
  obtain ⟨f,hf,hRep,hBelow,hLast⟩ := hMin.realized_below_top_d hM hC (hμ.graph.bounds hM.1 hAt).2
  exact ⟨m,A,f,hGraph,hf,hRep,hBelow,hLast⟩

theorem MinimumRank.le_representation_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {E : ExpressionData M.Domain} (hE : E.Valid M) {T : MatrixArithmetic M.Domain}
    {C : ArticleData M.Domain} (hC : C.Valid M) {μ s a m A f b : M.Domain}
    (hμ : MinimumRank M E T C μ) (hAt : MemPair M μ s a)
    (hGraph : ExpressionGraph M E T C.reflection s m A)
    (hRep : Representation M C.reflection C.table m A f) (hLast : LastValue M (C.numbers 0) m f b) :
    a=b ∨ M.mem a b := by
  obtain ⟨n,_,B,_,hGraph',hMin⟩ := (hμ.rows s a).mp hAt
  obtain ⟨hm,hA⟩ := hGraph'.unique_d hM hE hGraph
  subst n
  subst B
  exact hMin.le_representation_d hM hC hRep hLast

/-- 表达式集合、算术表、规范根图和μ全部实际构造，只保留本主线既有的R/κ数据。 -/
theorem article_expression_rank_exists_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ArticleData M.Domain} (hC : C.Valid M) (hκ : UncountableOrdinal M C.reflection.omega C.top) :
    ∃ (E : ExpressionData M.Domain) (T : MatrixArithmetic M.Domain) (μ : M.Domain),
      E.Valid M ∧ E.omega=C.reflection.omega ∧ T.Valid M E ∧ MinimumRank M E T C μ ∧
        MemPair M μ E.zero E.zero ∧ ∀ s a, MemPair M μ s a → s≠E.zero → M.mem E.zero a := by
  obtain ⟨E,hOmega,hE⟩ := expression_data_exists_d hM hC.numerals.omega
  obtain ⟨T,hT⟩ := matrix_arithmetic_exists_d hM hE
  obtain ⟨μ,hμ⟩ := minimum_rank_exists_d hM hE hT hC hκ hOmega.symm
  exact ⟨E,T,μ,hE,hOmega,hT,hμ,hμ.empty_d hM hE hC,
    fun _ _ hAt hNonempty => hμ.nonempty_positive_d hM hE hC hOmega.symm hAt hNonempty⟩

end KP1Y.OneYRank
