import KP1Y.OneYExpansion
import KP1Y.OneYMinimumRank

/-! 共享的实际秩见证语句。χ是序数，μ是实际函数图E→χ，μ(∅)=0，且对每个非空s∈E、
每个内部N∈ω的实际展开E_N(s)，μ值严格下降。展开关系就是`Expansion.Expands`；
N与全部长度均取模型内部ω。给定实际EN图参数时，整句为字面Δ₀公式。 -/
namespace KP1Y.OneYRank
open YesMetaZFC YesMetaZFC.SetTheory YesMetaZFC.SetTheory.Definitional
open KP1Y.Kuratowski KP1Y.Functions KP1Y.Naturals KP1Y.Bounded KP1Y.Cardinal
open KP1Y.ReflectionModel KP1Y.OneYFinite
universe u

/-- 实际展开严格下降：s非空、N∈ω、t=E_N(s)时μ(t)∈μ(s)。 -/
def RankDescends (M : SetTheory.Structure.{u}) (E : ExpressionData M.Domain) (T : MatrixArithmetic M.Domain)
    (μ : M.Domain) : Prop :=
  ∀ s, M.mem s E.expressions → s≠E.zero → ∀ N, M.mem N E.omega → ∀ t, Expansion.Expands M E T s N t →
    ∀ a b, MemPair M μ s a → MemPair M μ t b → M.mem b a

/-- 共享秩见证：被回传的是这个实际集合μ本身。 -/
structure RankWitness (M : SetTheory.Structure.{u}) (E : ExpressionData M.Domain) (T : MatrixArithmetic M.Domain)
    (χ μ : M.Domain) : Prop where
  ordinal : M.IsOrdinal χ
  graph : Graph M μ E.expressions χ
  empty : MemPair M μ E.zero E.zero
  descends : RankDescends M E T μ

theorem RankWitness.value_mem {M : SetTheory.Structure.{u}} (he : Extensional M) {E : ExpressionData M.Domain}
    {T : MatrixArithmetic M.Domain} {χ μ s a : M.Domain} (h : RankWitness M E T χ μ) (hAt : MemPair M μ s a) :
    M.mem a χ := (h.graph.bounds he hAt).2

theorem RankWitness.value_ordinal {M : SetTheory.Structure.{u}} (he : Extensional M) {E : ExpressionData M.Domain}
    {T : MatrixArithmetic M.Domain} {χ μ s a : M.Domain} (h : RankWitness M E T χ μ) (hAt : MemPair M μ s a) :
    M.IsOrdinal a := h.ordinal.mem (h.value_mem he hAt)

/-- EN图参数下的Δ₀下降子句；Keys=E×ω，EN为实际全局展开图。 -/
def rankDescentFormula {n : Nat} (E : ExpressionData (Project.Term n)) (Keys EN χ μ : Project.Term n) : Project.Formula 1 n :=
  Project.Formula.forallMem E.expressions
    (.imp (.neg (Project.Formula.extensionalEq (.bound 0) E.zero.weaken))
      (Project.Formula.forallMem E.omega.weaken
        (Project.Formula.forallMem Keys.weaken.weaken
          (.imp (codeFormula (.bound 0) (.bound 2) (.bound 1))
            (Project.Formula.forallMem E.expressions.weaken.weaken.weaken
              (.imp (memPairFormula EN.weaken.weaken.weaken.weaken (.bound 1) (.bound 0))
                (Project.Formula.forallMem χ.weaken.weaken.weaken.weaken
                  (Project.Formula.forallMem χ.weaken.weaken.weaken.weaken.weaken
                    (.imp (memPairFormula μ.weaken.weaken.weaken.weaken.weaken.weaken (.bound 5) (.bound 1))
                      (.imp (memPairFormula μ.weaken.weaken.weaken.weaken.weaken.weaken (.bound 2) (.bound 0))
                        (.mem (.bound 0) (.bound 1))))))))))))

def rankWitnessFormula {n : Nat} (E : ExpressionData (Project.Term n)) (Keys EN χ μ : Project.Term n) : Project.Formula 1 n :=
  .conj (ordinalFormula χ) (.conj (graphFormula μ E.expressions χ)
    (.conj (memPairFormula μ E.zero E.zero) (rankDescentFormula E Keys EN χ μ)))

theorem rankDescentFormula_delta0 {n : Nat} (E : ExpressionData (Project.Term n)) (Keys EN χ μ : Project.Term n) :
    (rankDescentFormula E Keys EN χ μ).IsDelta0 :=
  .forallMem _ (.imp (.neg (.atom _ _ _)) (.forallMem _ (.forallMem _ (.imp (codeFormula_delta0 _ _ _)
    (.forallMem _ (.imp (memPairFormula_delta0 _ _ _) (.forallMem _ (.forallMem _
      (.imp (memPairFormula_delta0 _ _ _) (.imp (memPairFormula_delta0 _ _ _) (.mem _ _)))))))))))

theorem rankWitnessFormula_delta0 {n : Nat} (E : ExpressionData (Project.Term n)) (Keys EN χ μ : Project.Term n) :
    (rankWitnessFormula E Keys EN χ μ).IsDelta0 :=
  .conj (ordinalFormula_delta0 _) (.conj (graphFormula_delta0 _ _ _)
    (.conj (memPairFormula_delta0 _ _ _) (rankDescentFormula_delta0 _ _ _ _ _)))

theorem rankWitnessFormula_freeClosed {n : Nat} {E : ExpressionData (Project.Term n)} (hE : E.Closed)
    (Keys EN χ μ : Project.Term n) (hKeys : Keys.freeSupport=[]) (hEN : EN.freeSupport=[])
    (hχ : χ.freeSupport=[]) (hμ : μ.freeSupport=[]) : (rankWitnessFormula E Keys EN χ μ).FreeClosed := by
  simp [rankWitnessFormula,rankDescentFormula,ordinalFormula,graphFormula,memPairFormula,codeFormula,pairFormula,
    Project.Formula.isTransitive,Project.Formula.forallMem,Project.Formula.existsMem,Definitional.Formula.FreeClosed,
    hE.omega,hE.zero,hE.expressions,hKeys,hEN,hχ,hμ]

/-- 语义读取：Graph给出Keys/EN的精确展开含义，μ图给出值的χ界。 -/
theorem rankDescent_graph_iff {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {E : ExpressionData M.Domain} (hE : E.Valid M) {T : MatrixArithmetic M.Domain} {Keys EN χ μ : M.Domain}
    (hG : Expansion.Graph M E T Keys EN) (hμ : Graph M μ E.expressions χ) :
    (∀ s, M.mem s E.expressions → ¬s=E.zero → ∀ N, M.mem N E.omega → ∀ key, M.mem key Keys → Codes M key s N →
      ∀ t, M.mem t E.expressions → MemPair M EN key t → ∀ a, M.mem a χ → ∀ b, M.mem b χ →
        MemPair M μ s a → MemPair M μ t b → M.mem b a) ↔ RankDescends M E T μ := by
  constructor
  · intro h s hs hne N hN t hExpand a b hsa htb
    obtain ⟨key,hCode⟩ := codes_total hM s N
    have hk : M.mem key Keys := (hG.keys key).mpr ⟨s,hs,N,hN,hCode⟩
    have hAt := (hG.at_iff hM.1 hE hCode).mpr hExpand
    exact h s hs hne N hN key hk hCode t (hG.graph.bounds hM.1 hAt).2 hAt a (hμ.bounds hM.1 hsa).2 b
      (hμ.bounds hM.1 htb).2 hsa htb
  · intro h s hs hne N hN key _ hCode t _ hAt a _ b _ hsa htb
    exact h s hs hne N hN t ((hG.at_iff hM.1 hE hCode).mp hAt) a b hsa htb

theorem rankDescentFormula_iff {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory) {n : Nat} (e : Env M n)
    (E : ExpressionData (Project.Term n)) (Keys EN χ μ : Project.Term n) (hE : (E.eval e).Valid M)
    {T : MatrixArithmetic M.Domain} (hG : Expansion.Graph M (E.eval e) T (Keys.eval e) (EN.eval e))
    (hμ : Graph M (μ.eval e) (E.eval e).expressions (χ.eval e)) :
    Project.Formula.satisfies e (rankDescentFormula E Keys EN χ μ) ↔ RankDescends M (E.eval e) T (μ.eval e) := by
  refine Iff.trans ?_ (rankDescent_graph_iff hM hE hG hμ)
  simp only [rankDescentFormula,Project.Formula.satisfies_forallMem_iff,Project.Formula.satisfies_imp_iff,
    Project.Formula.satisfies_neg_iff,Project.Formula.satisfies_extensionalEq_iff_eq hM.1,codeFormula_iff hM.1,
    memPairFormula_iff hM.1,Project.Formula.satisfies_mem_iff,Term.eval_weaken]
  rfl

theorem rankWitnessFormula_iff {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory) {n : Nat} (e : Env M n)
    (E : ExpressionData (Project.Term n)) (Keys EN χ μ : Project.Term n) (hE : (E.eval e).Valid M)
    {T : MatrixArithmetic M.Domain} (hG : Expansion.Graph M (E.eval e) T (Keys.eval e) (EN.eval e)) :
    Project.Formula.satisfies e (rankWitnessFormula E Keys EN χ μ) ↔ RankWitness M (E.eval e) T (χ.eval e) (μ.eval e) := by
  simp only [rankWitnessFormula,Project.Formula.satisfies_conj_iff,ordinalFormula_iff hM,graphFormula_iff hM.1,
    memPairFormula_iff hM.1]
  constructor
  · rintro ⟨hχ,hμ,hEmpty,hDesc⟩
    exact ⟨hχ,hμ,hEmpty,(rankDescentFormula_iff hM e E Keys EN χ μ hE hG hμ).mp hDesc⟩
  · rintro ⟨hχ,hμ,hEmpty,hDesc⟩
    exact ⟨hχ,hμ,hEmpty,(rankDescentFormula_iff hM e E Keys EN χ μ hE hG hμ).mpr hDesc⟩

/-- M02应交付的精确形状：任意KPω模型中，文章数据给出的实际最小秩μ对实际展开下降。 -/
def MinimumRankDescentStatement : Prop :=
  ∀ (M : SetTheory.Structure.{u}), M.Models KP1Y.theory → ∀ (C : ArticleData M.Domain) (E : ExpressionData M.Domain)
    (T : MatrixArithmetic M.Domain) (μ : M.Domain), C.Valid M → UncountableOrdinal M C.reflection.omega C.top →
      E.Valid M → E.omega=C.reflection.omega → T.Valid M E → MinimumRank M E T C μ → RankDescends M E T μ

/-- M03所消费的较弱存在形：任意KPω模型的有效文章数据给出top上的实际秩见证。 -/
def ArticleRankWitnessStatement : Prop :=
  ∀ (M : SetTheory.Structure.{u}), M.Models KP1Y.theory → ∀ (C : ArticleData M.Domain), C.Valid M →
    UncountableOrdinal M C.reflection.omega C.top →
      ∃ (E : ExpressionData M.Domain) (T : MatrixArithmetic M.Domain) (μ : M.Domain),
        E.Valid M ∧ E.omega=C.reflection.omega ∧ T.Valid M E ∧ RankWitness M E T C.top μ

/-- M02形状加上已证实际μ工厂即得存在形；此处不新增任何秩或下降前提。 -/
theorem article_rank_witness_of_descent (hDesc : MinimumRankDescentStatement.{u}) : ArticleRankWitnessStatement.{u} := by
  intro M hM C hC hκ
  obtain ⟨E,T,μ,hE,hOmega,hT,hμ,hEmpty,_⟩ := article_expression_rank_exists_d hM hC hκ
  exact ⟨E,T,μ,hE,hOmega,hT,⟨hC.top,hμ.graph,hEmpty,hDesc M hM C E T μ hC hκ hE hOmega hT hμ⟩⟩

end KP1Y.OneYRank
