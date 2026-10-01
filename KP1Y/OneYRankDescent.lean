import KP1Y.OneYRankDescentStatement
import KP1Y.OneYRankTransfer

/-! M02：由Lemma 3接口与实际最小秩μ得到μ对所有实际展开严格下降。空输出用μ(∅)=0且非空值>ω；
非空输出用Lemma 3给出的更小末标签表示与μ(t)的最小性。全部N为内部ω元素。 -/
namespace KP1Y.OneYRank
open YesMetaZFC YesMetaZFC.SetTheory YesMetaZFC.SetTheory.Definitional
open KP1Y.Kuratowski KP1Y.Functions KP1Y.Naturals KP1Y.Bounded KP1Y.Cardinal
open KP1Y.ReflectionModel KP1Y.OneYFinite KP1Y.OneYFinite.ExpressionDiagram
universe u

/-- 单模型版本：只用本模型中Lemma 3的实例。 -/
theorem MinimumRank.descends_of_copy_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ArticleData M.Domain} (hC : C.Valid M) {E : ExpressionData M.Domain} (hE : E.Valid M)
    (hOmega : E.omega=C.reflection.omega) {T : MatrixArithmetic M.Domain} {μ : M.Domain}
    (hμ : MinimumRank M E T C μ)
    (hCopy : ∀ s m A β, M.mem s E.expressions → s≠E.zero → ExpressionGraph M E T C.reflection s m A →
        M.mem β C.top → RealizesLast M C m A β →
        ∀ N, M.mem N E.omega → ∀ t, Expansion.Expands M E T s N t → t≠E.zero →
          ∀ m' A', ExpressionGraph M E T C.reflection t m' A' → ∃ b, M.mem b β ∧ RealizesLast M C m' A' b) :
    RankDescends M E T μ := by
  intro s hs hne N hN t hExp a b hsa htb
  by_cases ht : t=E.zero
  · subst ht
    have hb : b=E.zero := hμ.graph.unique E.zero b E.zero htb (hμ.empty_d hM hE hC)
    rw [hb]
    exact hμ.nonempty_positive_d hM hE hC hOmega.symm hsa hne
  · obtain ⟨m,_,A,_,hGraph,hMin⟩ := (hμ.rows s a).mp hsa
    obtain ⟨m',_,A',_,hGraph',hMin'⟩ := (hμ.rows t b).mp htb
    have haTop : M.mem a C.top := (hμ.graph.bounds hM.1 hsa).2
    obtain ⟨c,hca,hReal⟩ := hCopy s m A a hs hne hGraph haTop hMin.1 N hN t hExp ht m' A' hGraph'
    rcases hMin'.2 c (hReal.in_cap_d hM hC) hReal with hbc | hbc
    · rw [hbc]
      exact hca
    · exact (hC.top.mem haTop).transitive c hca b hbc

/-- M02：Lemma 3接口蕴含共享的最小秩下降语句。 -/
theorem minimum_rank_descent_of_copy_descent (h : CopyDescentStatement.{u}) : MinimumRankDescentStatement.{u} := by
  intro M hM C E T μ hC hκ hE hOmega hT hμ
  exact hμ.descends_of_copy_d hM hC hE hOmega (h M hM C E T hC hκ hE hOmega hT)

/-- M03只依赖Lemma 3接口。 -/
theorem rank_transfer_of_copy_descent_d (h : CopyDescentStatement.{u}) {M : SetTheory.Structure.{u}}
    (hM : M.Models KP1Y.theory) {ω ν : M.Domain} (hω : M.IsOmega ω) (hν : UncountableOrdinal M ω ν) :
    ∃ (E : ExpressionData M.Domain) (T : MatrixArithmetic M.Domain) (χ μ : M.Domain),
      E.Valid M ∧ E.omega=ω ∧ T.Valid M E ∧ (χ=ν ∨ M.mem χ ν) ∧ RankWitness M E T χ μ :=
  rank_transfer_of_descent_d (minimum_rank_descent_of_copy_descent h) hM hω hν

/-- 同上，附带实际外部EN图。 -/
theorem rank_transfer_graph_of_copy_descent_d (h : CopyDescentStatement.{u}) {M : SetTheory.Structure.{u}}
    (hM : M.Models KP1Y.theory) {ω ν : M.Domain} (hω : M.IsOmega ω) (hν : UncountableOrdinal M ω ν) :
    ∃ (E : ExpressionData M.Domain) (T : MatrixArithmetic M.Domain) (Keys EN χ μ : M.Domain),
      E.Valid M ∧ E.omega=ω ∧ T.Valid M E ∧ Expansion.Graph M E T Keys EN ∧ (χ=ν ∨ M.mem χ ν) ∧
        RankWitness M E T χ μ :=
  rank_transfer_graph_d (article_rank_witness_of_descent (minimum_rank_descent_of_copy_descent h)) hM hω hν

end KP1Y.OneYRank
