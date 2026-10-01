import KP1Y.OneYInnerAbsolutenessExpansion
import KP1Y.InnerEnumeration

/-! M03：去掉V=L。外部不可数ν在同ω构造内模型L中仍不可数；在L中取其最小不可数κ≤ν、
统一枚举与文章数据，由L侧秩语句得到实际集合μ:E→κ。Y08的绝对性把同一个μ集合回传为外部
秩见证。回传的是集合见证，不是"L中无降链"的断言；κ在外部是否仍不可数无关。 -/
namespace KP1Y.OneYRank
open YesMetaZFC YesMetaZFC.SetTheory YesMetaZFC.SetTheory.Definitional
open KP1Y.Kuratowski KP1Y.Functions KP1Y.Naturals KP1Y.Bounded KP1Y.SetLanguage KP1Y.Classes KP1Y.Constructible
open KP1Y.Cardinal KP1Y.ReflectionModel KP1Y.OneYFinite KP1Y.OneYFinite.InnerAbsoluteness
universe u

/-- 唯一额外前提是L侧（实际为任意KPω模型）的秩语句`ArticleRankWitnessStatement`。 -/
theorem rank_transfer_d (hRank : ArticleRankWitnessStatement.{u}) {M : SetTheory.Structure.{u}}
    (hM : M.Models KP1Y.theory) {ω ν : M.Domain} (hω : M.IsOmega ω) (hν : UncountableOrdinal M ω ν) :
    ∃ (E : ExpressionData M.Domain) (T : MatrixArithmetic M.Domain) (χ μ : M.Domain),
      E.Valid M ∧ E.omega=ω ∧ T.Valid M E ∧ (χ=ν ∨ M.mem χ ν) ∧ RankWitness M E T χ μ := by
  obtain ⟨env,_,h⟩ := KP1Y.Constructible.canonical_environment_exists_d hM hω
  obtain ⟨w,κ,Keys,En,hw,hwω,hκ,hκν,_,hEnum⟩ := inner_least_uncountable_enumeration_d hM env h hω hν
  have hL := inner_models_kp_d hM env h.toFixedSyntax
  obtain ⟨C,hTop,hRω,_,_,hC⟩ := article_data_exists_d hL hwω hκ.1 hκ.2.1 hEnum
  have hκC : UncountableOrdinal (innerModel hM env h.toFixedSyntax) C.reflection.omega C.top := by
    rw [hTop,hRω]
    exact hκ
  obtain ⟨E0,T0,μ,hE0,hE0ω,hT0,hW⟩ := hRank _ hL C hC hκC
  refine ⟨E0.map Subtype.val,T0.map Subtype.val,C.top.val,μ.val,
    inner_expression_data_outer_valid_d hM env h.toFixedSyntax hE0,?_,
    inner_matrix_arithmetic_up_d hM env h.toFixedSyntax hE0 hT0,?_,
    inner_rank_witness_up_d hM env h.toFixedSyntax hE0 hT0 hW⟩
  · change E0.omega.val=ω
    rw [hE0ω,hRω]
    exact hw
  · rw [hTop]
    exact hκν

/-- M02应交付形状直接给出M03结论。 -/
theorem rank_transfer_of_descent_d (hDesc : MinimumRankDescentStatement.{u}) {M : SetTheory.Structure.{u}}
    (hM : M.Models KP1Y.theory) {ω ν : M.Domain} (hω : M.IsOmega ω) (hν : UncountableOrdinal M ω ν) :
    ∃ (E : ExpressionData M.Domain) (T : MatrixArithmetic M.Domain) (χ μ : M.Domain),
      E.Valid M ∧ E.omega=ω ∧ T.Valid M E ∧ (χ=ν ∨ M.mem χ ν) ∧ RankWitness M E T χ μ :=
  rank_transfer_d (article_rank_witness_of_descent hDesc) hM hω hν

/-- 附带实际外部EN图，供最终Δ₀句`rankWitnessFormula`读取。 -/
theorem rank_transfer_graph_d (hRank : ArticleRankWitnessStatement.{u}) {M : SetTheory.Structure.{u}}
    (hM : M.Models KP1Y.theory) {ω ν : M.Domain} (hω : M.IsOmega ω) (hν : UncountableOrdinal M ω ν) :
    ∃ (E : ExpressionData M.Domain) (T : MatrixArithmetic M.Domain) (Keys EN χ μ : M.Domain),
      E.Valid M ∧ E.omega=ω ∧ T.Valid M E ∧ Expansion.Graph M E T Keys EN ∧ (χ=ν ∨ M.mem χ ν) ∧
        RankWitness M E T χ μ := by
  obtain ⟨E,T,χ,μ,hE,hEω,hT,hχ,hW⟩ := rank_transfer_d hRank hM hω hν
  obtain ⟨Keys,EN,hG⟩ := Expansion.expansion_graph_exists_d hM hE hT
  exact ⟨E,T,Keys,EN,χ,μ,hE,hEω,hT,hG,hχ,hW⟩

end KP1Y.OneYRank
