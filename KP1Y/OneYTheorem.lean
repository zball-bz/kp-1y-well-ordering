import KP1Y.OneYTheoremSentence
import KP1Y.Completeness

/-! M05：定理 1 闭句的模型层证明与真实 Hilbert `Derives` 封装。
模型层定理只消费两个显式前提：
* `RankTransferAt M`：每个不可数 ν 给出序数 χ≤ν 与实际 E,T 上的共享 `RankWitness`（M02+Y08+M03 的出口）；
* `OrderFactsAt M`：文稿 Lemma 9.1/§9 的有限数值事实（Y07a/Y07b 的出口）。
二者均为条件，尚未在此解除；本模块不声称定理 1 已完成。 -/
namespace KP1Y.OneYTheorem
open YesMetaZFC YesMetaZFC.SetTheory YesMetaZFC.SetTheory.Definitional
open KP1Y.Kuratowski KP1Y.Functions KP1Y.Naturals KP1Y.Bounded KP1Y.Cardinal
open KP1Y.OneYFinite KP1Y.OneYRank
universe u

/-- 秩回传出口：任意不可数 ν 上存在 χ≤ν 与实际秩见证。 -/
def RankTransferAt (M : SetTheory.Structure.{u}) : Prop :=
  ∀ (C : ExpressionData M.Domain) (T : MatrixArithmetic M.Domain) (ν : M.Domain),
    C.Valid M → T.Valid M C → UncountableOrdinal M C.omega ν →
      ∃ χ μ, RankWitness M C T χ μ ∧ (χ=ν ∨ M.mem χ ν)

/-- 有限数值事实出口。 -/
def OrderFactsAt (M : SetTheory.Structure.{u}) : Prop :=
  ∀ (C : ExpressionData M.Domain) (T : MatrixArithmetic M.Domain), C.Valid M → T.Valid M C → OrderFacts M C T

/-- 若某组有效 E,T 上有 χ≤ν 的秩见证，则由唯一性对每组有效 E,T 皆有。便于接入存在形回传结果。 -/
theorem rank_transfer_of_some_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    (h : ∀ w ν, M.IsOmega w → UncountableOrdinal M w ν →
      ∃ (C : ExpressionData M.Domain) (T : MatrixArithmetic M.Domain) (χ μ : M.Domain),
        C.Valid M ∧ T.Valid M C ∧ RankWitness M C T χ μ ∧ (χ=ν ∨ M.mem χ ν)) :
    RankTransferAt M := by
  intro C T ν hC hT hν
  obtain ⟨C',T',χ,μ,hC',hT',hW,hχ⟩ := h C.omega ν hC.omega hν
  have hCC := ExpressionData.Valid.unique hM.1 hC' hC
  subst C'
  have hTT := MatrixArithmetic.Valid.unique hM.1 hT' hT
  subst T'
  exact ⟨χ,μ,hW,hχ⟩

/-- 每组有效辅助集合上成立定理 1 的全部结论。 -/
theorem conclusion_clause_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {D : TheoremData M.Domain} (hD : D.Valid M) (hRank : RankTransferAt M) (hOrder : OrderFactsAt M) :
    ConclusionClause M D := by
  intro ν hν
  obtain ⟨χ,μ,hW,hχ⟩ := hRank D.expr D.arith ν hD.expr hD.arith hν
  have hF := hOrder D.expr D.arith hD.expr hD.arith
  exact ⟨⟨χ,μ,hW,hχ⟩,witness_wellFounded_clause_d hM hD hW,witness_termination_clause_d hM hD hW,
    desc_clause_d hM hD hW hF,gen_clause_d hM hD hW hF⟩

/-- 模型层主定理：两个出口前提给出闭句的完整语义。 -/
theorem main_semantic_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    (hRank : RankTransferAt M) (hOrder : OrderFactsAt M) : MainSemantic M :=
  ⟨theorem_data_exists_d hM,fun _ hD => conclusion_clause_d hM hD hRank hOrder⟩

/-- 完备性封装：任意模型的语义结论给出纯 ∈ 闭句的真实 Hilbert 推导。 -/
theorem main_derivable (h : ∀ M : SetTheory.Structure.{0}, M.Models KP1Y.theory → MainSemantic M) :
    KP1Y.Derives mainSentence := by
  apply KP1Y.derives_of_all_models
  intro M hM free
  exact (mainSentence_iff hM free).mpr (h M hM)

def RankTransferStatement : Prop := ∀ M : SetTheory.Structure.{0}, M.Models KP1Y.theory → RankTransferAt M

def OrderFactsStatement : Prop := ∀ M : SetTheory.Structure.{0}, M.Models KP1Y.theory → OrderFactsAt M

/-- 条件形式的最终推导；两个前提由 M03 与 Y07a/Y07b 解除后即为无条件 `Derives`。 -/
theorem main_derivable_of (hRank : RankTransferStatement) (hOrder : OrderFactsStatement) :
    KP1Y.Derives mainSentence :=
  main_derivable (fun M hM => main_semantic_d hM (hRank M hM) (hOrder M hM))

end KP1Y.OneYTheorem
