import KP1Y.OneYTheorem
import KP1Y.OneYExpansionOrder

/-! 用 Y07a 已交付的 `ExpansionOrder.index_mono_d` 解除 `OrderFacts.index_mono`。
剩余有限数值输入只有 E_N(s) <lex s 与 E₁(1,n+2)=(1,n+1)，统一记为 `OrderInputs`。 -/
namespace KP1Y.OneYTheorem
open YesMetaZFC YesMetaZFC.SetTheory YesMetaZFC.SetTheory.Definitional
open KP1Y.Kuratowski KP1Y.Functions KP1Y.Naturals KP1Y.Bounded KP1Y.Cardinal
open KP1Y.OneYFinite KP1Y.OneYRank
universe u

/-- 尚待 Y07a(c)/Y07b 的两项实际算法事实。 -/
structure OrderInputs (M : SetTheory.Structure.{u}) (C : ExpressionData M.Domain) (T : MatrixArithmetic M.Domain) : Prop where
  lex_descent : ∀ s, M.mem s C.expressions → s≠C.zero → ∀ N, M.mem N C.omega → ∀ t,
    Expansion.Expands M C T s N t → Lex M C t s
  seed_step : ∀ n, M.mem n C.omega → ∀ a b, M.SuccessorOf a n → M.SuccessorOf b a → ∀ s t,
    PairExpression M C s b → PairExpression M C t a → Expansion.Expands M C T s C.one t

theorem OrderInputs.order_facts_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    (h : OrderInputs M C T) : OrderFacts M C T :=
  ⟨fun _ _ _ hEN hR _ _ _ _ _ hij ht hu => ExpansionOrder.index_mono_d hM hC hT hEN hR hij ht hu,
    h.lex_descent,h.seed_step⟩

def OrderInputsAt (M : SetTheory.Structure.{u}) : Prop :=
  ∀ (C : ExpressionData M.Domain) (T : MatrixArithmetic M.Domain), C.Valid M → T.Valid M C → OrderInputs M C T

theorem order_facts_at_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory) (h : OrderInputsAt M) :
    OrderFactsAt M :=
  fun C T hC hT => (h C T hC hT).order_facts_d hM hC hT

def OrderInputsStatement : Prop := ∀ M : SetTheory.Structure.{0}, M.Models KP1Y.theory → OrderInputsAt M

/-- 剩余前提：秩回传出口与两项有限数值事实。 -/
theorem main_derivable_of_inputs (hRank : RankTransferStatement) (hInputs : OrderInputsStatement) :
    KP1Y.Derives mainSentence :=
  main_derivable_of hRank (fun M hM => order_facts_at_d hM (hInputs M hM))

end KP1Y.OneYTheorem
