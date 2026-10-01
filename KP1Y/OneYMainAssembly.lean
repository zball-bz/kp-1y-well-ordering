import KP1Y.OneYTheorem
import KP1Y.OneYCopyDescent
import KP1Y.OneYRankDescent
import KP1Y.OneYSeeds

/-! 协调者汇合：Y04b/Y06（复制下降）、M02/M03（μ 下降与 L 回传）接到 M05 闭句。
Y07a/Y07b 的有限次序事实由 OneYSeeds 无条件解除；剩余前提只有 Y05b 的 `CanonicalCopyBound`（A(E_N(s)) 边包含于同塔复制图）。 -/
namespace KP1Y.OneYTheorem
open YesMetaZFC YesMetaZFC.SetTheory YesMetaZFC.SetTheory.Definitional
open KP1Y.OneYFinite KP1Y.OneYRank
universe u

/-- 规范边包含 ⇒ 每个 KPω 模型的秩回传出口。 -/
theorem rank_transfer_at_of_canonical (hCanon : CopyDescent.CanonicalCopyBound.{u}) {M : SetTheory.Structure.{u}}
    (hM : M.Models KP1Y.theory) : RankTransferAt M := by
  apply rank_transfer_of_some_d hM
  intro w ν hw hν
  obtain ⟨E,T,χ,μ,hE,_,hT,hχ,hW⟩ :=
    rank_transfer_of_copy_descent_d (CopyDescent.copy_descent_of_canonical hCanon) hM hw hν
  exact ⟨E,T,χ,μ,hE,hT,hW,hχ⟩

theorem rank_transfer_statement_of_canonical (hCanon : CopyDescent.CanonicalCopyBound.{0}) :
    RankTransferStatement :=
  fun _ hM => rank_transfer_at_of_canonical hCanon hM

/-- 闭句的 Hilbert 推导，仅余规范边包含与有限次序事实两项。 -/
theorem main_derivable_of_canonical (hCanon : CopyDescent.CanonicalCopyBound.{0})
    (hOrder : OrderFactsStatement) : KP1Y.Derives mainSentence :=
  main_derivable_of (rank_transfer_statement_of_canonical hCanon) hOrder

/-- Y07a/Y07b：实际展开的三项次序事实在每个 KPω 模型中无条件成立。 -/
theorem order_facts_at_actual_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory) : OrderFactsAt M :=
  fun _ _ hC hT => ⟨Seeds.order_index_mono_d hM hC hT,Seeds.order_lex_descent_d hM hC hT,Seeds.order_seed_step_d hM hC hT⟩

theorem order_facts_statement : OrderFactsStatement := fun _ hM => order_facts_at_actual_d hM

/-- 定理 1 闭句的 Hilbert 推导，唯一剩余前提为 Y05b 的规范边包含。 -/
theorem main_derivable_of_canonical_bound (hCanon : CopyDescent.CanonicalCopyBound.{0}) :
    KP1Y.Derives mainSentence :=
  main_derivable_of_canonical hCanon order_facts_statement

end KP1Y.OneYTheorem
