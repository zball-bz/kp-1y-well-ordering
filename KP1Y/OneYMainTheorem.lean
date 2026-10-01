import KP1Y.OneYMainAssemblyCanonical
import KP1Y.OneYLowerLayerFinal
import KP1Y.OneYCanonHelperExits

/-! 定理 1 的最终无条件形式。

* `main_semantic_actual_d`：任意 KPω 模型中，闭句的精确语义 `MainSemantic` 成立
  （任意不可数 ν 给出序数 χ≤ν 与实际集合函数 μ:E→χ，μ(∅)=0、对一切内部 N 的实际展开严格下降；
  ≺ 良基、集合编码轨迹到达 ∅、字典序良序每个 Desc(s) 与 G）。
* `theorem1_derivable`：定理 1 纯 ∈ 闭句 `mainSentence` 的真实 Hilbert `Derives`。

所用的有限复制/规范重提取输入全部由实际对象证明给出：Terminal 底行出口 `terminal_exits_d`、
逐层 Lower 规范性 `lower_steps_d`。没有剩余前提。 -/
namespace KP1Y.OneYTheorem
open YesMetaZFC YesMetaZFC.SetTheory YesMetaZFC.SetTheory.Definitional
open KP1Y.OneYFinite
universe u

/-- Y05b：规范重提取边包含在每个 KPω 模型中成立。 -/
theorem canonical_copy_bound : CopyDescent.CanonicalCopyBound.{u} :=
  canonical_copy_bound_of_steps (fun _ hM => TerminalBase.terminal_exits_d hM) (fun _ hM => LowerLayer.lower_steps_d hM)

/-- Lemma 3（对象形式）无条件成立。 -/
theorem copy_descent : KP1Y.OneYRank.CopyDescentStatement.{u} :=
  CopyDescent.copy_descent_of_canonical canonical_copy_bound

/-- 每个 KPω 模型满足定理 1 的全部结论。 -/
theorem main_semantic_actual_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory) : MainSemantic M :=
  main_semantic_d hM (rank_transfer_at_of_canonical canonical_copy_bound hM) (order_facts_at_actual_d hM)

/-- 定理 1：KPω ⊢ mainSentence（纯 ∈ 闭句的真实 Hilbert 推导）。 -/
theorem theorem1_derivable : KP1Y.Derives mainSentence :=
  main_derivable_of_steps (fun _ hM => TerminalBase.terminal_exits_d hM) (fun _ hM => LowerLayer.lower_steps_d hM)

end KP1Y.OneYTheorem
