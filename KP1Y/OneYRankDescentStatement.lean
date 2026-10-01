import KP1Y.OneYRankStatement

/-! 文稿Lemma 3（有限复制接口）对实际算法的精确对象形状，供Y06交付。
若非空s的规范根图A(s)有末标签β的表示，则每个非空实际展开E_N(s)的规范根图有末标签<β的表示。
N取模型内部ω；表示的标签属于实际labels集合并满足实际R表的边真值。前提`β∈top`只是给证明方的
额外便利（μ的值都在top内），不改变结论。 -/
namespace KP1Y.OneYRank
open YesMetaZFC YesMetaZFC.SetTheory YesMetaZFC.SetTheory.Definitional
open KP1Y.Kuratowski KP1Y.Functions KP1Y.Naturals KP1Y.Bounded KP1Y.Cardinal
open KP1Y.ReflectionModel KP1Y.OneYFinite KP1Y.OneYFinite.ExpressionDiagram
universe u

def CopyDescentStatement : Prop :=
  ∀ (M : SetTheory.Structure.{u}), M.Models KP1Y.theory → ∀ (C : ArticleData M.Domain) (E : ExpressionData M.Domain)
    (T : MatrixArithmetic M.Domain), C.Valid M → UncountableOrdinal M C.reflection.omega C.top →
      E.Valid M → E.omega=C.reflection.omega → T.Valid M E →
      ∀ s m A β, M.mem s E.expressions → s≠E.zero → ExpressionGraph M E T C.reflection s m A →
        M.mem β C.top → RealizesLast M C m A β →
        ∀ N, M.mem N E.omega → ∀ t, Expansion.Expands M E T s N t → t≠E.zero →
          ∀ m' A', ExpressionGraph M E T C.reflection t m' A' → ∃ b, M.mem b β ∧ RealizesLast M C m' A' b

end KP1Y.OneYRank
