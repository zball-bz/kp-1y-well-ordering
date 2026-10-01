import KP1Y.Model
import KP1Y.BoundedSyntax

/-! 分离公式额外带源集合参数：x∈a∧φ(x,params)，原参数位置有精确重命名。 -/
namespace KP1Y
open YesMetaZFC YesMetaZFC.SetTheory YesMetaZFC.SetTheory.Definitional
universe u

def restrictSeparationSchema {n : Nat} (φ : Project.Delta0UnarySchema n) : Project.Delta0UnarySchema (n+1) where
  body := .conj (.mem (.bound 0) (.bound 1)) (φ.body.rename BoundEmbedding.unaryUnderOne)
  freeClosed := by simp [Definitional.Formula.FreeClosed,φ.freeClosed]
  delta0 := .conj (.mem _ _) (delta0_rename φ.delta0 _)

theorem restrictSeparationSchema_iff {M : SetTheory.Structure.{u}} {n : Nat} (φ : Project.Delta0UnarySchema n)
    (e : Env M n) (a x : M.Domain) :
    Project.Formula.satisfies ((e.push a).push x) (restrictSeparationSchema φ).body ↔
      M.mem x a ∧ Project.Formula.satisfies (e.push x) φ.body := by
  simp only [restrictSeparationSchema,Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_mem_iff,
    Project.Formula.satisfies_rename,Env.reindex_push_unaryUnderOne]
  rfl

end KP1Y
