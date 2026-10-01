import YesMetaZFC.SetTheory.Axioms.KP
import YesMetaZFC.SetTheory.Definitional.Project.Derivation

/-!
文稿的对象理论 KPω：完整集合归纳模式，而非仅集合基础。
此文件中的 Axiom 是一阶公理的语法谓词，不是新增 Lean 公理。
-/
namespace KP1Y
open YesMetaZFC YesMetaZFC.SetTheory
open YesMetaZFC.SetTheory.Definitional

/-- ∀x ((∀y∈x φ(y)) → φ(x)) → ∀x φ(x)，保留所有参数。 -/
def inductionCore {n : Nat} (φ : Project.UnarySchema n) : Project.Formula 1 n :=
  .imp
    (.forallE (.imp
      (Project.Formula.forallMem (.bound 0) (φ.body.rename BoundEmbedding.unaryUnderOne))
      φ.body))
    (.forallE φ.body)

def inductionSentence {n : Nat} (φ : Project.UnarySchema n) : Project.Sentence :=
  Project.Sentence.forallClosure (inductionCore φ) (by
    simp [inductionCore, Definitional.Formula.FreeClosed, φ.freeClosed,
      Project.Formula.forallMem, Project.Term.newest])

/-- 与文稿第 1 页逐项相同的 KPω 公理表。 -/
inductive Axiom : Project.Theory where
  | extensionality : Axiom Axioms.extensionality
  | emptySet : Axiom Axioms.emptySet
  | pairing : Axiom Axioms.pairing
  | union : Axiom Axioms.union
  | infinity : Axiom Axioms.infinity
  | separation {n : Nat} (φ : Project.Delta0UnarySchema n) :
      Axiom (Axioms.Schema.separation φ.toUnarySchema)
  | collection {n : Nat} (φ : Project.Delta0BinarySchema n) :
      Axiom (Axioms.Schema.collection φ.toBinarySchema)
  | setInduction {n : Nat} (φ : Project.UnarySchema n) :
      Axiom (inductionSentence φ)

abbrev theory : Project.Theory := Axiom

/-- 目标推导使用纯 ∈ 语言的真正 Hilbert 证明谓词。 -/
abbrev Derives (sentence : Project.Sentence) : Prop := Project.Derives theory sentence

theorem axiom_derivable {sentence : Project.Sentence} (h : theory sentence) :
    Derives sentence := by
  exact Logic.FirstOrder.Derives.theory_axiom ⟨sentence, h, rfl⟩

theorem induction_derivable {n : Nat} (φ : Project.UnarySchema n) :
    Derives (inductionSentence φ) := axiom_derivable (.setInduction φ)

end KP1Y
