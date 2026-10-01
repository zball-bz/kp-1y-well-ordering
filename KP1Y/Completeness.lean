import KP1Y.Model
import YesMetaZFC.SetTheory.Definitional.Project.FirstOrderSemantics
import YesMetaZFC.Automation.SyntaxNatCoding
import YesMetaZFC.Logic.FirstOrder.Completeness.StrongCompleteness

/-! 任意 KPω 模型中的证明，经过完整性转为纯 ∈ Hilbert 推导。 -/
namespace KP1Y
open YesMetaZFC YesMetaZFC.SetTheory YesMetaZFC.SetTheory.Definitional
open YesMetaZFC.Logic.FirstOrder
open YesMetaZFC.Automation.SyntaxNatCoding
attribute [local implicit_reducible] SetTheory.signature
universe u

/-- 只有一个排序和一个隶属关系，完全没有非逻辑函数符号。 -/
def pureSymbols : SymbolCoding ℒ where
  sort := ⟨fun _ => 0, by intro a b _; cases a; cases b; rfl⟩
  function := {
    encode := fun f => nomatch f
    injective := by intro f; cases f }
  relation := ⟨fun _ => 0, by intro a b _; cases a; cases b; rfl⟩

noncomputable def pureSchedule : Completeness.Henkin.Schedule ℒ := schedule pureSymbols

/-- 从对象理论本身的外延公理建立模型桥。 -/
theorem pure_extensional {M : Logic.FirstOrder.Structure.{0,0,0,u} ℒ}
    (hM : Logic.FirstOrder.Theory.Models M (Project.fo_theory theory)) :
    SetTheory.Extensional (Project.FirstOrderSemantics.reduct M) := by
  constructor
  intro left right h
  have hAx := hM _ ⟨_, Axiom.extensionality, rfl⟩
  simp only [Formula.TrueIn, Project.fo_sentence, SetTheory.Axioms.extensionality,
    Project.Sentence.ofFormula, Project.fo_formula, Project.fo_mem, Project.fo_term,
    Project.fo_bound_variable, Formula.satisfies, Arguments.eval, Logic.FirstOrder.Term.eval,
    Project.Term.newest, Project.Term.weaken, Definitional.Term.newest,
    Definitional.Term.weaken, Definitional.Term.rename, Definitional.Term.bind,
    Project.Formula.extensionalEq, Project.Formula.pairArguments] at hAx
  exact hAx left right h

/-- 这个结论是真实 Derives，不是给语义蕴涵重新命名。 -/
theorem derives_of_all_models {sentence : Project.Sentence}
    (h : ∀ M : SetTheory.Structure.{0}, M.Models theory → M.SatisfiesSentence sentence) :
    Derives sentence := by
  apply Completeness.strong_completeness pureSchedule
  intro M hM
  have hExt := pure_extensional hM
  apply (Project.FirstOrderSemantics.sentence_correct hExt sentence).mpr
  exact h _ ((Project.FirstOrderSemantics.models_iff hExt theory).mp hM)

/-- Foundation 的真实 KPω 对象推导。 -/
theorem foundation_derivable : Derives SetTheory.Axioms.foundation := by
  apply derives_of_all_models
  intro M hM free
  exact (SetTheory.Axioms.foundation_sat_iff_d free).mpr (foundation_d hM)

/-- 复用旧弱 KP 的对象推导，明确通过模型桥与完备性传输。 -/
theorem transfer_weakKP {sentence : Project.Sentence}
    (h : Project.Derives SetTheory.KP sentence) : Derives sentence := by
  apply Completeness.strong_completeness pureSchedule
  intro M hM
  have he := pure_extensional hM
  have hw := models_weakKP ((Project.FirstOrderSemantics.models_iff he theory).mp hM)
  exact h.semantically_entails M
    ((Project.FirstOrderSemantics.models_iff he SetTheory.KP).mpr hw)

end KP1Y
