import KP1Y.ReflectionBasicBlockTruth
import KP1Y.UniformConjoinBlock

/-! 已构造基本原子块的实际统一程序；保留扩展关系以接入其余图形约束。 -/
namespace KP1Y.ReflectionModel
open YesMetaZFC YesMetaZFC.SetTheory
open KP1Y.Kuratowski KP1Y.Functions KP1Y.Satisfaction
universe u

theorem basic_seed_exists_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory) {C : ArticleData M.Domain} (hC : C.Valid M)
    {S : ArticleStructure M.Domain} (hS : S.Valid M C) {T : TemplateShape M.Domain} {F : M.Domain} {V : NameFrame M.Domain}
    (hV : V.Valid M C F T.width T.edgeLength T.needLength) {B : BasicBlocks M.Domain} (hB : B.Valid M C S.relations T V) :
    ∃ p length head, FormulaResult M S.context S.relations p length head V.scope := by
  have hbD : M.mem V.scope S.relations.omega := Eq.mpr (congrArg (M.mem V.scope) hS.interpretation.omega) hV.scope
  have hb : M.mem V.scope S.context.omega := Eq.mpr (congrArg (M.mem V.scope) hS.omega) hV.scope
  have hName := (hV.scalars.graph.bounds hM.1 hB.omegaName).2
  obtain ⟨seed,hSeed⟩ := binary_code_exists_d hM hC hS.interpretation false hbD hName hName
  exact uniform_formula_seed_d hM hS.context hb hS.link.codes_bound (hSeed.code_mem_d hM hC hS.interpretation hbD)
    (hSeed.scoped_d hM hC hS.interpretation hbD)

theorem uniform_basic_input_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory) {C : ArticleData M.Domain} (hC : C.Valid M)
    {S : ArticleStructure M.Domain} (hS : S.Valid M C) {T : TemplateShape M.Domain} {F : M.Domain} {V : NameFrame M.Domain}
    (hV : V.Valid M C F T.width T.edgeLength T.needLength) {B : BasicBlocks M.Domain} (hB : B.Valid M C S.relations T V)
    {p length head : M.Domain} (hP : FormulaResult M S.context S.relations p length head V.scope) :
    ∃ q length' head', CompiledExtension M S.context S.relations p length V.scope q length' head' ∧
      ∀ A Assignments Columns Atom H, EvaluationInstance M S.context A Assignments Columns Atom H → ∀ s, M.mem s Assignments →
        (NodeTrue M (S.context.withInterpretation A Assignments Columns Atom) H q head' s ↔
          InputBasic M C (S.context.withInterpretation A Assignments Columns Atom) S.relations T B s) := by
  have hbD : M.mem V.scope S.relations.omega := Eq.mpr (congrArg (M.mem V.scope) hS.interpretation.omega) hV.scope
  have hm : M.mem T.width S.context.omega := Eq.mpr (congrArg (M.mem T.width) hS.omega) hV.width
  have hOne : M.mem (C.numbers 1) S.context.omega := Eq.mpr (congrArg (M.mem (C.numbers 1)) hS.omega) (hC.numerals.natural 1)
  exact uniform_compile_two_blocks_d hM hS.context hP hB.positiveInputs.graph hm hB.atCut.graph hOne hS.link.codes_bound
    (fun _ _ _ hAt => hB.positiveInputs.scoped_d hM hC hS.interpretation hbD hAt)
    (fun _ _ _ hAt => hB.atCut.scoped_d hM hC hS.interpretation hbD hAt)

theorem uniform_basic_output_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory) {C : ArticleData M.Domain} (hC : C.Valid M)
    {S : ArticleStructure M.Domain} (hS : S.Valid M C) {T : TemplateShape M.Domain} {F : M.Domain} {V : NameFrame M.Domain}
    (hV : V.Valid M C F T.width T.edgeLength T.needLength) {B : BasicBlocks M.Domain} (hB : B.Valid M C S.relations T V)
    {p length head : M.Domain} (hP : FormulaResult M S.context S.relations p length head V.scope) :
    ∃ q length' head', CompiledExtension M S.context S.relations p length V.scope q length' head' ∧
      ∀ A Assignments Columns Atom H, EvaluationInstance M S.context A Assignments Columns Atom H → ∀ s, M.mem s Assignments →
        (NodeTrue M (S.context.withInterpretation A Assignments Columns Atom) H q head' s ↔
          OutputBasic M (S.context.withInterpretation A Assignments Columns Atom) S.relations T B s) := by
  have hbD : M.mem V.scope S.relations.omega := Eq.mpr (congrArg (M.mem V.scope) hS.interpretation.omega) hV.scope
  have hm : M.mem T.width S.context.omega := Eq.mpr (congrArg (M.mem T.width) hS.omega) hV.width
  exact uniform_compile_two_blocks_d hM hS.context hP hB.positiveOutputs.graph hm hB.belowOutputs.graph hm hS.link.codes_bound
    (fun _ _ _ hAt => hB.positiveOutputs.scoped_d hM hC hS.interpretation hbD hAt)
    (fun _ _ _ hAt => hB.belowOutputs.scoped_d hM hC hS.interpretation hbD hAt)

end KP1Y.ReflectionModel
