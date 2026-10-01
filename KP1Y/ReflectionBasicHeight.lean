import KP1Y.ReflectionBasicBlockTruth
import KP1Y.ReflectionPrefixBlock

/-! 同一组基本/前缀代码在实际初等小结构中的语义，不另假定小结构关系解释。 -/
namespace KP1Y.ReflectionModel
open YesMetaZFC YesMetaZFC.SetTheory
open KP1Y.Kuratowski KP1Y.Functions KP1Y.Assignments KP1Y.Satisfaction
universe u

theorem Height.input_basic_iff_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory) {C : ArticleData M.Domain} (hC : C.Valid M)
    {S : ArticleStructure M.Domain} (hS : S.Valid M C) {δ : M.Domain} {small : EvaluationData M.Domain} (h : Height M C S δ small)
    {T : TemplateShape M.Domain} (hT : T.Valid M C) {F : M.Domain} {V : NameFrame M.Domain} (hV : V.Valid M C F T.width T.edgeLength T.needLength)
    {B : BasicBlocks M.Domain} (hB : B.Valid M C S.relations T V) {a θ s f : M.Domain}
    (hP : GroundParameters M C T V a θ small.carrier s) (hF : TupleValue M f V.inputs s T.width V.scope small.carrier) :
    InputBasic M C (small.context S.context) S.relations T B s ↔
      (∀ i, M.mem i T.width → ∀ x, M.mem x small.carrier → MemPair M f i x → M.mem C.reflection.omega x) ∧ MemPair M f T.cut a := by
  have hb : M.mem V.scope S.context.omega := Eq.mpr (congrArg (M.mem V.scope) hS.omega) hV.scope
  exact and_congr ((h.binary_block_iff_d hM hC hS hb hB.positiveInputs hP.graph).trans (hB.positive_inputs_iff hM.1 hV hP hF))
    ((h.binary_block_iff_d hM hC hS hb hB.atCut hP.graph).trans (hB.cut_iff_d hM hC hT hV hP hF))

theorem Height.output_basic_iff_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory) {C : ArticleData M.Domain} (hC : C.Valid M)
    {S : ArticleStructure M.Domain} (hS : S.Valid M C) {δ : M.Domain} {small : EvaluationData M.Domain} (h : Height M C S δ small)
    {T : TemplateShape M.Domain} {F : M.Domain} {V : NameFrame M.Domain} (hV : V.Valid M C F T.width T.edgeLength T.needLength)
    {B : BasicBlocks M.Domain} (hB : B.Valid M C S.relations T V) {a θ s g : M.Domain}
    (hP : GroundParameters M C T V a θ small.carrier s) (hG : TupleValue M g V.outputs s T.width V.scope small.carrier) :
    OutputBasic M (small.context S.context) S.relations T B s ↔
      (∀ i, M.mem i T.width → ∀ x, M.mem x small.carrier → MemPair M g i x → M.mem C.reflection.omega x) ∧
      (∀ i, M.mem i T.width → ∀ x, M.mem x small.carrier → MemPair M g i x → M.mem x a) := by
  have hb : M.mem V.scope S.context.omega := Eq.mpr (congrArg (M.mem V.scope) hS.omega) hV.scope
  exact and_congr ((h.binary_block_iff_d hM hC hS hb hB.positiveOutputs hP.graph).trans (hB.positive_outputs_iff hM.1 hV hP hG))
    ((h.binary_block_iff_d hM hC hS hb hB.belowOutputs hP.graph).trans (hB.below_outputs_iff hM.1 hV hP hG))

theorem Height.prefix_atoms_iff_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory) {C : ArticleData M.Domain} (hC : C.Valid M)
    {S : ArticleStructure M.Domain} (hS : S.Valid M C) {δ : M.Domain} {small : EvaluationData M.Domain} (h : Height M C S δ small)
    {T : TemplateShape M.Domain} (hT : T.Valid M C) {F : M.Domain} {V : NameFrame M.Domain} (hV : V.Valid M C F T.width T.edgeLength T.needLength)
    {Z B s f g : M.Domain} (hB : BinaryBlock M C S.relations false V.scope T.width V.outputs Z B)
    (hZ : ∀ i v, MemPair M Z i v ↔ (M.mem i T.cut ∧ MemPair M V.inputs i v) ∨ (¬M.mem i T.cut ∧ MemPair M V.outputs i v))
    (hF : TupleValue M f V.inputs s T.width V.scope small.carrier) (hG : TupleValue M g V.outputs s T.width V.scope small.carrier) :
    AllAtoms M (small.context S.context) S.relations B T.width s ↔ KP1Y.Reflection.PrefixAgree M C.reflection f g T.cut := by
  have hb : M.mem V.scope S.context.omega := Eq.mpr (congrArg (M.mem V.scope) hS.omega) hV.scope
  have hCutSub := ((KP1Y.Naturals.omega_isOrdinal_d hM hC.numerals.omega).mem hV.width).transitive T.cut hT.cut
  have hCmp := prefix_selector_iff hV.inputs.graph hV.outputs.graph hCutSub hZ hF hG
  refine ((h.binary_block_iff_d hM hC hS hb hB hF.source).trans hCmp).trans ⟨?_,?_⟩
  · intro hPrefix
    exact prefix_values_enlarge hM.1 hF.values hG.values hPrefix
  · intro hPrefix i hi x hx
    have hxTop := Eq.mp (congrArg (M.mem x) hS.carrier) (h.elementary.carrier_subset x hx)
    have hxCap := hC.reflection.cap.transitive C.top hC.cap.predecessor_mem x hxTop
    exact hPrefix i hi x hxCap

end KP1Y.ReflectionModel
