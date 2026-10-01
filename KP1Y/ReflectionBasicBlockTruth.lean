import KP1Y.ReflectionBasicBlocks

/-! 四个已构造代码块与标签正性、输出上界、cut值的精确对应。 -/
namespace KP1Y.ReflectionModel
open YesMetaZFC YesMetaZFC.SetTheory
open KP1Y.Kuratowski KP1Y.Functions KP1Y.Assignments KP1Y.Satisfaction
universe u

theorem BasicBlocks.Valid.positive_inputs_iff {M : SetTheory.Structure.{u}} (he : Extensional M) {C : ArticleData M.Domain}
    {D : RelationalData M.Domain} {T : TemplateShape M.Domain} {V : NameFrame M.Domain} {B : BasicBlocks M.Domain}
    (hB : B.Valid M C D T V) {F a θ A s f : M.Domain} (hV : V.Valid M C F T.width T.edgeLength T.needLength)
    (hP : GroundParameters M C T V a θ A s) (hF : TupleValue M f V.inputs s T.width V.scope A) :
    CompareSelectors true M B.omegaSelector V.inputs T.width V.scope A s ↔
      ∀ i, M.mem i T.width → ∀ x, M.mem x A → MemPair M f i x → M.mem C.reflection.omega x :=
  compare_fixed_left_iff he hB.positiveInputs.left hB.omegaConstant hB.positiveInputs.right hP.graph
    (hV.scalars.graph.bounds he hB.omegaName).2 (hP.omega B.omegaName hB.omegaName) hF

theorem BasicBlocks.Valid.positive_outputs_iff {M : SetTheory.Structure.{u}} (he : Extensional M) {C : ArticleData M.Domain}
    {D : RelationalData M.Domain} {T : TemplateShape M.Domain} {V : NameFrame M.Domain} {B : BasicBlocks M.Domain}
    (hB : B.Valid M C D T V) {F a θ A s g : M.Domain} (hV : V.Valid M C F T.width T.edgeLength T.needLength)
    (hP : GroundParameters M C T V a θ A s) (hG : TupleValue M g V.outputs s T.width V.scope A) :
    CompareSelectors true M B.omegaSelector V.outputs T.width V.scope A s ↔
      ∀ i, M.mem i T.width → ∀ x, M.mem x A → MemPair M g i x → M.mem C.reflection.omega x :=
  compare_fixed_left_iff he hB.positiveOutputs.left hB.omegaConstant hB.positiveOutputs.right hP.graph
    (hV.scalars.graph.bounds he hB.omegaName).2 (hP.omega B.omegaName hB.omegaName) hG

theorem BasicBlocks.Valid.below_outputs_iff {M : SetTheory.Structure.{u}} (he : Extensional M) {C : ArticleData M.Domain}
    {D : RelationalData M.Domain} {T : TemplateShape M.Domain} {V : NameFrame M.Domain} {B : BasicBlocks M.Domain}
    (hB : B.Valid M C D T V) {F a θ A s g : M.Domain} (hV : V.Valid M C F T.width T.edgeLength T.needLength)
    (hP : GroundParameters M C T V a θ A s) (hG : TupleValue M g V.outputs s T.width V.scope A) :
    CompareSelectors true M V.outputs B.pointSelector T.width V.scope A s ↔
      ∀ i, M.mem i T.width → ∀ x, M.mem x A → MemPair M g i x → M.mem x a :=
  compare_fixed_right_iff he hB.belowOutputs.left hB.belowOutputs.right hB.pointConstant hP.graph
    (hV.scalars.graph.bounds he hB.pointName).2 (hP.point B.pointName hB.pointName) hG

theorem BasicBlocks.Valid.cut_iff_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory) {C : ArticleData M.Domain} (hC : C.Valid M)
    {D : RelationalData M.Domain} {T : TemplateShape M.Domain} (hT : T.Valid M C) {V : NameFrame M.Domain} {B : BasicBlocks M.Domain}
    (hB : B.Valid M C D T V) {F a θ A s f : M.Domain} (hV : V.Valid M C F T.width T.edgeLength T.needLength)
    (hP : GroundParameters M C T V a θ A s) (hF : TupleValue M f V.inputs s T.width V.scope A) :
    CompareSelectors false M B.cutLeft B.cutRight (C.numbers 1) V.scope A s ↔ MemPair M f T.cut a := by
  obtain ⟨x,hx,hfx⟩ := hF.values.total T.cut hT.cut
  have hCutScope := (hV.inputs.graph.bounds hM.1 hB.cutName).2
  have hPointScope := (hV.scalars.graph.bounds hM.1 hB.pointName).2
  have hsx := (hF.rows T.cut hT.cut B.cutName hCutScope x hx hB.cutName).mp hfx
  have hsa := hP.point B.pointName hB.pointName
  have hCompare := compare_constants_iff (strict := false) hB.atCut.left hB.atCut.right hP.graph hB.cutLeftConstant hB.cutRightConstant
    (hC.numerals.lt (i := 0) (j := 1) (by decide)) hCutScope hPointScope hx (hP.graph.bounds hM.1 hsa).2 hsx hsa
  exact hCompare.trans ⟨fun he => he ▸ hfx,fun hfa => hF.values.unique T.cut x a hfx hfa⟩

def InputBasic (M : SetTheory.Structure.{u}) (C : ArticleData M.Domain) (PC : Context M.Domain) (D : RelationalData M.Domain)
    (T : TemplateShape M.Domain) (B : BasicBlocks M.Domain) (s : M.Domain) : Prop :=
  AllAtoms M PC D B.positiveInputs T.width s ∧ AllAtoms M PC D B.atCut (C.numbers 1) s

def OutputBasic (M : SetTheory.Structure.{u}) (PC : Context M.Domain) (D : RelationalData M.Domain)
    (T : TemplateShape M.Domain) (B : BasicBlocks M.Domain) (s : M.Domain) : Prop :=
  AllAtoms M PC D B.positiveOutputs T.width s ∧ AllAtoms M PC D B.belowOutputs T.width s

theorem input_basic_iff_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory) {C : ArticleData M.Domain} (hC : C.Valid M)
    {A : M.Domain} {D : RelationalData M.Domain} (hD : ArticleInterpretation M C A D) {PC : Context M.Domain} (hAtom : AtomicTable M D PC.atomic)
    {T : TemplateShape M.Domain} (hT : T.Valid M C) {F : M.Domain} {V : NameFrame M.Domain} (hV : V.Valid M C F T.width T.edgeLength T.needLength)
    {B : BasicBlocks M.Domain} (hB : B.Valid M C D T V) {a θ s f : M.Domain} (hSub : M.MemberSubset A C.top)
    (hP : GroundParameters M C T V a θ A s) (hF : TupleValue M f V.inputs s T.width V.scope A) :
    InputBasic M C PC D T B s ↔
      (∀ i, M.mem i T.width → ∀ x, M.mem x A → MemPair M f i x → M.mem C.reflection.omega x) ∧ MemPair M f T.cut a := by
  have hb : M.mem V.scope D.omega := Eq.mpr (congrArg (M.mem V.scope) hD.omega) hV.scope
  exact and_congr ((hB.positiveInputs.all_atoms_iff_d hM hC hD hAtom hSub hb hP.graph).trans (hB.positive_inputs_iff hM.1 hV hP hF))
    ((hB.atCut.all_atoms_iff_d hM hC hD hAtom hSub hb hP.graph).trans (hB.cut_iff_d hM hC hT hV hP hF))

theorem output_basic_iff_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory) {C : ArticleData M.Domain} (hC : C.Valid M)
    {A : M.Domain} {D : RelationalData M.Domain} (hD : ArticleInterpretation M C A D) {PC : Context M.Domain} (hAtom : AtomicTable M D PC.atomic)
    {T : TemplateShape M.Domain} {F : M.Domain} {V : NameFrame M.Domain} (hV : V.Valid M C F T.width T.edgeLength T.needLength)
    {B : BasicBlocks M.Domain} (hB : B.Valid M C D T V) {a θ s g : M.Domain} (hSub : M.MemberSubset A C.top)
    (hP : GroundParameters M C T V a θ A s) (hG : TupleValue M g V.outputs s T.width V.scope A) :
    OutputBasic M PC D T B s ↔
      (∀ i, M.mem i T.width → ∀ x, M.mem x A → MemPair M g i x → M.mem C.reflection.omega x) ∧
      (∀ i, M.mem i T.width → ∀ x, M.mem x A → MemPair M g i x → M.mem x a) := by
  have hb : M.mem V.scope D.omega := Eq.mpr (congrArg (M.mem V.scope) hD.omega) hV.scope
  exact and_congr ((hB.positiveOutputs.all_atoms_iff_d hM hC hD hAtom hSub hb hP.graph).trans (hB.positive_outputs_iff hM.1 hV hP hG))
    ((hB.belowOutputs.all_atoms_iff_d hM hC hD hAtom hSub hb hP.graph).trans (hB.below_outputs_iff hM.1 hV hP hG))

end KP1Y.ReflectionModel
