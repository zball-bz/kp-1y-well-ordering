import KP1Y.ReflectionTemplateCompilation
import KP1Y.ReflectionLabelingBridge
import KP1Y.ReflectionEdgeBlockTruth
import KP1Y.ReflectionEndpointBlockTruth
import KP1Y.ReflectionBasicHeight

/-! 完整图形原子块逐项恢复原文 Demand/Response；小结构输入的端点仍是 κ。 -/
namespace KP1Y.ReflectionModel
open YesMetaZFC YesMetaZFC.SetTheory
open KP1Y.Kuratowski KP1Y.Functions KP1Y.Assignments KP1Y.Satisfaction KP1Y.Reflection
universe u

def InputFacts (M : SetTheory.Structure.{u}) (C : ArticleData M.Domain) (T : TemplateShape M.Domain)
    (K a θ f A : M.Domain) : Prop :=
  ((((PositiveLabels M C.reflection f T.width A ∧ MemPair M f T.cut a) ∧ Increasing M f T.width A) ∧
    DiagramEdgeTruth M C T f) ∧ End M C.reflection C.table T.template f C.top) ∧
      Admissible M C.reflection K θ T.template f T.cut

def OutputFacts (M : SetTheory.Structure.{u}) (C : ArticleData M.Domain) (T : TemplateShape M.Domain)
    (a f g A : M.Domain) : Prop :=
  ((((PositiveLabels M C.reflection g T.width A ∧
    (∀ i, M.mem i T.width → ∀ x, M.mem x A → MemPair M g i x → M.mem x a)) ∧ Increasing M g T.width A) ∧
      DiagramEdgeTruth M C T g) ∧ End M C.reflection C.table T.template g a) ∧ PrefixValues M f g T.cut A

theorem input_facts_iff_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ArticleData M.Domain} (hC : C.Valid M) {T : TemplateShape M.Domain} (hT : T.Valid M C)
    {K a θ f A : M.Domain} (hF : Graph M f T.width A) (hSub : M.MemberSubset A C.top) :
    InputFacts M C T K a θ f A ↔
      Demand M C.reflection C.table K θ a C.top T.width T.diagram T.template T.cut f := by
  have hCap : M.MemberSubset A C.reflection.cap :=
    fun x hx => hC.reflection.cap.transitive C.top hC.cap.predecessor_mem x (hSub x hx)
  have hLabel := labeling_iff_positive_increasing hM.1 hT.diagram.1 hF hCap
  constructor
  · rintro ⟨⟨⟨⟨⟨hPos,hCut⟩,hInc⟩,hEdges⟩,hEnd⟩,hAdm⟩
    exact ⟨hT.template,⟨hT.diagram,hLabel.mpr ⟨hPos,hInc⟩,hEdges⟩,hCut,
      fun _ _ x _ hAt => hSub x (hF.bounds hM.1 hAt).2,hAdm,hEnd⟩
  · intro h
    obtain ⟨hPos,hInc⟩ := hLabel.mp h.representation.labeling
    exact ⟨⟨⟨⟨⟨hPos,h.cut⟩,hInc⟩,h.representation.edges⟩,h.endpoint⟩,h.admissible⟩

theorem output_facts_iff_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ArticleData M.Domain} (hC : C.Valid M) {T : TemplateShape M.Domain} (hT : T.Valid M C)
    {a f g A : M.Domain} (hF : Graph M f T.width A) (hG : Graph M g T.width A) (hSub : M.MemberSubset A C.top) :
    OutputFacts M C T a f g A ↔ Response M C.reflection C.table a T.width T.diagram T.template T.cut f g := by
  have hCap : M.MemberSubset A C.reflection.cap :=
    fun x hx => hC.reflection.cap.transitive C.top hC.cap.predecessor_mem x (hSub x hx)
  have hLabel := labeling_iff_positive_increasing hM.1 hT.diagram.1 hG hCap
  have hBelow := below_iff_on_carrier (C := C.reflection) (b := a) hM.1 hG hCap
  have hPrefix := prefix_iff_on_carrier (C := C.reflection) (c := T.cut) hM.1 hF hG hCap
  constructor
  · rintro ⟨⟨⟨⟨⟨hPos,hBelowA⟩,hInc⟩,hEdges⟩,hEnd⟩,hPref⟩
    exact ⟨⟨hT.diagram,hLabel.mpr ⟨hPos,hInc⟩,hEdges⟩,hBelow.mpr hBelowA,hPrefix.mpr hPref,hEnd⟩
  · intro h
    obtain ⟨hPos,hInc⟩ := hLabel.mp h.representation.labeling
    exact ⟨⟨⟨⟨⟨hPos,hBelow.mp h.below⟩,hInc⟩,h.representation.edges⟩,h.endpoint⟩,hPrefix.mp h.prefix_eq⟩

theorem input_template_iff_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ArticleData M.Domain} (hC : C.Valid M) {A : M.Domain} {D : RelationalData M.Domain}
    (hD : ArticleInterpretation M C A D) {PC : Context M.Domain} (hAtom : AtomicTable M D PC.atomic)
    {T : TemplateShape M.Domain} (hT : T.Valid M C) {F : M.Domain} {V : NameFrame M.Domain}
    (hV : V.Valid M C F T.width T.edgeLength T.needLength) {K : M.Domain} {B : TemplateBlocks M.Domain}
    (hB : B.Valid M C D T V K) {a θ s f : M.Domain} (hA : M.IsOrdinal A) (hSub : M.MemberSubset A C.top)
    (hP : GroundParameters M C T V a θ A s) (hF : TupleValue M f V.inputs s T.width V.scope A) :
    InputTemplate M C PC D T B s ↔
      Demand M C.reflection C.table K θ a C.top T.width T.diagram T.template T.cut f := by
  have hs : M.mem V.scope D.omega := Eq.mpr (congrArg (M.mem V.scope) hD.omega) hV.scope
  unfold InputTemplate
  rw [input_basic_iff_d hM hC hD hAtom hT hV hB.basic hSub hP hF,
    hB.inputIncreasing.all_atoms_iff_d hM hC hD hAtom hV.width hs hA hSub hF,
    hB.inputEdges.shape_iff_d hM hC hD hAtom hT hP hSub hs hF,
    hB.endpoints.input_top_iff_d hM hC hD hAtom hT hP hSub hs hF,
    hB.admission.ground_atoms_iff_d hM hC hD hAtom hT hV hB.rootName hSub hP hF]
  exact input_facts_iff_d hM hC hT hF.values hSub

theorem output_template_iff_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ArticleData M.Domain} (hC : C.Valid M) {A : M.Domain} {D : RelationalData M.Domain}
    (hD : ArticleInterpretation M C A D) {PC : Context M.Domain} (hAtom : AtomicTable M D PC.atomic)
    {T : TemplateShape M.Domain} (hT : T.Valid M C) {F : M.Domain} {V : NameFrame M.Domain}
    (hV : V.Valid M C F T.width T.edgeLength T.needLength) {K : M.Domain} {B : TemplateBlocks M.Domain}
    (hB : B.Valid M C D T V K) {a θ s f g : M.Domain} (hA : M.IsOrdinal A) (hSub : M.MemberSubset A C.top)
    (hP : GroundParameters M C T V a θ A s) (hF : TupleValue M f V.inputs s T.width V.scope A)
    (hG : TupleValue M g V.outputs s T.width V.scope A) :
    OutputTemplate M PC D T B s ↔ Response M C.reflection C.table a T.width T.diagram T.template T.cut f g := by
  have hs : M.mem V.scope D.omega := Eq.mpr (congrArg (M.mem V.scope) hD.omega) hV.scope
  have hCutSub := ((KP1Y.Naturals.omega_isOrdinal_d hM hC.numerals.omega).mem hV.width).transitive T.cut hT.cut
  unfold OutputTemplate
  rw [output_basic_iff_d hM hC hD hAtom hV hB.basic hSub hP hG,
    hB.outputIncreasing.all_atoms_iff_d hM hC hD hAtom hV.width hs hA hSub hG,
    hB.outputEdges.shape_iff_d hM hC hD hAtom hT hP hSub hs hG,
    hB.endpoints.output_relation_iff_d hM hC hD hAtom hT hP hSub hs hG,
    hB.prefixCode.all_atoms_iff_d hM hC hD hAtom hSub hs hP.graph,
    prefix_selector_iff hV.inputs.graph hV.outputs.graph hCutSub hB.prefixRows hF hG]
  exact output_facts_iff_d hM hC hT hF.values hG.values hSub

theorem Height.input_template_iff_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ArticleData M.Domain} (hC : C.Valid M) {S : ArticleStructure M.Domain} (hS : S.Valid M C)
    {δ : M.Domain} {small : EvaluationData M.Domain} (h : Height M C S δ small)
    {T : TemplateShape M.Domain} (hT : T.Valid M C) {F : M.Domain} {V : NameFrame M.Domain}
    (hV : V.Valid M C F T.width T.edgeLength T.needLength) {K : M.Domain} {B : TemplateBlocks M.Domain}
    (hB : B.Valid M C S.relations T V K) {a θ s f : M.Domain}
    (hP : GroundParameters M C T V a θ small.carrier s) (hF : TupleValue M f V.inputs s T.width V.scope small.carrier) :
    InputTemplate M C (small.context S.context) S.relations T B s ↔
      Demand M C.reflection C.table K θ a C.top T.width T.diagram T.template T.cut f := by
  have hs : M.mem V.scope S.context.omega := Eq.mpr (congrArg (M.mem V.scope) hS.omega) hV.scope
  have hSub : M.MemberSubset small.carrier C.top := fun x hx =>
    Eq.mp (congrArg (M.mem x) hS.carrier) (h.elementary.carrier_subset x hx)
  unfold InputTemplate
  rw [h.input_basic_iff_d hM hC hS hT hV hB.basic hP hF,
    h.increasing_block_iff_d hM hC hS hB.inputIncreasing hV.width hs hF,
    h.shape_edge_iff_d hM hC hS hT hB.inputEdges hP hs hF,
    h.input_top_iff_d hM hC hS hT hB.endpoints hP hs hF,
    h.ground_admission_iff_d hM hC hS hT hV hB.rootName hB.admission hP hF]
  exact input_facts_iff_d hM hC hT hF.values hSub

theorem Height.output_template_iff_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ArticleData M.Domain} (hC : C.Valid M) {S : ArticleStructure M.Domain} (hS : S.Valid M C)
    {δ : M.Domain} {small : EvaluationData M.Domain} (h : Height M C S δ small)
    {T : TemplateShape M.Domain} (hT : T.Valid M C) {F : M.Domain} {V : NameFrame M.Domain}
    (hV : V.Valid M C F T.width T.edgeLength T.needLength) {K : M.Domain} {B : TemplateBlocks M.Domain}
    (hB : B.Valid M C S.relations T V K) {a θ s f g : M.Domain}
    (hP : GroundParameters M C T V a θ small.carrier s) (hF : TupleValue M f V.inputs s T.width V.scope small.carrier)
    (hG : TupleValue M g V.outputs s T.width V.scope small.carrier) :
    OutputTemplate M (small.context S.context) S.relations T B s ↔
      Response M C.reflection C.table a T.width T.diagram T.template T.cut f g := by
  have hs : M.mem V.scope S.context.omega := Eq.mpr (congrArg (M.mem V.scope) hS.omega) hV.scope
  have hSub : M.MemberSubset small.carrier C.top := fun x hx =>
    Eq.mp (congrArg (M.mem x) hS.carrier) (h.elementary.carrier_subset x hx)
  have hCap : M.MemberSubset small.carrier C.reflection.cap :=
    fun x hx => hC.reflection.cap.transitive C.top hC.cap.predecessor_mem x (hSub x hx)
  unfold OutputTemplate
  rw [h.output_basic_iff_d hM hC hS hV hB.basic hP hG,
    h.increasing_block_iff_d hM hC hS hB.outputIncreasing hV.width hs hG,
    h.shape_edge_iff_d hM hC hS hT hB.outputEdges hP hs hG,
    h.output_relation_iff_d hM hC hS hT hB.endpoints hP hs hG,
    h.prefix_atoms_iff_d hM hC hS hT hV hB.prefixCode hB.prefixRows hF hG,
    prefix_iff_on_carrier hM.1 hF.values hG.values hCap]
  exact output_facts_iff_d hM hC hT hF.values hG.values hSub

end KP1Y.ReflectionModel
