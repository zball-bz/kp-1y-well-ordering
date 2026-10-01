import KP1Y.ReflectionCounterexampleCompilation
import KP1Y.ReflectionOutputRestriction

/-! 反例程序与文稿 Demand/Response 的精确对应；任意响应因 g<a 自动落入含 a 的序数载域。 -/
namespace KP1Y.ReflectionModel
open YesMetaZFC YesMetaZFC.SetTheory
open KP1Y.Kuratowski KP1Y.Functions KP1Y.Assignments KP1Y.Satisfaction KP1Y.Reflection
universe u

theorem response_graph_on_carrier {M : SetTheory.Structure.{u}} (he : Extensional M)
    {C : Data M.Domain} {H a m diagram template cut f g A : M.Domain} (hA : M.IsOrdinal A) (ha : M.mem a A)
    (h : Response M C H a m diagram template cut f g) : Graph M g m A :=
  graph_tighten_values h.representation.labeling.graph
    (fun _ x hAt => hA.transitive a ha x (h.below.at he h.representation.labeling.graph hAt))

theorem demand_graph_below {M : SetTheory.Structure.{u}} (he : Extensional M)
    {C : Data M.Domain} {H K θ a b m diagram template cut f : M.Domain}
    (h : Demand M C H K θ a b m diagram template cut f) : Graph M f m b :=
  graph_tighten_values h.representation.labeling.graph (fun _ _ hAt => h.below.at he h.representation.labeling.graph hAt)

private theorem output_exists_meaning_iff {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ArticleData M.Domain} (hC : C.Valid M) {PC : Context M.Domain} {D : RelationalData M.Domain}
    {T : TemplateShape M.Domain} {F : M.Domain} {V : NameFrame M.Domain}
    (hV : V.Valid M C F T.width T.edgeLength T.needLength) {B : TemplateBlocks M.Domain} {a θ s f : M.Domain}
    (hParams : GroundParameters M C T V a θ PC.carrier s) (hF : TupleValue M f V.inputs s T.width V.scope PC.carrier)
    (hA : M.IsOrdinal PC.carrier) (ha : M.mem a PC.carrier)
    (hAssignments : ∀ t, Graph M t V.scope PC.carrier → M.mem t PC.assignments)
    (hBody : ∀ t g, GroundParameters M C T V a θ PC.carrier t →
      TupleValue M f V.inputs t T.width V.scope PC.carrier → TupleValue M g V.outputs t T.width V.scope PC.carrier →
      (OutputTemplate M PC D T B t ↔ Response M C.reflection C.table a T.width T.diagram T.template T.cut f g)) :
    TemplateOutputExists M PC D T V B s ↔ ∃ g, Response M C.reflection C.table a T.width T.diagram T.template T.cut f g := by
  constructor
  · rintro ⟨t,_,hFrame,hTrue⟩
    have hParamsT := hParams.preserve_family_d hM hC hV 1 (by decide) (by decide) (by decide) hFrame
    have hFT := hF.preserve_outside hFrame (fun _ _ hAt => hV.untouched_d hM hC (i := 0) (j := 1) (by decide) hAt)
    obtain ⟨g,hG⟩ := tuple_value_exists_d hM hV.outputs.graph hFrame.target
    exact ⟨g,(hBody t g hParamsT hFT hG).mp hTrue⟩
  · rintro ⟨g,hResponse⟩
    have hGraph := response_graph_on_carrier hM.1 hA ha hResponse
    obtain ⟨t,hFrame,hG⟩ := patch_assignment_d hM hParams.graph hV.outputs.graph
      (fun _ _ _ hi hj => hV.outputs.injective hM.1 hV.basis hi hj) hGraph
    have hParamsT := hParams.preserve_family_d hM hC hV 1 (by decide) (by decide) (by decide) hFrame
    have hFT := hF.preserve_outside hFrame (fun _ _ hAt => hV.untouched_d hM hC (i := 0) (j := 1) (by decide) hAt)
    exact ⟨t,hAssignments t hFrame.target,hFrame,(hBody t g hParamsT hFT hG).mpr hResponse⟩

theorem template_output_exists_iff_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ArticleData M.Domain} (hC : C.Valid M) {A : M.Domain} {D : RelationalData M.Domain}
    (hD : ArticleInterpretation M C A D) {PC : Context M.Domain} {Assignments Columns Atom H : M.Domain}
    (hI : EvaluationInstance M PC A Assignments Columns Atom H) (hAtom : AtomicTable M D Atom)
    {T : TemplateShape M.Domain} (hT : T.Valid M C) {F : M.Domain} {V : NameFrame M.Domain}
    (hV : V.Valid M C F T.width T.edgeLength T.needLength) {K : M.Domain} {B : TemplateBlocks M.Domain} (hB : B.Valid M C D T V K)
    {a θ s f : M.Domain} (hParams : GroundParameters M C T V a θ A s) (hA : M.IsOrdinal A)
    (ha : M.mem a A) (hSub : M.MemberSubset A C.top) (hs : M.mem V.scope PC.omega)
    (hF : TupleValue M f V.inputs s T.width V.scope A) :
    TemplateOutputExists M (PC.withInterpretation A Assignments Columns Atom) D T V B s ↔
      ∃ g, Response M C.reflection C.table a T.width T.diagram T.template T.cut f g :=
  output_exists_meaning_iff hM hC hV hParams hF hA ha (fun t ht => (hI.assignments_exact t).mpr ⟨V.scope,hs,ht⟩)
    (fun _ _ hPT hFT hGT => output_template_iff_d hM hC hD hAtom hT hV hB hA hSub hPT hFT hGT)

theorem Height.template_output_exists_iff_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ArticleData M.Domain} (hC : C.Valid M) {S : ArticleStructure M.Domain} (hS : S.Valid M C)
    {δ : M.Domain} {small : EvaluationData M.Domain} (h : Height M C S δ small)
    {T : TemplateShape M.Domain} (hT : T.Valid M C) {F : M.Domain} {V : NameFrame M.Domain}
    (hV : V.Valid M C F T.width T.edgeLength T.needLength) {K : M.Domain} {B : TemplateBlocks M.Domain}
    (hB : B.Valid M C S.relations T V K) {a θ s f : M.Domain} (ha : M.mem a δ)
    (hParams : GroundParameters M C T V a θ small.carrier s) (hF : TupleValue M f V.inputs s T.width V.scope small.carrier) :
    TemplateOutputExists M (small.context S.context) S.relations T V B s ↔
      ∃ g, Response M C.reflection C.table a T.width T.diagram T.template T.cut f g := by
  have hA : M.IsOrdinal small.carrier := Eq.mpr (congrArg M.IsOrdinal h.carrier) h.ordinal
  have haA : M.mem a small.carrier := Eq.mpr (congrArg (M.mem a) h.carrier) ha
  have hs : M.mem V.scope S.context.omega := Eq.mpr (congrArg (M.mem V.scope) hS.omega) hV.scope
  exact output_exists_meaning_iff hM hC hV hParams hF hA haA (fun t ht => (h.valid.assignments_exact t).mpr ⟨V.scope,hs,ht⟩)
    (fun _ _ hPT hFT hGT => h.output_template_iff_d hM hC hS hT hV hB hPT hFT hGT)

private theorem counterexample_meaning_iff {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ArticleData M.Domain} (hC : C.Valid M) {PC : Context M.Domain} {D : RelationalData M.Domain}
    {T : TemplateShape M.Domain} {F : M.Domain} {V : NameFrame M.Domain}
    (hV : V.Valid M C F T.width T.edgeLength T.needLength) {B : TemplateBlocks M.Domain} {K a θ s : M.Domain}
    (hParams : GroundParameters M C T V a θ PC.carrier s)
    (hAssignments : ∀ t, Graph M t V.scope PC.carrier → M.mem t PC.assignments)
    (hInput : ∀ t f, GroundParameters M C T V a θ PC.carrier t → TupleValue M f V.inputs t T.width V.scope PC.carrier →
      (InputTemplate M C PC D T B t ↔ Demand M C.reflection C.table K θ a C.top T.width T.diagram T.template T.cut f))
    (hOutput : ∀ t f, GroundParameters M C T V a θ PC.carrier t → TupleValue M f V.inputs t T.width V.scope PC.carrier →
      (TemplateOutputExists M PC D T V B t ↔ ∃ g, Response M C.reflection C.table a T.width T.diagram T.template T.cut f g)) :
    TemplateCounterexample M C PC D T V B s ↔ ∃ f, Graph M f T.width PC.carrier ∧
      Demand M C.reflection C.table K θ a C.top T.width T.diagram T.template T.cut f ∧
        ¬∃ g, Response M C.reflection C.table a T.width T.diagram T.template T.cut f g := by
  constructor
  · rintro ⟨t,_,hFrame,hTrue,hNone⟩
    have hParamsT := hParams.preserve_family_d hM hC hV 0 (by decide) (by decide) (by decide) hFrame
    obtain ⟨f,hF⟩ := tuple_value_exists_d hM hV.inputs.graph hFrame.target
    exact ⟨f,hF.values,(hInput t f hParamsT hF).mp hTrue,fun hOut => hNone ((hOutput t f hParamsT hF).mpr hOut)⟩
  · rintro ⟨f,hGraph,hDemand,hNone⟩
    obtain ⟨t,hFrame,hF⟩ := patch_assignment_d hM hParams.graph hV.inputs.graph
      (fun _ _ _ hi hj => hV.inputs.injective hM.1 hV.basis hi hj) hGraph
    have hParamsT := hParams.preserve_family_d hM hC hV 0 (by decide) (by decide) (by decide) hFrame
    exact ⟨t,hAssignments t hFrame.target,hFrame,(hInput t f hParamsT hF).mpr hDemand,
      fun hOut => hNone ((hOutput t f hParamsT hF).mp hOut)⟩

theorem template_counterexample_iff_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ArticleData M.Domain} (hC : C.Valid M) {A : M.Domain} {D : RelationalData M.Domain}
    (hD : ArticleInterpretation M C A D) {PC : Context M.Domain} {Assignments Columns Atom H : M.Domain}
    (hI : EvaluationInstance M PC A Assignments Columns Atom H) (hAtom : AtomicTable M D Atom)
    {T : TemplateShape M.Domain} (hT : T.Valid M C) {F : M.Domain} {V : NameFrame M.Domain}
    (hV : V.Valid M C F T.width T.edgeLength T.needLength) {K : M.Domain} {B : TemplateBlocks M.Domain} (hB : B.Valid M C D T V K)
    {a θ s : M.Domain} (hParams : GroundParameters M C T V a θ A s) (hA : M.IsOrdinal A)
    (ha : M.mem a A) (hSub : M.MemberSubset A C.top) (hs : M.mem V.scope PC.omega) :
    TemplateCounterexample M C (PC.withInterpretation A Assignments Columns Atom) D T V B s ↔ ∃ f, Graph M f T.width A ∧
      Demand M C.reflection C.table K θ a C.top T.width T.diagram T.template T.cut f ∧
        ¬∃ g, Response M C.reflection C.table a T.width T.diagram T.template T.cut f g :=
  counterexample_meaning_iff hM hC hV hParams (fun t ht => (hI.assignments_exact t).mpr ⟨V.scope,hs,ht⟩)
    (fun _ _ hPT hFT => input_template_iff_d hM hC hD hAtom hT hV hB hA hSub hPT hFT)
    (fun _ _ hPT hFT => template_output_exists_iff_d hM hC hD hI hAtom hT hV hB hPT hA ha hSub hs hFT)

theorem Height.template_counterexample_iff_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ArticleData M.Domain} (hC : C.Valid M) {S : ArticleStructure M.Domain} (hS : S.Valid M C)
    {δ : M.Domain} {small : EvaluationData M.Domain} (h : Height M C S δ small)
    {T : TemplateShape M.Domain} (hT : T.Valid M C) {F : M.Domain} {V : NameFrame M.Domain}
    (hV : V.Valid M C F T.width T.edgeLength T.needLength) {K : M.Domain} {B : TemplateBlocks M.Domain}
    (hB : B.Valid M C S.relations T V K) {a θ s : M.Domain} (ha : M.mem a δ)
    (hParams : GroundParameters M C T V a θ small.carrier s) :
    TemplateCounterexample M C (small.context S.context) S.relations T V B s ↔ ∃ f, Graph M f T.width small.carrier ∧
      Demand M C.reflection C.table K θ a C.top T.width T.diagram T.template T.cut f ∧
        ¬∃ g, Response M C.reflection C.table a T.width T.diagram T.template T.cut f g := by
  have hs : M.mem V.scope S.context.omega := Eq.mpr (congrArg (M.mem V.scope) hS.omega) hV.scope
  exact counterexample_meaning_iff hM hC hV hParams (fun t ht => (h.valid.assignments_exact t).mpr ⟨V.scope,hs,ht⟩)
    (fun _ _ hPT hFT => h.input_template_iff_d hM hC hS hT hV hB hPT hFT)
    (fun _ _ hPT hFT => h.template_output_exists_iff_d hM hC hS hT hV hB ha hPT hFT)

theorem Height.localize_counterexample_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ArticleData M.Domain} (hC : C.Valid M) {S : ArticleStructure M.Domain} (hS : S.Valid M C)
    {δ : M.Domain} {small : EvaluationData M.Domain} (h : Height M C S δ small)
    {T : TemplateShape M.Domain} (hT : T.Valid M C) {F : M.Domain} {V : NameFrame M.Domain}
    (hV : V.Valid M C F T.width T.edgeLength T.needLength) {K : M.Domain} {B : TemplateBlocks M.Domain}
    (hB : B.Valid M C S.relations T V K) {a θ f : M.Domain} (ha : M.mem a δ) (hθ : M.mem θ δ)
    (hDemand : Demand M C.reflection C.table K θ a C.top T.width T.diagram T.template T.cut f)
    (hNone : ¬∃ g, Response M C.reflection C.table a T.width T.diagram T.template T.cut f g) :
    ∃ f', Graph M f' T.width δ ∧ Demand M C.reflection C.table K θ a C.top T.width T.diagram T.template T.cut f' ∧
      ¬∃ g, Response M C.reflection C.table a T.width T.diagram T.template T.cut f' g := by
  have hSmallOrd : M.IsOrdinal small.carrier := Eq.mpr (congrArg M.IsOrdinal h.carrier) h.ordinal
  have hSmallω : M.mem C.reflection.omega small.carrier := Eq.mpr (congrArg (M.mem C.reflection.omega) h.carrier) h.omega
  have haSmall : M.mem a small.carrier := Eq.mpr (congrArg (M.mem a) h.carrier) ha
  have hθSmall : M.mem θ small.carrier := Eq.mpr (congrArg (M.mem θ) h.carrier) hθ
  obtain ⟨s,hParams⟩ := ground_parameters_exists_d hM hC hT hV hSmallOrd hSmallω haSmall hθSmall
  obtain ⟨p,length,head,hProgram⟩ := uniform_counterexample_program_d hM hC hS hT hV hB
  have hD : ArticleInterpretation M C S.large.carrier S.relations :=
    Eq.mpr (congrArg (fun A => ArticleInterpretation M C A S.relations) hS.carrier) hS.interpretation
  have hA : M.IsOrdinal S.large.carrier := Eq.mpr (congrArg M.IsOrdinal hS.carrier) hC.top
  have hSub : M.MemberSubset S.large.carrier C.top := fun x hx => Eq.mp (congrArg (M.mem x) hS.carrier) hx
  have haLarge := h.elementary.carrier_subset a haSmall
  have hs : M.mem V.scope S.context.omega := Eq.mpr (congrArg (M.mem V.scope) hS.omega) hV.scope
  have hParamsLarge := hParams.enlarge h.elementary.carrier_subset
  have hFLarge : Graph M f T.width S.large.carrier :=
    Eq.mpr (congrArg (Graph M f T.width) hS.carrier) (demand_graph_below hM.1 hDemand)
  have hLarge := (KP1Y.ReflectionModel.template_counterexample_iff_d hM hC hD hS.large hS.atomic hT hV hB
    hParamsLarge hA haLarge hSub hs).mpr ⟨f,hFLarge,hDemand,hNone⟩
  have hSmall := (hProgram.reflect_d hS h hParams.graph).mpr hLarge
  obtain ⟨f',hGraph,hDemand',hNone'⟩ := (h.template_counterexample_iff_d hM hC hS hT hV hB ha hParams).mp hSmall
  exact ⟨f',Eq.mp (congrArg (Graph M f' T.width) h.carrier) hGraph,hDemand',hNone'⟩

end KP1Y.ReflectionModel
