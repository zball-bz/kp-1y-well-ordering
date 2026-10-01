import KP1Y.ReflectionTemplateCompilation
import KP1Y.ReflectionLabelingBridge
import KP1Y.ReflectionEdgeBlockTruth
import KP1Y.ReflectionEndpointBlockTruth
import KP1Y.ReflectionBasicHeight
import KP1Y.ReflectionOutputRestriction

/-! 观察 (8) 的纯前缀存在程序：不含 cut 值、输出上界或可容许性原子。 -/
namespace KP1Y.ReflectionModel
open YesMetaZFC YesMetaZFC.SetTheory YesMetaZFC.SetTheory.Definitional
open KP1Y.Kuratowski KP1Y.Functions KP1Y.Assignments KP1Y.Satisfaction KP1Y.Reflection
universe u

def PrefixBody (M : SetTheory.Structure.{u}) (PC : Context M.Domain) (D : RelationalData M.Domain)
    (T : TemplateShape M.Domain) (B : TemplateBlocks M.Domain) (s : M.Domain) : Prop :=
  (((AllAtoms M PC D B.basic.positiveOutputs T.width s ∧
      AllAtoms M PC D B.outputIncreasing.codes B.outputIncreasing.length s) ∧
    AllAtoms M PC D B.outputEdges T.edgeLength s) ∧
    AllAtoms M PC D B.endpoints.outputTop T.needLength s) ∧ AllAtoms M PC D B.prefixCode T.width s

def PrefixExists (M : SetTheory.Structure.{u}) (PC : Context M.Domain) (D : RelationalData M.Domain)
    (T : TemplateShape M.Domain) (V : NameFrame M.Domain) (B : TemplateBlocks M.Domain) (s : M.Domain) : Prop :=
  ∃ t, M.mem t PC.assignments ∧ AgreeOutside M V.outputs T.width s t V.scope PC.carrier ∧ PrefixBody M PC D T B t

def PrefixWitness (M : SetTheory.Structure.{u}) (C : ArticleData M.Domain) (T : TemplateShape M.Domain) (u A g : M.Domain) : Prop :=
  Graph M g T.width A ∧ Representation M C.reflection C.table T.width T.diagram g ∧
    PrefixAgree M C.reflection u g T.cut ∧ End M C.reflection C.table T.template g C.top

structure UniformPrefixProgram (M : SetTheory.Structure.{u}) (PC : Context M.Domain) (D : RelationalData M.Domain)
    (T : TemplateShape M.Domain) (V : NameFrame M.Domain) (B : TemplateBlocks M.Domain) (p length head : M.Domain) : Prop where
  result : FormulaResult M PC D p length head V.scope
  truth : ∀ A Assignments Columns Atom H, EvaluationInstance M PC A Assignments Columns Atom H →
    ∀ s, Graph M s V.scope A →
      (NodeTrue M (PC.withInterpretation A Assignments Columns Atom) H p head s ↔
        PrefixExists M (PC.withInterpretation A Assignments Columns Atom) D T V B s)

theorem uniform_prefix_body_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ArticleData M.Domain} (hC : C.Valid M) {S : ArticleStructure M.Domain} (hS : S.Valid M C)
    {T : TemplateShape M.Domain} (hT : T.Valid M C) {F : M.Domain} {V : NameFrame M.Domain}
    (hV : V.Valid M C F T.width T.edgeLength T.needLength) {K : M.Domain} {B : TemplateBlocks M.Domain}
    (hB : B.Valid M C S.relations T V K) {p length head : M.Domain}
    (hP : FormulaResult M S.context S.relations p length head V.scope) :
    ∃ q length' head', CompiledExtension M S.context S.relations p length V.scope q length' head' ∧
      UniformTemplateResult M S.context S.relations q length' head' V.scope (fun PC s => PrefixBody M PC S.relations T B s) := by
  have hs : M.mem V.scope S.relations.omega := Eq.mpr (congrArg (M.mem V.scope) hS.interpretation.omega) hV.scope
  have nat (n : M.Domain) (hn : M.mem n C.reflection.omega) : M.mem n S.context.omega :=
    Eq.mpr (congrArg (M.mem n) hS.omega) hn
  obtain ⟨p0,l0,j0,h0,hTruth0⟩ := uniform_compile_two_blocks_d hM hS.context hP
    hB.basic.positiveOutputs.graph (nat _ hV.width) hB.outputIncreasing.block.graph (nat _ hB.outputIncreasing.natural)
    hS.link.codes_bound (fun _ _ _ hAt => hB.basic.positiveOutputs.scoped_d hM hC hS.interpretation hs hAt)
    (fun _ _ _ hAt => hB.outputIncreasing.block.scoped_d hM hC hS.interpretation hs hAt)
  have u0 : UniformTemplateResult M S.context S.relations p0 l0 j0 V.scope
      (fun PC s => AllAtoms M PC S.relations B.basic.positiveOutputs T.width s ∧
        AllAtoms M PC S.relations B.outputIncreasing.codes B.outputIncreasing.length s) := ⟨h0.result,hTruth0⟩
  obtain ⟨p1,l1,j1,h1,u1⟩ := u0.conjoin_d hM hS.context hB.outputEdges.graph (nat _ hT.edgeLength) hS.link.codes_bound
    (fun _ _ _ hAt => hB.outputEdges.scoped_d hM hC hS.interpretation hs hAt)
  obtain ⟨p2,l2,j2,h2,u2⟩ := u1.conjoin_d hM hS.context hB.endpoints.outputTop.graph (nat _ hT.needLength) hS.link.codes_bound
    (fun _ _ _ hAt => hB.endpoints.outputTop.scoped_d hM hC hS.interpretation hT hs hAt)
  obtain ⟨p3,l3,j3,h3,u3⟩ := u2.conjoin_d hM hS.context hB.prefixCode.graph (nat _ hV.width) hS.link.codes_bound
    (fun _ _ _ hAt => hB.prefixCode.scoped_d hM hC hS.interpretation hs hAt)
  exact ⟨p3,l3,j3,((h0.trans hM.1 h1).trans hM.1 h2).trans hM.1 h3,u3⟩

theorem uniform_prefix_program_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ArticleData M.Domain} (hC : C.Valid M) {S : ArticleStructure M.Domain} (hS : S.Valid M C)
    {T : TemplateShape M.Domain} (hT : T.Valid M C) {F : M.Domain} {V : NameFrame M.Domain}
    (hV : V.Valid M C F T.width T.edgeLength T.needLength) {K : M.Domain} {B : TemplateBlocks M.Domain}
    (hB : B.Valid M C S.relations T V K) :
    ∃ p length head, UniformPrefixProgram M S.context S.relations T V B p length head := by
  obtain ⟨p0,l0,j0,h0⟩ := basic_seed_exists_d hM hC hS hV hB.basic
  obtain ⟨p1,l1,j1,_,h1⟩ := uniform_prefix_body_d hM hC hS hT hV hB h0
  have hm : M.mem T.width S.context.omega := Eq.mpr (congrArg (M.mem T.width) hS.omega) hV.width
  obtain ⟨p2,l2,j2,h2,hTruth⟩ := uniform_compile_existential_block_d hM hS.context h1.result hV.outputs.graph hm
  refine ⟨p2,l2,j2,h2.result,?_⟩
  intro A Assignments Columns Atom H hI s hs
  apply (hTruth A Assignments Columns Atom H hI s hs).trans
  exact ⟨fun ⟨t,ht,hFrame,hTrue⟩ => ⟨t,ht,hFrame,(h1.truth A Assignments Columns Atom H hI t ht).mp hTrue⟩,
    fun ⟨t,ht,hFrame,hTrue⟩ => ⟨t,ht,hFrame,(h1.truth A Assignments Columns Atom H hI t ht).mpr hTrue⟩⟩

private theorem prefix_body_meaning_iff {M : SetTheory.Structure.{u}} (he : Extensional M)
    {C : ArticleData M.Domain} {PC : Context M.Domain} {D : RelationalData M.Domain} {T : TemplateShape M.Domain} (hT : T.Valid M C)
    {B : TemplateBlocks M.Domain} {A s f g : M.Domain} (hG : Graph M g T.width A) (hSub : M.MemberSubset A C.reflection.cap)
    (hPos : AllAtoms M PC D B.basic.positiveOutputs T.width s ↔ PositiveLabels M C.reflection g T.width A)
    (hInc : AllAtoms M PC D B.outputIncreasing.codes B.outputIncreasing.length s ↔ Increasing M g T.width A)
    (hEdges : AllAtoms M PC D B.outputEdges T.edgeLength s ↔ DiagramEdgeTruth M C T g)
    (hEnd : AllAtoms M PC D B.endpoints.outputTop T.needLength s ↔ End M C.reflection C.table T.template g C.top)
    (hPrefix : AllAtoms M PC D B.prefixCode T.width s ↔ PrefixAgree M C.reflection f g T.cut) :
    PrefixBody M PC D T B s ↔ Representation M C.reflection C.table T.width T.diagram g ∧
      PrefixAgree M C.reflection f g T.cut ∧ End M C.reflection C.table T.template g C.top := by
  have hAll := and_congr (and_congr (and_congr (and_congr hPos hInc) hEdges) hEnd) hPrefix
  have hLabel := labeling_iff_positive_increasing he hT.diagram.1 hG hSub
  constructor
  · intro h
    obtain ⟨⟨⟨hLabels,hEdges'⟩,hEnd'⟩,hPrefix'⟩ := hAll.mp h
    exact ⟨⟨hT.diagram,hLabel.mpr hLabels,hEdges'⟩,hPrefix',hEnd'⟩
  · rintro ⟨hRep,hPrefix',hEnd'⟩
    exact hAll.mpr ⟨⟨⟨hLabel.mp hRep.labeling,hRep.edges⟩,hEnd'⟩,hPrefix'⟩

theorem prefix_body_iff_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory) {C : ArticleData M.Domain} (hC : C.Valid M)
    {A : M.Domain} {D : RelationalData M.Domain} (hD : ArticleInterpretation M C A D) {PC : Context M.Domain}
    (hAtom : AtomicTable M D PC.atomic) {T : TemplateShape M.Domain} (hT : T.Valid M C) {F : M.Domain} {V : NameFrame M.Domain}
    (hV : V.Valid M C F T.width T.edgeLength T.needLength) {K : M.Domain} {B : TemplateBlocks M.Domain} (hB : B.Valid M C D T V K)
    {a θ s f g : M.Domain} (hParams : GroundParameters M C T V a θ A s) (hA : M.IsOrdinal A) (hSub : M.MemberSubset A C.top)
    (hF : TupleValue M f V.inputs s T.width V.scope A) (hG : TupleValue M g V.outputs s T.width V.scope A) :
    PrefixBody M PC D T B s ↔ Representation M C.reflection C.table T.width T.diagram g ∧
      PrefixAgree M C.reflection f g T.cut ∧ End M C.reflection C.table T.template g C.top := by
  have hs : M.mem V.scope D.omega := Eq.mpr (congrArg (M.mem V.scope) hD.omega) hV.scope
  have hCap : M.MemberSubset A C.reflection.cap := fun x hx => hC.reflection.cap.transitive C.top hC.cap.predecessor_mem x (hSub x hx)
  have hCut := ((KP1Y.Naturals.omega_isOrdinal_d hM hC.numerals.omega).mem hV.width).transitive T.cut hT.cut
  exact prefix_body_meaning_iff hM.1 hT hG.values hCap
    ((hB.basic.positiveOutputs.all_atoms_iff_d hM hC hD hAtom hSub hs hParams.graph).trans (hB.basic.positive_outputs_iff hM.1 hV hParams hG))
    (hB.outputIncreasing.all_atoms_iff_d hM hC hD hAtom hV.width hs hA hSub hG)
    (hB.outputEdges.shape_iff_d hM hC hD hAtom hT hParams hSub hs hG)
    (hB.endpoints.output_top_iff_d hM hC hD hAtom hT hParams hSub hs hG)
    (((hB.prefixCode.all_atoms_iff_d hM hC hD hAtom hSub hs hParams.graph).trans
      (prefix_selector_iff hV.inputs.graph hV.outputs.graph hCut hB.prefixRows hF hG)).trans
        (prefix_iff_on_carrier hM.1 hF.values hG.values hCap).symm)

theorem Height.prefix_body_iff_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory) {C : ArticleData M.Domain} (hC : C.Valid M)
    {S : ArticleStructure M.Domain} (hS : S.Valid M C) {δ : M.Domain} {small : EvaluationData M.Domain} (h : Height M C S δ small)
    {T : TemplateShape M.Domain} (hT : T.Valid M C) {F : M.Domain} {V : NameFrame M.Domain}
    (hV : V.Valid M C F T.width T.edgeLength T.needLength) {K : M.Domain} {B : TemplateBlocks M.Domain} (hB : B.Valid M C S.relations T V K)
    {a θ s f g : M.Domain} (hParams : GroundParameters M C T V a θ small.carrier s)
    (hF : TupleValue M f V.inputs s T.width V.scope small.carrier) (hG : TupleValue M g V.outputs s T.width V.scope small.carrier) :
    PrefixBody M (small.context S.context) S.relations T B s ↔ Representation M C.reflection C.table T.width T.diagram g ∧
      PrefixAgree M C.reflection f g T.cut ∧ End M C.reflection C.table T.template g C.top := by
  have hs : M.mem V.scope S.context.omega := Eq.mpr (congrArg (M.mem V.scope) hS.omega) hV.scope
  have hSub : M.MemberSubset small.carrier C.top := fun x hx => Eq.mp (congrArg (M.mem x) hS.carrier) (h.elementary.carrier_subset x hx)
  exact prefix_body_meaning_iff hM.1 hT hG.values
    (fun x hx => hC.reflection.cap.transitive C.top hC.cap.predecessor_mem x (hSub x hx))
    ((h.binary_block_iff_d hM hC hS hs hB.basic.positiveOutputs hParams.graph).trans (hB.basic.positive_outputs_iff hM.1 hV hParams hG))
    (h.increasing_block_iff_d hM hC hS hB.outputIncreasing hV.width hs hG)
    (h.shape_edge_iff_d hM hC hS hT hB.outputEdges hParams hs hG)
    (h.output_top_iff_d hM hC hS hT hB.endpoints hParams hs hG)
    (h.prefix_atoms_iff_d hM hC hS hT hV hB.prefixCode hB.prefixRows hF hG)

private theorem prefix_exists_meaning_iff {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ArticleData M.Domain} (hC : C.Valid M) {PC : Context M.Domain} {D : RelationalData M.Domain}
    {T : TemplateShape M.Domain} {F : M.Domain} {V : NameFrame M.Domain}
    (hV : V.Valid M C F T.width T.edgeLength T.needLength) {B : TemplateBlocks M.Domain} {a θ s f : M.Domain}
    (hParams : GroundParameters M C T V a θ PC.carrier s) (hF : TupleValue M f V.inputs s T.width V.scope PC.carrier)
    (hAssignments : ∀ t, Graph M t V.scope PC.carrier → M.mem t PC.assignments)
    (hBody : ∀ t g, GroundParameters M C T V a θ PC.carrier t →
      TupleValue M f V.inputs t T.width V.scope PC.carrier → TupleValue M g V.outputs t T.width V.scope PC.carrier →
      (PrefixBody M PC D T B t ↔ Representation M C.reflection C.table T.width T.diagram g ∧
        PrefixAgree M C.reflection f g T.cut ∧ End M C.reflection C.table T.template g C.top)) :
    PrefixExists M PC D T V B s ↔ ∃ g, PrefixWitness M C T f PC.carrier g := by
  constructor
  · rintro ⟨t,_,hFrame,hTrue⟩
    have hParamsT := hParams.preserve_family_d hM hC hV 1 (by decide) (by decide) (by decide) hFrame
    have hFT := hF.preserve_outside hFrame (fun _ _ hAt => hV.untouched_d hM hC (i := 0) (j := 1) (by decide) hAt)
    obtain ⟨g,hG⟩ := tuple_value_exists_d hM hV.outputs.graph hFrame.target
    exact ⟨g,hG.values,(hBody t g hParamsT hFT hG).mp hTrue⟩
  · rintro ⟨g,hGraph,hRep,hPrefix,hEnd⟩
    obtain ⟨t,hFrame,hG⟩ := patch_assignment_d hM hParams.graph hV.outputs.graph
      (fun _ _ _ hi hj => hV.outputs.injective hM.1 hV.basis hi hj) hGraph
    have hParamsT := hParams.preserve_family_d hM hC hV 1 (by decide) (by decide) (by decide) hFrame
    have hFT := hF.preserve_outside hFrame (fun _ _ hAt => hV.untouched_d hM hC (i := 0) (j := 1) (by decide) hAt)
    exact ⟨t,hAssignments t hFrame.target,hFrame,(hBody t g hParamsT hFT hG).mpr ⟨hRep,hPrefix,hEnd⟩⟩

theorem prefix_exists_iff_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory) {C : ArticleData M.Domain} (hC : C.Valid M)
    {A : M.Domain} {D : RelationalData M.Domain} (hD : ArticleInterpretation M C A D) {PC : Context M.Domain}
    {Assignments Columns Atom H : M.Domain} (hI : EvaluationInstance M PC A Assignments Columns Atom H)
    (hAtom : AtomicTable M D Atom) {T : TemplateShape M.Domain} (hT : T.Valid M C) {F : M.Domain} {V : NameFrame M.Domain}
    (hV : V.Valid M C F T.width T.edgeLength T.needLength) {K : M.Domain} {B : TemplateBlocks M.Domain} (hB : B.Valid M C D T V K)
    {a θ s f : M.Domain} (hParams : GroundParameters M C T V a θ A s) (hA : M.IsOrdinal A) (hSub : M.MemberSubset A C.top)
    (hs : M.mem V.scope PC.omega) (hF : TupleValue M f V.inputs s T.width V.scope A) :
    PrefixExists M (PC.withInterpretation A Assignments Columns Atom) D T V B s ↔ ∃ g, PrefixWitness M C T f A g :=
  prefix_exists_meaning_iff hM hC hV hParams hF (fun t ht => (hI.assignments_exact t).mpr ⟨V.scope,hs,ht⟩)
    (fun _ _ hPT hFT hGT => prefix_body_iff_d hM hC hD hAtom hT hV hB hPT hA hSub hFT hGT)

theorem Height.prefix_exists_iff_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory) {C : ArticleData M.Domain} (hC : C.Valid M)
    {S : ArticleStructure M.Domain} (hS : S.Valid M C) {δ : M.Domain} {small : EvaluationData M.Domain} (h : Height M C S δ small)
    {T : TemplateShape M.Domain} (hT : T.Valid M C) {F : M.Domain} {V : NameFrame M.Domain}
    (hV : V.Valid M C F T.width T.edgeLength T.needLength) {K : M.Domain} {B : TemplateBlocks M.Domain} (hB : B.Valid M C S.relations T V K)
    {a θ s f : M.Domain} (hParams : GroundParameters M C T V a θ small.carrier s)
    (hF : TupleValue M f V.inputs s T.width V.scope small.carrier) :
    PrefixExists M (small.context S.context) S.relations T V B s ↔ ∃ g, PrefixWitness M C T f small.carrier g := by
  have hs : M.mem V.scope S.context.omega := Eq.mpr (congrArg (M.mem V.scope) hS.omega) hV.scope
  exact prefix_exists_meaning_iff hM hC hV hParams hF (fun t ht => (h.valid.assignments_exact t).mpr ⟨V.scope,hs,ht⟩)
    (fun _ _ hPT hFT hGT => h.prefix_body_iff_d hM hC hS hT hV hB hPT hFT hGT)

theorem UniformPrefixProgram.reflect_d {M : SetTheory.Structure.{u}} {PC : Context M.Domain} {D : RelationalData M.Domain}
    {T : TemplateShape M.Domain} {V : NameFrame M.Domain} {B : TemplateBlocks M.Domain} {p length head : M.Domain}
    (hP : UniformPrefixProgram M PC D T V B p length head) {small large : EvaluationData M.Domain}
    (hSmall : small.Valid PC) (hLarge : large.Valid PC) (hElem : ProgramElementary M PC D small large)
    {s : M.Domain} (hS : Graph M s V.scope small.carrier) :
    PrefixExists M (small.context PC) D T V B s ↔ PrefixExists M (large.context PC) D T V B s :=
  (hP.truth small.carrier small.assignments small.columns small.atomic small.table hSmall s hS).symm.trans
    ((hElem.truth p length head V.scope hP.result s hS).trans
      (hP.truth large.carrier large.assignments large.columns large.atomic large.table hLarge s (hS.mono_values hElem.carrier_subset)))

structure PrefixPadding (M : SetTheory.Structure.{u}) (C : ArticleData M.Domain) (T : TemplateShape M.Domain)
    (f A u : M.Domain) : Prop where
  graph : Graph M u T.width A
  prefixAgreement : PrefixAgree M C.reflection f u T.cut
  zeroTail : ∀ i, M.mem i T.width → ¬M.mem i T.cut → MemPair M u i (C.numbers 0)

theorem prefix_padding_exists_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ArticleData M.Domain} {T : TemplateShape M.Domain} {f A : M.Domain}
    (hF : Graph M f T.width C.reflection.cap) (hSub : M.MemberSubset A C.reflection.cap)
    (hZero : M.mem (C.numbers 0) A)
    (hPrefix : ∀ i x, M.mem i T.cut → MemPair M f i x → M.mem x A) :
    ∃ u, PrefixPadding M C T f A u := by
  obtain ⟨zeroValues,hZeros,hZeroRows⟩ := constant_assignment_d hM T.width C.reflection.cap (hSub _ hZero)
  obtain ⟨u,hU,hRows⟩ := select_name_graph_d hM hF hZeros T.cut
  have hGraph : Graph M u T.width A := graph_tighten_values hU (by
    intro i x hAt
    rcases (hRows i x).mp hAt with ⟨hi,hfi⟩ | ⟨_,hzi⟩
    · exact hPrefix i x hi hfi
    · have hx := hZeros.unique i x (C.numbers 0) hzi (hZeroRows i (hU.bounds hM.1 hAt).1)
      exact hx ▸ hZero)
  refine ⟨u,hGraph,?_,?_⟩
  · intro i hi x _
    exact ⟨fun hfi => (hRows i x).mpr (Or.inl ⟨hi,hfi⟩),fun hui => ((hRows i x).mp hui).elim And.right (fun h => False.elim (h.1 hi))⟩
  · intro i hi hNot
    exact (hRows i (C.numbers 0)).mpr (Or.inr ⟨hNot,hZeroRows i hi⟩)

theorem prefix_parameters_exists_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ArticleData M.Domain} (hC : C.Valid M) {T : TemplateShape M.Domain} (hT : T.Valid M C)
    {F : M.Domain} {V : NameFrame M.Domain} (hV : V.Valid M C F T.width T.edgeLength T.needLength) {f A : M.Domain}
    (hF : Graph M f T.width C.reflection.cap) (hA : M.IsOrdinal A) (hωA : M.mem C.reflection.omega A)
    (hSub : M.MemberSubset A C.reflection.cap)
    (hPrefix : ∀ i x, M.mem i T.cut → MemPair M f i x → M.mem x A) :
    ∃ u s, PrefixPadding M C T f A u ∧ GroundParameters M C T V (C.numbers 0) (C.numbers 0) A s ∧
      TupleValue M u V.inputs s T.width V.scope A := by
  have hZero : M.mem (C.numbers 0) A := hA.transitive C.reflection.omega hωA _ (hC.numerals.natural 0)
  obtain ⟨u,hU⟩ := prefix_padding_exists_d hM hF hSub hZero hPrefix
  obtain ⟨base,hBase⟩ := ground_parameters_exists_d hM hC hT hV hA hωA hZero hZero
  obtain ⟨s,hFrame,hRead⟩ := patch_assignment_d hM hBase.graph hV.inputs.graph
    (fun _ _ _ hi hj => hV.inputs.injective hM.1 hV.basis hi hj) hU.graph
  exact ⟨u,s,hU,hBase.preserve_family_d hM hC hV 0 (by decide) (by decide) (by decide) hFrame,hRead⟩

theorem Height.prefix_parameters_exists_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ArticleData M.Domain} (hC : C.Valid M) {S : ArticleStructure M.Domain} {δ : M.Domain} {small : EvaluationData M.Domain}
    (h : Height M C S δ small) {T : TemplateShape M.Domain} (hT : T.Valid M C) {F : M.Domain} {V : NameFrame M.Domain}
    (hV : V.Valid M C F T.width T.edgeLength T.needLength) {f : M.Domain}
    (hRep : Representation M C.reflection C.table T.width T.diagram f) (hCut : MemPair M f T.cut δ) :
    ∃ u s, PrefixPadding M C T f small.carrier u ∧ GroundParameters M C T V (C.numbers 0) (C.numbers 0) small.carrier s ∧
      TupleValue M u V.inputs s T.width V.scope small.carrier := by
  have hA : M.IsOrdinal small.carrier := Eq.mpr (congrArg M.IsOrdinal h.carrier) h.ordinal
  have hωA : M.mem C.reflection.omega small.carrier := Eq.mpr (congrArg (M.mem C.reflection.omega) h.carrier) h.omega
  have hδCap := hC.reflection.cap.transitive C.top hC.cap.predecessor_mem δ h.below
  have hSub : M.MemberSubset small.carrier C.reflection.cap := by
    intro x hx
    exact hC.reflection.cap.transitive δ hδCap x (Eq.mp (congrArg (M.mem x) h.carrier) hx)
  have hWidth := (KP1Y.Naturals.omega_isOrdinal_d hM hC.numerals.omega).mem hV.width
  exact KP1Y.ReflectionModel.prefix_parameters_exists_d hM hC hT hV hRep.labeling.graph hA hωA hSub (by
    intro i x hi hAt
    have hiW := hWidth.transitive T.cut hT.cut i hi
    have hxδ := hRep.labeling.increasing i hiW T.cut hT.cut hi x (hRep.labeling.graph.bounds hM.1 hAt).2 δ hδCap hAt hCut
    exact Eq.mpr (congrArg (M.mem x) h.carrier) hxδ)

theorem Height.reflect_prefix_witness_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ArticleData M.Domain} (hC : C.Valid M) {S : ArticleStructure M.Domain} (hS : S.Valid M C)
    {δ : M.Domain} {small : EvaluationData M.Domain} (h : Height M C S δ small)
    {T : TemplateShape M.Domain} (hT : T.Valid M C) {F : M.Domain} {V : NameFrame M.Domain}
    (hV : V.Valid M C F T.width T.edgeLength T.needLength) {K : M.Domain} {B : TemplateBlocks M.Domain}
    (hB : B.Valid M C S.relations T V K) {f : M.Domain}
    (hF : Graph M f T.width C.top) (hRep : Representation M C.reflection C.table T.width T.diagram f)
    (hCut : MemPair M f T.cut δ) (hEnd : End M C.reflection C.table T.template f C.top) :
    ∃ g, Graph M g T.width δ ∧ Representation M C.reflection C.table T.width T.diagram g ∧
      PrefixAgree M C.reflection f g T.cut ∧ End M C.reflection C.table T.template g C.top := by
  obtain ⟨u,s,hPadding,hParams,hU⟩ := h.prefix_parameters_exists_d hM hC hT hV hRep hCut
  obtain ⟨p,length,head,hProgram⟩ := uniform_prefix_program_d hM hC hS hT hV hB
  have hD : ArticleInterpretation M C S.large.carrier S.relations :=
    Eq.mpr (congrArg (fun A => ArticleInterpretation M C A S.relations) hS.carrier) hS.interpretation
  have hA : M.IsOrdinal S.large.carrier := Eq.mpr (congrArg M.IsOrdinal hS.carrier) hC.top
  have hSub : M.MemberSubset S.large.carrier C.top := fun x hx => Eq.mp (congrArg (M.mem x) hS.carrier) hx
  have hs : M.mem V.scope S.context.omega := Eq.mpr (congrArg (M.mem V.scope) hS.omega) hV.scope
  have hParamsLarge := hParams.enlarge h.elementary.carrier_subset
  have hULarge := tuple_value_enlarge hM.1 h.elementary.carrier_subset hU
  have hFLarge : Graph M f T.width S.large.carrier := Eq.mpr (congrArg (Graph M f T.width) hS.carrier) hF
  have hWitness : PrefixWitness M C T u S.large.carrier f :=
    ⟨hFLarge,hRep,fun i hi x hx => (hPadding.prefixAgreement i hi x hx).symm,hEnd⟩
  have hLarge := (KP1Y.ReflectionModel.prefix_exists_iff_d hM hC hD hS.large hS.atomic hT hV hB hParamsLarge hA hSub hs hULarge).mpr ⟨f,hWitness⟩
  have hSmall := (hProgram.reflect_d h.valid hS.large h.elementary hParams.graph).mpr hLarge
  obtain ⟨g,hG,hRepG,hPrefix,hEndG⟩ := (h.prefix_exists_iff_d hM hC hS hT hV hB hParams hU).mp hSmall
  exact ⟨g,Eq.mp (congrArg (Graph M g T.width) h.carrier) hG,hRepG,
    fun i hi x hx => (hPadding.prefixAgreement i hi x hx).trans (hPrefix i hi x hx),hEndG⟩

end KP1Y.ReflectionModel
