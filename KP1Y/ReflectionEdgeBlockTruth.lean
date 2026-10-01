import KP1Y.ReflectionEdgeBlocks
import KP1Y.ReflectionRelationCodeTruth

/-! 内部图边代码块的精确真值；所有内部 ω 中的层号均保留，无当前层 K 的限制。 -/
namespace KP1Y.ReflectionModel
open YesMetaZFC YesMetaZFC.SetTheory
open KP1Y.Kuratowski KP1Y.Functions KP1Y.Assignments KP1Y.Satisfaction KP1Y.Reflection
universe u

def DiagramEdgeTruth (M : SetTheory.Structure.{u}) (C : ArticleData M.Domain) (T : TemplateShape M.Domain) (f : M.Domain) : Prop :=
  ∀ k, M.mem k C.reflection.omega → ∀ q, M.mem q C.reflection.omega → ∀ p, M.mem p C.reflection.omega →
    ∀ j, M.mem j C.reflection.omega → EdgeAt M C.reflection T.diagram k q p j →
      EdgeTruth M C.reflection C.table f k q p j

theorem diagram_edge_truth_iff_representation {M : SetTheory.Structure.{u}} {C : ArticleData M.Domain}
    {T : TemplateShape M.Domain} (hT : T.Valid M C) {f : M.Domain} (hLabel : Labeling M C.reflection T.width f) :
    DiagramEdgeTruth M C T f ↔ Representation M C.reflection C.table T.width T.diagram f :=
  ⟨fun h => ⟨hT.diagram,hLabel,h⟩,fun h => h.edges⟩

private theorem edge_truth_iff {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory) {C : ArticleData M.Domain} (hC : C.Valid M)
    {D : RelationalData M.Domain} {PC : Context M.Domain} {T : TemplateShape M.Domain} (hT : T.Valid M C)
    {scope names layers B A s f : M.Domain} (hB : EdgeBlock M C D T scope names layers B)
    (hF : TupleValue M f names s T.width scope A) (hSub : M.MemberSubset A C.reflection.cap)
    (hLayers : ∀ i k q p j, EdgeEntry M C.reflection T.diagram i k q p j → ∀ uk, MemPair M layers i uk → MemPair M s uk k)
    (hEval : ∀ uk uq up uj code k η a b,
      RelationCode M (C.numbers 0) (C.numbers 1) (C.numbers 2) (C.numbers 3) (C.numbers 4) D.variables scope uk uq up uj code →
        MemPair M s uk k → MemPair M s uq η → MemPair M s up a → MemPair M s uj b →
          (MemPair M PC.atomic code s ↔ Query M C.reflection.toIndexData C.table k η a b)) :
    AllAtoms M PC D B T.edgeLength s ↔ DiagramEdgeTruth M C T f := by
  constructor
  · intro hAll k _ q _ p _ j _ hEdge η _ a _ b _ hfq hfp hfj
    obtain ⟨i,_,hEntry⟩ := hEdge
    have hi := hT.edge_index hM.1 hEntry
    obtain ⟨hqW,hpW,hjW⟩ := hT.edge_columns_d hM hC hEntry
    obtain ⟨code,_,hAt,hTrue⟩ := hAll i hi
    obtain ⟨uk,_,uq,huq,up,hup,uj,huj,hL,hQ,hP,hJ,hCode⟩ := hB.at_entry_d hM hT hAt hEntry
    exact (hEval uk uq up uj code k η a b hCode (hLayers i k q p j hEntry uk hL)
      ((hF.rows q hqW uq huq η (hF.values.bounds hM.1 hfq).2 hQ).mp hfq)
      ((hF.rows p hpW up hup a (hF.values.bounds hM.1 hfp).2 hP).mp hfp)
      ((hF.rows j hjW uj huj b (hF.values.bounds hM.1 hfj).2 hJ).mp hfj)).mp hTrue
  · intro hEdges i hi
    obtain ⟨k,q,p,j,hEntry⟩ := edge_entry_exists hC.reflection hT.edges hi
    have hiω := (KP1Y.Naturals.omega_isOrdinal_d hM hC.numerals.omega).transitive T.edgeLength hT.edgeLength i hi
    have hEdge := hEntry.occurs hiω
    obtain ⟨hkω,hqω,hpω,hjω⟩ := hEdge.bounds hM.1 hC.reflection
    obtain ⟨hqW,hpW,hjW⟩ := hT.edge_columns_d hM hC hEntry
    obtain ⟨code,hCodeMem,hAt⟩ := hB.graph.total i hi
    obtain ⟨uk,_,uq,huq,up,hup,uj,huj,hL,hQ,hP,hJ,hCode⟩ := hB.at_entry_d hM hT hAt hEntry
    obtain ⟨η,hη,hfq⟩ := hF.values.total q hqW
    obtain ⟨a,ha,hfp⟩ := hF.values.total p hpW
    obtain ⟨b,hb,hfj⟩ := hF.values.total j hjW
    exact ⟨code,hCodeMem,hAt,(hEval uk uq up uj code k η a b hCode (hLayers i k q p j hEntry uk hL)
      ((hF.rows q hqW uq huq η hη hQ).mp hfq) ((hF.rows p hpW up hup a ha hP).mp hfp)
      ((hF.rows j hjW uj huj b hb hJ).mp hfj)).mpr
        (hEdges k hkω q hqω p hpω j hjω hEdge η (hSub η hη) a (hSub a ha) b (hSub b hb) hfq hfp hfj)⟩

theorem EdgeBlock.all_atoms_iff_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory) {C : ArticleData M.Domain} (hC : C.Valid M)
    {A : M.Domain} {D : RelationalData M.Domain} (hD : ArticleInterpretation M C A D) {PC : Context M.Domain}
    (hAtom : AtomicTable M D PC.atomic) {T : TemplateShape M.Domain} (hT : T.Valid M C)
    {scope names layers B s f : M.Domain} (hSub : M.MemberSubset A C.top) (hs : M.mem scope D.omega)
    (hB : EdgeBlock M C D T scope names layers B) (hF : TupleValue M f names s T.width scope A)
    (hLayers : ∀ i k q p j, EdgeEntry M C.reflection T.diagram i k q p j → ∀ uk, MemPair M layers i uk → MemPair M s uk k) :
    AllAtoms M PC D B T.edgeLength s ↔ DiagramEdgeTruth M C T f :=
  edge_truth_iff hM hC hT hB hF (fun x hx => hC.reflection.cap.transitive C.top hC.cap.predecessor_mem x (hSub x hx)) hLayers
    (fun _ _ _ _ _ _ _ _ _ hCode hk hq hp hj => hCode.value_iff_d hM hC hD hAtom hSub hs hF.source hk hq hp hj)

theorem Height.edge_block_iff_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory) {C : ArticleData M.Domain} (hC : C.Valid M)
    {S : ArticleStructure M.Domain} (hS : S.Valid M C) {δ : M.Domain} {small : EvaluationData M.Domain} (h : Height M C S δ small)
    {T : TemplateShape M.Domain} (hT : T.Valid M C) {scope names layers B s f : M.Domain}
    (hs : M.mem scope S.context.omega) (hB : EdgeBlock M C S.relations T scope names layers B)
    (hF : TupleValue M f names s T.width scope small.carrier)
    (hLayers : ∀ i k q p j, EdgeEntry M C.reflection T.diagram i k q p j → ∀ uk, MemPair M layers i uk → MemPair M s uk k) :
    AllAtoms M (small.context S.context) S.relations B T.edgeLength s ↔ DiagramEdgeTruth M C T f := by
  have hSub : M.MemberSubset small.carrier C.top := by
    intro z hz
    exact Eq.mp (congrArg (M.mem z) hS.carrier) (h.elementary.carrier_subset z hz)
  exact edge_truth_iff hM hC hT hB hF
    (fun x hx => hC.reflection.cap.transitive C.top hC.cap.predecessor_mem x (hSub x hx)) hLayers
    (fun _ _ _ _ _ _ _ _ _ hCode hk hq hp hj => h.relation_value_iff_d hM hC hS hs hCode hF.source hk hq hp hj)

theorem EdgeBlock.shape_iff_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory) {C : ArticleData M.Domain} (hC : C.Valid M)
    {A : M.Domain} {D : RelationalData M.Domain} (hD : ArticleInterpretation M C A D) {PC : Context M.Domain}
    (hAtom : AtomicTable M D PC.atomic) {T : TemplateShape M.Domain} (hT : T.Valid M C) {V : NameFrame M.Domain}
    {names B a θ s f : M.Domain} (hB : EdgeBlock M C D T V.scope names V.edgeLayers B)
    (hParams : GroundParameters M C T V a θ A s) (hSub : M.MemberSubset A C.top) (hs : M.mem V.scope D.omega)
    (hF : TupleValue M f names s T.width V.scope A) :
    AllAtoms M PC D B T.edgeLength s ↔ DiagramEdgeTruth M C T f :=
  hB.all_atoms_iff_d hM hC hD hAtom hT hSub hs hF hParams.edges

theorem Height.shape_edge_iff_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory) {C : ArticleData M.Domain} (hC : C.Valid M)
    {S : ArticleStructure M.Domain} (hS : S.Valid M C) {δ : M.Domain} {small : EvaluationData M.Domain} (h : Height M C S δ small)
    {T : TemplateShape M.Domain} (hT : T.Valid M C) {V : NameFrame M.Domain}
    {names B a θ s f : M.Domain} (hB : EdgeBlock M C S.relations T V.scope names V.edgeLayers B)
    (hParams : GroundParameters M C T V a θ small.carrier s) (hs : M.mem V.scope S.context.omega)
    (hF : TupleValue M f names s T.width V.scope small.carrier) :
    AllAtoms M (small.context S.context) S.relations B T.edgeLength s ↔ DiagramEdgeTruth M C T f :=
  h.edge_block_iff_d hM hC hS hT hs hB hF hParams.edges

end KP1Y.ReflectionModel
