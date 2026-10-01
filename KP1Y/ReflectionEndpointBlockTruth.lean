import KP1Y.ReflectionEndpointBlocks

/-! 三个端点块的精确 End 语义。P 块不需要读取 point 参数；R 块读取实际 a。 -/
namespace KP1Y.ReflectionModel
open YesMetaZFC YesMetaZFC.SetTheory
open KP1Y.Kuratowski KP1Y.Functions KP1Y.Assignments KP1Y.Satisfaction KP1Y.Reflection
universe u

theorem EndpointCode.value_iff_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory) {C : ArticleData M.Domain} (hC : C.Valid M)
    {A : M.Domain} {D : RelationalData M.Domain} (hD : ArticleInterpretation M C A D) {Atom : M.Domain} (hAtom : AtomicTable M D Atom)
    {top : Bool} {scope uk uq up point code s k η a b : M.Domain} (hSub : M.MemberSubset A C.top) (hs : M.mem scope D.omega)
    (hCode : EndpointCode top M C D scope uk uq up point code) (hS : Graph M s scope A)
    (hk : MemPair M s uk k) (hq : MemPair M s uq η) (hp : MemPair M s up a)
    (hPoint : top=false → MemPair M s point b) :
    MemPair M Atom code s ↔ Query M C.reflection.toIndexData C.table k η a (if top then C.top else b) := by
  cases top
  · exact RelationCode.value_iff_d hM hC hD hAtom hSub hs hCode hS hk hq hp (hPoint rfl)
  · exact TopCode.value_iff_d hM hC hD hAtom hSub hs hCode hS hk hq hp

theorem Height.endpoint_value_iff_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory) {C : ArticleData M.Domain} (hC : C.Valid M)
    {S : ArticleStructure M.Domain} (hS : S.Valid M C) {δ : M.Domain} {small : EvaluationData M.Domain} (h : Height M C S δ small)
    {top : Bool} {scope uk uq up point code s k η a b : M.Domain} (hs : M.mem scope S.context.omega)
    (hCode : EndpointCode top M C S.relations scope uk uq up point code) (hAssign : Graph M s scope small.carrier)
    (hk : MemPair M s uk k) (hq : MemPair M s uq η) (hp : MemPair M s up a)
    (hPoint : top=false → MemPair M s point b) :
    MemPair M small.atomic code s ↔ Query M C.reflection.toIndexData C.table k η a (if top then C.top else b) := by
  cases top
  · exact h.relation_value_iff_d hM hC hS hs hCode hAssign hk hq hp (hPoint rfl)
  · exact h.top_value_iff_d hM hC hS hs hCode hAssign hk hq hp

private theorem endpoint_truth_iff {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory) {C : ArticleData M.Domain} (hC : C.Valid M)
    {D : RelationalData M.Domain} {PC : Context M.Domain} {T : TemplateShape M.Domain} (hT : T.Valid M C)
    {V : NameFrame M.Domain} {top : Bool} {names point B A s f b : M.Domain} (hB : EndpointBlock top M C D T V names point B)
    (hF : TupleValue M f names s T.width V.scope A) (hSub : M.MemberSubset A C.reflection.cap)
    (hNeeds : ∀ i k q p, NeedEntry M C.reflection T.template i k q p → ∀ uk, MemPair M V.needLayers i uk → MemPair M s uk k)
    (hEval : ∀ uk uq up code k η a, EndpointCode top M C D V.scope uk uq up point code →
      MemPair M s uk k → MemPair M s uq η → MemPair M s up a →
      (MemPair M PC.atomic code s ↔ Query M C.reflection.toIndexData C.table k η a b)) :
    AllAtoms M PC D B T.needLength s ↔ End M C.reflection C.table T.template f b := by
  constructor
  · intro hAll k _ q _ p _ hNeed η _ a _ hfq hfp
    obtain ⟨i,_,hEntry⟩ := hNeed
    have hi := hT.need_index hM.1 hEntry
    obtain ⟨hqW,hpW⟩ := hT.need_columns_d hM hC hEntry
    obtain ⟨uk,_,hk⟩ := hB.layers.total i hi
    obtain ⟨uq,huq,hq⟩ := hB.nameGraph.total q hqW
    obtain ⟨up,hup,hp⟩ := hB.nameGraph.total p hpW
    obtain ⟨code,_,hAt,hTrue⟩ := hAll i hi
    have hCode := (hB.rows i k q p hEntry uk uq up hk hq hp code).mp hAt
    exact (hEval uk uq up code k η a hCode (hNeeds i k q p hEntry uk hk)
      ((hF.rows q hqW uq huq η (hF.values.bounds hM.1 hfq).2 hq).mp hfq)
      ((hF.rows p hpW up hup a (hF.values.bounds hM.1 hfp).2 hp).mp hfp)).mp hTrue
  · intro hEnd i hi
    obtain ⟨k,q,p,hEntry⟩ := need_entry_exists hC.reflection hT.needs hi
    have hiω := (KP1Y.Naturals.omega_isOrdinal_d hM hC.numerals.omega).transitive T.needLength hT.needLength i hi
    have hNeed := hEntry.occurs hiω
    obtain ⟨hkω,hqω,hpω⟩ := hNeed.bounds hM.1 hC.reflection
    obtain ⟨hqW,hpW⟩ := hT.need_columns_d hM hC hEntry
    obtain ⟨uk,_,hk⟩ := hB.layers.total i hi
    obtain ⟨uq,huq,hq⟩ := hB.nameGraph.total q hqW
    obtain ⟨up,hup,hp⟩ := hB.nameGraph.total p hpW
    obtain ⟨η,hη,hfq⟩ := hF.values.total q hqW
    obtain ⟨a,ha,hfp⟩ := hF.values.total p hpW
    obtain ⟨code,hCodeMem,hAt⟩ := hB.graph.total i hi
    have hCode := (hB.rows i k q p hEntry uk uq up hk hq hp code).mp hAt
    exact ⟨code,hCodeMem,hAt,(hEval uk uq up code k η a hCode (hNeeds i k q p hEntry uk hk)
      ((hF.rows q hqW uq huq η hη hq).mp hfq) ((hF.rows p hpW up hup a ha hp).mp hfp)).mpr
        (hEnd k hkω q hqω p hpω hNeed η (hSub η hη) a (hSub a ha) hfq hfp)⟩

theorem EndpointBlock.all_atoms_iff_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory) {C : ArticleData M.Domain} (hC : C.Valid M)
    {A : M.Domain} {D : RelationalData M.Domain} (hD : ArticleInterpretation M C A D) {PC : Context M.Domain}
    (hAtom : AtomicTable M D PC.atomic) {T : TemplateShape M.Domain} (hT : T.Valid M C)
    {V : NameFrame M.Domain} {top : Bool} {names point B s f b : M.Domain} (hSub : M.MemberSubset A C.top)
    (hs : M.mem V.scope D.omega) (hB : EndpointBlock top M C D T V names point B)
    (hF : TupleValue M f names s T.width V.scope A)
    (hNeeds : ∀ i k q p, NeedEntry M C.reflection T.template i k q p → ∀ uk, MemPair M V.needLayers i uk → MemPair M s uk k)
    (hPoint : top=false → MemPair M s point b) :
    AllAtoms M PC D B T.needLength s ↔ End M C.reflection C.table T.template f (if top then C.top else b) :=
  endpoint_truth_iff hM hC hT hB hF (fun x hx => hC.reflection.cap.transitive C.top hC.cap.predecessor_mem x (hSub x hx)) hNeeds
    (fun _ _ _ _ _ _ _ hCode hk hq hp => hCode.value_iff_d hM hC hD hAtom hSub hs hF.source hk hq hp hPoint)

theorem Height.endpoint_block_iff_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory) {C : ArticleData M.Domain} (hC : C.Valid M)
    {S : ArticleStructure M.Domain} (hS : S.Valid M C) {δ : M.Domain} {small : EvaluationData M.Domain} (h : Height M C S δ small)
    {T : TemplateShape M.Domain} (hT : T.Valid M C) {V : NameFrame M.Domain} {top : Bool} {names point B s f b : M.Domain}
    (hs : M.mem V.scope S.context.omega) (hB : EndpointBlock top M C S.relations T V names point B)
    (hF : TupleValue M f names s T.width V.scope small.carrier)
    (hNeeds : ∀ i k q p, NeedEntry M C.reflection T.template i k q p → ∀ uk, MemPair M V.needLayers i uk → MemPair M s uk k)
    (hPoint : top=false → MemPair M s point b) :
    AllAtoms M (small.context S.context) S.relations B T.needLength s ↔
      End M C.reflection C.table T.template f (if top then C.top else b) := by
  have hSub : M.MemberSubset small.carrier C.top := by
    intro z hz
    exact Eq.mp (congrArg (M.mem z) hS.carrier) (h.elementary.carrier_subset z hz)
  exact endpoint_truth_iff hM hC hT hB hF
    (fun x hx => hC.reflection.cap.transitive C.top hC.cap.predecessor_mem x (hSub x hx)) hNeeds
    (fun _ _ _ _ _ _ _ hCode hk hq hp => h.endpoint_value_iff_d hM hC hS hs hCode hF.source hk hq hp hPoint)

theorem EndpointBlocks.Valid.input_top_iff_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory) {C : ArticleData M.Domain} (hC : C.Valid M)
    {A : M.Domain} {D : RelationalData M.Domain} (hD : ArticleInterpretation M C A D) {PC : Context M.Domain}
    (hAtom : AtomicTable M D PC.atomic) {T : TemplateShape M.Domain} (hT : T.Valid M C) {V : NameFrame M.Domain}
    {B : EndpointBlocks M.Domain} (hB : B.Valid M C D T V) {a θ s f : M.Domain} (hParams : GroundParameters M C T V a θ A s)
    (hSub : M.MemberSubset A C.top) (hs : M.mem V.scope D.omega) (hF : TupleValue M f V.inputs s T.width V.scope A) :
    AllAtoms M PC D B.inputTop T.needLength s ↔ End M C.reflection C.table T.template f C.top :=
  hB.inputTop.all_atoms_iff_d (b := a) hM hC hD hAtom hT hSub hs hF hParams.needs (by intro he; cases he)

theorem EndpointBlocks.Valid.output_relation_iff_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory) {C : ArticleData M.Domain} (hC : C.Valid M)
    {A : M.Domain} {D : RelationalData M.Domain} (hD : ArticleInterpretation M C A D) {PC : Context M.Domain}
    (hAtom : AtomicTable M D PC.atomic) {T : TemplateShape M.Domain} (hT : T.Valid M C) {V : NameFrame M.Domain}
    {B : EndpointBlocks M.Domain} (hB : B.Valid M C D T V) {a θ s g : M.Domain} (hParams : GroundParameters M C T V a θ A s)
    (hSub : M.MemberSubset A C.top) (hs : M.mem V.scope D.omega) (hG : TupleValue M g V.outputs s T.width V.scope A) :
    AllAtoms M PC D B.outputRelation T.needLength s ↔ End M C.reflection C.table T.template g a :=
  hB.outputRelation.all_atoms_iff_d hM hC hD hAtom hT hSub hs hG hParams.needs (fun _ => hParams.point B.pointName hB.pointName)

theorem EndpointBlocks.Valid.output_top_iff_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory) {C : ArticleData M.Domain} (hC : C.Valid M)
    {A : M.Domain} {D : RelationalData M.Domain} (hD : ArticleInterpretation M C A D) {PC : Context M.Domain}
    (hAtom : AtomicTable M D PC.atomic) {T : TemplateShape M.Domain} (hT : T.Valid M C) {V : NameFrame M.Domain}
    {B : EndpointBlocks M.Domain} (hB : B.Valid M C D T V) {a θ s g : M.Domain} (hParams : GroundParameters M C T V a θ A s)
    (hSub : M.MemberSubset A C.top) (hs : M.mem V.scope D.omega) (hG : TupleValue M g V.outputs s T.width V.scope A) :
    AllAtoms M PC D B.outputTop T.needLength s ↔ End M C.reflection C.table T.template g C.top :=
  hB.outputTop.all_atoms_iff_d (b := a) hM hC hD hAtom hT hSub hs hG hParams.needs (by intro he; cases he)

theorem Height.input_top_iff_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory) {C : ArticleData M.Domain} (hC : C.Valid M)
    {S : ArticleStructure M.Domain} (hS : S.Valid M C) {δ : M.Domain} {small : EvaluationData M.Domain} (h : Height M C S δ small)
    {T : TemplateShape M.Domain} (hT : T.Valid M C) {V : NameFrame M.Domain}
    {B : EndpointBlocks M.Domain} (hB : B.Valid M C S.relations T V)
    {a θ s f : M.Domain} (hParams : GroundParameters M C T V a θ small.carrier s)
    (hs : M.mem V.scope S.context.omega) (hF : TupleValue M f V.inputs s T.width V.scope small.carrier) :
    AllAtoms M (small.context S.context) S.relations B.inputTop T.needLength s ↔ End M C.reflection C.table T.template f C.top :=
  h.endpoint_block_iff_d (b := a) hM hC hS hT hs hB.inputTop hF hParams.needs (by intro he; cases he)

theorem Height.output_relation_iff_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory) {C : ArticleData M.Domain} (hC : C.Valid M)
    {S : ArticleStructure M.Domain} (hS : S.Valid M C) {δ : M.Domain} {small : EvaluationData M.Domain} (h : Height M C S δ small)
    {T : TemplateShape M.Domain} (hT : T.Valid M C) {V : NameFrame M.Domain}
    {B : EndpointBlocks M.Domain} (hB : B.Valid M C S.relations T V)
    {a θ s g : M.Domain} (hParams : GroundParameters M C T V a θ small.carrier s)
    (hs : M.mem V.scope S.context.omega) (hG : TupleValue M g V.outputs s T.width V.scope small.carrier) :
    AllAtoms M (small.context S.context) S.relations B.outputRelation T.needLength s ↔ End M C.reflection C.table T.template g a :=
  h.endpoint_block_iff_d hM hC hS hT hs hB.outputRelation hG hParams.needs (fun _ => hParams.point B.pointName hB.pointName)

theorem Height.output_top_iff_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory) {C : ArticleData M.Domain} (hC : C.Valid M)
    {S : ArticleStructure M.Domain} (hS : S.Valid M C) {δ : M.Domain} {small : EvaluationData M.Domain} (h : Height M C S δ small)
    {T : TemplateShape M.Domain} (hT : T.Valid M C) {V : NameFrame M.Domain}
    {B : EndpointBlocks M.Domain} (hB : B.Valid M C S.relations T V)
    {a θ s g : M.Domain} (hParams : GroundParameters M C T V a θ small.carrier s)
    (hs : M.mem V.scope S.context.omega) (hG : TupleValue M g V.outputs s T.width V.scope small.carrier) :
    AllAtoms M (small.context S.context) S.relations B.outputTop T.needLength s ↔ End M C.reflection C.table T.template g C.top :=
  h.endpoint_block_iff_d (b := a) hM hC hS hT hs hB.outputTop hG hParams.needs (by intro he; cases he)

end KP1Y.ReflectionModel
