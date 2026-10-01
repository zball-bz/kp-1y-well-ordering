import KP1Y.ReflectionBasicCompilation
import KP1Y.ReflectionIncreasingBlock
import KP1Y.ReflectionEdgeBlocks
import KP1Y.ReflectionEndpointBlocks
import KP1Y.ReflectionAdmissionBlock
import KP1Y.ReflectionPrefixBlock

/-! 固定图形的完整输入/输出原子块及同一程序代码的统一编译。 -/
namespace KP1Y.ReflectionModel
open YesMetaZFC YesMetaZFC.SetTheory
open KP1Y.Kuratowski KP1Y.Functions KP1Y.Satisfaction
universe u

structure TemplateBlocks (α : Type u) where
  basic : BasicBlocks α
  inputIncreasing : IncreasingBlock α
  outputIncreasing : IncreasingBlock α
  inputEdges : α
  outputEdges : α
  endpoints : EndpointBlocks α
  rootName : α
  admission : α
  prefixSelector : α
  prefixCode : α

structure TemplateBlocks.Valid (M : SetTheory.Structure.{u}) (C : ArticleData M.Domain) (D : RelationalData M.Domain)
    (T : TemplateShape M.Domain) (V : NameFrame M.Domain) (K : M.Domain) (B : TemplateBlocks M.Domain) : Prop where
  basic : B.basic.Valid M C D T V
  inputIncreasing : B.inputIncreasing.Valid M C D V.inputs T.width V.scope
  outputIncreasing : B.outputIncreasing.Valid M C D V.outputs T.width V.scope
  inputEdges : EdgeBlock M C D T V.scope V.inputs V.edgeLayers B.inputEdges
  outputEdges : EdgeBlock M C D T V.scope V.outputs V.edgeLayers B.outputEdges
  endpoints : B.endpoints.Valid M C D T V
  rootName : MemPair M V.scalars (C.numbers 2) B.rootName
  admission : AdmissionBlock M C D T K V.scope V.inputs B.rootName B.admission
  prefixCode : BinaryBlock M C D false V.scope T.width V.outputs B.prefixSelector B.prefixCode
  prefixRows : ∀ i v, MemPair M B.prefixSelector i v ↔
    (M.mem i T.cut ∧ MemPair M V.inputs i v) ∨ (¬M.mem i T.cut ∧ MemPair M V.outputs i v)

theorem template_blocks_exists_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ArticleData M.Domain} (hC : C.Valid M) {A : M.Domain} {D : RelationalData M.Domain}
    (hD : ArticleInterpretation M C A D) {T : TemplateShape M.Domain} (hT : T.Valid M C)
    {F : M.Domain} {V : NameFrame M.Domain} (hV : V.Valid M C F T.width T.edgeLength T.needLength) (K : M.Domain) :
    ∃ B, TemplateBlocks.Valid M C D T V K B := by
  obtain ⟨basic,hBasic⟩ := basic_blocks_exists_d hM hC hD hT hV
  obtain ⟨BI,BO,hBI,hBO⟩ := shape_increasing_blocks_exists_d hM hC hD hT hV
  obtain ⟨EI,EO,hEI,hEO⟩ := shape_edge_blocks_exists_d hM hC hD hT hV
  obtain ⟨ends,hEnds⟩ := endpoint_blocks_exists_d hM hC hD hT hV
  obtain ⟨root,adm,hRoot,hAdm⟩ := shape_admission_block_exists_d hM hC hD hT hV K
  obtain ⟨Z,P,hP,hZ⟩ := prefix_block_exists_d hM hC hD hV
  exact ⟨⟨basic,BI,BO,EI,EO,ends,root,adm,Z,P⟩,hBasic,hBI,hBO,hEI,hEO,hEnds,hRoot,hAdm,hP,hZ⟩

def InputTemplate (M : SetTheory.Structure.{u}) (C : ArticleData M.Domain) (PC : Context M.Domain)
    (D : RelationalData M.Domain) (T : TemplateShape M.Domain) (B : TemplateBlocks M.Domain) (s : M.Domain) : Prop :=
  (((InputBasic M C PC D T B.basic s ∧ AllAtoms M PC D B.inputIncreasing.codes B.inputIncreasing.length s) ∧
    AllAtoms M PC D B.inputEdges T.edgeLength s) ∧ AllAtoms M PC D B.endpoints.inputTop T.needLength s) ∧
      AllAtoms M PC D B.admission T.needLength s

def OutputTemplate (M : SetTheory.Structure.{u}) (PC : Context M.Domain)
    (D : RelationalData M.Domain) (T : TemplateShape M.Domain) (B : TemplateBlocks M.Domain) (s : M.Domain) : Prop :=
  (((OutputBasic M PC D T B.basic s ∧ AllAtoms M PC D B.outputIncreasing.codes B.outputIncreasing.length s) ∧
    AllAtoms M PC D B.outputEdges T.edgeLength s) ∧ AllAtoms M PC D B.endpoints.outputRelation T.needLength s) ∧
      AllAtoms M PC D B.prefixCode T.width s

structure UniformTemplateResult (M : SetTheory.Structure.{u}) (PC : Context M.Domain) (D : RelationalData M.Domain)
    (p length head scope : M.Domain) (meaning : Context M.Domain → M.Domain → Prop) : Prop where
  result : FormulaResult M PC D p length head scope
  truth : ∀ A Assignments Columns Atom H, EvaluationInstance M PC A Assignments Columns Atom H →
    ∀ s, M.mem s Assignments → (NodeTrue M (PC.withInterpretation A Assignments Columns Atom) H p head s ↔
      meaning (PC.withInterpretation A Assignments Columns Atom) s)

theorem UniformTemplateResult.conjoin_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {PC : Context M.Domain} (hPC : ContextSpaces M PC) {D : RelationalData M.Domain}
    {p length head scope B n : M.Domain} {meaning : Context M.Domain → M.Domain → Prop}
    (h : UniformTemplateResult M PC D p length head scope meaning)
    (hB : Graph M B n D.codes) (hn : M.mem n PC.omega) (hCodes : M.MemberSubset D.codes PC.operands)
    (hScoped : ∀ i, M.mem i n → ∀ code, MemPair M B i code → ScopedAtom M D code scope) :
    ∃ q length' head', CompiledExtension M PC D p length scope q length' head' ∧
      UniformTemplateResult M PC D q length' head' scope (fun C s => meaning C s ∧ AllAtoms M C D B n s) := by
  obtain ⟨q,length',head',hQ,hTruth⟩ := uniform_conjoin_block_d hM hPC h.result hB hn hCodes hScoped
  refine ⟨q,length',head',hQ,hQ.result,?_⟩
  intro A Assignments Columns Atom H hI s hs
  exact (hTruth A Assignments Columns Atom H hI s hs).trans
    (and_congr (h.truth A Assignments Columns Atom H hI s hs) Iff.rfl)

theorem uniform_input_template_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ArticleData M.Domain} (hC : C.Valid M) {S : ArticleStructure M.Domain} (hS : S.Valid M C)
    {T : TemplateShape M.Domain} (hT : T.Valid M C) {F : M.Domain} {V : NameFrame M.Domain}
    (hV : V.Valid M C F T.width T.edgeLength T.needLength) {K : M.Domain} {B : TemplateBlocks M.Domain}
    (hB : B.Valid M C S.relations T V K) {p length head : M.Domain}
    (hP : FormulaResult M S.context S.relations p length head V.scope) :
    ∃ q length' head', CompiledExtension M S.context S.relations p length V.scope q length' head' ∧
      UniformTemplateResult M S.context S.relations q length' head' V.scope (fun PC s => InputTemplate M C PC S.relations T B s) := by
  have hs : M.mem V.scope S.relations.omega := Eq.mpr (congrArg (M.mem V.scope) hS.interpretation.omega) hV.scope
  have nat (n : M.Domain) (hn : M.mem n C.reflection.omega) : M.mem n S.context.omega :=
    Eq.mpr (congrArg (M.mem n) hS.omega) hn
  obtain ⟨p0,l0,j0,h0,hTruth0⟩ := uniform_basic_input_d hM hC hS hV hB.basic hP
  have u0 : UniformTemplateResult M S.context S.relations p0 l0 j0 V.scope
      (fun PC s => InputBasic M C PC S.relations T B.basic s) := ⟨h0.result,hTruth0⟩
  obtain ⟨p1,l1,j1,h1,u1⟩ := u0.conjoin_d hM hS.context hB.inputIncreasing.block.graph
    (nat _ hB.inputIncreasing.natural) hS.link.codes_bound
    (fun _ _ _ hAt => hB.inputIncreasing.block.scoped_d hM hC hS.interpretation hs hAt)
  obtain ⟨p2,l2,j2,h2,u2⟩ := u1.conjoin_d hM hS.context hB.inputEdges.graph (nat _ hT.edgeLength) hS.link.codes_bound
    (fun _ _ _ hAt => hB.inputEdges.scoped_d hM hC hS.interpretation hs hAt)
  obtain ⟨p3,l3,j3,h3,u3⟩ := u2.conjoin_d hM hS.context hB.endpoints.inputTop.graph (nat _ hT.needLength) hS.link.codes_bound
    (fun _ _ _ hAt => hB.endpoints.inputTop.scoped_d hM hC hS.interpretation hT hs hAt)
  obtain ⟨p4,l4,j4,h4,u4⟩ := u3.conjoin_d hM hS.context hB.admission.graph (nat _ hT.needLength) hS.link.codes_bound
    (fun _ _ _ hAt => hB.admission.scoped_d hM hC hS.interpretation hT hs hV.inputs.graph hAt)
  exact ⟨p4,l4,j4,(((h0.trans hM.1 h1).trans hM.1 h2).trans hM.1 h3).trans hM.1 h4,u4⟩

theorem uniform_output_template_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ArticleData M.Domain} (hC : C.Valid M) {S : ArticleStructure M.Domain} (hS : S.Valid M C)
    {T : TemplateShape M.Domain} (hT : T.Valid M C) {F : M.Domain} {V : NameFrame M.Domain}
    (hV : V.Valid M C F T.width T.edgeLength T.needLength) {K : M.Domain} {B : TemplateBlocks M.Domain}
    (hB : B.Valid M C S.relations T V K) {p length head : M.Domain}
    (hP : FormulaResult M S.context S.relations p length head V.scope) :
    ∃ q length' head', CompiledExtension M S.context S.relations p length V.scope q length' head' ∧
      UniformTemplateResult M S.context S.relations q length' head' V.scope (fun PC s => OutputTemplate M PC S.relations T B s) := by
  have hs : M.mem V.scope S.relations.omega := Eq.mpr (congrArg (M.mem V.scope) hS.interpretation.omega) hV.scope
  have nat (n : M.Domain) (hn : M.mem n C.reflection.omega) : M.mem n S.context.omega :=
    Eq.mpr (congrArg (M.mem n) hS.omega) hn
  obtain ⟨p0,l0,j0,h0,hTruth0⟩ := uniform_basic_output_d hM hC hS hV hB.basic hP
  have u0 : UniformTemplateResult M S.context S.relations p0 l0 j0 V.scope
      (fun PC s => OutputBasic M PC S.relations T B.basic s) := ⟨h0.result,hTruth0⟩
  obtain ⟨p1,l1,j1,h1,u1⟩ := u0.conjoin_d hM hS.context hB.outputIncreasing.block.graph
    (nat _ hB.outputIncreasing.natural) hS.link.codes_bound
    (fun _ _ _ hAt => hB.outputIncreasing.block.scoped_d hM hC hS.interpretation hs hAt)
  obtain ⟨p2,l2,j2,h2,u2⟩ := u1.conjoin_d hM hS.context hB.outputEdges.graph (nat _ hT.edgeLength) hS.link.codes_bound
    (fun _ _ _ hAt => hB.outputEdges.scoped_d hM hC hS.interpretation hs hAt)
  obtain ⟨p3,l3,j3,h3,u3⟩ := u2.conjoin_d hM hS.context hB.endpoints.outputRelation.graph (nat _ hT.needLength) hS.link.codes_bound
    (fun _ _ _ hAt => hB.endpoints.outputRelation.scoped_d hM hC hS.interpretation hT hs hAt)
  obtain ⟨p4,l4,j4,h4,u4⟩ := u3.conjoin_d hM hS.context hB.prefixCode.graph (nat _ hV.width) hS.link.codes_bound
    (fun _ _ _ hAt => hB.prefixCode.scoped_d hM hC hS.interpretation hs hAt)
  exact ⟨p4,l4,j4,(((h0.trans hM.1 h1).trans hM.1 h2).trans hM.1 h3).trans hM.1 h4,u4⟩

end KP1Y.ReflectionModel
