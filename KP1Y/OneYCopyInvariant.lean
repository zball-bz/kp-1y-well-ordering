import KP1Y.OneYAtomTransport
import KP1Y.OneYCopyCoordinates
import KP1Y.OneYFiniteFilter
import KP1Y.ReflectionRow
import KP1Y.ReflectionEndpoints

/-! 复制所需的实际源事实与端点模板：逐位置平移，以及原末列父边的稳定筛选。 -/
namespace KP1Y.OneYFinite.CopyInvariant
open YesMetaZFC YesMetaZFC.SetTheory YesMetaZFC.SetTheory.Definitional
open KP1Y.Kuratowski KP1Y.Functions KP1Y.Naturals KP1Y.Bounded KP1Y.Ranking
open KP1Y.Reflection KP1Y.OneYFinite.CopyCoordinates
universe u

structure CopyColumns (M : SetTheory.Structure.{u}) (E : ExpressionData M.Domain) (T : MatrixArithmetic M.Domain)
    (X : Context M.Domain) (b J : M.Domain) : Prop where
  embedding : ColumnEmbedding M E.omega E.omega J
  rows : ∀ p target, MemPair M J p target ↔ ParentCopy M E T X b p target

theorem copy_columns_exists_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {E : ExpressionData M.Domain} (hE : E.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M E)
    {X : Context M.Domain} (hX : X.Valid M E) {b : M.Domain} (hb : M.mem b E.omega) : ∃ J, CopyColumns M E T X b J := by
  obtain ⟨J,hJ,hRows⟩ := parent_copy_graph_exists_d hM hE hT hX hb
  exact ⟨J,hJ,hRows⟩

theorem CopyColumns.unique {M : SetTheory.Structure.{u}} (he : Extensional M)
    {E : ExpressionData M.Domain} {T : MatrixArithmetic M.Domain} {X : Context M.Domain} {b J K : M.Domain}
    (hJ : CopyColumns M E T X b J) (hK : CopyColumns M E T X b K) : J=K :=
  hJ.embedding.graph.ext he hK.embedding.graph (fun p _ q => (hJ.rows p q).trans (hK.rows p q).symm)

theorem CopyColumns.range_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {E : ExpressionData M.Domain} (hE : E.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M E)
    {X : Context M.Domain} (hX : X.Valid M E) {b J width p q : M.Domain}
    (hJ : CopyColumns M E T X b J) (hWidth : Width M E T X b width) (hp : M.mem p X.last) (hAt : MemPair M J p q) : M.mem q width :=
  parent_copy_below_encode_d hM hE hT hX hX.below hp ((hJ.rows p q).mp hAt) hWidth

theorem width_natural {M : SetTheory.Structure.{u}} (he : Extensional M)
    {E : ExpressionData M.Domain} {T : MatrixArithmetic M.Domain} (hT : T.Valid M E)
    {X : Context M.Domain} {b width : M.Domain} (h : Width M E T X b width) : M.mem width E.omega := by
  obtain ⟨_,_,_,_,_,hAdd⟩ := h
  exact (hAdd.bounds he hT.add).2.2

def CopiedFacts (M : SetTheory.Structure.{u}) (E : ExpressionData M.Domain) (T : MatrixArithmetic M.Domain)
    (D : Reflection.Data M.Domain) (X : Context M.Domain) (b A B : M.Domain) : Prop :=
  ∃ J len, CopyColumns M E T X b J ∧ EdgeListTransport M D J len A B

def CopiedTemplates (M : SetTheory.Structure.{u}) (E : ExpressionData M.Domain) (T : MatrixArithmetic M.Domain)
    (D : Reflection.Data M.Domain) (X : Context M.Domain) (b A B : M.Domain) : Prop :=
  ∃ J len, CopyColumns M E T X b J ∧ NeedListTransport M D J len A B

theorem copied_facts_exists_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {E : ExpressionData M.Domain} (hE : E.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M E)
    {D : Reflection.Data M.Domain} (hD : D.Valid M) (hOmega : D.omega=E.omega)
    {X : Context M.Domain} (hX : X.Valid M E) {b A width : M.Domain} (hb : M.mem b E.omega)
    (hWidth : Width M E T X b width) (hA : Diagram M D X.last A) :
    ∃ B, CopiedFacts M E T D X b A B ∧ Diagram M D width B := by
  obtain ⟨J,hJ⟩ := copy_columns_exists_d hM hE hT hX hb
  have hJD : ColumnEmbedding M D.omega D.omega J := by simpa only [hOmega] using hJ.embedding
  obtain ⟨len,B,hB⟩ := edge_list_transport_exists_d hM hD hJD.graph hA.2.1
  exact ⟨B,⟨J,len,hJ,hB⟩,hB.diagram_d hM hD hJD (hOmega.symm ▸ width_natural hM.1 hT hWidth)
    (fun p hp q hAt => hJ.range_d hM hE hT hX hWidth hp hAt) hA⟩

theorem copied_templates_exists_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {E : ExpressionData M.Domain} (hE : E.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M E)
    {D : Reflection.Data M.Domain} (hD : D.Valid M) (hOmega : D.omega=E.omega)
    {X : Context M.Domain} (hX : X.Valid M E) {b A width : M.Domain} (hb : M.mem b E.omega)
    (hWidth : Width M E T X b width) (hA : Template M D X.last A) :
    ∃ B, CopiedTemplates M E T D X b A B ∧ Template M D width B := by
  obtain ⟨J,hJ⟩ := copy_columns_exists_d hM hE hT hX hb
  have hJD : ColumnEmbedding M D.omega D.omega J := by simpa only [hOmega] using hJ.embedding
  obtain ⟨len,B,hB⟩ := need_list_transport_exists_d hM hD hJD.graph hA.2.1
  exact ⟨B,⟨J,len,hJ,hB⟩,hB.template_d hM hD hJD (hOmega.symm ▸ width_natural hM.1 hT hWidth)
    (fun p hp q hAt => hJ.range_d hM hE hT hX hWidth hp hAt) hA⟩

theorem CopiedFacts.unique {M : SetTheory.Structure.{u}} (he : Extensional M)
    {E : ExpressionData M.Domain} {T : MatrixArithmetic M.Domain} {D : Reflection.Data M.Domain}
    {X : Context M.Domain} {b A B B' : M.Domain} (h : CopiedFacts M E T D X b A B) (h' : CopiedFacts M E T D X b A B') : B=B' := by
  obtain ⟨J,len,hJ,hB⟩ := h
  obtain ⟨J',len',hJ',hB'⟩ := h'
  have hJJ := hJ.unique he hJ'
  subst J'
  exact hB.unique he hB'

theorem CopiedTemplates.unique {M : SetTheory.Structure.{u}} (he : Extensional M)
    {E : ExpressionData M.Domain} {T : MatrixArithmetic M.Domain} {D : Reflection.Data M.Domain}
    {X : Context M.Domain} {b A B B' : M.Domain} (h : CopiedTemplates M E T D X b A B) (h' : CopiedTemplates M E T D X b A B') : B=B' := by
  obtain ⟨J,len,hJ,hB⟩ := h
  obtain ⟨J',len',hJ',hB'⟩ := h'
  have hJJ := hJ.unique he hJ'
  subst J'
  exact hB.unique he hB'

theorem CopiedFacts.edge_iff {M : SetTheory.Structure.{u}} (he : Extensional M)
    {E : ExpressionData M.Domain} {T : MatrixArithmetic M.Domain} {D : Reflection.Data M.Domain} (hOmega : D.omega=E.omega)
    {X : Context M.Domain} {b A B k q' p' c' : M.Domain} (h : CopiedFacts M E T D X b A B) :
    EdgeAt M D B k q' p' c' ↔ ∃ q p c, EdgeAt M D A k q p c ∧
      ParentCopy M E T X b q q' ∧ ParentCopy M E T X b p p' ∧ ParentCopy M E T X b c c' := by
  obtain ⟨J,len,hJ,hB⟩ := h
  have hJD : Graph M J D.omega D.omega := by simpa only [hOmega] using hJ.embedding.graph
  simpa only [hJ.rows] using (hB.edge_iff he hJD (k := k) (a := q') (b := p') (d := c'))

theorem CopiedTemplates.need_iff {M : SetTheory.Structure.{u}} (he : Extensional M)
    {E : ExpressionData M.Domain} {T : MatrixArithmetic M.Domain} {D : Reflection.Data M.Domain} (hOmega : D.omega=E.omega)
    {X : Context M.Domain} {b A B k q' p' : M.Domain} (h : CopiedTemplates M E T D X b A B) :
    NeedAt M D B k q' p' ↔ ∃ q p, NeedAt M D A k q p ∧ ParentCopy M E T X b q q' ∧ ParentCopy M E T X b p p' := by
  obtain ⟨J,len,hJ,hB⟩ := h
  have hJD : Graph M J D.omega D.omega := by simpa only [hOmega] using hJ.embedding.graph
  simpa only [hJ.rows] using (hB.need_iff he hJD (k := k) (a := q') (b := p'))

/-- 对原边表稳定过滤“层号<horizon且child=last”，投影为(k,root,parent)，保留重复及位置。 -/
def LastNeed (M : SetTheory.Structure.{u}) (D : Reflection.Data M.Domain) (A horizon last i need : M.Domain) : Prop :=
  ∃ k, M.mem k D.omega ∧ ∃ q, M.mem q D.omega ∧ ∃ p, M.mem p D.omega ∧
    M.mem k horizon ∧ EdgeEntry M D A i k q p last ∧ Packet M need k q p

def lastNeedFormula {n : Nat} (D : Reflection.Data (Project.Term n)) (A horizon last i need : Project.Term n) : Project.Formula 1 n :=
  Project.Formula.existsMem D.omega (Project.Formula.existsMem D.omega.weaken (Project.Formula.existsMem D.omega.weaken.weaken
    (.conj (.mem (.bound 2) horizon.weaken.weaken.weaken)
      (.conj (edgeEntryFormula D.weaken.weaken.weaken A.weaken.weaken.weaken i.weaken.weaken.weaken
        (.bound 2) (.bound 1) (.bound 0) last.weaken.weaken.weaken)
        (packetFormula need.weaken.weaken.weaken (.bound 2) (.bound 1) (.bound 0))))))

theorem lastNeedFormula_delta0 {n : Nat} (D : Reflection.Data (Project.Term n)) (A horizon last i need : Project.Term n) :
    (lastNeedFormula D A horizon last i need).IsDelta0 := .existsMem _ (.existsMem _ (.existsMem _
      (.conj (.mem _ _) (.conj (edgeEntryFormula_delta0 _ _ _ _ _ _ _) (packetFormula_delta0 _ _ _ _)))))

theorem lastNeedFormula_freeClosed {n : Nat} {D : Reflection.Data (Project.Term n)} (hD : D.Closed)
    (A horizon last i need : Project.Term n) (hA : A.freeSupport=[]) (hH : horizon.freeSupport=[])
    (hL : last.freeSupport=[]) (hI : i.freeSupport=[]) (hN : need.freeSupport=[]) :
    (lastNeedFormula D A horizon last i need).FreeClosed := by
  have hEdge := edgeEntryFormula_freeClosed hD.weaken.weaken.weaken A.weaken.weaken.weaken i.weaken.weaken.weaken
    (.bound 2) (.bound 1) (.bound 0) last.weaken.weaken.weaken (by simpa using hA) (by simpa using hI) rfl rfl rfl (by simpa using hL)
  simp [lastNeedFormula,packetFormula,codeFormula,pairFormula,Project.Formula.existsMem,Project.Formula.forallMem,
    Definitional.Formula.FreeClosed,hD.omega,hH,hN,hEdge]

theorem lastNeedFormula_iff {M : SetTheory.Structure.{u}} (he : Extensional M) {n : Nat} (env : Env M n)
    (D : Reflection.Data (Project.Term n)) (A horizon last i need : Project.Term n) :
    Project.Formula.satisfies env (lastNeedFormula D A horizon last i need) ↔
      LastNeed M (D.eval env) (A.eval env) (horizon.eval env) (last.eval env) (i.eval env) (need.eval env) := by
  simp only [lastNeedFormula,LastNeed,Project.Formula.satisfies_existsMem_iff,Project.Formula.satisfies_conj_iff,
    Project.Formula.satisfies_mem_iff,edgeEntryFormula_iff he,packetFormula_iff he,Reflection.Data.eval_weaken,Term.eval_weaken]
  rfl

theorem LastNeed.unique {M : SetTheory.Structure.{u}} (he : Extensional M)
    {D : Reflection.Data M.Domain} {A horizon last len i e e' : M.Domain} (hA : Graph M A len D.edgeCodes)
    (h : LastNeed M D A horizon last i e) (h' : LastNeed M D A horizon last i e') : e=e' := by
  obtain ⟨k,_,q,_,p,_,_,hEdge,hPacket⟩ := h
  obtain ⟨k',_,q',_,p',_,_,hEdge',hPacket'⟩ := h'
  obtain ⟨hk,hq,hp,_⟩ := hEdge.unique he hA hEdge'
  subst k'; subst q'; subst p'
  exact hPacket.unique he hPacket'

private def lastNeedSchema : Project.Delta0BinarySchema 16 where
  body := lastNeedFormula dataTerms.weaken.weaken.weaken.weaken.weaken (.bound 4) (.bound 3) (.bound 2) (.bound 1) (.bound 0)
  freeClosed := by
    have hD : dataTerms.Closed := by constructor <;> rfl
    exact lastNeedFormula_freeClosed hD.weaken.weaken.weaken.weaken.weaken _ _ _ _ _ rfl rfl rfl rfl rfl
  delta0 := lastNeedFormula_delta0 _ _ _ _ _ _

theorem last_need_partial_graph_exists_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {D : Reflection.Data M.Domain} (hD : D.Valid M) {A len horizon last : M.Domain} (hA : Graph M A len D.edgeCodes) :
    ∃ P, Filter.PartialGraph M P len D.needCodes ∧ ∀ i e, MemPair M P i e ↔ LastNeed M D A horizon last i e := by
  let env := (((dataEnv D).push A).push horizon).push last
  have hφ (i e : M.Domain) : Project.Formula.satisfies ((env.push i).push e) lastNeedSchema.body ↔ LastNeed M D A horizon last i e := by
    rw [lastNeedSchema,lastNeedFormula_iff hM.1]
    rfl
  obtain ⟨P,hSupport,hRaw⟩ := relation_comprehension_d hM lastNeedSchema env len D.needCodes
  have hRows (i e : M.Domain) : MemPair M P i e ↔ LastNeed M D A horizon last i e := by
    rw [hRaw i e,hφ]
    constructor
    · exact fun h => h.2.2
    · rintro h
      have hAll := h
      obtain ⟨k,hk,q,hq,p,hp,_,⟨code,_,hAt,_⟩,hPacket⟩ := h
      exact ⟨(hA.bounds hM.1 hAt).1,packet_mem_need_codes hD hk hq hp hPacket,hAll⟩
  exact ⟨P,⟨hSupport,fun i e e' hE hE' => ((hRows i e).mp hE).unique hM.1 hA ((hRows i e').mp hE')⟩,hRows⟩

structure OriginalTemplates (M : SetTheory.Structure.{u}) (D : Reflection.Data M.Domain)
    (A horizon last len P size N I : M.Domain) : Prop where
  source : Graph M A len D.edgeCodes
  source_length : M.mem len D.omega
  source_map : Filter.PartialGraph M P len D.needCodes
  partial_rows : ∀ i e, MemPair M P i e ↔ LastNeed M D A horizon last i e
  filtered : Filter.Filtered M D.omega P len D.needCodes size N I

theorem original_templates_exists_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {E : ExpressionData M.Domain} (hE : E.Valid M) {D : Reflection.Data M.Domain} (hD : D.Valid M)
    (hOmega : D.omega=E.omega) {A horizon last : M.Domain} (hA : M.mem A D.edgeLists) :
    ∃ len P size N I, OriginalTemplates M D A horizon last len P size N I := by
  obtain ⟨len,hlen,hList⟩ := (hD.edgeLists A).mp hA
  obtain ⟨P,hP,hRows⟩ := last_need_partial_graph_exists_d hM hD hList (horizon := horizon) (last := last)
  obtain ⟨size,N,I,hFilter⟩ := Filter.filtered_exists_d hM hE (hOmega ▸ hlen) hP
  exact ⟨len,P,size,N,I,hList,hlen,hP,hRows,by simpa only [hOmega] using hFilter⟩

theorem OriginalTemplates.list_mem {M : SetTheory.Structure.{u}} {D : Reflection.Data M.Domain} (hD : D.Valid M)
    {A horizon last len P size N I : M.Domain} (h : OriginalTemplates M D A horizon last len P size N I) : M.mem N D.needLists :=
  (hD.needLists N).mpr ⟨size,h.filtered.length,h.filtered.output⟩

theorem OriginalTemplates.need_iff {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {D : Reflection.Data M.Domain} (hD : D.Valid M) {A horizon last len P size N I k q p : M.Domain}
    (h : OriginalTemplates M D A horizon last len P size N I) :
    NeedAt M D N k q p ↔ M.mem k horizon ∧ EdgeAt M D A k q p last := by
  have hw := omega_isOrdinal_d hM hD.omega
  constructor
  · rintro ⟨j,_,e,he,hAt,hPacket⟩
    obtain ⟨i,hi,hIndex⟩ := h.filtered.indices.total j (h.filtered.output.bounds hM.1 hAt).1
    have hP := (h.filtered.values j (h.filtered.output.bounds hM.1 hAt).1 i hi hIndex e he).mp hAt
    obtain ⟨k',_,q',_,p',_,hk,hEdge,hPacket'⟩ := (h.partial_rows i e).mp hP
    obtain ⟨hkk,hqq,hpp⟩ := hPacket'.injective hM.1 hPacket
    subst k'; subst q'; subst p'
    exact ⟨hk,⟨i,hw.transitive len h.source_length i hi,hEdge⟩⟩
  · rintro ⟨hk,⟨i,hi,hEdge⟩⟩
    have hBounds := (EdgeEntry.occurs (C := D) hi hEdge).bounds hM.1 hD
    obtain ⟨e,he,hPacket⟩ := need_code_exists_d hM hD hBounds.1 hBounds.2.1 hBounds.2.2.1
    have hP := (h.partial_rows i e).mpr ⟨k,hBounds.1,q,hBounds.2.1,p,hBounds.2.2.1,hk,hEdge,hPacket⟩
    obtain ⟨j,hj,_,hAt⟩ := (h.filtered.entry_iff hM.1 h.source_map).mp hP
    exact ⟨j,hw.transitive size h.filtered.length j hj,e,he,hAt,hPacket⟩

theorem OriginalTemplates.template_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {D : Reflection.Data M.Domain} (hD : D.Valid M) {A horizon last len P size N I m : M.Domain}
    (h : OriginalTemplates M D A horizon last len P size N I) (hLast : M.mem last D.omega)
    (hA : Diagram M D m A) : Template M D last N := by
  refine ⟨hLast,h.list_mem hD,?_⟩
  intro k _ q _ p _ hNeed
  have hEdge := ((h.need_iff hM hD).mp hNeed).2
  have hCols := hA.edge_columns_d hM hD hEdge
  exact ⟨hCols.2.2.2.1,hCols.2.2.2.2⟩

/-- 原末列有标签β时，真实末列模板自动在β成立。 -/
theorem OriginalTemplates.end_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {D : Reflection.Data M.Domain} (hD : D.Valid M) {A horizon last len P size N I H m f beta : M.Domain}
    (h : OriginalTemplates M D A horizon last len P size N I) (hRep : Representation M D H m A f)
    (hLast : MemPair M f last beta) : End M D H N f beta := by
  intro k hk q hq p hp hNeed η hη a ha hQ hP
  have hEdge := ((h.need_iff hM hD).mp hNeed).2
  have hLastNat := (hEdge.bounds hM.1 hD).2.2.2
  exact hRep.edges k hk q hq p hp last hLastNat hEdge η hη a ha beta
    (hRep.labeling.graph.bounds hM.1 hLast).2 hQ hP hLast

def LabelsAlong (M : SetTheory.Structure.{u}) (bound J f g : M.Domain) : Prop :=
  ∀ i, M.mem i bound → ∀ target, MemPair M J i target → ∀ a, MemPair M g target a ↔ MemPair M f i a

theorem EdgeListTransport.truth_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {D : Reflection.Data M.Domain} (hD : D.Valid M) {J len A B m H f g : M.Domain}
    (hJ : Graph M J D.omega D.omega) (h : EdgeListTransport M D J len A B)
    (hRep : Representation M D H m A f) (hAlong : LabelsAlong M m J f g) :
    ∀ k q p c, EdgeAt M D B k q p c → EdgeTruth M D H g k q p c := by
  intro k q p c hEdge η hη a ha b hb hQ hP hC
  obtain ⟨q',p',c',hOld,hJQ,hJP,hJC⟩ := (h.edge_iff hM.1 hJ).mp hEdge
  have hCols := hRep.diagram.edge_columns_d hM hD hOld
  have hBounds := hOld.bounds hM.1 hD
  exact hRep.edges k hBounds.1 q' hBounds.2.1 p' hBounds.2.2.1 c' hBounds.2.2.2 hOld η hη a ha b hb
    ((hAlong q' hCols.1 q hJQ η).mp hQ)
    ((hAlong p' hCols.2.1 p hJP a).mp hP)
    ((hAlong c' hCols.2.2.1 c hJC b).mp hC)

theorem NeedListTransport.end_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {D : Reflection.Data M.Domain} (hD : D.Valid M) {J len A B m H f g beta : M.Domain}
    (hJ : Graph M J D.omega D.omega) (h : NeedListTransport M D J len A B)
    (hTemplate : Template M D m A) (hEnd : End M D H A f beta) (hAlong : LabelsAlong M m J f g) : End M D H B g beta := by
  intro k _ q _ p _ hNeed η hη a ha hQ hP
  obtain ⟨q',p',hOld,hJQ,hJP⟩ := (h.need_iff hM.1 hJ).mp hNeed
  have hCols := hTemplate.need_columns_d hM hD hOld
  have hBounds := hOld.bounds hM.1 hD
  exact hEnd k hBounds.1 q' hBounds.2.1 p' hBounds.2.2 hOld η hη a ha
    ((hAlong q' hCols.1 q hJQ η).mp hQ) ((hAlong p' hCols.2.1 p hJP a).mp hP)

end KP1Y.OneYFinite.CopyInvariant
