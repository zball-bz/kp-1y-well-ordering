import KP1Y.OneYCopyInvariant
import KP1Y.OneYExpressionDiagram

/-! 原实际根图中层号<horizon、子列<last的源事实表，稳定过滤且保留重复。 -/
namespace KP1Y.OneYFinite.CopyInvariant
open YesMetaZFC YesMetaZFC.SetTheory YesMetaZFC.SetTheory.Definitional
open KP1Y.Kuratowski KP1Y.Functions KP1Y.Naturals KP1Y.Bounded KP1Y.Ranking KP1Y.Reflection
universe u

def SelectedFact (M : SetTheory.Structure.{u}) (D : Reflection.Data M.Domain) (A horizon last i e : M.Domain) : Prop :=
  MemPair M A i e ∧ ∃ k, M.mem k D.omega ∧ ∃ q, M.mem q D.omega ∧ ∃ p, M.mem p D.omega ∧ ∃ c, M.mem c D.omega ∧
    Quad M D.pairs e k q p c ∧ M.mem k horizon ∧ M.mem c last

def selectedFactFormula {n : Nat} (D : Reflection.Data (Project.Term n)) (A horizon last i e : Project.Term n) : Project.Formula 1 n :=
  .conj (memPairFormula A i e) (Project.Formula.existsMem D.omega (Project.Formula.existsMem D.omega.weaken
    (Project.Formula.existsMem D.omega.weaken.weaken (Project.Formula.existsMem D.omega.weaken.weaken.weaken
      (.conj (quadFormula D.pairs.weaken.weaken.weaken.weaken e.weaken.weaken.weaken.weaken (.bound 3) (.bound 2) (.bound 1) (.bound 0))
        (.conj (.mem (.bound 3) horizon.weaken.weaken.weaken.weaken) (.mem (.bound 0) last.weaken.weaken.weaken.weaken)))))))

theorem selectedFactFormula_delta0 {n : Nat} (D : Reflection.Data (Project.Term n)) (A horizon last i e : Project.Term n) :
    (selectedFactFormula D A horizon last i e).IsDelta0 :=
  .conj (memPairFormula_delta0 _ _ _) (.existsMem _ (.existsMem _ (.existsMem _ (.existsMem _
    (.conj (quadFormula_delta0 _ _ _ _ _ _) (.conj (.mem _ _) (.mem _ _)))))))

theorem selectedFactFormula_freeClosed {n : Nat} {D : Reflection.Data (Project.Term n)} (hD : D.Closed)
    (A horizon last i e : Project.Term n) (hA : A.freeSupport=[]) (hB : horizon.freeSupport=[])
    (hL : last.freeSupport=[]) (hI : i.freeSupport=[]) (hE : e.freeSupport=[]) :
    (selectedFactFormula D A horizon last i e).FreeClosed := by
  simp [selectedFactFormula,Project.Formula.existsMem,Project.Formula.forallMem,Definitional.Formula.FreeClosed,
    memPairFormula,quadFormula,codeFormula,pairFormula,hD.omega,hD.pairs,hA,hB,hL,hI,hE]

theorem selectedFactFormula_iff {M : SetTheory.Structure.{u}} (he : Extensional M) {n : Nat} (env : Env M n)
    (D : Reflection.Data (Project.Term n)) (A horizon last i e : Project.Term n) :
    Project.Formula.satisfies env (selectedFactFormula D A horizon last i e) ↔
      SelectedFact M (D.eval env) (A.eval env) (horizon.eval env) (last.eval env) (i.eval env) (e.eval env) := by
  simp only [selectedFactFormula,SelectedFact,Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_existsMem_iff,
    Project.Formula.satisfies_mem_iff,memPairFormula_iff he,quadFormula_iff he,Term.eval_weaken]
  rfl

private def selectedFactSchema : Project.Delta0BinarySchema 16 where
  body := selectedFactFormula dataTerms.weaken.weaken.weaken.weaken.weaken (.bound 4) (.bound 3) (.bound 2) (.bound 1) (.bound 0)
  freeClosed := by
    have hD : dataTerms.Closed := by constructor <;> rfl
    exact selectedFactFormula_freeClosed hD.weaken.weaken.weaken.weaken.weaken _ _ _ _ _ rfl rfl rfl rfl rfl
  delta0 := selectedFactFormula_delta0 _ _ _ _ _ _

theorem selected_fact_map_exists_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {D : Reflection.Data M.Domain} {A len horizon last : M.Domain} (hA : Graph M A len D.edgeCodes) :
    ∃ P, Filter.PartialGraph M P len D.edgeCodes ∧ ∀ i e, MemPair M P i e ↔ SelectedFact M D A horizon last i e := by
  let env := (((dataEnv D).push A).push horizon).push last
  have hφ (i e : M.Domain) : Project.Formula.satisfies ((env.push i).push e) selectedFactSchema.body ↔ SelectedFact M D A horizon last i e := by
    rw [selectedFactSchema,selectedFactFormula_iff hM.1]
    rfl
  obtain ⟨P,hSupport,hRaw⟩ := relation_comprehension_d hM selectedFactSchema env len D.edgeCodes
  have hRows (i e : M.Domain) : MemPair M P i e ↔ SelectedFact M D A horizon last i e := by
    rw [hRaw i e,hφ]
    exact ⟨fun h => h.2.2,fun h => ⟨(hA.bounds hM.1 h.1).1,(hA.bounds hM.1 h.1).2,h⟩⟩
  exact ⟨P,⟨hSupport,fun i e e' hE hE' => hA.unique i e e' ((hRows i e).mp hE).1 ((hRows i e').mp hE').1⟩,hRows⟩

structure OriginalFacts (M : SetTheory.Structure.{u}) (D : Reflection.Data M.Domain)
    (A horizon last len P size F I : M.Domain) : Prop where
  source : Graph M A len D.edgeCodes
  source_length : M.mem len D.omega
  source_map : Filter.PartialGraph M P len D.edgeCodes
  partial_rows : ∀ i e, MemPair M P i e ↔ SelectedFact M D A horizon last i e
  filtered : Filter.Filtered M D.omega P len D.edgeCodes size F I

theorem original_facts_exists_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {D : Reflection.Data M.Domain} (hD : D.Valid M)
    (hOmega : D.omega=C.omega) {A horizon last : M.Domain} (hA : M.mem A D.edgeLists) :
    ∃ len P size F I, OriginalFacts M D A horizon last len P size F I := by
  obtain ⟨len,hlen,hList⟩ := (hD.edgeLists A).mp hA
  obtain ⟨P,hP,hRows⟩ := selected_fact_map_exists_d hM hList (horizon := horizon) (last := last)
  obtain ⟨size,F,I,hFilter⟩ := Filter.filtered_exists_d hM hC (hOmega ▸ hlen) hP
  exact ⟨len,P,size,F,I,hList,hlen,hP,hRows,by simpa only [hOmega] using hFilter⟩

theorem OriginalFacts.list_mem {M : SetTheory.Structure.{u}} {D : Reflection.Data M.Domain} (hD : D.Valid M)
    {A horizon last len P size F I : M.Domain} (h : OriginalFacts M D A horizon last len P size F I) : M.mem F D.edgeLists :=
  (hD.edgeLists F).mpr ⟨size,h.filtered.length,h.filtered.output⟩

theorem OriginalFacts.edges_iff {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {D : Reflection.Data M.Domain} (hD : D.Valid M) {A horizon last len P size F I k q p c : M.Domain}
    (h : OriginalFacts M D A horizon last len P size F I) :
    EdgeAt M D F k q p c ↔ M.mem k horizon ∧ M.mem c last ∧ EdgeAt M D A k q p c := by
  have hw := omega_isOrdinal_d hM hD.omega
  constructor
  · rintro ⟨j,_,e,he,hAt,hQuad⟩
    obtain ⟨i,hi,hP⟩ := (h.filtered.range_iff hM.1 h.source_map).mp ⟨j,(h.filtered.output.bounds hM.1 hAt).1,hAt⟩
    obtain ⟨hOld,k',_,q',_,p',_,c',_,hQuad',hk,hc⟩ := (h.partial_rows i e).mp hP
    obtain ⟨hkk,hqq,hpp,hcc⟩ := hQuad'.injective hM.1 hQuad
    subst k'; subst q'; subst p'; subst c'
    exact ⟨hk,hc,i,hw.transitive len h.source_length i hi,e,he,hOld,hQuad⟩
  · rintro ⟨hk,hc,i,hi,e,he,hOld,hQuad⟩
    have hb := hQuad.bounds hM.1 hD.pairs
    have hP := (h.partial_rows i e).mpr ⟨hOld,k,hb.1,q,hb.2.1,p,hb.2.2.1,c,hb.2.2.2,hQuad,hk,hc⟩
    obtain ⟨j,hj,_,hAt⟩ := (h.filtered.entry_iff hM.1 h.source_map).mp hP
    exact ⟨j,hw.transitive size h.filtered.length j hj,e,he,hAt,hQuad⟩

theorem OriginalFacts.diagram_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {D : Reflection.Data M.Domain} (hD : D.Valid M) {A horizon last len P size F I m : M.Domain}
    (h : OriginalFacts M D A horizon last len P size F I) (hLast : M.mem last D.omega) (hA : Diagram M D m A) : Diagram M D last F := by
  refine ⟨hLast,h.list_mem hD,?_⟩
  intro k hk q hq p hp c hc hEdge
  obtain ⟨_,hCLast,hOld⟩ := (h.edges_iff hM hD).mp hEdge
  have hShape := hA.2.2 k hk q hq p hp c hc hOld
  exact ⟨hShape.1,hShape.2.1,hCLast⟩

theorem OriginalFacts.unique_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {D : Reflection.Data M.Domain} (hOmega : D.omega=C.omega)
    {A horizon last len P size F I len' P' size' F' I' : M.Domain}
    (h : OriginalFacts M D A horizon last len P size F I) (h' : OriginalFacts M D A horizon last len' P' size' F' I') : F=F' := by
  have hLen := graph_domain_unique hM.1 h.source h'.source
  subst len'
  have hPP := relation_ext hM.1 h.source_map.support h'.source_map.support (fun i e => (h.partial_rows i e).trans (h'.partial_rows i e).symm)
  subst P'
  have hf : Filter.Filtered M C.omega P len D.edgeCodes size F I := by simpa only [hOmega] using h.filtered
  have hf' : Filter.Filtered M C.omega P len D.edgeCodes size' F' I' := by simpa only [hOmega] using h'.filtered
  exact (hf.unique_d hM hC (hOmega ▸ h.source_length) h.source_map hf').2.1

theorem OriginalFacts.truth_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {D : Reflection.Data M.Domain} (hD : D.Valid M) {A horizon last len P size F I H m f : M.Domain}
    (h : OriginalFacts M D A horizon last len P size F I) (hRep : Representation M D H m A f) :
    ∀ k, M.mem k D.omega → ∀ q, M.mem q D.omega → ∀ p, M.mem p D.omega → ∀ c, M.mem c D.omega →
      EdgeAt M D F k q p c → EdgeTruth M D H f k q p c :=
  fun k hk q hq p hp c hc hEdge => hRep.edges k hk q hq p hp c hc ((h.edges_iff hM hD).mp hEdge).2.2

theorem OriginalFacts.actual_edges_iff_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {D : Reflection.Data M.Domain} (hD : D.Valid M) (hOmega : D.omega=C.omega)
    {m : M.Domain} {L : LayerStateSpace M.Domain} {V Q H A horizon last len P size F I k q p c : M.Domain}
    (hLayers : LayerRun M C m L V Q H) (hOriginal : ExpressionDiagram.Enumerated M C T D m L V H A)
    (h : OriginalFacts M D A horizon last len P size F I) :
    EdgeAt M D F k q p c ↔ M.mem k horizon ∧ M.mem c last ∧ ExpressionDiagram.ActualAtom M C m L H k q p c := by
  rw [h.edges_iff hM hD,hOriginal.edges_iff_d hM hC hT hD hOmega hLayers]

theorem actual_copied_facts_exists_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {D : Reflection.Data M.Domain} (hD : D.Valid M) (hOmega : D.omega=C.omega)
    {m : M.Domain} {L : LayerStateSpace M.Domain} {V Q H A horizon b width : M.Domain}
    (hLayers : LayerRun M C m L V Q H) (hOriginal : ExpressionDiagram.Enumerated M C T D m L V H A)
    {X : CopyCoordinates.Context M.Domain} (hX : X.Valid M C) (hb : M.mem b C.omega)
    (hWidth : CopyCoordinates.Width M C T X b width) :
    ∃ len P size Base I Facts, OriginalFacts M D A horizon X.last len P size Base I ∧
      CopiedFacts M C T D X b Base Facts ∧ Diagram M D X.last Base ∧ Diagram M D width Facts := by
  have hDiagram := hOriginal.diagram_d hM hC hT hD hOmega hLayers
  obtain ⟨len,P,size,Base,I,hBase⟩ := original_facts_exists_d (horizon := horizon) (last := X.last) hM hC hD hOmega hDiagram.2.1
  have hBaseDiagram := hBase.diagram_d hM hD (hOmega.symm ▸ hX.last) hDiagram
  obtain ⟨Facts,hFacts,hFactsDiagram⟩ := copied_facts_exists_d hM hC hT hD hOmega hX hb hWidth hBaseDiagram
  exact ⟨len,P,size,Base,I,Facts,hBase,hFacts,hBaseDiagram,hFactsDiagram⟩

theorem actual_copied_facts_edges_iff_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {D : Reflection.Data M.Domain} (hD : D.Valid M) (hOmega : D.omega=C.omega)
    {m : M.Domain} {L : LayerStateSpace M.Domain} {V Q H A horizon len P size Base I b Facts k q p c : M.Domain}
    (hLayers : LayerRun M C m L V Q H) (hOriginal : ExpressionDiagram.Enumerated M C T D m L V H A)
    {X : CopyCoordinates.Context M.Domain} (hBase : OriginalFacts M D A horizon X.last len P size Base I)
    (hFacts : CopiedFacts M C T D X b Base Facts) :
    EdgeAt M D Facts k q p c ↔ ∃ qOld pOld cOld,
      (M.mem k horizon ∧ M.mem cOld X.last ∧ ExpressionDiagram.ActualAtom M C m L H k qOld pOld cOld) ∧
      CopyCoordinates.ParentCopy M C T X b qOld q ∧ CopyCoordinates.ParentCopy M C T X b pOld p ∧ CopyCoordinates.ParentCopy M C T X b cOld c := by
  rw [hFacts.edge_iff hM.1 hOmega]
  simp only [hBase.actual_edges_iff_d hM hC hT hD hOmega hLayers hOriginal]

end KP1Y.OneYFinite.CopyInvariant
