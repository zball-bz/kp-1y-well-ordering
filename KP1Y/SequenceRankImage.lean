import KP1Y.RankedSequenceSpace

/-! 给定载域排名后，序列逐项映像的精确有界验证与唯一性。 -/
namespace KP1Y.Ranking
open YesMetaZFC YesMetaZFC.SetTheory YesMetaZFC.SetTheory.Definitional
open KP1Y.Kuratowski KP1Y.Functions KP1Y.Assignments
universe u

def sequenceRankPointFormula {n : Nat} (ω FA A θ s t : Project.Term n) : Project.Formula 1 n :=
  Project.Formula.existsMem ω (tupleValueFormula t.weaken s.weaken FA.weaken (.bound 0) A.weaken θ.weaken)

theorem sequenceRankPointFormula_delta0 {n : Nat} (ω FA A θ s t : Project.Term n) :
    (sequenceRankPointFormula ω FA A θ s t).IsDelta0 := .existsMem _ (tupleValueFormula_delta0 _ _ _ _ _ _)

theorem sequenceRankPointFormula_iff {M : SetTheory.Structure.{u}} (he : Extensional M) {n : Nat}
    (e : Env M n) (ω FA A θ s t : Project.Term n) :
    Project.Formula.satisfies e (sequenceRankPointFormula ω FA A θ s t) ↔
      ∃ i, M.mem i (ω.eval e) ∧ TupleValue M (t.eval e) (s.eval e) (FA.eval e) i (A.eval e) (θ.eval e) := by
  simp only [sequenceRankPointFormula,Project.Formula.satisfies_existsMem_iff,tupleValueFormula_iff he,Term.eval_weaken]
  rfl

structure SequenceRankImage (M : SetTheory.Structure.{u}) (ω FA A θ Words OrdWords G : M.Domain) : Prop where
  graph : Graph M G Words OrdWords
  rows : ∀ s, M.mem s Words → ∀ t, M.mem t OrdWords → MemPair M G s t →
    ∃ n, M.mem n ω ∧ TupleValue M t s FA n A θ

def sequenceRankImageFormula {n : Nat} (ω FA A θ Words OrdWords G : Project.Term n) : Project.Formula 1 n :=
  .conj (graphFormula G Words OrdWords)
    (Project.Formula.forallMem Words (Project.Formula.forallMem OrdWords.weaken
      (.imp (memPairFormula G.weaken.weaken (.bound 1) (.bound 0))
        (sequenceRankPointFormula ω.weaken.weaken FA.weaken.weaken A.weaken.weaken θ.weaken.weaken (.bound 1) (.bound 0)))))

theorem sequenceRankImageFormula_delta0 {n : Nat} (ω FA A θ Words OrdWords G : Project.Term n) :
    (sequenceRankImageFormula ω FA A θ Words OrdWords G).IsDelta0 :=
  .conj (graphFormula_delta0 _ _ _) (.forallMem _ (.forallMem _ (.imp (memPairFormula_delta0 _ _ _)
    (sequenceRankPointFormula_delta0 _ _ _ _ _ _))))

theorem sequenceRankImageFormula_freeClosed {n : Nat} (ω FA A θ Words OrdWords G : Project.Term n)
    (hω : ω.freeSupport=[]) (hFA : FA.freeSupport=[]) (hA : A.freeSupport=[]) (hθ : θ.freeSupport=[])
    (hWords : Words.freeSupport=[]) (hOrdWords : OrdWords.freeSupport=[]) (hG : G.freeSupport=[]) :
    (sequenceRankImageFormula ω FA A θ Words OrdWords G).FreeClosed := by
  simp [sequenceRankImageFormula,sequenceRankPointFormula,tupleValueFormula,graphFormula,memPairFormula,codeFormula,pairFormula,
    Project.Formula.forallMem,Project.Formula.existsMem,Definitional.Formula.FreeClosed,hω,hFA,hA,hθ,hWords,hOrdWords,hG]

theorem sequenceRankImageFormula_iff {M : SetTheory.Structure.{u}} (he : Extensional M) {n : Nat}
    (e : Env M n) (ω FA A θ Words OrdWords G : Project.Term n) :
    Project.Formula.satisfies e (sequenceRankImageFormula ω FA A θ Words OrdWords G) ↔
      SequenceRankImage M (ω.eval e) (FA.eval e) (A.eval e) (θ.eval e) (Words.eval e) (OrdWords.eval e) (G.eval e) := by
  simp only [sequenceRankImageFormula,Project.Formula.satisfies_conj_iff,graphFormula_iff he,
    Project.Formula.satisfies_forallMem_iff,Project.Formula.satisfies_imp_iff,memPairFormula_iff he,
    sequenceRankPointFormula_iff he,Term.eval_weaken]
  exact ⟨fun h => ⟨h.1,h.2⟩,fun h => ⟨h.graph,h.rows⟩⟩

private def pointSchema : Project.Delta0BinarySchema 4 where
  body := sequenceRankPointFormula (.bound 2) (.bound 3) (.bound 4) (.bound 5) (.bound 1) (.bound 0)
  freeClosed := by
    simp [sequenceRankPointFormula,tupleValueFormula,graphFormula,memPairFormula,codeFormula,pairFormula,
      Project.Formula.forallMem,Project.Formula.existsMem,Definitional.Formula.FreeClosed]
  delta0 := sequenceRankPointFormula_delta0 _ _ _ _ _ _

theorem sequence_rank_image_exists_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {ω FA A θ Words OrdWords : M.Domain} (hFA : Graph M FA A θ)
    (hWords : ∀ s, M.mem s Words ↔ ∃ n, M.mem n ω ∧ Graph M s n A)
    (hOrdWords : ∀ t, M.mem t OrdWords ↔ ∃ n, M.mem n ω ∧ Graph M t n θ) :
    ∃ G, SequenceRankImage M ω FA A θ Words OrdWords G := by
  obtain ⟨G,hSupport,hRaw⟩ := relation_comprehension_d hM pointSchema ((((oneEnv θ).push A).push FA).push ω) Words OrdWords
  have hPoint (s t : M.Domain) :
      Project.Formula.satisfies ((((((oneEnv θ).push A).push FA).push ω).push s).push t) pointSchema.body ↔
        ∃ n, M.mem n ω ∧ TupleValue M t s FA n A θ := by
    rw [pointSchema,sequenceRankPointFormula_iff hM.1]
    rfl
  have hRows (s t : M.Domain) : MemPair M G s t ↔ M.mem s Words ∧ M.mem t OrdWords ∧
      ∃ n, M.mem n ω ∧ TupleValue M t s FA n A θ := by
    simpa only [hPoint] using hRaw s t
  refine ⟨G,⟨hSupport,?_,?_⟩,fun s _ t _ h => ((hRows s t).mp h).2.2⟩
  · intro s hs
    obtain ⟨n,hn,hS⟩ := (hWords s).mp hs
    obtain ⟨t,hT⟩ := tuple_value_exists_d hM hS hFA
    have ht := (hOrdWords t).mpr ⟨n,hn,hT.values⟩
    exact ⟨t,ht,(hRows s t).mpr ⟨hs,ht,n,hn,hT⟩⟩
  · intro s t t' hst hst'
    obtain ⟨_,_,n,_,hT⟩ := (hRows s t).mp hst
    obtain ⟨_,_,n',_,hT'⟩ := (hRows s t').mp hst'
    have hnn' := domain_unique hM.1 hT.variables hT'.variables
    subst n'
    exact tuple_value_unique hM.1 hT hT'

theorem SequenceRankImage.unique {M : SetTheory.Structure.{u}} (he : Extensional M)
    {ω FA A θ Words OrdWords G G' : M.Domain} (h : SequenceRankImage M ω FA A θ Words OrdWords G)
    (h' : SequenceRankImage M ω FA A θ Words OrdWords G') : G=G' := by
  apply h.graph.ext he h'.graph
  intro s hs t
  obtain ⟨v,hv,hvAt⟩ := h.graph.total s hs
  obtain ⟨v',hv',hvAt'⟩ := h'.graph.total s hs
  obtain ⟨n,_,hV⟩ := h.rows s hs v hv hvAt
  obtain ⟨n',_,hV'⟩ := h'.rows s hs v' hv' hvAt'
  have hnn' := domain_unique he hV.variables hV'.variables
  subst n'
  have hvv' := tuple_value_unique he hV hV'
  subst v'
  constructor
  · intro hst
    exact (h.graph.unique s v t hvAt hst) ▸ hvAt'
  · intro hst
    exact (h'.graph.unique s v t hvAt' hst) ▸ hvAt

theorem SequenceRankImage.injective_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {ω FA A θ Words OrdWords G : M.Domain} (hRank : OrdinalRank M FA A θ)
    (h : SequenceRankImage M ω FA A θ Words OrdWords G) :
    ∀ s t v, MemPair M G s v → MemPair M G t v → s=t := by
  intro s t v hsv htv
  have hS := h.graph.bounds hM.1 hsv
  have hT := h.graph.bounds hM.1 htv
  obtain ⟨n,_,hSV⟩ := h.rows s hS.1 v hS.2 hsv
  obtain ⟨m,_,hTV⟩ := h.rows t hT.1 v hT.2 htv
  exact sequence_image_injective_d hM hRank hSV hTV

end KP1Y.Ranking
