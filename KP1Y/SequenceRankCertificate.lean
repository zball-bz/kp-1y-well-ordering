import KP1Y.SequenceRankImage
import KP1Y.OrdinalWordCertificate
import KP1Y.SequenceCertificateTerms

/-! 任意已排名集合的完整内部有限序列空间：固定算法、有界证书及唯一输出。 -/
namespace KP1Y.Ranking
open YesMetaZFC YesMetaZFC.SetTheory YesMetaZFC.SetTheory.Definitional
open KP1Y.Kuratowski KP1Y.Functions KP1Y.Assignments KP1Y.Sequences KP1Y.WordRank
universe u v

structure SequenceRankWitness (α : Type u) where
  ordWords : α
  ordSpace : α
  image : α
  ordRank : α
  ceiling : α
  ceilingWitness : α
  rangeWitness : α
  rowsWitness : α

def SequenceRankWitness.map {α : Type u} {β : Type v} (W : SequenceRankWitness α) (f : α → β) : SequenceRankWitness β :=
  ⟨f W.ordWords,f W.ordSpace,f W.image,f W.ordRank,f W.ceiling,f W.ceilingWitness,f W.rangeWitness,f W.rowsWitness⟩

def SequenceRankWitness.eval {M : SetTheory.Structure.{u}} {n : Nat}
    (W : SequenceRankWitness (Project.Term n)) (e : Env M n) : SequenceRankWitness M.Domain := W.map (fun t => t.eval e)

structure SequenceRankWitness.Valid (M : SetTheory.Structure.{u}) (ω FA A θ Words Γ R : M.Domain)
    (W : SequenceRankWitness M.Domain) : Prop where
  sequences : SpaceCertificate M ω θ W.ordWords W.ordSpace
  image : SequenceRankImage M ω FA A θ Words W.ordWords W.image
  words : OrdinalWordCertificate M ω θ W.ordWords Γ W.ordRank W.ceiling W.ceilingWitness W.rangeWitness W.rowsWitness
  composition : TupleValue M R W.image W.ordRank Words W.ordWords Γ

def sequenceRankWitnessFormula {n : Nat} (ω FA A θ Words Γ R : Project.Term n)
    (W : SequenceRankWitness (Project.Term n)) : Project.Formula 1 n :=
  .conj (spaceCertificateFormula ω θ W.ordWords W.ordSpace)
    (.conj (sequenceRankImageFormula ω FA A θ Words W.ordWords W.image)
      (.conj (ordinalWordCertificateFormula ω θ W.ordWords Γ W.ordRank W.ceiling W.ceilingWitness W.rangeWitness W.rowsWitness)
        (tupleValueFormula R W.image W.ordRank Words W.ordWords Γ)))

theorem sequenceRankWitnessFormula_delta0 {n : Nat} (ω FA A θ Words Γ R : Project.Term n)
    (W : SequenceRankWitness (Project.Term n)) : (sequenceRankWitnessFormula ω FA A θ Words Γ R W).IsDelta0 :=
  .conj (spaceCertificateFormula_delta0 _ _ _ _) (.conj (sequenceRankImageFormula_delta0 _ _ _ _ _ _ _)
    (.conj (ordinalWordCertificateFormula_delta0 _ _ _ _ _ _ _ _ _) (tupleValueFormula_delta0 _ _ _ _ _ _)))

def SequenceRankWitness.Closed {n : Nat} (W : SequenceRankWitness (Project.Term n)) : Prop :=
  W.ordWords.freeSupport=[] ∧ W.ordSpace.freeSupport=[] ∧ W.image.freeSupport=[] ∧ W.ordRank.freeSupport=[] ∧
    W.ceiling.freeSupport=[] ∧ W.ceilingWitness.freeSupport=[] ∧ W.rangeWitness.freeSupport=[] ∧ W.rowsWitness.freeSupport=[]

theorem sequenceRankWitnessFormula_freeClosed {n : Nat} (ω FA A θ Words Γ R : Project.Term n)
    (W : SequenceRankWitness (Project.Term n)) (hω : ω.freeSupport=[]) (hFA : FA.freeSupport=[])
    (hA : A.freeSupport=[]) (hθ : θ.freeSupport=[]) (hWords : Words.freeSupport=[])
    (hΓ : Γ.freeSupport=[]) (hR : R.freeSupport=[]) (hW : W.Closed) :
    (sequenceRankWitnessFormula ω FA A θ Words Γ R W).FreeClosed := by
  obtain ⟨hOW,hOS,hI,hOR,hC,hCW,hRW,hBW⟩ := hW
  simp only [sequenceRankWitnessFormula,Definitional.Formula.FreeClosed]
  refine ⟨spaceCertificateFormula_freeClosed _ _ _ _ hω hθ hOW hOS,
    sequenceRankImageFormula_freeClosed _ _ _ _ _ _ _ hω hFA hA hθ hWords hOW hI,
    ordinalWordCertificateFormula_freeClosed _ _ _ _ _ _ _ _ _ hω hθ hOW hΓ hOR hC hCW hRW hBW,?_⟩
  simp [tupleValueFormula,graphFormula,memPairFormula,codeFormula,pairFormula,Project.Formula.forallMem,
    Project.Formula.existsMem,Definitional.Formula.FreeClosed,hR,hI,hOR,hWords,hOW,hΓ]

theorem sequenceRankWitnessFormula_iff {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory) {n : Nat}
    (e : Env M n) (ω FA A θ Words Γ R : Project.Term n) (W : SequenceRankWitness (Project.Term n)) :
    Project.Formula.satisfies e (sequenceRankWitnessFormula ω FA A θ Words Γ R W) ↔
      SequenceRankWitness.Valid M (ω.eval e) (FA.eval e) (A.eval e) (θ.eval e) (Words.eval e) (Γ.eval e) (R.eval e) (W.eval e) := by
  simp only [sequenceRankWitnessFormula,Project.Formula.satisfies_conj_iff,spaceCertificateFormula_iff hM,
    sequenceRankImageFormula_iff hM.1,ordinalWordCertificateFormula_iff hM,tupleValueFormula_iff hM.1]
  exact ⟨fun h => ⟨h.1,h.2.1,h.2.2.1,h.2.2.2⟩,fun h => ⟨h.sequences,h.image,h.words,h.composition⟩⟩

theorem sequence_rank_witness_exists_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {ω FA A θ Words : M.Domain} (hω : M.IsOmega ω) (hRank : OrdinalRank M FA A θ)
    (hWords : ∀ s, M.mem s Words ↔ ∃ n, M.mem n ω ∧ Graph M s n A) :
    ∃ Γ R W, SequenceRankWitness.Valid M ω FA A θ Words Γ R W := by
  obtain ⟨OW,OB,hOW⟩ := space_certificate_exists_d hM hω θ
  have hOWExact := space_certificate_exact_d hM hω hOW
  obtain ⟨Γ,OR,C,BC,BP,BG,hOR⟩ := ordinal_word_certificate_exists_d hM hω hRank.ordinal hOWExact
  obtain ⟨G,hG⟩ := sequence_rank_image_exists_d hM hRank.graph hWords hOWExact
  obtain ⟨R,hR⟩ := tuple_value_exists_d hM hG.graph hOR.values.graph
  exact ⟨Γ,R,⟨OW,OB,G,OR,C,BC,BP,BG⟩,hOW,hG,hOR,hR⟩

theorem SequenceRankWitness.Valid.rank_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {ω FA A θ Words Γ R : M.Domain} {W : SequenceRankWitness M.Domain}
    (hω : M.IsOmega ω) (hRank : OrdinalRank M FA A θ) (h : W.Valid M ω FA A θ Words Γ R) :
    OrdinalRank M R Words Γ := by
  have hOR := h.words.rank_d hM hω hRank.ordinal
  refine ⟨hOR.ordinal,h.composition.values,?_⟩
  intro s t r hsr htr
  have hS := h.composition.values.bounds hM.1 hsr
  have hT := h.composition.values.bounds hM.1 htr
  obtain ⟨a,ha,hsa⟩ := h.image.graph.total s hS.1
  obtain ⟨b,hb,htb⟩ := h.image.graph.total t hT.1
  have har := (h.composition.rows s hS.1 a ha r hS.2 hsa).mp hsr
  have hbr := (h.composition.rows t hT.1 b hb r hT.2 htb).mp htr
  have hab := hOR.injective a b r har hbr
  subst b
  exact h.image.injective_d hM hRank s t a hsa htb

theorem SequenceRankWitness.Valid.unique_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {ω FA A θ Words Γ R Γ' R' : M.Domain} {W W' : SequenceRankWitness M.Domain}
    (hω : M.IsOmega ω) (h : W.Valid M ω FA A θ Words Γ R) (h' : W'.Valid M ω FA A θ Words Γ' R') :
    Γ=Γ' ∧ R=R' := by
  rcases W with ⟨OW,OB,G,OR,C,BC,BP,BG⟩
  rcases W' with ⟨OW',OB',G',OR',C',BC',BP',BG'⟩
  have hOW := space_certificate_unique_d hM hω h.sequences h'.sequences
  change OW=OW' at hOW
  subst OW'
  obtain ⟨hΓ,hOR⟩ := h.words.unique_d hM hω h'.words
  change OR=OR' at hOR
  subst Γ'
  subst OR'
  have hG := h.image.unique hM.1 h'.image
  change G=G' at hG
  subst G'
  exact ⟨rfl,tuple_value_unique hM.1 h.composition h'.composition⟩

end KP1Y.Ranking
