import KP1Y.OrdinalWordRank
import KP1Y.RankComposition

/-! 将任意已排名集合A的全部内部有限序列映到序数字词，再拉回其序数排名。 -/
namespace KP1Y.Ranking
open YesMetaZFC YesMetaZFC.SetTheory YesMetaZFC.SetTheory.Definitional
open KP1Y.Kuratowski KP1Y.Functions KP1Y.Assignments
universe u

private def imageSchema : Project.Delta0BinarySchema 4 where
  body := Project.Formula.existsMem (.bound 2)
    (tupleValueFormula (.bound 1) (.bound 2) (.bound 6) (.bound 0) (.bound 4) (.bound 5))
  freeClosed := by
    simp [tupleValueFormula,graphFormula,memPairFormula,codeFormula,pairFormula,
      Project.Formula.forallMem,Project.Formula.existsMem,Definitional.Formula.FreeClosed]
  delta0 := .existsMem _ (tupleValueFormula_delta0 _ _ _ _ _ _)

private theorem imageSchema_iff {M : SetTheory.Structure.{u}} (he : Extensional M) (R θ A ω s t : M.Domain) :
    Project.Formula.satisfies ((((((oneEnv R).push θ).push A).push ω).push s).push t) imageSchema.body ↔
      ∃ n, M.mem n ω ∧ TupleValue M t s R n A θ := by
  simp only [imageSchema,Project.Formula.satisfies_existsMem_iff,tupleValueFormula_iff he]
  rfl

theorem sequence_image_injective_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {R A θ s t v n m : M.Domain} (hRank : OrdinalRank M R A θ)
    (hS : TupleValue M v s R n A θ) (hT : TupleValue M v t R m A θ) : s=t := by
  have hnm := domain_unique hM.1 hS.values hT.values
  subst m
  apply hS.variables.ext hM.1 hT.variables
  intro i hi x
  obtain ⟨a,ha,hsa⟩ := hS.variables.total i hi
  obtain ⟨b,hb,htb⟩ := hT.variables.total i hi
  obtain ⟨α,hα,hRa⟩ := hRank.graph.total a ha
  obtain ⟨β,hβ,hRb⟩ := hRank.graph.total b hb
  have hvα := (hS.rows i hi a ha α hα hsa).mpr hRa
  have hvβ := (hT.rows i hi b hb β hβ htb).mpr hRb
  have hαβ := hS.values.unique i α β hvα hvβ
  subst β
  have hab := hRank.injective a b α hRa hRb
  subst b
  constructor
  · intro hsx
    have hxa := hS.variables.unique i x a hsx hsa
    exact hxa ▸ htb
  · intro htx
    have hxa := hT.variables.unique i x a htx htb
    exact hxa ▸ hsa

theorem ranked_sequence_space_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {ω R A θ Words : M.Domain} (hω : M.IsOmega ω) (hRank : OrdinalRank M R A θ)
    (hWords : ∀ s, M.mem s Words ↔ ∃ n, M.mem n ω ∧ Graph M s n A) :
    ∃ Γ F, OrdinalRank M F Words Γ := by
  obtain ⟨OrdWords,hOrdWords⟩ := KP1Y.Sequences.finite_sequences_exist_d hM hω θ
  obtain ⟨Γ,F,hOrdRank⟩ := KP1Y.WordRank.ordinal_word_rank_d hM hω hRank.ordinal hOrdWords
  obtain ⟨G,hSupport,hRaw⟩ := relation_comprehension_d hM imageSchema ((((oneEnv R).push θ).push A).push ω) Words OrdWords
  have hRows (s t : M.Domain) : MemPair M G s t ↔ M.mem s Words ∧ M.mem t OrdWords ∧
      ∃ n, M.mem n ω ∧ TupleValue M t s R n A θ := by
    simpa only [imageSchema_iff hM.1] using hRaw s t
  have hG : Graph M G Words OrdWords := by
    refine ⟨hSupport,?_,?_⟩
    · intro s hs
      obtain ⟨n,hn,hS⟩ := (hWords s).mp hs
      obtain ⟨t,hT⟩ := tuple_value_exists_d hM hS hRank.graph
      have ht := (hOrdWords t).mpr ⟨n,hn,hT.values⟩
      exact ⟨t,ht,(hRows s t).mpr ⟨hs,ht,n,hn,hT⟩⟩
    · intro s t t' hst hst'
      obtain ⟨_,_,n,_,hT⟩ := (hRows s t).mp hst
      obtain ⟨_,_,n',_,hT'⟩ := (hRows s t').mp hst'
      have hnn' := domain_unique hM.1 hT.variables hT'.variables
      subst n'
      exact tuple_value_unique hM.1 hT hT'
  have hInj : ∀ s t v, MemPair M G s v → MemPair M G t v → s=t := by
    intro s t v hsv htv
    obtain ⟨_,_,n,_,hS⟩ := (hRows s v).mp hsv
    obtain ⟨_,_,m,_,hT⟩ := (hRows t v).mp htv
    exact sequence_image_injective_d hM hRank hS hT
  obtain ⟨G',hG'⟩ := rank_pullback_d hM hG hInj hOrdRank
  exact ⟨Γ,G',hG'⟩

end KP1Y.Ranking
