import KP1Y.CountableSections

/-! 任意给出实际 ω 满射的集合，其全部内部有限序列也有实际 ω 满射。 -/
namespace KP1Y.Cardinal
open YesMetaZFC YesMetaZFC.SetTheory YesMetaZFC.SetTheory.Definitional
open KP1Y.Kuratowski KP1Y.Functions KP1Y.Assignments
universe u

def WordMap (M : SetTheory.Structure.{u}) (ω A f u t : M.Domain) : Prop :=
  ∃ n, M.mem n ω ∧ TupleValue M t u f n ω A

def wordMapFormula {n : Nat} (ω A f u t : Project.Term n) : Project.Formula 1 n :=
  Project.Formula.existsMem ω (tupleValueFormula t.weaken u.weaken f.weaken (.bound 0) ω.weaken A.weaken)

theorem wordMapFormula_delta0 {n : Nat} (ω A f u t : Project.Term n) : (wordMapFormula ω A f u t).IsDelta0 :=
  .existsMem _ (tupleValueFormula_delta0 _ _ _ _ _ _)

theorem wordMapFormula_iff {M : SetTheory.Structure.{u}} (he : Extensional M) {n : Nat}
    (env : Env M n) (ω A f u t : Project.Term n) :
    Project.Formula.satisfies env (wordMapFormula ω A f u t) ↔ WordMap M (ω.eval env) (A.eval env) (f.eval env) (u.eval env) (t.eval env) := by
  simp only [wordMapFormula, Project.Formula.satisfies_existsMem_iff, tupleValueFormula_iff he, Definitional.Term.eval_weaken]
  rfl

private def wordMapSchema : Project.Delta0BinarySchema 3 where
  body := wordMapFormula (.bound 2) (.bound 3) (.bound 4) (.bound 1) (.bound 0)
  freeClosed := by
    simp [wordMapFormula, tupleValueFormula, graphFormula, memPairFormula, codeFormula, pairFormula,
      Project.Formula.existsMem, Project.Formula.forallMem, Definitional.Formula.FreeClosed]
  delta0 := wordMapFormula_delta0 _ _ _ _ _

private theorem wordMapSchema_iff {M : SetTheory.Structure.{u}} (he : Extensional M) (ω A f u t : M.Domain) :
    Project.Formula.satisfies (((((oneEnv f).push A).push ω).push u).push t) wordMapSchema.body ↔ WordMap M ω A f u t := by
  rw [wordMapSchema,wordMapFormula_iff he]
  rfl

theorem word_map_surjection_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {ω A f NW AW : M.Domain} (hω : M.IsOmega ω) (hf : Onto M f ω A)
    (hNW : ∀ u, M.mem u NW ↔ ∃ n, M.mem n ω ∧ Graph M u n ω)
    (hAW : ∀ t, M.mem t AW ↔ ∃ n, M.mem n ω ∧ Graph M t n A) : ∃ map, Onto M map NW AW := by
  have hF := hf.toGraph hM.1
  obtain ⟨map,hSupport,hRaw⟩ := relation_comprehension_d hM wordMapSchema (((oneEnv f).push A).push ω) NW AW
  have hRows (u t : M.Domain) : MemPair M map u t ↔ M.mem u NW ∧ M.mem t AW ∧ WordMap M ω A f u t := by
    simpa only [wordMapSchema_iff hM.1] using hRaw u t
  refine ⟨map,hSupport,?_,?_,?_⟩
  · intro u hu
    obtain ⟨n,hn,hU⟩ := (hNW u).mp hu
    obtain ⟨t,hValue⟩ := tuple_value_exists_d hM hU hF
    have ht := (hAW t).mpr ⟨n,hn,hValue.values⟩
    exact ⟨t,ht,(hRows u t).mpr ⟨hu,ht,n,hn,hValue⟩⟩
  · intro u _ t _ t' _ hut hut'
    obtain ⟨_,_,n,_,hValue⟩ := (hRows u t).mp hut
    obtain ⟨_,_,n',_,hValue'⟩ := (hRows u t').mp hut'
    have hnn' := domain_unique hM.1 hValue.variables hValue'.variables
    subst n'
    exact tuple_value_unique hM.1 hValue hValue'
  · intro t ht
    obtain ⟨n,hn,hT⟩ := (hAW t).mp ht
    obtain ⟨inv,hInv,hSection⟩ := least_section_exists_d hM hω hf
    obtain ⟨u,hIndex⟩ := tuple_value_exists_d hM hT hInv
    have hu := (hNW u).mpr ⟨n,hn,hIndex.values⟩
    have hValue : TupleValue M t u f n ω A := by
      refine ⟨hIndex.values,hF,hT,?_⟩
      intro k hk j hj a ha hUkj
      obtain ⟨b,hb,hTkb⟩ := hT.total k hk
      have hInvbj := (hIndex.rows k hk b hb j hj hTkb).mp hUkj
      have hFjb := hSection b j hInvbj
      constructor
      · intro hTka
        have hab := hT.unique k a b hTka hTkb
        subst a
        exact hFjb
      · intro hFja
        have hab := hF.unique j a b hFja hFjb
        subst a
        exact hTkb
    exact ⟨u,hu,(hRows u t).mpr ⟨hu,ht,n,hn,hValue⟩⟩

theorem countable_sequences_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {ω A f : M.Domain} (hω : M.IsOmega ω) (hf : Onto M f ω A) :
    ∃ AW E, (∀ t, M.mem t AW ↔ ∃ n, M.mem n ω ∧ Graph M t n A) ∧ Onto M E ω AW := by
  obtain ⟨NW,hNW⟩ := KP1Y.Sequences.finite_sequences_exist_d hM hω ω
  obtain ⟨NWEnum,hNWEnum⟩ := KP1Y.Naturals.natural_words_countable_d hM hω hNW
  obtain ⟨AW,hAW⟩ := KP1Y.Sequences.finite_sequences_exist_d hM hω A
  obtain ⟨map,hMap⟩ := word_map_surjection_d hM hω hf hNW hAW
  obtain ⟨E,hE⟩ := onto_compose_d hM hNWEnum hMap
  exact ⟨AW,E,hAW,hE⟩

end KP1Y.Cardinal
