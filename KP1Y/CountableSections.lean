import KP1Y.CountableFunctions

/-! 对实际 ω 满射选择最小原像，得到对象集合上的真实截面函数。 -/
namespace KP1Y.Cardinal
open YesMetaZFC YesMetaZFC.SetTheory YesMetaZFC.SetTheory.Definitional
open KP1Y.Kuratowski KP1Y.Functions
universe u

def LeastPreimage (M : SetTheory.Structure.{u}) (f n a : M.Domain) : Prop :=
  MemPair M f n a ∧ ∀ m, M.mem m n → ¬MemPair M f m a

private def preimageSchema : Project.Delta0UnarySchema 2 where
  body := memPairFormula (.bound 2) (.bound 0) (.bound 1)
  freeClosed := by
    simp [memPairFormula, codeFormula, pairFormula, Project.Formula.existsMem,
      Project.Formula.forallMem, Definitional.Formula.FreeClosed]
  delta0 := memPairFormula_delta0 _ _ _

private theorem preimageSchema_iff {M : SetTheory.Structure.{u}} (he : Extensional M) (f a n : M.Domain) :
    Project.Formula.satisfies (((oneEnv f).push a).push n) preimageSchema.body ↔ MemPair M f n a := by
  rw [preimageSchema,memPairFormula_iff he]
  rfl

theorem least_preimage_exists_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {ω Y f a : M.Domain} (hω : M.IsOmega ω) (hf : Onto M f ω Y) (ha : M.mem a Y) :
    ∃ n, M.mem n ω ∧ LeastPreimage M f n a := by
  obtain ⟨D,hD⟩ := SetTheory.KP.separation_exists_d (KP1Y.models_weakKP hM) preimageSchema ((oneEnv f).push a) ω
  have hChar (n : M.Domain) : M.mem n D ↔ M.mem n ω ∧ MemPair M f n a := by
    simpa only [preimageSchema_iff hM.1] using hD n
  obtain ⟨i,hi,hAt⟩ := hf.2.2.2 a ha
  have hOrd := KP1Y.Naturals.omega_isOrdinal_d hM hω
  obtain ⟨n,hn,hMin⟩ := hOrd.wellOrder.least D (fun m hm => ((hChar m).mp hm).1)
    ⟨i,(hChar i).mpr ⟨hi,hAt⟩⟩
  have hnω := ((hChar n).mp hn).1
  refine ⟨n,hnω,((hChar n).mp hn).2,?_⟩
  intro m hmn hma
  have hmω := hOrd.transitive n hnω m hmn
  rcases hMin m ((hChar m).mpr ⟨hmω,hma⟩) with he | hnm
  · have hEq := hM.1.eq_of_same_members n m he
    subst m
    exact hOrd.wellOrder.linear.irrefl n hnω hmn
  · exact hOrd.wellOrder.linear.irrefl n hnω (hOrd.wellOrder.linear.trans n hnω m hmω n hnω hnm hmn)

private def sectionSchema : Project.Delta0BinarySchema 2 where
  body := .conj (memPairFormula (.bound 3) (.bound 0) (.bound 1))
    (Project.Formula.forallMem (.bound 0) (.neg (memPairFormula (.bound 4) (.bound 0) (.bound 2))))
  freeClosed := by
    simp [memPairFormula, codeFormula, pairFormula, Project.Formula.existsMem,
      Project.Formula.forallMem, Definitional.Formula.FreeClosed]
  delta0 := .conj (memPairFormula_delta0 _ _ _) (.forallMem _ (.neg (memPairFormula_delta0 _ _ _)))

private theorem sectionSchema_iff {M : SetTheory.Structure.{u}} (he : Extensional M) (f ω a n : M.Domain) :
    Project.Formula.satisfies ((((oneEnv f).push ω).push a).push n) sectionSchema.body ↔ LeastPreimage M f n a := by
  simp only [sectionSchema, Project.Formula.satisfies_conj_iff, Project.Formula.satisfies_forallMem_iff,
    Project.Formula.satisfies_neg_iff, memPairFormula_iff he]
  rfl

theorem least_section_exists_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {ω Y f : M.Domain} (hω : M.IsOmega ω) (hf : Onto M f ω Y) :
    ∃ inv, Graph M inv Y ω ∧ ∀ a n, MemPair M inv a n → MemPair M f n a := by
  obtain ⟨inv,hSupport,hRaw⟩ := relation_comprehension_d hM sectionSchema ((oneEnv f).push ω) Y ω
  have hRows (a n : M.Domain) : MemPair M inv a n ↔ M.mem a Y ∧ M.mem n ω ∧ LeastPreimage M f n a := by
    simpa only [sectionSchema_iff hM.1] using hRaw a n
  refine ⟨inv,⟨hSupport,?_,?_⟩,fun a n h => ((hRows a n).mp h).2.2.1⟩
  · intro a ha
    obtain ⟨n,hn,hLeast⟩ := least_preimage_exists_d hM hω hf ha
    exact ⟨n,hn,(hRows a n).mpr ⟨ha,hn,hLeast⟩⟩
  · intro a n m han ham
    have hN := (hRows a n).mp han
    have hM' := (hRows a m).mp ham
    rcases (KP1Y.Naturals.omega_isOrdinal_d hM hω).wellOrder.linear.compare n hN.2.1 m hM'.2.1 with he | hnm | hmn
    · exact hM.1.eq_of_same_members n m he
    · exact False.elim (hM'.2.2.2 n hnm hN.2.2.1)
    · exact False.elim (hN.2.2.2 m hmn hM'.2.2.1)

end KP1Y.Cardinal
