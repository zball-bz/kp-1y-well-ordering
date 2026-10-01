import KP1Y.CountableProducts
import KP1Y.CountableSegments

/-! 两个实际可数枚举的并，及非空种子所需的常值枚举。 -/
namespace KP1Y.Cardinal
open YesMetaZFC YesMetaZFC.SetTheory YesMetaZFC.SetTheory.Definitional
open KP1Y.Kuratowski KP1Y.Functions KP1Y.Bounded
universe u

private def unionLiftSchema : Project.Delta0BinarySchema 3 where
  body := Project.Formula.existsMem (.bound 2) (Project.Formula.existsMem (.bound 3)
    (.conj (codeFormula (.bound 3) (.bound 1) (.bound 0))
      (.disj (.conj (emptyFormula (.bound 1)) (memPairFormula (.bound 5) (.bound 0) (.bound 2)))
        (.conj (.neg (emptyFormula (.bound 1))) (memPairFormula (.bound 6) (.bound 0) (.bound 2))))))
  freeClosed := by
    simp [emptyFormula, memPairFormula, codeFormula, pairFormula, Project.Formula.existsMem,
      Project.Formula.forallMem, Definitional.Formula.FreeClosed]
  delta0 := .existsMem _ (.existsMem _ (.conj (codeFormula_delta0 _ _ _)
    (.disj (.conj (emptyFormula_delta0 _) (memPairFormula_delta0 _ _ _))
      (.conj (.neg (emptyFormula_delta0 _)) (memPairFormula_delta0 _ _ _)))))

private def unionLiftEnv {M : SetTheory.Structure.{u}} (ω f g : M.Domain) : Env M 3 :=
  ⟨Fin.cases ω (Fin.cases f (fun _ => g)),fun _ => ω⟩

private theorem unionLiftSchema_iff {M : SetTheory.Structure.{u}} (he : Extensional M) (ω f g q x : M.Domain) :
    Project.Formula.satisfies (((unionLiftEnv ω f g).push q).push x) unionLiftSchema.body ↔
      ∃ i, M.mem i ω ∧ ∃ j, M.mem j ω ∧ Codes M q i j ∧
        (((∀ z, ¬M.mem z i) ∧ MemPair M f j x) ∨ (¬(∀ z, ¬M.mem z i) ∧ MemPair M g j x)) := by
  simp only [unionLiftSchema, Project.Formula.satisfies_existsMem_iff, Project.Formula.satisfies_conj_iff,
    Project.Formula.satisfies_disj_iff, Project.Formula.satisfies_neg_iff,
    codeFormula_iff he, emptyFormula_iff, memPairFormula_iff he]
  rfl

theorem union_surjection_lift_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {ω X Y f g NP U : M.Domain} (hω : M.IsOmega ω) (hf : Onto M f ω X) (hg : Onto M g ω Y)
    (hNP : IsProduct M NP ω ω) (hU : M.IsUnionOfTwo U X Y) : ∃ lift, Onto M lift NP U := by
  classical
  obtain ⟨lift,hSupport,hRaw⟩ := relation_comprehension_d hM unionLiftSchema (unionLiftEnv ω f g) NP U
  have hRows (q x : M.Domain) : MemPair M lift q x ↔ M.mem q NP ∧ M.mem x U ∧
      ∃ i, M.mem i ω ∧ ∃ j, M.mem j ω ∧ Codes M q i j ∧
        (((∀ z, ¬M.mem z i) ∧ MemPair M f j x) ∨ (¬(∀ z, ¬M.mem z i) ∧ MemPair M g j x)) := by
    simpa only [unionLiftSchema_iff hM.1] using hRaw q x
  refine ⟨lift,hSupport,?_,?_,?_⟩
  · intro q hq
    obtain ⟨i,hi,j,hj,hCode⟩ := (hNP q).mp hq
    by_cases he : ∀ z, ¬M.mem z i
    · obtain ⟨x,hx,hAt⟩ := hf.2.1 j hj
      have hxU := (hU x).mpr (Or.inl hx)
      exact ⟨x,hxU,(hRows q x).mpr ⟨hq,hxU,i,hi,j,hj,hCode,Or.inl ⟨he,hAt⟩⟩⟩
    · obtain ⟨x,hx,hAt⟩ := hg.2.1 j hj
      have hxU := (hU x).mpr (Or.inr hx)
      exact ⟨x,hxU,(hRows q x).mpr ⟨hq,hxU,i,hi,j,hj,hCode,Or.inr ⟨he,hAt⟩⟩⟩
  · intro q _ x _ y _ hqx hqy
    obtain ⟨_,_,i,_,j,_,hCode,hCase⟩ := (hRows q x).mp hqx
    obtain ⟨_,_,i',_,j',_,hCode',hCase'⟩ := (hRows q y).mp hqy
    obtain ⟨hii',hjj'⟩ := codes_injective hM.1 hCode hCode'
    subst i'
    subst j'
    rcases hCase with ⟨he,hAt⟩ | ⟨he,hAt⟩ <;> rcases hCase' with ⟨he',hAt'⟩ | ⟨he',hAt'⟩
    · exact (hf.toGraph hM.1).unique j x y hAt hAt'
    · exact False.elim (he' he)
    · exact False.elim (he he')
    · exact (hg.toGraph hM.1).unique j x y hAt hAt'
  · intro x hx
    obtain ⟨zero,hEmpty,hZero⟩ := hω.1.1
    rcases (hU x).mp hx with hxX | hxY
    · obtain ⟨j,hj,hAt⟩ := hf.2.2.2 x hxX
      obtain ⟨q,hCode⟩ := codes_total hM zero j
      have hq := (hNP q).mpr ⟨zero,hZero,j,hj,hCode⟩
      exact ⟨q,hq,(hRows q x).mpr ⟨hq,hx,zero,hZero,j,hj,hCode,Or.inl ⟨hEmpty,hAt⟩⟩⟩
    · obtain ⟨one,hSucc,hOne⟩ := hω.1.2 zero hZero
      have hNot : ¬(∀ z, ¬M.mem z one) := fun h => h zero hSucc.predecessor_mem
      obtain ⟨j,hj,hAt⟩ := hg.2.2.2 x hxY
      obtain ⟨q,hCode⟩ := codes_total hM one j
      have hq := (hNP q).mpr ⟨one,hOne,j,hj,hCode⟩
      exact ⟨q,hq,(hRows q x).mpr ⟨hq,hx,one,hOne,j,hj,hCode,Or.inr ⟨hNot,hAt⟩⟩⟩

theorem countable_union_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {ω X Y f g : M.Domain} (hω : M.IsOmega ω) (hf : Onto M f ω X) (hg : Onto M g ω Y) :
    ∃ U E, M.IsUnionOfTwo U X Y ∧ Onto M E ω U := by
  obtain ⟨U,hU⟩ := SetTheory.KP.exists_unionOfTwo (KP1Y.models_weakKP hM) X Y
  obtain ⟨NP,decode,hDecode⟩ := KP1Y.Naturals.natural_pairing_exists_d hM hω
  obtain ⟨lift,hLift⟩ := union_surjection_lift_d hM hω hf hg hDecode.product hU
  obtain ⟨E,hE⟩ := onto_compose_d hM hDecode.onto hLift
  exact ⟨U,E,hU,hE⟩

private def constantSchema : Project.Delta0BinarySchema 1 where
  body := Project.Formula.extensionalEq (.bound 0) (.bound 2)
  freeClosed := by simp
  delta0 := .atom _ _ _

private theorem constantSchema_iff {M : SetTheory.Structure.{u}} (he : Extensional M) (a i x : M.Domain) :
    Project.Formula.satisfies (((oneEnv a).push i).push x) constantSchema.body ↔ x=a := by
  rw [constantSchema,Project.Formula.satisfies_extensionalEq_iff_eq he]
  rfl

theorem constant_onto_singleton_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {ω : M.Domain} (hω : M.IsOmega ω) (a : M.Domain) :
    ∃ S E, (∀ x, M.mem x S ↔ x=a) ∧ Onto M E ω S := by
  obtain ⟨S,hS⟩ := SetTheory.KP.exists_singleton (KP1Y.models_weakKP hM) a
  obtain ⟨E,hSupport,hRaw⟩ := relation_comprehension_d hM constantSchema (oneEnv a) ω S
  have hRows (i x : M.Domain) : MemPair M E i x ↔ M.mem i ω ∧ M.mem x S ∧ x=a := by
    simpa only [constantSchema_iff hM.1] using hRaw i x
  refine ⟨S,E,hS,hSupport,?_,?_,?_⟩
  · intro i hi
    exact ⟨a,(hS a).mpr rfl,(hRows i a).mpr ⟨hi,(hS a).mpr rfl,rfl⟩⟩
  · intro i _ x _ y _ hix hiy
    exact ((hRows i x).mp hix).2.2.trans ((hRows i y).mp hiy).2.2.symm
  · intro x hx
    obtain ⟨zero,_,hZero⟩ := hω.1.1
    exact ⟨zero,hZero,(hRows zero x).mpr ⟨hZero,hx,(hS x).mp hx⟩⟩

end KP1Y.Cardinal
