import KP1Y.CountableSequences
import KP1Y.CountableUnions

/-! 将可数性证明运输到已有的实际集合，避免重复构造同义但未识别的空间。 -/
namespace KP1Y.Cardinal
open YesMetaZFC YesMetaZFC.SetTheory YesMetaZFC.SetTheory.Definitional
open KP1Y.Kuratowski KP1Y.Functions
universe u

private def identitySchema : Project.Delta0BinarySchema 0 where
  body := Project.Formula.extensionalEq (.bound 0) (.bound 1)
  freeClosed := by simp
  delta0 := .atom _ _ _

private theorem identitySchema_iff {M : SetTheory.Structure.{u}} (he : Extensional M) (env : Env M 0) (x y : M.Domain) :
    Project.Formula.satisfies ((env.push x).push y) identitySchema.body ↔ y=x := by
  rw [identitySchema,Project.Formula.satisfies_extensionalEq_iff_eq he]
  rfl

theorem identity_onto_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory) (X : M.Domain) : ∃ f, Onto M f X X := by
  let env : Env M 0 := ⟨Fin.elim0,fun _ => X⟩
  obtain ⟨f,hSupport,hRaw⟩ := relation_comprehension_d hM identitySchema env X X
  have hRows (x y : M.Domain) : MemPair M f x y ↔ M.mem x X ∧ M.mem y X ∧ y=x := by
    simpa only [identitySchema_iff hM.1] using hRaw x y
  refine ⟨f,hSupport,?_,?_,?_⟩
  · intro x hx
    exact ⟨x,hx,(hRows x x).mpr ⟨hx,hx,rfl⟩⟩
  · intro x _ a _ b _ hxa hxb
    exact ((hRows x a).mp hxa).2.2.trans ((hRows x b).mp hxb).2.2.symm
  · intro x hx
    exact ⟨x,hx,(hRows x x).mpr ⟨hx,hx,rfl⟩⟩

theorem countable_existing_product_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {ω X Y f g P : M.Domain} (hω : M.IsOmega ω) (hf : Onto M f ω X) (hg : Onto M g ω Y)
    (hP : IsProduct M P X Y) : ∃ E, Onto M E ω P := by
  obtain ⟨Q,E,hQ,hE⟩ := countable_product_d hM hω hf hg
  have hPQ : Q=P := hM.1.eq_of_same_members Q P (fun x => (hQ x).trans (hP x).symm)
  subst Q
  exact ⟨E,hE⟩

theorem countable_existing_sequences_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {ω X f Seq : M.Domain} (hω : M.IsOmega ω) (hf : Onto M f ω X)
    (hSeq : ∀ t, M.mem t Seq ↔ ∃ n, M.mem n ω ∧ Graph M t n X) : ∃ E, Onto M E ω Seq := by
  obtain ⟨Seq',E,hSeq',hE⟩ := countable_sequences_d hM hω hf
  have hEq : Seq'=Seq := hM.1.eq_of_same_members Seq' Seq (fun t => (hSeq' t).trans (hSeq t).symm)
  subst Seq'
  exact ⟨E,hE⟩

end KP1Y.Cardinal
