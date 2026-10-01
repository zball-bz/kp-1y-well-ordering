import KP1Y.BoundedSets
import YesMetaZFC.SetTheory.Ord.Natural

/-! KPω 内构造最小归纳集。这里的有限序数属于模型内部，不假定外部 ω 标准性。 -/
namespace KP1Y.Naturals
open YesMetaZFC YesMetaZFC.SetTheory YesMetaZFC.SetTheory.Definitional
open KP1Y.Bounded
universe u

def EmptyOrSuccessor (M : SetTheory.Structure.{u}) (a : M.Domain) : Prop :=
  (∀ x, ¬M.mem x a) ∨ ∃ p, M.mem p a ∧ M.SuccessorOf a p

def FiniteOrdinal (M : SetTheory.Structure.{u}) (a : M.Domain) : Prop :=
  M.IsOrdinal a ∧ EmptyOrSuccessor M a ∧ ∀ p, M.mem p a → EmptyOrSuccessor M p

def emptyOrSuccessorFormula {n : Nat} (a : Project.Term n) : Project.Formula 1 n :=
  .disj (emptyFormula a) (Project.Formula.existsMem a (successorFormula a.weaken (.bound 0)))

theorem emptyOrSuccessorFormula_delta0 {n : Nat} (a : Project.Term n) :
    (emptyOrSuccessorFormula a).IsDelta0 :=
  .disj (emptyFormula_delta0 _) (.existsMem _ (successorFormula_delta0 _ _))

theorem emptyOrSuccessorFormula_iff {M : SetTheory.Structure.{u}} (he : Extensional M) {n : Nat}
    (env : Env M n) (a : Project.Term n) :
    Project.Formula.satisfies env (emptyOrSuccessorFormula a) ↔ EmptyOrSuccessor M (a.eval env) := by
  simp only [emptyOrSuccessorFormula, Project.Formula.satisfies_disj_iff,
    emptyFormula_iff, Project.Formula.satisfies_existsMem_iff,
    successorFormula_iff he, Definitional.Term.eval_weaken]
  rfl

def finiteFormula {n : Nat} (a : Project.Term n) : Project.Formula 1 n :=
  .conj (ordinalFormula a) (.conj (emptyOrSuccessorFormula a)
    (Project.Formula.forallMem a (emptyOrSuccessorFormula (.bound 0))))

theorem finiteFormula_delta0 {n : Nat} (a : Project.Term n) : (finiteFormula a).IsDelta0 :=
  .conj (ordinalFormula_delta0 _) (.conj (emptyOrSuccessorFormula_delta0 _)
    (.forallMem _ (emptyOrSuccessorFormula_delta0 _)))

theorem finiteFormula_iff {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory) {n : Nat}
    (env : Env M n) (a : Project.Term n) :
    Project.Formula.satisfies env (finiteFormula a) ↔ FiniteOrdinal M (a.eval env) := by
  simp only [finiteFormula, Project.Formula.satisfies_conj_iff, ordinalFormula_iff hM,
    emptyOrSuccessorFormula_iff hM.1, Project.Formula.satisfies_forallMem_iff]
  rfl

theorem FiniteOrdinal.mem {M : SetTheory.Structure.{u}} {a p : M.Domain}
    (ha : FiniteOrdinal M a) (hp : M.mem p a) : FiniteOrdinal M p :=
  ⟨ha.1.mem hp,ha.2.2 p hp,fun q hq => ha.2.2 q (ha.1.transitive p hp q hq)⟩

theorem finite_empty {M : SetTheory.Structure.{u}} {e : M.Domain}
    (he : ∀ x, ¬M.mem x e) : FiniteOrdinal M e :=
  ⟨Structure.IsOrdinal.of_no_members he,Or.inl he,fun x hx => False.elim (he x hx)⟩

theorem finite_successor_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {a b : M.Domain} (ha : FiniteOrdinal M a) (hs : M.SuccessorOf b a) : FiniteOrdinal M b := by
  refine ⟨SetTheory.KP.successor_isOrdinal (KP1Y.models_weakKP hM) ha.1 hs,
    Or.inr ⟨a,hs.predecessor_mem,hs⟩,?_⟩
  intro p hp
  rcases (hs p).mp hp with hp | he
  · exact ha.2.2 p hp
  · exact (hM.1.eq_of_same_members p a he) ▸ ha.2.1

def finiteSchema : Project.Delta0UnarySchema 0 where
  body := finiteFormula (.bound 0)
  freeClosed := by
    simp [finiteFormula, ordinalFormula, emptyOrSuccessorFormula, emptyFormula,
      successorFormula, Project.Formula.isTransitive, Project.Formula.forallMem,
      Project.Formula.existsMem, Definitional.Formula.FreeClosed]
  delta0 := finiteFormula_delta0 _

private def inductiveGuard : Project.UnarySchema 1 where
  body := .imp (finiteFormula (.bound 0)) (.mem (.bound 0) (.bound 1))
  freeClosed := by
    simp [finiteFormula, ordinalFormula, emptyOrSuccessorFormula, emptyFormula,
      successorFormula, Project.Formula.isTransitive, Project.Formula.forallMem,
      Project.Formula.existsMem, Definitional.Formula.FreeClosed]

private def setEnv {M : SetTheory.Structure.{u}} (I : M.Domain) : Env M 1 :=
  ⟨fun _ => I,fun _ => I⟩

private theorem inductiveGuard_iff {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    (I x : M.Domain) :
    Project.Formula.satisfies ((setEnv I).push x) inductiveGuard.body ↔
      (FiniteOrdinal M x → M.mem x I) := by
  simp only [inductiveGuard, Project.Formula.satisfies_imp_iff,
    finiteFormula_iff hM, Project.Formula.satisfies_mem_iff]
  rfl

/-- 完整集合归纳替代 ZF 中“属于所有归纳集”的无界分离。 -/
theorem finite_in_inductive_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {I : M.Domain} (hI : M.IsInductive I) : ∀ x, FiniteOrdinal M x → M.mem x I := by
  have hAll := KP1Y.induction_d hM inductiveGuard (setEnv I) (fun x ih =>
    (inductiveGuard_iff hM I x).mpr (by
      intro hx
      rcases hx.2.1 with hEmpty | ⟨p,hp,hSucc⟩
      · obtain ⟨e,he,heI⟩ := hI.1
        have hxe : x=e := hM.1.eq_of_same_members x e (fun y => iff_of_false (hEmpty y) (he y))
        exact hxe ▸ heI
      · have hpI := (inductiveGuard_iff hM I p).mp (ih p hp) (hx.mem hp)
        obtain ⟨b,hb,hbI⟩ := hI.2 p hpI
        exact (Structure.SuccessorOf.eq hM.1 hSucc hb) ▸ hbI))
  exact fun x => (inductiveGuard_iff hM I x).mp (hAll x)

theorem exists_omega_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory) :
    ∃ ω, M.IsOmega ω ∧ ∀ x, M.mem x ω ↔ FiniteOrdinal M x := by
  have hw := KP1Y.models_weakKP hM
  obtain ⟨I,hI⟩ := SetTheory.KP.exists_inductive hw
  let env : Env M 0 := ⟨Fin.elim0,fun _ => I⟩
  obtain ⟨ω,hSep⟩ := SetTheory.KP.separation_exists_d hw finiteSchema env I
  have hChar : ∀ x, M.mem x ω ↔ FiniteOrdinal M x := by
    intro x
    have h := hSep x
    change M.mem x ω ↔ M.mem x I ∧ Project.Formula.satisfies (env.push x) (finiteFormula (.bound 0)) at h
    rw [finiteFormula_iff hM] at h
    exact h.trans ⟨And.right,fun hx => ⟨finite_in_inductive_d hM hI x hx,hx⟩⟩
  refine ⟨ω,⟨⟨?_,?_⟩,?_⟩,hChar⟩
  · obtain ⟨e,he,_⟩ := hI.1
    exact ⟨e,he,(hChar e).mpr (finite_empty he)⟩
  · intro x hx
    obtain ⟨b,hb⟩ := SetTheory.KP.exists_successor hw x
    exact ⟨b,hb,(hChar b).mpr (finite_successor_d hM ((hChar x).mp hx) hb)⟩
  · intro J hJ x hx
    exact finite_in_inductive_d hM hJ x ((hChar x).mp hx)

theorem omega_unique {M : SetTheory.Structure.{u}} (he : Extensional M) {ω ω' : M.Domain}
    (hω : M.IsOmega ω) (hω' : M.IsOmega ω') : ω=ω' :=
  he.eq_of_same_members ω ω' (fun x => ⟨hω.2 ω' hω'.1 x,hω'.2 ω hω.1 x⟩)

theorem omega_members_iff_finite {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {ω : M.Domain} (hω : M.IsOmega ω) (x : M.Domain) : M.mem x ω ↔ FiniteOrdinal M x := by
  obtain ⟨ω',hω',hChar⟩ := exists_omega_d hM
  exact (omega_unique hM.1 hω hω') ▸ hChar x

theorem omega_isOrdinal_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {ω : M.Domain} (hω : M.IsOmega ω) : M.IsOrdinal ω := by
  apply ordinal_of_transitive_members_d hM
  · intro x hx y hy
    exact (omega_members_iff_finite hM hω y).mpr (((omega_members_iff_finite hM hω x).mp hx).mem hy)
  · intro x hx
    exact ((omega_members_iff_finite hM hω x).mp hx).1

theorem omega_isLimit_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {ω : M.Domain} (hω : M.IsOmega ω) : M.IsLimitOrdinal ω := by
  refine ⟨omega_isOrdinal_d hM hω,?_,?_⟩
  · obtain ⟨e,_,he⟩ := hω.1.1
    exact ⟨e,he⟩
  · intro x hx
    obtain ⟨b,hb,hbω⟩ := hω.1.2 x hx
    exact ⟨b,hbω,hb.predecessor_mem⟩

theorem natural_cases {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {ω x : M.Domain} (hω : M.IsOmega ω) (hx : M.mem x ω) :
    (∀ y, ¬M.mem y x) ∨ ∃ p, M.mem p ω ∧ M.SuccessorOf x p := by
  rcases ((omega_members_iff_finite hM hω x).mp hx).2.1 with hEmpty | ⟨p,hp,hs⟩
  · exact Or.inl hEmpty
  · exact Or.inr ⟨p,(omega_isOrdinal_d hM hω).transitive x hx p hp,hs⟩

def omegaSentence : Project.Sentence :=
  Project.Sentence.ofFormula (.existsE (Project.Formula.isOmega (.bound 0))) (by
    simp [Project.Formula.isOmega, Project.Formula.isInductive, Project.Formula.isEmpty,
      Project.Formula.isSuccessor, Project.Formula.forallMem, Definitional.Formula.FreeClosed])

theorem omega_derivable : KP1Y.Derives omegaSentence := by
  apply KP1Y.derives_of_all_models
  intro M hM free
  change Project.Formula.satisfies ({bound := Fin.elim0,free := free} : Env M 0)
    (.existsE (Project.Formula.isOmega (.bound 0)))
  apply (Project.Formula.satisfies_exists_iff _ _).mpr
  obtain ⟨ω,hω,_⟩ := exists_omega_d hM
  exact ⟨ω,(Project.Formula.satisfies_isOmega_iff _ _).mpr hω⟩

end KP1Y.Naturals
