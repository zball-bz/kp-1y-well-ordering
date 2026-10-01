import KP1Y.OrdinalIterationGrowth
import KP1Y.ClosedEnvironments

/-! 序数加法的实际KPω实现：从任意左集合开始连续迭代后继，右参数为序数。 -/
namespace KP1Y.Arithmetic
open YesMetaZFC YesMetaZFC.SetTheory YesMetaZFC.SetTheory.Definitional
open KP1Y.Kuratowski KP1Y.Functions KP1Y.Bounded
universe u

def successorMatrix : KP1Y.WitnessMatrix 0 where
  body := successorFormula (.bound 1) (.bound 2)
  freeClosed := by simp [successorFormula,Project.Formula.forallMem,Definitional.Formula.FreeClosed]
  delta0 := successorFormula_delta0 _ _

theorem successorMatrix_iff {M : SetTheory.Structure.{u}} (he : Extensional M) (e : Env M 0) (x y z : M.Domain) :
    KP1Y.OrdinalIteration.Next successorMatrix e x y z ↔ M.SuccessorOf y x := by
  rw [KP1Y.OrdinalIteration.Next,successorMatrix,successorFormula_iff he]
  rfl

theorem successor_total_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory) (e : Env M 0) :
    KP1Y.OrdinalIteration.Total successorMatrix e := by
  intro x
  obtain ⟨y,hy⟩ := SetTheory.KP.exists_successor (KP1Y.models_weakKP hM) x
  exact ⟨y,x,(successorMatrix_iff hM.1 e x y x).mpr hy⟩

theorem successor_functional {M : SetTheory.Structure.{u}} (he : Extensional M) (e : Env M 0) :
    KP1Y.OrdinalIteration.Functional successorMatrix e := by
  intro x y y' z z' h h'
  have hs := (successorMatrix_iff he e x y z).mp h
  have hs' := (successorMatrix_iff he e x y' z').mp h'
  exact he.eq_of_same_members y y' (fun a => (hs a).trans (hs' a).symm)

theorem successor_preserves_ordinals_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory) (e : Env M 0) :
    KP1Y.OrdinalIteration.PreservesOrdinals successorMatrix e :=
  fun x hx y z h => SetTheory.KP.successor_isOrdinal (KP1Y.models_weakKP hM) hx ((successorMatrix_iff hM.1 e x y z).mp h)

theorem successor_strict {M : SetTheory.Structure.{u}} (he : Extensional M) (e : Env M 0) :
    KP1Y.OrdinalIteration.StrictGrowth successorMatrix e :=
  fun x _ y z h => ((successorMatrix_iff he e x y z).mp h).predecessor_mem

def Sum (M : SetTheory.Structure.{u}) (α β γ : M.Domain) : Prop :=
  KP1Y.OrdinalIteration.Value successorMatrix (oneEnv α) β γ

def sumMatrix : KP1Y.WitnessMatrix 1 := KP1Y.OrdinalIteration.valueMatrix successorMatrix

theorem sumMatrix_iff {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory) (e : Env M 1) (β γ B : M.Domain) :
    Project.Formula.satisfies (((e.push β).push γ).push B) sumMatrix.body ↔
      KP1Y.OrdinalIteration.ValueCertificate successorMatrix (oneEnv (e.bound 0)) β γ B := by
  apply (KP1Y.formula_bound_congr sumMatrix.body sumMatrix.freeClosed _
    ((((oneEnv (e.bound 0)).push β).push γ).push B) ?_).trans
    (KP1Y.OrdinalIteration.valueMatrix_iff hM successorMatrix (oneEnv (e.bound 0)) β γ B)
  intro i
  refine Fin.cases ?_ (fun i => ?_) i
  · rfl
  · refine Fin.cases ?_ (fun i => ?_) i
    · rfl
    · refine Fin.cases ?_ (fun i => ?_) i
      · rfl
      · exact Fin.cases rfl (fun i => Fin.elim0 i) i

theorem sum_sigmaOne_iff_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory) (e : Env M 1) (β γ : M.Domain) :
    Sum M (e.bound 0) β γ ↔ ∃ B, Project.Formula.satisfies (((e.push β).push γ).push B) sumMatrix.body := by
  constructor
  · rintro ⟨B,hB⟩
    exact ⟨B,(sumMatrix_iff hM e β γ B).mpr hB⟩
  · rintro ⟨B,hB⟩
    exact ⟨B,(sumMatrix_iff hM e β γ B).mp hB⟩

theorem sum_exists_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory) (α : M.Domain)
    {β : M.Domain} (hβ : M.IsOrdinal β) : ∃ γ, Sum M α β γ :=
  KP1Y.OrdinalIteration.value_exists_d hM successorMatrix (oneEnv α) (successor_total_d hM _) (successor_functional hM.1 _) hβ

theorem sum_unique_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory) {α β γ δ : M.Domain}
    (h : Sum M α β γ) (h' : Sum M α β δ) : γ=δ :=
  KP1Y.OrdinalIteration.value_unique_d hM successorMatrix (oneEnv α) (successor_functional hM.1 _) h h'

theorem Sum.right_ordinal {M : SetTheory.Structure.{u}} {α β γ : M.Domain} (h : Sum M α β γ) : M.IsOrdinal β := h.ordinal

theorem Sum.isOrdinal_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory) {α β γ : M.Domain}
    (hα : M.IsOrdinal α) (h : Sum M α β γ) : M.IsOrdinal γ :=
  KP1Y.OrdinalIteration.Value.isOrdinal_d hM successorMatrix (oneEnv α) hα (successor_preserves_ordinals_d hM _) h

theorem Sum.zero_value_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory) {α β γ : M.Domain}
    (hβ : ∀ x, ¬M.mem x β) (h : Sum M α β γ) : γ=α := h.initial_d hM hβ

theorem sum_zero_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory) (α : M.Domain)
    {zero : M.Domain} (hZero : ∀ x, ¬M.mem x zero) : Sum M α zero α := by
  obtain ⟨γ,hγ⟩ := sum_exists_d hM α (Structure.IsOrdinal.of_no_members hZero)
  have hEq := hγ.zero_value_d hM hZero
  exact hEq ▸ hγ

theorem sum_successor_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory) {α β β' γ γ' : M.Domain}
    (hβ : M.SuccessorOf β' β) (h : Sum M α β γ) (h' : Sum M α β' γ') : M.SuccessorOf γ' γ := by
  obtain ⟨z,hNext⟩ := KP1Y.OrdinalIteration.Value.next_d hM successorMatrix (oneEnv α) (successor_functional hM.1 _) hβ h h'
  exact (successorMatrix_iff hM.1 _ γ γ' z).mp hNext

theorem sum_strict_right_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory) {α β β' γ γ' : M.Domain}
    (hα : M.IsOrdinal α) (h : Sum M α β γ) (h' : Sum M α β' γ') (hββ' : M.mem β β') : M.mem γ γ' :=
  KP1Y.OrdinalIteration.value_strict_d hM successorMatrix (oneEnv α) hα (successor_functional hM.1 _)
    (successor_preserves_ordinals_d hM _) (successor_strict hM.1 _) h h' hββ'

theorem sum_mono_right_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory) {α β β' γ γ' : M.Domain}
    (hα : M.IsOrdinal α) (h : Sum M α β γ) (h' : Sum M α β' γ') (hββ' : M.MemberSubset β β') : M.MemberSubset γ γ' :=
  KP1Y.OrdinalIteration.value_mono_d hM successorMatrix (oneEnv α) hα (successor_functional hM.1 _)
    (successor_preserves_ordinals_d hM _) (successor_strict hM.1 _) h h' hββ'

theorem sum_base_subset_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory) {α β γ : M.Domain}
    (hα : M.IsOrdinal α) (h : Sum M α β γ) : M.MemberSubset α γ := by
  obtain ⟨zero,hZero⟩ := SetTheory.KP.exists_empty (KP1Y.models_weakKP hM)
  exact sum_mono_right_d hM hα (sum_zero_d hM α hZero) h (fun x hx => False.elim (hZero x hx))

theorem sum_base_mem_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory) {α β γ : M.Domain}
    (hα : M.IsOrdinal α) (h : Sum M α β γ) (hβ : ∃ x, M.mem x β) : M.mem α γ := by
  obtain ⟨zero,hZero⟩ := SetTheory.KP.exists_empty (KP1Y.models_weakKP hM)
  have hSub : M.MemberSubset zero β := fun x hx => False.elim (hZero x hx)
  rcases KP1Y.Naturals.ordinal_subset_cases_d hM (Structure.IsOrdinal.of_no_members hZero) h.right_ordinal hSub with he | hLess
  · subst β
    obtain ⟨x,hx⟩ := hβ
    exact False.elim (hZero x hx)
  · exact sum_strict_right_d hM hα (sum_zero_d hM α hZero) h hLess

end KP1Y.Arithmetic
