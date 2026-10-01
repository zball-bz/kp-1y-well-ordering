import KP1Y.NamedAssignments
import KP1Y.NaturalNumbers

/-! 为每个宿主有限公式的有限变量表构造实际内部自然数名字及赋值图；不声称枚举全部内部ω。 -/
namespace KP1Y.Named
open YesMetaZFC YesMetaZFC.SetTheory
open KP1Y.Kuratowski KP1Y.Functions KP1Y.Naturals
universe u

noncomputable def natEntry {M : SetTheory.Structure.{u}} {ω : M.Domain} (hω : M.IsOmega ω) : Nat → {x : M.Domain // M.mem x ω}
  | 0 => ⟨Classical.choose hω.1.1,(Classical.choose_spec hω.1.1).2⟩
  | n+1 =>
      let prev := natEntry hω n
      ⟨Classical.choose (hω.1.2 prev.val prev.property),(Classical.choose_spec (hω.1.2 prev.val prev.property)).2⟩

noncomputable def natValue {M : SetTheory.Structure.{u}} {ω : M.Domain} (hω : M.IsOmega ω) (n : Nat) : M.Domain :=
  (natEntry hω n).val

theorem natValue_nat {M : SetTheory.Structure.{u}} {ω : M.Domain} (hω : M.IsOmega ω) (n : Nat) : M.mem (natValue hω n) ω :=
  (natEntry hω n).property

theorem natValue_zero_empty {M : SetTheory.Structure.{u}} {ω : M.Domain} (hω : M.IsOmega ω) :
    ∀ x, ¬M.mem x (natValue hω 0) := (Classical.choose_spec hω.1.1).1

theorem natValue_successor {M : SetTheory.Structure.{u}} {ω : M.Domain} (hω : M.IsOmega ω) (n : Nat) :
    M.SuccessorOf (natValue hω (n+1)) (natValue hω n) :=
  (Classical.choose_spec (hω.1.2 (natValue hω n) (natValue_nat hω n))).1

theorem natValue_lt {M : SetTheory.Structure.{u}} {ω : M.Domain} (hω : M.IsOmega ω) {i j : Nat} (hij : i<j) :
    M.mem (natValue hω i) (natValue hω j) := by
  induction j generalizing i with
  | zero => omega
  | succ j ih =>
      by_cases he : i=j
      · subst i
        exact (natValue_successor hω j).predecessor_mem
      · exact (natValue_successor hω j (natValue hω i)).mpr (Or.inl (ih (by omega)))

theorem natValue_injective_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {ω : M.Domain} (hω : M.IsOmega ω) (i j : Nat) (he : natValue hω i=natValue hω j) : i=j := by
  apply Classical.byContradiction
  intro hNe
  by_cases hij : i<j
  · have hMem := natValue_lt hω hij
    rw [he] at hMem
    exact SetTheory.KP.mem_irrefl_d (KP1Y.models_weakKP hM) (natValue hω j) hMem
  · have hji : j<i := by omega
    have hMem := natValue_lt hω hji
    rw [he] at hMem
    exact SetTheory.KP.mem_irrefl_d (KP1Y.models_weakKP hM) (natValue hω j) hMem

noncomputable def natNames {M : SetTheory.Structure.{u}} {ω : M.Domain} (hω : M.IsOmega ω) {k : Nat} : Fin k → M.Domain :=
  fun i => natValue hω i.val

theorem natNames_bounded {M : SetTheory.Structure.{u}} {ω : M.Domain} (hω : M.IsOmega ω) {k : Nat} (i : Fin k) :
    M.mem (natNames hω i) (natValue hω k) := natValue_lt hω i.isLt

theorem natNames_injective_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {ω : M.Domain} (hω : M.IsOmega ω) (k : Nat) : InjectiveNames (natNames hω (k := k)) := by
  intro i j he
  exact Fin.ext (natValue_injective_d hM hω i.val j.val he)

theorem natValue_zero_eq {M : SetTheory.Structure.{u}} (he : Extensional M) {ω zero : M.Domain}
    (hω : M.IsOmega ω) (hZero : ∀ x, ¬M.mem x zero) : natValue hω 0=zero :=
  he.eq_of_same_members _ _ (fun x => iff_of_false (natValue_zero_empty hω x) (hZero x))

theorem finite_assignment_exists_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {ω A : M.Domain} (hω : M.IsOmega ω) {k : Nat} (vals : Fin k → M.Domain) (hVals : ∀ i, M.mem (vals i) A) :
    ∃ s, Graph M s (natValue hω k) A ∧ Reads M s (natNames hω) vals := by
  induction k with
  | zero =>
      exact ⟨natValue hω 0,empty_graph (natValue_zero_empty hω),fun i => Fin.elim0 i⟩
  | succ k ih =>
      obtain ⟨s,hS,hReads⟩ := ih (fun i => vals i.castSucc) (fun i => hVals i.castSucc)
      obtain ⟨t,hT,hRows⟩ := append_graph_d hM hS (natValue_successor hω k) (fun _ h => h) (hVals (Fin.last k))
      refine ⟨t,hT,?_⟩
      intro i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · exact (hRows (natValue hω k) (vals (Fin.last k))).mpr (Or.inr ⟨rfl,rfl⟩)
      · exact (hRows (natNames hω j) (vals j.castSucc)).mpr (Or.inl (hReads j))

end KP1Y.Named
