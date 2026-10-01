import KP1Y.FiniteVariableNames

/-! 六符号签名所需的固定自然数0..6，全部来自模型实际ω的空集/后继。 -/
namespace KP1Y.Named
open YesMetaZFC YesMetaZFC.SetTheory
universe u

theorem natValue_members_iff {M : SetTheory.Structure.{u}} (he : Extensional M) {ω : M.Domain}
    (hω : M.IsOmega ω) (n : Nat) (x : M.Domain) : M.mem x (natValue hω n) ↔ ∃ i : Fin n, x=natValue hω i.val := by
  constructor
  · intro hx
    induction n with
    | zero => exact False.elim (natValue_zero_empty hω x hx)
    | succ n ih =>
        rcases (natValue_successor hω n x).mp hx with hx | hSame
        · obtain ⟨i,hi⟩ := ih hx
          exact ⟨i.castSucc,hi⟩
        · exact ⟨Fin.last n,he.eq_of_same_members x (natValue hω n) hSame⟩
  · rintro ⟨i,rfl⟩
    exact natValue_lt hω i.isLt

end KP1Y.Named

namespace KP1Y.ReflectionModel
open YesMetaZFC YesMetaZFC.SetTheory
open KP1Y.Named
universe u

abbrev Numbers (α : Type u) := Fin 7 → α

structure Numerals (M : SetTheory.Structure.{u}) (ω : M.Domain) (N : Numbers M.Domain) : Prop where
  omega : M.IsOmega ω
  values : ∀ i, N i=natValue omega i.val

theorem numerals_exists {M : SetTheory.Structure.{u}} {ω : M.Domain} (hω : M.IsOmega ω) : ∃ N, Numerals M ω N :=
  ⟨fun i => natValue hω i.val,hω,fun _ => rfl⟩

theorem Numerals.natural {M : SetTheory.Structure.{u}} {ω : M.Domain} {N : Numbers M.Domain} (h : Numerals M ω N) (i : Fin 7) :
    M.mem (N i) ω := h.values i ▸ natValue_nat h.omega i.val

theorem Numerals.lt {M : SetTheory.Structure.{u}} {ω : M.Domain} {N : Numbers M.Domain} (h : Numerals M ω N)
    {i j : Fin 7} (hij : i.val<j.val) : M.mem (N i) (N j) := by
  rw [h.values i,h.values j]
  exact natValue_lt h.omega hij

theorem Numerals.injective_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory) {ω : M.Domain} {N : Numbers M.Domain}
    (h : Numerals M ω N) {i j : Fin 7} (hij : N i=N j) : i=j := by
  apply Fin.ext
  apply natValue_injective_d hM h.omega
  exact (h.values i).symm.trans (hij.trans (h.values j))

theorem Numerals.zero_empty {M : SetTheory.Structure.{u}} {ω : M.Domain} {N : Numbers M.Domain} (h : Numerals M ω N) :
    ∀ x, ¬M.mem x (N 0) := by
  rw [h.values 0]
  exact natValue_zero_empty h.omega

theorem Numerals.symbols_iff {M : SetTheory.Structure.{u}} (he : Extensional M) {ω : M.Domain} {N : Numbers M.Domain}
    (h : Numerals M ω N) (r : M.Domain) : M.mem r (N 6) ↔ ∃ i : Fin 6, r=N i.castSucc := by
  simp only [h.values]
  exact natValue_members_iff he h.omega 6 r

theorem Numerals.symbol_mem {M : SetTheory.Structure.{u}} {ω : M.Domain} {N : Numbers M.Domain}
    (h : Numerals M ω N) (i : Fin 6) : M.mem (N i.castSucc) (N 6) := h.lt i.isLt

end KP1Y.ReflectionModel
