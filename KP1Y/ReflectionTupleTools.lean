import KP1Y.ReflectionNumerals

/-! 固定小元数的真实元组图构造；不枚举任意内部ω长度。 -/
namespace KP1Y.ReflectionModel
open YesMetaZFC YesMetaZFC.SetTheory
open KP1Y.Kuratowski KP1Y.Functions KP1Y.Named
universe u

def tupleName (n : Fin 7) (i : Fin n.val) : Fin 7 := ⟨i.val,Nat.lt_trans i.isLt n.isLt⟩

theorem fixed_tuple_exists_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory) {ω A : M.Domain} {N : Numbers M.Domain}
    (hN : Numerals M ω N) (n : Fin 7) (values : Fin n.val → M.Domain) (hValues : ∀ i, M.mem (values i) A) :
    ∃ t, Graph M t (N n) A ∧ ∀ i, MemPair M t (N (tupleName n i)) (values i) := by
  obtain ⟨t,hT,hRead⟩ := finite_assignment_exists_d hM hN.omega values hValues
  refine ⟨t,?_,?_⟩
  · rw [hN.values n]
    exact hT
  · intro i
    rw [hN.values (tupleName n i)]
    exact hRead i

theorem fixed_tuple_unique {M : SetTheory.Structure.{u}} (he : Extensional M) {ω A B t s : M.Domain} {N : Numbers M.Domain}
    (hN : Numerals M ω N) (n : Fin 7) (values : Fin n.val → M.Domain)
    (hT : Graph M t (N n) A) (hS : Graph M s (N n) B)
    (hReadT : ∀ i, MemPair M t (N (tupleName n i)) (values i))
    (hReadS : ∀ i, MemPair M s (N (tupleName n i)) (values i)) : t=s := by
  apply hT.ext he hS
  intro x hx y
  rw [hN.values n] at hx
  obtain ⟨i,hi⟩ := (natValue_members_iff he hN.omega n.val x).mp hx
  have hxi : x=N (tupleName n i) := hi.trans (hN.values (tupleName n i)).symm
  clear hi
  subst x
  constructor
  · intro hxy
    exact (hT.unique (N (tupleName n i)) (values i) y (hReadT i) hxy) ▸ hReadS i
  · intro hxy
    exact (hS.unique (N (tupleName n i)) (values i) y (hReadS i) hxy) ▸ hReadT i

end KP1Y.ReflectionModel
