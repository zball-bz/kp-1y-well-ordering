import KP1Y.SmallNaturals
import KP1Y.SequenceAppend

/-! 纯集合语言原子所需的真实二元函数元组。 -/
namespace KP1Y.Sequences
open YesMetaZFC YesMetaZFC.SetTheory
open KP1Y.Kuratowski KP1Y.Functions KP1Y.Naturals
universe u

theorem binary_tuple_exists_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {ω zero one two A x y : M.Domain} (hN : SmallNaturals M ω zero one two) (hx : M.mem x A) (hy : M.mem y A) :
    ∃ t, Graph M t two A ∧ MemPair M t zero x ∧ MemPair M t one y := by
  obtain ⟨t0,hT0,hRows0⟩ := append_graph_d hM (empty_graph (V := A) hN.zero_empty) hN.one_succ (fun _ h => h) hx
  obtain ⟨t,hT,hRows⟩ := append_graph_d hM hT0 hN.two_succ (fun _ h => h) hy
  refine ⟨t,hT,?_,?_⟩
  · exact (hRows zero x).mpr (Or.inl ((hRows0 zero x).mpr (Or.inr ⟨rfl,rfl⟩)))
  · exact (hRows one y).mpr (Or.inr ⟨rfl,rfl⟩)

theorem binary_tuple_unique {M : SetTheory.Structure.{u}} (he : Extensional M)
    {ω zero one two A B t u x y : M.Domain} (hN : SmallNaturals M ω zero one two)
    (ht : Graph M t two A) (hu : Graph M u two B)
    (ht0 : MemPair M t zero x) (ht1 : MemPair M t one y)
    (hu0 : MemPair M u zero x) (hu1 : MemPair M u one y) : t=u := by
  apply ht.ext he hu
  intro i hi a
  rcases (hN.two_members he i).mp hi with heq | heq
  · subst i
    constructor
    · intro hAt
      have hax := ht.unique zero a x hAt ht0
      subst a
      exact hu0
    · intro hAt
      have hax := hu.unique zero a x hAt hu0
      subst a
      exact ht0
  · subst i
    constructor
    · intro hAt
      have hay := ht.unique one a y hAt ht1
      subst a
      exact hu1
    · intro hAt
      have hay := hu.unique one a y hAt hu1
      subst a
      exact ht1

end KP1Y.Sequences
