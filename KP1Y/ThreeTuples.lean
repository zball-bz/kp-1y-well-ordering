import KP1Y.BinaryTuples

/-! 配对和并集公式所需的三个变量名及真实三项赋值图。 -/
namespace KP1Y.Naturals
open YesMetaZFC YesMetaZFC.SetTheory
universe u

theorem SmallNaturals.zero_ne_two {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {ω zero one two : M.Domain} (h : SmallNaturals M ω zero one two) : zero≠two := by
  intro he
  exact SetTheory.KP.mem_irrefl_d (KP1Y.models_weakKP hM) two (he ▸ h.zero_mem_two)

theorem SmallNaturals.one_ne_two {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {ω zero one two : M.Domain} (h : SmallNaturals M ω zero one two) : one≠two := by
  intro he
  exact SetTheory.KP.mem_irrefl_d (KP1Y.models_weakKP hM) two (he ▸ h.two_succ.predecessor_mem)

theorem SmallNaturals.three_exists {M : SetTheory.Structure.{u}} {ω zero one two : M.Domain}
    (hω : M.IsOmega ω) (h : SmallNaturals M ω zero one two) : ∃ three, M.SuccessorOf three two ∧ M.mem three ω :=
  hω.1.2 two h.two_nat

end KP1Y.Naturals

namespace KP1Y.Sequences
open YesMetaZFC YesMetaZFC.SetTheory
open KP1Y.Kuratowski KP1Y.Functions KP1Y.Naturals
universe u

theorem triple_tuple_exists_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {ω zero one two three A x y z : M.Domain} (hN : SmallNaturals M ω zero one two)
    (hThree : M.SuccessorOf three two) (hx : M.mem x A) (hy : M.mem y A) (hz : M.mem z A) :
    ∃ t, Graph M t three A ∧ MemPair M t zero x ∧ MemPair M t one y ∧ MemPair M t two z := by
  obtain ⟨s,hS,h0,h1⟩ := binary_tuple_exists_d hM hN hx hy
  obtain ⟨t,hT,hRows⟩ := append_graph_d hM hS hThree (fun _ h => h) hz
  exact ⟨t,hT,(hRows zero x).mpr (Or.inl h0),(hRows one y).mpr (Or.inl h1),
    (hRows two z).mpr (Or.inr ⟨rfl,rfl⟩)⟩

end KP1Y.Sequences
