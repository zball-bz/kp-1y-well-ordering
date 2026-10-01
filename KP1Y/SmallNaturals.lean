import KP1Y.NaturalNumbers

/-! 明确固定对象语言中0、1、2的含义，而非只假定三个不同标签。 -/
namespace KP1Y.Naturals
open YesMetaZFC YesMetaZFC.SetTheory
universe u

structure SmallNaturals (M : SetTheory.Structure.{u}) (ω zero one two : M.Domain) : Prop where
  zero_empty : ∀ x, ¬M.mem x zero
  zero_nat : M.mem zero ω
  one_succ : M.SuccessorOf one zero
  one_nat : M.mem one ω
  two_succ : M.SuccessorOf two one
  two_nat : M.mem two ω

theorem small_naturals_exist {M : SetTheory.Structure.{u}} {ω : M.Domain} (hω : M.IsOmega ω) :
    ∃ zero one two, SmallNaturals M ω zero one two := by
  obtain ⟨zero,hZero,hZeroNat⟩ := hω.1.1
  obtain ⟨one,hOne,hOneNat⟩ := hω.1.2 zero hZeroNat
  obtain ⟨two,hTwo,hTwoNat⟩ := hω.1.2 one hOneNat
  exact ⟨zero,one,two,hZero,hZeroNat,hOne,hOneNat,hTwo,hTwoNat⟩

theorem SmallNaturals.one_members {M : SetTheory.Structure.{u}} (he : Extensional M)
    {ω zero one two : M.Domain} (h : SmallNaturals M ω zero one two) (x : M.Domain) : M.mem x one ↔ x=zero := by
  constructor
  · intro hx
    rcases (h.one_succ x).mp hx with hx | hx
    · exact False.elim (h.zero_empty x hx)
    · exact he.eq_of_same_members x zero hx
  · intro hx
    subst x
    exact h.one_succ.predecessor_mem

theorem SmallNaturals.two_members {M : SetTheory.Structure.{u}} (he : Extensional M)
    {ω zero one two : M.Domain} (h : SmallNaturals M ω zero one two) (x : M.Domain) : M.mem x two ↔ x=zero ∨ x=one := by
  constructor
  · intro hx
    rcases (h.two_succ x).mp hx with hx | hx
    · exact Or.inl ((h.one_members he x).mp hx)
    · exact Or.inr (he.eq_of_same_members x one hx)
  · rintro (hx | hx)
    · exact (h.two_succ x).mpr (Or.inl ((h.one_members he x).mpr hx))
    · subst x
      exact h.two_succ.predecessor_mem

theorem SmallNaturals.zero_ne_one {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {ω zero one two : M.Domain} (h : SmallNaturals M ω zero one two) : zero≠one := by
  intro he
  have hSelf : M.mem one one := he ▸ h.one_succ.predecessor_mem
  exact SetTheory.KP.mem_irrefl_d (KP1Y.models_weakKP hM) one hSelf

theorem SmallNaturals.zero_mem_two {M : SetTheory.Structure.{u}} {ω zero one two : M.Domain}
    (h : SmallNaturals M ω zero one two) : M.mem zero two := (h.two_succ zero).mpr (Or.inl h.one_succ.predecessor_mem)

end KP1Y.Naturals
