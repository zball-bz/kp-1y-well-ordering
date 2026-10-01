import KP1Y.CountableNamedSpaces

/-! 初等高度所需种子 ω∪{ω,γ} 的实际可数枚举，值域位于给定序数κ。 -/
namespace KP1Y.Closure
open YesMetaZFC YesMetaZFC.SetTheory
open KP1Y.Kuratowski KP1Y.Functions KP1Y.Cardinal KP1Y.Iteration
universe u

structure HeightSeed (M : SetTheory.Structure.{u}) (ω κ γ base : M.Domain) : Prop where
  graph : Graph M base ω κ
  naturals : ∀ n, M.mem n ω → Reached M ω base n
  omega : Reached M ω base ω
  point : Reached M ω base γ

theorem height_seed_exists_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {ω κ γ : M.Domain} (hω : M.IsOmega ω) (hκ : M.IsOrdinal κ) (hωκ : M.mem ω κ) (hγκ : M.mem γ κ) :
    ∃ base, HeightSeed M ω κ γ base := by
  obtain ⟨EOmega,hEOmega⟩ := identity_onto_d hM ω
  obtain ⟨SOmega,ESOmega,hSOmega,hESOmega⟩ := constant_onto_singleton_d hM hω ω
  obtain ⟨S0,E0,hS0,hE0⟩ := countable_union_d hM hω hEOmega hESOmega
  obtain ⟨SGamma,ESGamma,hSGamma,hESGamma⟩ := constant_onto_singleton_d hM hω γ
  obtain ⟨S,base,hS,hBase⟩ := countable_union_d hM hω hE0 hESGamma
  have hSub : M.MemberSubset S κ := by
    intro x hx
    rcases (hS x).mp hx with hx | hx
    · rcases (hS0 x).mp hx with hx | hx
      · exact hκ.transitive ω hωκ x hx
      · exact (hSOmega x).mp hx ▸ hωκ
    · exact (hSGamma x).mp hx ▸ hγκ
  refine ⟨base,(hBase.toGraph hM.1).mono_values hSub,?_,?_,?_⟩
  · intro n hn
    exact hBase.2.2.2 n ((hS n).mpr (Or.inl ((hS0 n).mpr (Or.inl hn))))
  · exact hBase.2.2.2 ω ((hS ω).mpr (Or.inl ((hS0 ω).mpr (Or.inr ((hSOmega ω).mpr rfl)))))
  · exact hBase.2.2.2 γ ((hS γ).mpr (Or.inr ((hSGamma γ).mpr rfl)))

end KP1Y.Closure
