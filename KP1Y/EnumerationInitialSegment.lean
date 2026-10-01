import KP1Y.AugmentedClosure
import KP1Y.HeightSeed

/-! 给定全局正初段枚举后，可数且对它封闭的子集是严格较小的序数初始段。 -/
namespace KP1Y.Closure
open YesMetaZFC YesMetaZFC.SetTheory
open KP1Y.Kuratowski KP1Y.Functions KP1Y.Cardinal
universe u

structure UniformEnumeration (M : SetTheory.Structure.{u}) (ω κ Keys e : M.Domain) : Prop where
  keys : IsProduct M Keys κ ω
  graph : Graph M e Keys κ
  positive_range : ∀ a, M.mem a κ → (∃ z, M.mem z a) → ∀ n, M.mem n ω →
    ∀ key, Codes M key a n → ∀ x, MemPair M e key x → M.mem x a
  covers : ∀ a, M.mem a κ → ∀ x, M.mem x a → ∃ n, M.mem n ω ∧
    ∃ key, M.mem key Keys ∧ Codes M key a n ∧ MemPair M e key x

theorem enumeration_closed_transitive {M : SetTheory.Structure.{u}}
    {ω κ Keys e X : M.Domain} (hEnum : UniformEnumeration M ω κ Keys e)
    (hSub : M.MemberSubset X κ) (hClosed : EnumerationClosed M ω e X) : M.TransitiveSet X := by
  intro a ha x hx
  obtain ⟨n,hn,key,_,hCode,hAt⟩ := hEnum.covers a (hSub a ha) x hx
  exact hClosed a ha n hn key hCode x hAt

theorem countable_initial_segment_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {ω κ Keys e X f : M.Domain} (hκ : UncountableOrdinal M ω κ)
    (hEnum : UniformEnumeration M ω κ Keys e) (hSub : M.MemberSubset X κ)
    (hCountable : Onto M f ω X) (hClosed : EnumerationClosed M ω e X) : M.IsOrdinal X ∧ M.mem X κ := by
  have hOrd := hκ.1.of_transitive_subset hSub (enumeration_closed_transitive hEnum hSub hClosed)
  refine ⟨hOrd,?_⟩
  rcases KP1Y.Naturals.ordinal_subset_cases_d hM hOrd hκ.1 hSub with he | hXκ
  · have hOnto : Onto M f ω κ := by simpa only [he] using hCountable
    exact False.elim (hκ.2.2 ⟨f,hOnto⟩)
  · exact hXκ

end KP1Y.Closure
