import KP1Y.CountableSections
import KP1Y.OrdinalRank

/-! 实际ω满射通过最小原像截面给出到ω的单射排名。 -/
namespace KP1Y.Ranking
open YesMetaZFC YesMetaZFC.SetTheory
open KP1Y.Kuratowski KP1Y.Cardinal
universe u

theorem countable_rank_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory) {ω X E : M.Domain}
    (hω : M.IsOmega ω) (hE : Onto M E ω X) : ∃ R, OrdinalRank M R X ω := by
  obtain ⟨R,hR,hRows⟩ := least_section_exists_d hM hω hE
  refine ⟨R,KP1Y.Naturals.omega_isOrdinal_d hM hω,hR,?_⟩
  intro x y n hxn hyn
  exact (hE.toGraph hM.1).unique n x y (hRows x n hxn) (hRows y n hyn)

end KP1Y.Ranking
