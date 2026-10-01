import KP1Y.OrdinalRank
import KP1Y.AssignmentTuple

/-! 实际单射函数与序数排名复合，仍得到实际序数排名。 -/
namespace KP1Y.Ranking
open YesMetaZFC YesMetaZFC.SetTheory
open KP1Y.Kuratowski KP1Y.Functions KP1Y.Assignments
universe u

theorem rank_pullback_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {G X Y F Γ : M.Domain} (hG : Graph M G X Y)
    (hGInj : ∀ x y a, MemPair M G x a → MemPair M G y a → x=y) (hRank : OrdinalRank M F Y Γ) :
    ∃ R, OrdinalRank M R X Γ := by
  obtain ⟨R,hValue⟩ := tuple_value_exists_d hM hG hRank.graph
  refine ⟨R,hRank.ordinal,hValue.values,?_⟩
  intro x y r hxr hyr
  have hx := (hValue.values.bounds hM.1 hxr).1
  have hy := (hValue.values.bounds hM.1 hyr).1
  have hr := (hValue.values.bounds hM.1 hxr).2
  obtain ⟨a,ha,hxa⟩ := hG.total x hx
  obtain ⟨b,hb,hyb⟩ := hG.total y hy
  have hFar := (hValue.rows x hx a ha r hr hxa).mp hxr
  have hFbr := (hValue.rows y hy b hb r hr hyb).mp hyr
  have hab := hRank.injective a b r hFar hFbr
  subst b
  exact hGInj x y a hxa hyb

end KP1Y.Ranking
