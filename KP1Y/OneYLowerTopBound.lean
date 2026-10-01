import KP1Y.OneYReconstructionRecovery
import KP1Y.OneYLowerCopyNesting

/-! Lower顶部约束从真实相邻上层的选择与高度几何导出。 -/
namespace KP1Y.OneYFinite.CopiedMountain.Lower
open YesMetaZFC YesMetaZFC.SetTheory YesMetaZFC.SetTheory.Definitional
open KP1Y.Kuratowski KP1Y.Functions KP1Y.Naturals KP1Y.Bounded
universe u

/-- 已选提取父边严格降低原列高度。后续由严格高度森林的真实祖先读取解除。 -/
def ExtractedHeightDecrease (M : SetTheory.Structure.{u}) (X : Data M.Domain) (Q : M.Domain) : Prop :=
  ∀c p hc hp, MemPair M Q c p → MemPair M X.heights c hc → MemPair M X.heights p hp → M.mem hp hc

/-- 若严格高度条件成立，任何同高度伪父都不能有更小正Top值。 -/
theorem pseudo_top_bound_of_decreasing_selection_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {X : Data M.Domain} (_hX : X.Valid M C)
    {Top P Q : M.Domain} (hTop : Graph M Top X.width C.omega)
    (hPositive : ∀c t, MemPair M Top c t → M.mem C.zero t)
    (hP : GraphPseudoForest M C X P) (hSelect : Selects true M C X.width P Top Q)
    (hDecrease : ExtractedHeightDecrease M X Q) : ReconstructionSelection.PseudoTopBound M C X Top := by
  intro c p height tc tp hPseudo hHC hHP hTC hTP
  have hPC := (hP.rows c p).mpr hPseudo
  have hTCNat := (hTop.bounds hM.1 hTC).2
  have hTPNat := (hTop.bounds hM.1 hTP).2
  rcases (omega_isOrdinal_d hM hC.omega).wellOrder.linear.compare tc hTCNat tp hTPNat with he | hlt | hgt
  · exact Or.inl (hM.1.eq_of_same_members tc tp he)
  · exact Or.inr hlt
  · have hRestricted : RestrictedParent true M C X.width P Top c p :=
      ⟨⟨ancestor_direct_d hM hC hP.forest hPC,tp,hTPNat,tc,hTCNat,hTP,hTC,hgt,hPositive p tp hTP⟩,
        fun q _ hQ => ancestor_le_parent_d hM hC hP.forest hPC hQ.1⟩
    have hSelected := (hSelect.parents c p).mpr hRestricted
    exact False.elim (SetTheory.KP.mem_irrefl_d (KP1Y.models_weakKP hM) height (hDecrease c p height height hSelected hHC hHP))

end KP1Y.OneYFinite.CopiedMountain.Lower
