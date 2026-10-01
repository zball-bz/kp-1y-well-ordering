import KP1Y.SigmaHistoryUnique

/-! 对集合值递归历史作实际限制，保持前缀函数与全部一步证书。 -/
namespace KP1Y.SigmaRecursion
open YesMetaZFC YesMetaZFC.SetTheory YesMetaZFC.SetTheory.Definitional
open KP1Y.Kuratowski KP1Y.Functions
universe u

theorem history_prefix_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {step : M.Domain → M.Domain → M.Domain → M.Domain → Prop} {H δ V Q ρ : M.Domain}
    (hρ : M.IsOrdinal ρ) (hρδ : M.MemberSubset ρ δ) (hH : ValueHistory M step H δ V Q) :
    ∃ J R, ValueHistory M step J ρ V R ∧
      ∀ i v, MemPair M J i v ↔ M.mem i ρ ∧ MemPair M H i v := by
  obtain ⟨J,hJ,hRows⟩ := restrict_graph_d hM hH.values hρδ
  obtain ⟨R,hR,hPrefixRows⟩ := restrict_graph_d hM hH.prefixes hρδ
  refine ⟨J,R,⟨hJ,hR,?_⟩,hRows⟩
  intro i hi P hP v hv hRP hJv
  have hQP := ((hPrefixRows i P).mp hRP).2
  have hHv := ((hRows i v).mp hJv).2
  obtain ⟨hPref,w,hw,hStep⟩ := hH.obeys i (hρδ i hi) P hP v hv hQP hHv
  refine ⟨?_,w,hw,hStep⟩
  apply hPref.transport hM.1 hH.values (fun _ h => h)
  intro j hj y
  have hjρ := hρ.transitive i hi j hj
  exact ((hRows j y).trans ⟨And.right,fun h => ⟨hjρ,h⟩⟩).symm

theorem certificate_prefix_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {step : M.Domain → M.Domain → M.Domain → M.Domain → Prop} {H δ B ρ : M.Domain}
    (hρ : M.IsOrdinal ρ) (hρδ : M.MemberSubset ρ δ) (hH : Certificate M step δ H B) :
    ∃ J C, Certificate M step ρ J C ∧
      ∀ i v, MemPair M J i v ↔ M.mem i ρ ∧ MemPair M H i v := by
  obtain ⟨V,_,Q,_,hH⟩ := hH
  obtain ⟨J,R,hJ,hRows⟩ := history_prefix_d hM hρ hρδ hH
  obtain ⟨C,hC⟩ := certificate_exists hM hJ
  exact ⟨J,C,hC,hRows⟩

theorem history_overlap {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {step : M.Domain → M.Domain → M.Domain → M.Domain → Prop}
    {Γ δ ε H J V W Q R : M.Domain} (hδ : M.IsOrdinal δ) (hε : M.IsOrdinal ε)
    (hδΓ : M.MemberSubset δ Γ) (hεΓ : M.MemberSubset ε Γ) (hFun : Functional M Γ step)
    (hH : ValueHistory M step H δ V Q) (hJ : ValueHistory M step J ε W R) :
    ∀ i, M.mem i δ → M.mem i ε → ∀ v, MemPair M H i v ↔ MemPair M J i v := by
  have hw := KP1Y.models_weakKP hM
  rcases Structure.IsOrdinal.trichotomy hM.1 hδ hε
    (SetTheory.KP.difference_exists_d hw) (SetTheory.KP.intersection_exists_d hw δ ε) with
    he | hδε | hεδ
  · have heq := hM.1.eq_of_same_members δ ε he
    cases heq
    intro i hi _ v
    exact history_rows_agree hM hδ hδΓ hFun hH hJ i hi v
  · obtain ⟨P,S,hP,hRows⟩ := history_prefix_d hM hδ (hε.transitive δ hδε) hJ
    intro i hi _ v
    have hPJ := (hRows i v).trans ⟨And.right,fun h => ⟨hi,h⟩⟩
    exact (history_rows_agree hM hδ hδΓ hFun hH hP i hi v).trans hPJ
  · obtain ⟨P,S,hP,hRows⟩ := history_prefix_d hM hε (hδ.transitive ε hεδ) hH
    intro i _ hi v
    have hPH := (hRows i v).trans ⟨And.right,fun h => ⟨hi,h⟩⟩
    exact hPH.symm.trans (history_rows_agree hM hε hεΓ hFun hP hJ i hi v)

end KP1Y.SigmaRecursion
