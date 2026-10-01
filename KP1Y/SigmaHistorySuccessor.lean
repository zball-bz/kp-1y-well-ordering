import KP1Y.SigmaHistoryPrefix

/-! 给集合值历史追加一个序数阶段，同时加入新值、一步证书和完整旧前缀。 -/
namespace KP1Y.SigmaRecursion
open YesMetaZFC YesMetaZFC.SetTheory YesMetaZFC.SetTheory.Definitional
open KP1Y.Kuratowski KP1Y.Functions
universe u

private theorem enlarge_pool {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    (V a b c : M.Domain) : ∃ W, M.MemberSubset V W ∧ M.mem a W ∧ M.mem b W ∧ M.mem c W := by
  have hw := KP1Y.models_weakKP hM
  obtain ⟨V1,h1⟩ := SetTheory.KP.exists_insert hw V a
  obtain ⟨V2,h2⟩ := SetTheory.KP.exists_insert hw V1 b
  obtain ⟨W,h3⟩ := SetTheory.KP.exists_insert hw V2 c
  refine ⟨W,?_,?_,?_,?_⟩
  · intro x hx
    exact (h3 x).mpr (Or.inl ((h2 x).mpr (Or.inl ((h1 x).mpr (Or.inl hx)))))
  · exact (h3 a).mpr (Or.inl ((h2 a).mpr (Or.inl ((h1 a).mpr (Or.inr rfl)))))
  · exact (h3 b).mpr (Or.inl ((h2 b).mpr (Or.inr rfl)))
  · exact (h3 c).mpr (Or.inr rfl)

theorem history_successor_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {step : M.Domain → M.Domain → M.Domain → M.Domain → Prop}
    {Γ δ γ H V Q : M.Domain} (hδ : M.IsOrdinal δ) (hδΓ : M.mem δ Γ)
    (hSucc : M.SuccessorOf γ δ) (hTotal : Total M Γ step) (hH : ValueHistory M step H δ V Q) :
    ∃ J W R, ValueHistory M step J γ W R := by
  have hw := KP1Y.models_weakKP hM
  obtain ⟨v,w,hStep⟩ := hTotal δ hδΓ H V hH.values
  obtain ⟨W,hVW,hHW,hvW,hwW⟩ := enlarge_pool hM V H v w
  obtain ⟨J,hJ,hJRows⟩ := append_graph_d hM hH.values hSucc hVW hvW
  obtain ⟨R,hR,hRRows⟩ := append_graph_d hM hH.prefixes hSucc hVW hHW
  have hOldRows : ∀ i, M.mem i δ → ∀ a, MemPair M H i a ↔ MemPair M J i a := by
    intro i hi a
    have hne : i ≠ δ := by
      intro he
      cases he
      exact SetTheory.KP.mem_irrefl_d hw δ hi
    exact ((hJRows i a).trans (by simp only [hne,false_and,or_false])).symm
  refine ⟨J,W,R,hJ,hR,?_⟩
  intro i hi P hP value hvalue hRP hJvalue
  rcases (hSucc i).mp hi with hiδ | he
  · have hne : i ≠ δ := by
      intro he
      cases he
      exact SetTheory.KP.mem_irrefl_d hw δ hiδ
    have hQP : MemPair M Q i P := by
      rcases (hRRows i P).mp hRP with h | h
      · exact h
      · exact False.elim (hne h.1)
    have hHvalue := (hOldRows i hiδ value).mpr hJvalue
    obtain ⟨hPref,z,hz,hzStep⟩ := hH.obeys i hiδ P (hH.prefixes.bounds hM.1 hQP).2
      value (hH.values.bounds hM.1 hHvalue).2 hQP hHvalue
    refine ⟨?_,z,hVW z hz,hzStep⟩
    exact hPref.transport hM.1 hH.values hVW
      (fun j hj a => hOldRows j (hδ.transitive i hiδ j hj) a)
  · have hiδ := hM.1.eq_of_same_members i δ he
    subst i
    have hPH : P=H := by
      rcases (hRRows δ P).mp hRP with h | h
      · exact False.elim (SetTheory.KP.mem_irrefl_d hw δ (hH.prefixes.bounds hM.1 h).1)
      · exact h.2
    have hvaluev : value=v := by
      rcases (hJRows δ value).mp hJvalue with h | h
      · exact False.elim (SetTheory.KP.mem_irrefl_d hw δ (hH.values.bounds hM.1 h).1)
      · exact h.2
    subst P
    subst value
    exact ⟨⟨hH.values.mono_values hVW,fun j hj a _ => hOldRows j hj a⟩,w,hwW,hStep⟩

theorem certificate_successor_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {step : M.Domain → M.Domain → M.Domain → M.Domain → Prop}
    {Γ δ γ H B : M.Domain} (hδ : M.IsOrdinal δ) (hδΓ : M.mem δ Γ)
    (hSucc : M.SuccessorOf γ δ) (hTotal : Total M Γ step) (hH : Certificate M step δ H B) :
    ∃ J C, Certificate M step γ J C := by
  obtain ⟨V,_,Q,_,hH⟩ := hH
  obtain ⟨J,W,R,hJ⟩ := history_successor_d hM hδ hδΓ hSucc hTotal hH
  obtain ⟨C,hC⟩ := certificate_exists hM hJ
  exact ⟨J,C,hC⟩

end KP1Y.SigmaRecursion
