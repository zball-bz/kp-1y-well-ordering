import KP1Y.CollectedHistories

/-! Σ₁ 集合值递归的极限步骤：兼容历史取并，前缀及一步证书仍有实际集合界。 -/
namespace KP1Y.SigmaRecursion
open YesMetaZFC YesMetaZFC.SetTheory YesMetaZFC.SetTheory.Definitional
open KP1Y.Kuratowski KP1Y.Functions
universe u

theorem history_limit_from_family {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {step : M.Domain → M.Domain → M.Domain → M.Domain → Prop}
    {Γ δ C Q D W : M.Domain} (hδ : M.IsLimitOrdinal δ) (hδΓ : M.MemberSubset δ Γ)
    (hFun : Functional M Γ step) (hFamily : CollectedFamily M step δ C Q D W) :
    ∃ U, ValueHistory M step U δ W Q := by
  have hsmall {ε : M.Domain} (hε : M.mem ε δ) : M.MemberSubset ε Γ :=
    fun i hi => hδΓ i (hδ.1.transitive ε hε i hi)
  obtain ⟨U,hU⟩ := SetTheory.KP.exists_union (KP1Y.models_weakKP hM) D
  have hAgree : ∀ H ε V R, M.mem H D → M.mem ε δ → ValueHistory M step H ε V R →
      ∀ i, M.mem i ε → ∀ v, MemPair M U i v ↔ MemPair M H i v := by
    intro H ε V R hHD hε hH i hi v
    constructor
    · rintro ⟨p,hp,hcode⟩
      obtain ⟨J,hJD,hpJ⟩ := (hU p).mp hp
      obtain ⟨ζ,hζ,_,B,_,V',_,R',_,hJ⟩ := (hFamily.members J).mp hJD
      have hiζ := (hJ.values.bounds hM.1 ⟨p,hpJ,hcode⟩).1
      exact (history_overlap hM (hδ.1.mem hε) (hδ.1.mem hζ)
        (hsmall hε) (hsmall hζ) hFun hH hJ i hi hiζ v).mpr ⟨p,hpJ,hcode⟩
    · rintro ⟨p,hp,hcode⟩
      exact ⟨p,(hU p).mpr ⟨H,hHD,hp⟩,hcode⟩
  have hGraph : Graph M U δ W := by
    refine ⟨?_,?_,?_⟩
    · intro p hp
      obtain ⟨H,hHD,hpH⟩ := (hU p).mp hp
      obtain ⟨ε,hε,_,B,hBC,V,hVB,R,_,hH⟩ := (hFamily.members H).mp hHD
      obtain ⟨i,hi,v,hv,hcode⟩ := hH.values.support p hpH
      exact ⟨i,hδ.1.transitive ε hε i hi,v,hFamily.pools B hBC V hVB v hv,hcode⟩
    · intro i hi
      obtain ⟨ε,hε,hiε⟩ := hδ.2.2 i hi
      obtain ⟨H,hHC,B,hBC,hCert⟩ := hFamily.total ε hε
      have hHD := (hFamily.members H).mpr ⟨ε,hε,hHC,B,hBC,hCert⟩
      obtain ⟨V,hVB,R,_,hH⟩ := hCert
      obtain ⟨v,hv,hHv⟩ := hH.values.total i hiε
      exact ⟨v,hFamily.pools B hBC V hVB v hv,(hAgree H ε V R hHD hε hH i hiε v).mpr hHv⟩
    · intro i v v' hUv hUv'
      obtain ⟨p,hp,hcode⟩ := hUv
      obtain ⟨H,hHD,hpH⟩ := (hU p).mp hp
      obtain ⟨ε,hε,_,B,_,V,_,R,_,hH⟩ := (hFamily.members H).mp hHD
      have hiε := (hH.values.bounds hM.1 ⟨p,hpH,hcode⟩).1
      exact hH.values.unique i v v' ⟨p,hpH,hcode⟩
        ((hAgree H ε V R hHD hε hH i hiε v').mp hUv')
  refine ⟨U,hGraph,hFamily.graph.mono_values hFamily.candidates,?_⟩
  intro i hi P _ v _ hQi hUi
  obtain ⟨_,hPC,Bi,hBi,hCertPi⟩ := (hFamily.rows i P).mp hQi
  have hPD := (hFamily.members P).mpr ⟨i,hi,hPC,Bi,hBi,hCertPi⟩
  obtain ⟨Vi,hVi,Ri,_,hPi⟩ := hCertPi
  have hPref : Prefix M P U i W := by
    refine ⟨hPi.values.mono_values (hFamily.pools Bi hBi Vi hVi),?_⟩
    exact fun j hj a _ => (hAgree P i Vi Ri hPD hi hPi j hj a).symm
  obtain ⟨ε,hε,hiε⟩ := hδ.2.2 i hi
  obtain ⟨H,hHC,B,hBC,hCertH⟩ := hFamily.total ε hε
  have hHD := (hFamily.members H).mpr ⟨ε,hε,hHC,B,hBC,hCertH⟩
  obtain ⟨V,hVB,R,_,hH⟩ := hCertH
  obtain ⟨S,hSV,hRi⟩ := hH.prefixes.total i hiε
  obtain ⟨a,haV,hHi⟩ := hH.values.total i hiε
  obtain ⟨hS,w,hw,hStep⟩ := hH.obeys i hiε S hSV a haV hRi hHi
  have hPS : P=S := by
    apply hPi.values.ext hM.1 hS.graph
    intro j hj value
    have hjε := (hδ.1.mem hε).transitive i hiε j hj
    exact (history_overlap hM (hδ.1.mem hi) (hδ.1.mem hε)
      (hsmall hi) (hsmall hε) hFun hPi hH j hj hjε value).trans
        (hS.all_rows hM.1 hH.values j hj value).symm
  have hva : v=a := hGraph.unique i v a hUi ((hAgree H ε V R hHD hε hH i hiε a).mpr hHi)
  have hStepP : step i P a w := hPS.symm ▸ hStep
  exact ⟨hPref,w,hFamily.pools B hBC V hVB w hw,hva.symm ▸ hStepP⟩

theorem history_limit_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {n : Nat} (φ : StepMatrix n) (env : Env M n) {Γ δ : M.Domain}
    (hδ : M.IsLimitOrdinal δ) (hδΓ : M.MemberSubset δ Γ) (hFun : Functional M Γ (φ.denote env))
    (ih : ∀ i, M.mem i δ → ∃ H B, Certificate M (φ.denote env) i H B) :
    ∃ U V Q, ValueHistory M (φ.denote env) U δ V Q := by
  obtain ⟨C,Q,D,W,hFamily⟩ := collect_histories_d hM φ env hδ.1 hδΓ hFun ih
  obtain ⟨U,hU⟩ := history_limit_from_family hM hδ hδΓ hFun hFamily
  exact ⟨U,W,Q,hU⟩

theorem certificate_limit_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {n : Nat} (φ : StepMatrix n) (env : Env M n) {Γ δ : M.Domain}
    (hδ : M.IsLimitOrdinal δ) (hδΓ : M.MemberSubset δ Γ) (hFun : Functional M Γ (φ.denote env))
    (ih : ∀ i, M.mem i δ → ∃ H B, Certificate M (φ.denote env) i H B) :
    ∃ H B, Certificate M (φ.denote env) δ H B := by
  obtain ⟨H,V,Q,hH⟩ := history_limit_d hM φ env hδ hδΓ hFun ih
  obtain ⟨B,hB⟩ := certificate_exists hM hH
  exact ⟨H,B,hB⟩

end KP1Y.SigmaRecursion
