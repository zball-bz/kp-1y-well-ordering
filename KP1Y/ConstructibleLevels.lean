import KP1Y.LevelCertificateSyntax

/-! 独立层Lα的存在、证书唯一性及任意较长历史中的相容解释。 -/
namespace KP1Y.Constructible
open YesMetaZFC YesMetaZFC.SetTheory YesMetaZFC.SetTheory.Definitional
open KP1Y.Kuratowski KP1Y.Functions KP1Y.SetLanguage
universe u

theorem level_certificate_from_history_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {env : Env M 24} {α T δ H V Q : M.Domain} (hα : M.IsOrdinal α) (hs : M.SuccessorOf δ α)
    (h : KP1Y.SigmaRecursion.ValueHistory M (levelStepMatrix.denote env) H δ V Q) (hAt : MemPair M H α T) :
    ∃ B, LevelCertificate M env α T B := by
  obtain ⟨C,hC⟩ := KP1Y.SigmaRecursion.certificate_exists hM h
  obtain ⟨B0,hB0⟩ := SetTheory.KP.exists_pair (KP1Y.models_weakKP hM) δ H
  obtain ⟨B,hB⟩ := SetTheory.KP.exists_insert (KP1Y.models_weakKP hM) B0 C
  exact ⟨B,hα,δ,(hB δ).mpr (Or.inl ((hB0 δ).mpr (Or.inl rfl))),
    H,(hB H).mpr (Or.inl ((hB0 H).mpr (Or.inr rfl))),C,(hB C).mpr (Or.inr rfl),hs,hC,hAt⟩

theorem is_level_from_history_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {env : Env M 24} {α T Γ H V Q : M.Domain} (hΓ : M.IsOrdinal Γ)
    (h : KP1Y.SigmaRecursion.ValueHistory M (levelStepMatrix.denote env) H Γ V Q)
    (hαΓ : M.mem α Γ) (hAt : MemPair M H α T) : IsLevel M env α T := by
  have hα := hΓ.mem hαΓ
  obtain ⟨δ,hs⟩ := SetTheory.KP.exists_successor (KP1Y.models_weakKP hM) α
  have hδ := SetTheory.KP.successor_isOrdinal (KP1Y.models_weakKP hM) hα hs
  have hδΓ : M.MemberSubset δ Γ := by
    intro x hx
    rcases (hs x).mp hx with hx | hSame
    · exact hΓ.transitive α hαΓ x hx
    · exact (hM.1.eq_of_same_members x α hSame) ▸ hαΓ
  obtain ⟨J,R,hJ,hRows⟩ := KP1Y.SigmaRecursion.history_prefix_d hM hδ hδΓ h
  exact level_certificate_from_history_d hM hα hs hJ ((hRows α T).mpr ⟨hs.predecessor_mem,hAt⟩)

theorem IsLevel.history {M : SetTheory.Structure.{u}} {env : Env M 24} {α T : M.Domain}
    (h : IsLevel M env α T) : ∃ δ H V Q, M.SuccessorOf δ α ∧
      KP1Y.SigmaRecursion.ValueHistory M (levelStepMatrix.denote env) H δ V Q ∧ MemPair M H α T := by
  obtain ⟨_,_,δ,_,H,_,_,_,hs,hCert,hAt⟩ := h
  obtain ⟨V,_,Q,_,hHistory⟩ := hCert
  exact ⟨δ,H,V,Q,hs,hHistory,hAt⟩

theorem is_level_exists_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    (env : Env M 24) (hS : FixedSyntax M (defContext.eval env) (defData.eval env)
      (env.bound 0) (env.bound 1) (env.bound 2)) {α : M.Domain} (hα : M.IsOrdinal α) : ∃ T, IsLevel M env α T := by
  obtain ⟨δ,hs⟩ := SetTheory.KP.exists_successor (KP1Y.models_weakKP hM) α
  have hδ := SetTheory.KP.successor_isOrdinal (KP1Y.models_weakKP hM) hα hs
  obtain ⟨H,V,Q,hH⟩ := constructible_history_exists_d hM env hS hδ
  obtain ⟨T,_,hAt⟩ := hH.values.total α hs.predecessor_mem
  exact ⟨T,level_certificate_from_history_d hM hα hs hH hAt⟩

theorem is_level_unique_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    (env : Env M 24) (hS : FixedSyntax M (defContext.eval env) (defData.eval env)
      (env.bound 0) (env.bound 1) (env.bound 2)) {α T T' : M.Domain}
    (h : IsLevel M env α T) (h' : IsLevel M env α T') : T=T' := by
  obtain ⟨δ,H,V,Q,hs,hH,hAt⟩ := h.history
  obtain ⟨δ',H',V',Q',hs',hH',hAt'⟩ := h'.history
  have hδδ' := hM.1.eq_of_same_members δ δ' (fun x => (hs x).trans (hs' x).symm)
  subst δ'
  have hδ := SetTheory.KP.successor_isOrdinal (KP1Y.models_weakKP hM) h.ordinal hs
  have hHH' := KP1Y.SigmaRecursion.history_unique hM hδ (fun _ hx => hx)
    (level_step_matrix_functional_d hM env hS hδ) hH hH'
  subst H'
  exact hH.values.unique α T T' hAt hAt'

theorem level_sigmaOne_iff_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    (env : Env M 24) (α T : M.Domain) : IsLevel M env α T ↔
      ∃ B, Project.Formula.satisfies (((env.push α).push T).push B) levelCertificateMatrix.body := by
  constructor
  · rintro ⟨B,hB⟩
    exact ⟨B,(levelCertificateMatrix_iff hM env α T B).mpr hB⟩
  · rintro ⟨B,hB⟩
    exact ⟨B,(levelCertificateMatrix_iff hM env α T B).mp hB⟩

theorem level_matrix_total_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    (env : Env M 24) (hS : FixedSyntax M (defContext.eval env) (defData.eval env)
      (env.bound 0) (env.bound 1) (env.bound 2)) {α : M.Domain} (hα : M.IsOrdinal α) :
    ∃ T B, Project.Formula.satisfies (((env.push α).push T).push B) levelCertificateMatrix.body := by
  obtain ⟨T,hT⟩ := is_level_exists_d hM env hS hα
  exact ⟨T,(level_sigmaOne_iff_d hM env α T).mp hT⟩

theorem level_matrix_functional_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    (env : Env M 24) (hS : FixedSyntax M (defContext.eval env) (defData.eval env)
      (env.bound 0) (env.bound 1) (env.bound 2)) {α T T' B B' : M.Domain}
    (h : Project.Formula.satisfies (((env.push α).push T).push B) levelCertificateMatrix.body)
    (h' : Project.Formula.satisfies (((env.push α).push T').push B') levelCertificateMatrix.body) : T=T' :=
  is_level_unique_d hM env hS ⟨B,(levelCertificateMatrix_iff hM env α T B).mp h⟩
    ⟨B',(levelCertificateMatrix_iff hM env α T' B').mp h'⟩

end KP1Y.Constructible
