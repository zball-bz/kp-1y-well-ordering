import KP1Y.RankedLevelStepSyntax

/-! 排名层级步骤对任意前缀图全定义且单值；每个输出本身已经携带有效排名。 -/
namespace KP1Y.ConstructibleRank
open YesMetaZFC YesMetaZFC.SetTheory YesMetaZFC.SetTheory.Definitional
open KP1Y.Kuratowski KP1Y.Functions KP1Y.Ranking KP1Y.SetLanguage
universe u

theorem ranked_step_total_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    (e : Env M 26) (hS : FixedSyntax M (rankContext.eval e) (rankData.eval e) (e.bound 2) (e.bound 3) (e.bound 4))
    (hP : OrdinalRank M (e.bound 0) (rankContext.eval e).programs (e.bound 1))
    {i P V : M.Domain} (hi : M.IsOrdinal i) (hGraph : Graph M P i V) : ∃ Out w, RankedStep M e i P Out w := by
  classical
  by_cases hGood : RankedFamily M P i V
  · by_cases hSucc : ∃ j, M.mem j i ∧ M.SuccessorOf i j
    · obtain ⟨j,hj,hs⟩ := hSucc
      obtain ⟨p,hp,hAt⟩ := hGraph.total j hj
      obtain ⟨Out,B,hOut⟩ := successor_packet_total_d hM e hS hP (hGood.ranked j p hAt)
      obtain ⟨w,hw⟩ := SetTheory.KP.exists_pair (KP1Y.models_weakKP hM) V B
      exact ⟨Out,w,V,(hw V).mpr (Or.inl rfl),hGraph,Or.inr ⟨hGood,
        Or.inl ⟨j,hj,p,hp,B,(hw B).mpr (Or.inr rfl),hs,hAt,hOut⟩⟩⟩
    · obtain ⟨Out,B,hOut⟩ := ranked_union_total_d hM (oneEnv i) hi hGood
      obtain ⟨w,hw⟩ := SetTheory.KP.exists_pair (KP1Y.models_weakKP hM) V B
      exact ⟨Out,w,V,(hw V).mpr (Or.inl rfl),hGraph,Or.inr ⟨hGood,
        Or.inr ⟨fun j hj hs => hSucc ⟨j,hj,hs⟩,B,(hw B).mpr (Or.inr rfl),hOut⟩⟩⟩
  · obtain ⟨Out,hOut,_⟩ := empty_ranked_packet_d hM hS.interpretation.naturals.zero_empty
    obtain ⟨w,hw⟩ := SetTheory.KP.exists_pair (KP1Y.models_weakKP hM) V V
    exact ⟨Out,w,V,(hw V).mpr (Or.inl rfl),hGraph,Or.inl ⟨hGood,hOut⟩⟩

theorem ranked_step_unique_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    (e : Env M 26) (hS : FixedSyntax M (rankContext.eval e) (rankData.eval e) (e.bound 2) (e.bound 3) (e.bound 4))
    (hP : Graph M (e.bound 0) (rankContext.eval e).programs (e.bound 1))
    {i P Out Out' w w' : M.Domain} (hi : M.IsOrdinal i)
    (h : RankedStep M e i P Out w) (h' : RankedStep M e i P Out' w') : Out=Out' := by
  obtain ⟨V,_,hGraph,hCases⟩ := h
  obtain ⟨V',_,hGraph',hCases'⟩ := h'
  rcases hCases with ⟨hBad,hOut⟩ | ⟨hGood,hCases⟩
  · rcases hCases' with ⟨_,hOut'⟩ | ⟨hGood',_⟩
    · exact hOut.unique hM.1 hOut'
    · exact False.elim (hBad ⟨hGraph,hGood'.ranked⟩)
  · rcases hCases' with ⟨hBad',_⟩ | ⟨_,hCases'⟩
    · exact False.elim (hBad' ⟨hGraph',hGood.ranked⟩)
    · rcases hCases with ⟨j,hj,p,_,B,_,hs,hAt,hOut⟩ | ⟨hNo,B,_,hOut⟩
      · rcases hCases' with ⟨j',_,p',_,B',_,hs',hAt',hOut'⟩ | ⟨hNo',_,_,_⟩
        · have hjj' := Structure.SuccessorOf.predecessor_eq hM.1 (hi.mem hj) hs hs'
          subst j'
          have hpp' := hGraph.unique j p p' hAt hAt'
          subst p'
          exact successor_packet_functional_d hM e hS hP hOut hOut'
        · exact False.elim (hNo' j hj hs)
      · rcases hCases' with ⟨j',hj',_,_,_,_,hs',_,_⟩ | ⟨_,_,_,hOut'⟩
        · exact False.elim (hNo j' hj' hs')
        · exact ranked_union_functional_d hM (oneEnv i) hOut hOut'

theorem RankedStep.ranked_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    (e : Env M 26) (hS : FixedSyntax M (rankContext.eval e) (rankData.eval e) (e.bound 2) (e.bound 3) (e.bound 4))
    (hP : OrdinalRank M (e.bound 0) (rankContext.eval e).programs (e.bound 1))
    {i P Out w : M.Domain} (h : RankedStep M e i P Out w) : RankedPacket M Out := by
  obtain ⟨_,_,_,hCases⟩ := h
  rcases hCases with ⟨_,hPacket⟩ | ⟨hGood,hCases⟩
  · obtain ⟨p,hp,hRank⟩ := empty_ranked_packet_d hM hS.interpretation.naturals.zero_empty
    have hOut := hPacket.unique hM.1 hp
    exact hOut.symm ▸ hRank
  · rcases hCases with ⟨j,_,p,_,B,_,_,hAt,hOut⟩ | ⟨_,B,_,hOut⟩
    · exact successor_packet_ranked_d hM e hS.spaces.omega hP (hGood.ranked j p hAt) hOut
    · exact ranked_union_ranked_d hM (oneEnv i) hOut

theorem ranked_step_matrix_total_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    (e : Env M 26) (hS : FixedSyntax M (rankContext.eval e) (rankData.eval e) (e.bound 2) (e.bound 3) (e.bound 4))
    (hP : OrdinalRank M (e.bound 0) (rankContext.eval e).programs (e.bound 1)) {Γ : M.Domain} (hΓ : M.IsOrdinal Γ) :
    KP1Y.SigmaRecursion.Total M Γ (rankedStepMatrix.denote e) := by
  intro i hi P V hGraph
  obtain ⟨Out,w,hOut⟩ := ranked_step_total_d hM e hS hP (hΓ.mem hi) hGraph
  exact ⟨Out,w,(rankedStepMatrix_iff hM e i P Out w).mpr hOut⟩

theorem ranked_step_matrix_functional_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    (e : Env M 26) (hS : FixedSyntax M (rankContext.eval e) (rankData.eval e) (e.bound 2) (e.bound 3) (e.bound 4))
    (hP : Graph M (e.bound 0) (rankContext.eval e).programs (e.bound 1)) {Γ : M.Domain} (hΓ : M.IsOrdinal Γ) :
    KP1Y.SigmaRecursion.Functional M Γ (rankedStepMatrix.denote e) := by
  intro i hi P Out Out' w w' h h'
  exact ranked_step_unique_d hM e hS hP (hΓ.mem hi)
    ((rankedStepMatrix_iff hM e i P Out w).mp h) ((rankedStepMatrix_iff hM e i P Out' w').mp h')

theorem ranked_history_exists_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    (e : Env M 26) (hS : FixedSyntax M (rankContext.eval e) (rankData.eval e) (e.bound 2) (e.bound 3) (e.bound 4))
    (hP : OrdinalRank M (e.bound 0) (rankContext.eval e).programs (e.bound 1)) {Γ : M.Domain} (hΓ : M.IsOrdinal Γ) :
    ∃ H V Q, KP1Y.SigmaRecursion.ValueHistory M (rankedStepMatrix.denote e) H Γ V Q :=
  KP1Y.SigmaRecursion.value_recursion_d hM rankedStepMatrix e hΓ
    (ranked_step_matrix_total_d hM e hS hP hΓ) (ranked_step_matrix_functional_d hM e hS hP.graph hΓ)

end KP1Y.ConstructibleRank
