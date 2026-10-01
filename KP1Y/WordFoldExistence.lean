import KP1Y.WordFoldSyntax

/-! 折叠在任何合法内部字词上有实际历史；全定义性涵盖任意前缀图的非序数旧值。 -/
namespace KP1Y.WordRank
open YesMetaZFC YesMetaZFC.SetTheory
open KP1Y.Kuratowski KP1Y.Functions KP1Y.Naturals KP1Y.Arithmetic
universe u

theorem fold_step_total_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {ω κ s n δ i P V : M.Domain} (hω : M.IsOmega ω) (hκ : M.IsOrdinal κ) (hS : Graph M s n κ)
    (hsδ : M.SuccessorOf δ n) (hδω : M.mem δ ω) (hiδ : M.mem i δ) (hP : Graph M P i V) :
    ∃ c W, FoldStep M s κ i P c W := by
  classical
  have hωOrd := omega_isOrdinal_d hM hω
  have hiω := hωOrd.transitive δ hδω i hiδ
  rcases natural_cases hM hω hiω with hEmpty | ⟨p,_,hs⟩
  · obtain ⟨W,hW⟩ := SetTheory.KP.exists_pair (KP1Y.models_weakKP hM) V V
    exact ⟨i,W,V,(hW V).mpr (Or.inl rfl),hP,Or.inl ⟨hEmpty,hEmpty⟩⟩
  · have hnω := hωOrd.transitive δ hδω n hsδ.predecessor_mem
    have hpn : M.mem p n := by
      rcases (hsδ i).mp hiδ with hin | hSame
      · exact (hωOrd.mem hnω).transitive i hin p hs.predecessor_mem
      · have hin := hM.1.eq_of_same_members i n hSame
        exact hin ▸ hs.predecessor_mem
    obtain ⟨b,hbV,hPb⟩ := hP.total p hs.predecessor_mem
    obtain ⟨a,ha,hSa⟩ := hS.total p hpn
    by_cases hb : M.IsOrdinal b
    · obtain ⟨u,hu⟩ := product_exists_d hM hκ hb
      obtain ⟨c,hc⟩ := sum_exists_d hM u (hκ.mem ha)
      obtain ⟨C,hC⟩ := (product_sigmaOne_iff_d hM (oneEnv κ) b u).mp hu
      obtain ⟨D,hD⟩ := hc
      obtain ⟨W0,hW0⟩ := SetTheory.KP.exists_pair (KP1Y.models_weakKP hM) V u
      obtain ⟨W1,hW1⟩ := SetTheory.KP.exists_pair (KP1Y.models_weakKP hM) C D
      obtain ⟨W,hW⟩ := SetTheory.KP.exists_unionOfTwo (KP1Y.models_weakKP hM) W0 W1
      exact ⟨c,W,V,(hW V).mpr (Or.inl ((hW0 V).mpr (Or.inl rfl))),hP,
        Or.inr ⟨p,hs.predecessor_mem,b,hbV,a,ha,hs,hPb,hSa,Or.inl ⟨hb,
          u,(hW u).mpr (Or.inl ((hW0 u).mpr (Or.inr rfl))),C,(hW C).mpr (Or.inr ((hW1 C).mpr (Or.inl rfl))),
          D,(hW D).mpr (Or.inr ((hW1 D).mpr (Or.inr rfl))),
          (productMatrix_iff hM (oneEnv κ) b u C).mp hC,hD⟩⟩⟩
    · obtain ⟨c,hEmpty⟩ := SetTheory.KP.exists_empty (KP1Y.models_weakKP hM)
      obtain ⟨W,hW⟩ := SetTheory.KP.exists_pair (KP1Y.models_weakKP hM) V V
      exact ⟨c,W,V,(hW V).mpr (Or.inl rfl),hP,
        Or.inr ⟨p,hs.predecessor_mem,b,hbV,a,ha,hs,hPb,hSa,Or.inr ⟨hb,hEmpty⟩⟩⟩

theorem fold_step_unique_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {s n κ i P c c' W W' : M.Domain} (hS : Graph M s n κ) (hi : M.IsOrdinal i)
    (h : FoldStep M s κ i P c W) (h' : FoldStep M s κ i P c' W') : c=c' := by
  obtain ⟨_,_,hP,hCase⟩ := h
  obtain ⟨_,_,_,hCase'⟩ := h'
  rcases hCase with ⟨hEmpty,hc⟩ | ⟨p,hp,b,_,a,_,hs,hPb,hSa,hOp⟩
  · rcases hCase' with ⟨_,hc'⟩ | ⟨p,hp,_,_,_,_,_,_,_,_⟩
    · exact hM.1.eq_of_same_members c c' (fun x => iff_of_false (hc x) (hc' x))
    · exact False.elim (hEmpty p hp)
  · rcases hCase' with ⟨hEmpty,_⟩ | ⟨p',_,b',_,a',_,hs',hPb',hSa',hOp'⟩
    · exact False.elim (hEmpty p hp)
    · have hpp' := Structure.SuccessorOf.predecessor_eq hM.1 (hi.mem hp) hs hs'
      subst p'
      have hbb' := hP.unique p b b' hPb hPb'
      subst b'
      have haa' := hS.unique p a a' hSa hSa'
      subst a'
      rcases hOp with ⟨hb,u,_,C,_,D,_,hu,hc⟩ | ⟨hb,hc⟩
      · rcases hOp' with ⟨_,u',_,C',_,D',_,hu',hc'⟩ | ⟨hb',_⟩
        · have huu' := product_unique_d hM hu.meaning hu'.meaning
          subst u'
          exact sum_unique_d hM ⟨D,hc⟩ ⟨D',hc'⟩
        · exact False.elim (hb' hb)
      · rcases hOp' with ⟨hb',_⟩ | ⟨_,hc'⟩
        · exact False.elim (hb hb')
        · exact hM.1.eq_of_same_members c c' (fun x => iff_of_false (hc x) (hc' x))

theorem fold_matrix_total_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {ω κ s n δ : M.Domain} (hω : M.IsOmega ω) (hκ : M.IsOrdinal κ) (hS : Graph M s n κ)
    (hsδ : M.SuccessorOf δ n) (hδω : M.mem δ ω) :
    KP1Y.SigmaRecursion.Total M δ (foldMatrix.denote ((oneEnv κ).push s)) := by
  intro i hi P V hP
  obtain ⟨c,W,hStep⟩ := fold_step_total_d hM hω hκ hS hsδ hδω hi hP
  exact ⟨c,W,(foldMatrix_iff hM ((oneEnv κ).push s) i P c W).mpr hStep⟩

theorem fold_matrix_functional_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {κ s n δ : M.Domain} (hS : Graph M s n κ) (hδ : M.IsOrdinal δ) :
    KP1Y.SigmaRecursion.Functional M δ (foldMatrix.denote ((oneEnv κ).push s)) := by
  intro i hi P c c' W W' h h'
  exact fold_step_unique_d hM hS (hδ.mem hi)
    ((foldMatrix_iff hM ((oneEnv κ).push s) i P c W).mp h)
    ((foldMatrix_iff hM ((oneEnv κ).push s) i P c' W').mp h')

theorem fold_history_exists_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {ω κ s n δ : M.Domain} (hω : M.IsOmega ω) (hκ : M.IsOrdinal κ) (hS : Graph M s n κ)
    (hsδ : M.SuccessorOf δ n) (hδω : M.mem δ ω) :
    ∃ H V Q, KP1Y.SigmaRecursion.ValueHistory M (foldMatrix.denote ((oneEnv κ).push s)) H δ V Q := by
  have hδ := (omega_isOrdinal_d hM hω).mem hδω
  exact KP1Y.SigmaRecursion.value_recursion_d hM foldMatrix ((oneEnv κ).push s) hδ
    (fold_matrix_total_d hM hω hκ hS hsδ hδω) (fold_matrix_functional_d hM hS hδ)

end KP1Y.WordRank
