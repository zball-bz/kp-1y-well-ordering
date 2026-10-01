import KP1Y.WordFoldCertificate
import KP1Y.OrdinalRectangle

/-! 合法折叠历史的零与后继方程；由旧代码序数性排除默认分支。 -/
namespace KP1Y.WordRank
open YesMetaZFC YesMetaZFC.SetTheory
open KP1Y.Kuratowski KP1Y.Functions KP1Y.Arithmetic
universe u

theorem fold_history_step_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {s κ H δ V Q i c : M.Domain}
    (h : KP1Y.SigmaRecursion.ValueHistory M (foldMatrix.denote ((oneEnv κ).push s)) H δ V Q)
    (hi : M.mem i δ) (hAt : MemPair M H i c) : ∃ P W, Prefix M P H i V ∧ FoldStep M s κ i P c W := by
  obtain ⟨P,hP,hQ⟩ := h.prefixes.total i hi
  obtain ⟨hPrefix,W,_,hStep⟩ := h.obeys i hi P hP c (h.values.bounds hM.1 hAt).2 hQ hAt
  exact ⟨P,W,hPrefix,(foldMatrix_iff hM ((oneEnv κ).push s) i P c W).mp hStep⟩

theorem fold_history_initial_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {s κ H δ V Q i c : M.Domain}
    (h : KP1Y.SigmaRecursion.ValueHistory M (foldMatrix.denote ((oneEnv κ).push s)) H δ V Q)
    (hi : M.mem i δ) (hEmpty : ∀ x, ¬M.mem x i) (hAt : MemPair M H i c) : ∀ x, ¬M.mem x c := by
  obtain ⟨_,_,_,_,_,_,hCase⟩ := fold_history_step_d hM h hi hAt
  rcases hCase with ⟨_,hc⟩ | ⟨p,hp,_⟩
  · exact hc
  · exact False.elim (hEmpty p hp)

theorem fold_history_next_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {s n κ H δ V Q i p b a c : M.Domain} (hS : Graph M s n κ) (hδ : M.IsOrdinal δ)
    (h : KP1Y.SigmaRecursion.ValueHistory M (foldMatrix.denote ((oneEnv κ).push s)) H δ V Q)
    (hi : M.mem i δ) (hs : M.SuccessorOf i p) (hAt : MemPair M H i c) (hPrev : MemPair M H p b)
    (hDigit : MemPair M s p a) (hb : M.IsOrdinal b) : RectangleCode M κ b a c := by
  obtain ⟨P,_,hPrefix,_,_,_,hCase⟩ := fold_history_step_d hM h hi hAt
  rcases hCase with ⟨hEmpty,_⟩ | ⟨p',hp',b',_,a',_,hs',hPb',hSa',hOp⟩
  · exact False.elim (hEmpty p hs.predecessor_mem)
  · have hpp' := Structure.SuccessorOf.predecessor_eq hM.1 ((hδ.mem hi).mem hp') hs' hs
    subst p'
    have hHpb' := (hPrefix.all_rows hM.1 h.values p hs.predecessor_mem b').mp hPb'
    have hbb' := h.values.unique p b' b hHpb' hPrev
    subst b'
    have haa' := hS.unique p a' a hSa' hDigit
    subst a'
    rcases hOp with ⟨_,u,_,C,_,D,_,hu,hc⟩ | ⟨hn,_⟩
    · exact ⟨u,hu.meaning,⟨D,hc⟩⟩
    · exact False.elim (hn hb)

end KP1Y.WordRank
