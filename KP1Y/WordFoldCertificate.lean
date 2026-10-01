import KP1Y.WordFoldExistence
import KP1Y.AssignmentUpdate

/-! 整个内部有限字词折叠的Σ₁证书，包括真实长度、后继长度历史和最终读取项。 -/
namespace KP1Y.WordRank
open YesMetaZFC YesMetaZFC.SetTheory YesMetaZFC.SetTheory.Definitional
open KP1Y.Kuratowski KP1Y.Functions KP1Y.Bounded KP1Y.Naturals
universe u

def FoldCertificate (M : SetTheory.Structure.{u}) (ω κ s c W : M.Domain) : Prop :=
  ∃ n, M.mem n ω ∧ ∃ δ, M.mem δ ω ∧ ∃ H, M.mem H W ∧ ∃ V, M.mem V W ∧ ∃ Q, M.mem Q W ∧
    Graph M s n κ ∧ M.SuccessorOf δ n ∧
      KP1Y.SigmaRecursion.ValueHistory M (foldMatrix.denote ((oneEnv κ).push s)) H δ V Q ∧ MemPair M H n c

private def foldHistorySlots : Fin 6 → Fin 10 :=
  Fin.cases 0 (Fin.cases 1 (Fin.cases 2 (Fin.cases 3 (Fin.cases 7 (fun _ => 9)))))

def foldCertificateMatrix : KP1Y.WitnessMatrix 2 where
  body := Project.Formula.existsMem (.bound 3) (Project.Formula.existsMem (.bound 4)
    (Project.Formula.existsMem (.bound 2) (Project.Formula.existsMem (.bound 3) (Project.Formula.existsMem (.bound 4)
      (.conj (graphFormula (.bound 7) (.bound 4) (.bound 9))
        (.conj (successorFormula (.bound 3) (.bound 4))
          (.conj ((KP1Y.SigmaRecursion.historyVerifier foldMatrix).rename foldHistorySlots)
            (memPairFormula (.bound 2) (.bound 4) (.bound 6)))))))))
  freeClosed := by
    simp [graphFormula,successorFormula,memPairFormula,codeFormula,pairFormula,Project.Formula.existsMem,
      Project.Formula.forallMem,Definitional.Formula.FreeClosed,KP1Y.SigmaRecursion.historyVerifier_freeClosed]
  delta0 := .existsMem _ (.existsMem _ (.existsMem _ (.existsMem _ (.existsMem _
    (.conj (graphFormula_delta0 _ _ _) (.conj (successorFormula_delta0 _ _)
      (.conj (KP1Y.delta0_rename (KP1Y.SigmaRecursion.historyVerifier_delta0 foldMatrix) _) (memPairFormula_delta0 _ _ _))))))))

private theorem foldHistorySlots_iff {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    (e : Env M 2) (s c W n δ H V Q : M.Domain) :
    Project.Formula.satisfies ((((((((e.push s).push c).push W).push n).push δ).push H).push V).push Q)
      ((KP1Y.SigmaRecursion.historyVerifier foldMatrix).rename foldHistorySlots) ↔
        KP1Y.SigmaRecursion.ValueHistory M (foldMatrix.denote ((oneEnv (e.bound 1)).push s)) H δ V Q := by
  rw [Project.Formula.satisfies_rename]
  apply (KP1Y.formula_bound_congr (KP1Y.SigmaRecursion.historyVerifier foldMatrix)
    (KP1Y.SigmaRecursion.historyVerifier_freeClosed foldMatrix) _
    ((((((oneEnv (e.bound 1)).push s).push δ).push H).push V).push Q) ?_).trans
      (KP1Y.SigmaRecursion.historyVerifier_iff hM.1 foldMatrix ((oneEnv (e.bound 1)).push s) δ H V Q)
  intro i
  refine Fin.cases ?_ (fun i => ?_) i
  · rfl
  · refine Fin.cases ?_ (fun i => ?_) i
    · rfl
    · refine Fin.cases ?_ (fun i => ?_) i
      · rfl
      · refine Fin.cases ?_ (fun i => ?_) i
        · rfl
        · refine Fin.cases ?_ (fun i => ?_) i
          · rfl
          · exact Fin.cases rfl (fun i => Fin.elim0 i) i

theorem foldCertificateMatrix_iff {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory) (e : Env M 2) (s c W : M.Domain) :
    Project.Formula.satisfies (((e.push s).push c).push W) foldCertificateMatrix.body ↔ FoldCertificate M (e.bound 0) (e.bound 1) s c W := by
  simp only [foldCertificateMatrix,Project.Formula.satisfies_existsMem_iff,Project.Formula.satisfies_conj_iff,
    graphFormula_iff hM.1,successorFormula_iff hM.1,memPairFormula_iff hM.1,foldHistorySlots_iff hM]
  rfl

def Fold (M : SetTheory.Structure.{u}) (ω κ s c : M.Domain) : Prop := ∃ W, FoldCertificate M ω κ s c W

theorem Fold.history {M : SetTheory.Structure.{u}} {ω κ s c : M.Domain} (h : Fold M ω κ s c) :
    ∃ n δ H V Q, M.mem n ω ∧ M.mem δ ω ∧ Graph M s n κ ∧ M.SuccessorOf δ n ∧
      KP1Y.SigmaRecursion.ValueHistory M (foldMatrix.denote ((oneEnv κ).push s)) H δ V Q ∧ MemPair M H n c := by
  obtain ⟨_,n,hn,δ,hδ,H,_,V,_,Q,_,hS,hs,hH,hAt⟩ := h
  exact ⟨n,δ,H,V,Q,hn,hδ,hS,hs,hH,hAt⟩

theorem fold_from_history_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {ω κ s c n δ H V Q : M.Domain} (hn : M.mem n ω) (hδ : M.mem δ ω) (hS : Graph M s n κ) (hs : M.SuccessorOf δ n)
    (hH : KP1Y.SigmaRecursion.ValueHistory M (foldMatrix.denote ((oneEnv κ).push s)) H δ V Q) (hAt : MemPair M H n c) :
    Fold M ω κ s c := by
  obtain ⟨W0,hW0⟩ := SetTheory.KP.exists_pair (KP1Y.models_weakKP hM) H V
  obtain ⟨W,hW⟩ := SetTheory.KP.exists_insert (KP1Y.models_weakKP hM) W0 Q
  exact ⟨W,n,hn,δ,hδ,H,(hW H).mpr (Or.inl ((hW0 H).mpr (Or.inl rfl))),
    V,(hW V).mpr (Or.inl ((hW0 V).mpr (Or.inr rfl))),Q,(hW Q).mpr (Or.inr rfl),hS,hs,hH,hAt⟩

theorem fold_exists_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory) {ω κ s n : M.Domain}
    (hω : M.IsOmega ω) (hκ : M.IsOrdinal κ) (hn : M.mem n ω) (hS : Graph M s n κ) : ∃ c, Fold M ω κ s c := by
  obtain ⟨δ,hs,hδ⟩ := hω.1.2 n hn
  obtain ⟨H,V,Q,hH⟩ := fold_history_exists_d hM hω hκ hS hs hδ
  obtain ⟨c,_,hAt⟩ := hH.values.total n hs.predecessor_mem
  exact ⟨c,fold_from_history_d hM hn hδ hS hs hH hAt⟩

theorem fold_unique_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory) {ω κ s c c' : M.Domain}
    (hω : M.IsOmega ω) (h : Fold M ω κ s c) (h' : Fold M ω κ s c') : c=c' := by
  obtain ⟨n,δ,H,V,Q,_,hδ,hS,hs,hH,hAt⟩ := h.history
  obtain ⟨n',δ',H',V',Q',_,_,hS',hs',hH',hAt'⟩ := h'.history
  have hnn' := KP1Y.Assignments.domain_unique hM.1 hS hS'
  subst n'
  have hδδ' := hM.1.eq_of_same_members δ δ' (fun x => (hs x).trans (hs' x).symm)
  subst δ'
  have hδOrd := (omega_isOrdinal_d hM hω).mem hδ
  have hHH' := KP1Y.SigmaRecursion.history_unique hM hδOrd (fun _ hx => hx) (fold_matrix_functional_d hM hS hδOrd) hH hH'
  subst H'
  exact hH.values.unique n c c' hAt hAt'

end KP1Y.WordRank
