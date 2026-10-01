import KP1Y.WordFoldBounds

/-! 同长度内部字词的折叠单射性：对象归纳中用矩形单射恢复前缀代码和末项。 -/
namespace KP1Y.WordRank
open YesMetaZFC YesMetaZFC.SetTheory YesMetaZFC.SetTheory.Definitional
open KP1Y.Kuratowski KP1Y.Functions KP1Y.Naturals KP1Y.Arithmetic
universe u

def AgreementAt (M : SetTheory.Structure.{u}) (H V J W s t κ δ i : M.Domain) : Prop :=
  M.mem i δ → ∀ c, M.mem c V → ∀ d, M.mem d W → MemPair M H i c → MemPair M J i d → c=d →
    ∀ p, M.mem p i → ∀ a, M.mem a κ → (MemPair M s p a ↔ MemPair M t p a)

private def agreementSchema : Project.Delta0UnarySchema 8 where
  body := .imp (.mem (.bound 0) (.bound 1)) (Project.Formula.forallMem (.bound 7)
    (Project.Formula.forallMem (.bound 6)
      (.imp (memPairFormula (.bound 10) (.bound 2) (.bound 1))
        (.imp (memPairFormula (.bound 8) (.bound 2) (.bound 0))
          (.imp (Project.Formula.extensionalEq (.bound 1) (.bound 0))
            (Project.Formula.forallMem (.bound 2) (Project.Formula.forallMem (.bound 5)
              (.iff (memPairFormula (.bound 8) (.bound 1) (.bound 0)) (memPairFormula (.bound 7) (.bound 1) (.bound 0))))))))))
  freeClosed := by
    simp [memPairFormula,codeFormula,pairFormula,Project.Formula.forallMem,Project.Formula.existsMem,Definitional.Formula.FreeClosed]
  delta0 := .imp (.mem _ _) (.forallMem _ (.forallMem _ (.imp (memPairFormula_delta0 _ _ _)
    (.imp (memPairFormula_delta0 _ _ _) (.imp (.atom _ _ _) (.forallMem _ (.forallMem _
      (.iff (memPairFormula_delta0 _ _ _) (memPairFormula_delta0 _ _ _)))))))))

private def agreementEnv {M : SetTheory.Structure.{u}} (H V J W s t κ δ : M.Domain) : Env M 8 :=
  (((((((oneEnv H).push V).push J).push W).push s).push t).push κ).push δ

private theorem agreementSchema_iff {M : SetTheory.Structure.{u}} (he : Extensional M) (H V J W s t κ δ i : M.Domain) :
    Project.Formula.satisfies ((agreementEnv H V J W s t κ δ).push i) agreementSchema.body ↔ AgreementAt M H V J W s t κ δ i := by
  simp only [agreementSchema,Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_mem_iff,
    Project.Formula.satisfies_forallMem_iff,Project.Formula.satisfies_iff_iff,
    Project.Formula.satisfies_extensionalEq_iff_eq he,memPairFormula_iff he]
  rfl

theorem fold_history_agreement_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {κ ω zero one C F s t n δ H V Q J W R : M.Domain} (hBudget : Budget M κ ω zero one C F)
    (hS : Graph M s n κ) (hT : Graph M t n κ) (hsδ : M.SuccessorOf δ n) (hδω : M.mem δ ω)
    (hH : KP1Y.SigmaRecursion.ValueHistory M (foldMatrix.denote ((oneEnv κ).push s)) H δ V Q)
    (hJ : KP1Y.SigmaRecursion.ValueHistory M (foldMatrix.denote ((oneEnv κ).push t)) J δ W R) :
    ∀ i, M.mem i δ → ∀ c d, MemPair M H i c → MemPair M J i d → c=d →
      ∀ p, M.mem p i → ∀ a, M.mem a κ → (MemPair M s p a ↔ MemPair M t p a) := by
  have hω := omega_isOrdinal_d hM hBudget.omega
  have hδ := hω.mem hδω
  have hnω := hω.transitive δ hδω n hsδ.predecessor_mem
  have hAll := KP1Y.ordinal_induction_d hM agreementSchema.toUnarySchema (agreementEnv H V J W s t κ δ) (by
    intro i _ ih
    apply (agreementSchema_iff hM.1 H V J W s t κ δ i).mpr
    intro hiδ c _ d _ hAt hAt' hcd
    have hiω := hω.transitive δ hδω i hiδ
    rcases natural_cases hM hBudget.omega hiω with hEmpty | ⟨p,_,hs⟩
    · intro j hj
      exact False.elim (hEmpty j hj)
    · have hp := hs.predecessor_mem
      have hpδ := hδ.transitive i hiδ p hp
      have hpω := hω.transitive δ hδω p hpδ
      have hpn : M.mem p n := by
        rcases (hsδ i).mp hiδ with hin | hSame
        · exact (hω.mem hnω).transitive i hin p hp
        · exact (hM.1.eq_of_same_members i n hSame) ▸ hp
      obtain ⟨b,hbV,hPrev⟩ := hH.values.total p hpδ
      obtain ⟨b',hbW,hPrev'⟩ := hJ.values.total p hpδ
      obtain ⟨B,_,hFB⟩ := hBudget.graph.total p hpω
      have hbB := fold_history_bounded_d hM hBudget hS hsδ hδω hH p hpδ b B hPrev hFB
      have hb'B := fold_history_bounded_d hM hBudget hT hsδ hδω hJ p hpδ b' B hPrev' hFB
      obtain ⟨a,ha,hSa⟩ := hS.total p hpn
      obtain ⟨a',ha',hTa'⟩ := hT.total p hpn
      have hRect := fold_history_next_d hM hS hδ hH hiδ hs hAt hPrev hSa ((hBudget.value_ordinal_d hM hFB).mem hbB)
      have hRect' := fold_history_next_d hM hT hδ hJ hiδ hs hAt' hPrev' hTa' ((hBudget.value_ordinal_d hM hFB).mem hb'B)
      obtain ⟨hbb',haa'⟩ := rectangle_injective_d hM hRect hRect' ha ha' hcd
      have hEarlier := (agreementSchema_iff hM.1 H V J W s t κ δ p).mp (ih p hp) hpδ b hbV b' hbW hPrev hPrev' hbb'
      subst a'
      intro j hj v hv
      rcases (hs j).mp hj with hjp | hSame
      · exact hEarlier j hjp v hv
      · have hjp := hM.1.eq_of_same_members j p hSame
        subst j
        constructor
        · intro hSv
          have hva := hS.unique p v a hSv hSa
          exact hva ▸ hTa'
        · intro hTv
          have hva := hT.unique p v a hTv hTa'
          exact hva ▸ hSa)
  intro i hi c d hAt hAt' hcd
  exact (agreementSchema_iff hM.1 H V J W s t κ δ i).mp (hAll i (hδ.mem hi)) hi c (hH.values.bounds hM.1 hAt).2
    d (hJ.values.bounds hM.1 hAt').2 hAt hAt' hcd

theorem fold_injective_same_length_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {κ ω zero one C F s t n c d : M.Domain} (hBudget : Budget M κ ω zero one C F)
    (hS : Graph M s n κ) (hT : Graph M t n κ) (hc : Fold M ω κ s c) (hd : Fold M ω κ t d) (hcd : c=d) : s=t := by
  classical
  obtain ⟨n0,δ,H,V,Q,_,hδ,hS0,hs,hH,hAt⟩ := hc.history
  obtain ⟨n1,δ',J,W,R,_,_,hT0,hs',hJ,hAt'⟩ := hd.history
  have hN0 := KP1Y.Assignments.domain_unique hM.1 hS0 hS
  have hN1 := KP1Y.Assignments.domain_unique hM.1 hT0 hT
  subst n0
  subst n1
  have hδδ' := hM.1.eq_of_same_members δ δ' (fun x => (hs x).trans (hs' x).symm)
  subst δ'
  have hAgree := fold_history_agreement_d hM hBudget hS hT hs hδ hH hJ n hs.predecessor_mem c d hAt hAt' hcd
  apply hS.ext hM.1 hT
  intro i hi a
  by_cases ha : M.mem a κ
  · exact hAgree i hi a ha
  · exact iff_of_false (fun h => ha (hS.bounds hM.1 h).2) (fun h => ha (hT.bounds hM.1 h).2)

end KP1Y.WordRank
