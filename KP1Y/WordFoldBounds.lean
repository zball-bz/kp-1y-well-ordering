import KP1Y.WordFoldClauses

/-! 用实际对象序数归纳证明每个内部折叠前缀处于对应预算界内。 -/
namespace KP1Y.WordRank
open YesMetaZFC YesMetaZFC.SetTheory YesMetaZFC.SetTheory.Definitional
open KP1Y.Kuratowski KP1Y.Functions KP1Y.Naturals KP1Y.Arithmetic
universe u

def FoldBoundAt (M : SetTheory.Structure.{u}) (H δ V F C i : M.Domain) : Prop :=
  M.mem i δ → ∀ c, M.mem c V → MemPair M H i c → ∀ B, M.mem B C → MemPair M F i B → M.mem c B

private def foldBoundSchema : Project.Delta0UnarySchema 5 where
  body := .imp (.mem (.bound 0) (.bound 3)) (Project.Formula.forallMem (.bound 4)
    (.imp (memPairFormula (.bound 6) (.bound 1) (.bound 0)) (Project.Formula.forallMem (.bound 2)
      (.imp (memPairFormula (.bound 4) (.bound 2) (.bound 0)) (.mem (.bound 1) (.bound 0))))))
  freeClosed := by
    simp [memPairFormula,codeFormula,pairFormula,Project.Formula.forallMem,Project.Formula.existsMem,Definitional.Formula.FreeClosed]
  delta0 := .imp (.mem _ _) (.forallMem _ (.imp (memPairFormula_delta0 _ _ _)
    (.forallMem _ (.imp (memPairFormula_delta0 _ _ _) (.mem _ _)))))

private theorem foldBoundSchema_iff {M : SetTheory.Structure.{u}} (he : Extensional M) (H δ V F C i : M.Domain) :
    Project.Formula.satisfies ((((((oneEnv H).push V).push δ).push F).push C).push i) foldBoundSchema.body ↔
      FoldBoundAt M H δ V F C i := by
  simp only [foldBoundSchema,Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_mem_iff,
    Project.Formula.satisfies_forallMem_iff,memPairFormula_iff he]
  rfl

theorem fold_history_bounded_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {κ ω zero one C F s n δ H V Q : M.Domain} (hBudget : Budget M κ ω zero one C F)
    (hS : Graph M s n κ) (hsδ : M.SuccessorOf δ n) (hδω : M.mem δ ω)
    (h : KP1Y.SigmaRecursion.ValueHistory M (foldMatrix.denote ((oneEnv κ).push s)) H δ V Q) :
    ∀ i, M.mem i δ → ∀ c B, MemPair M H i c → MemPair M F i B → M.mem c B := by
  have hω := omega_isOrdinal_d hM hBudget.omega
  have hδ := hω.mem hδω
  have hnω := hω.transitive δ hδω n hsδ.predecessor_mem
  have hAll := KP1Y.ordinal_induction_d hM foldBoundSchema.toUnarySchema (((((oneEnv H).push V).push δ).push F).push C) (by
    intro i _ ih
    apply (foldBoundSchema_iff hM.1 H δ V F C i).mpr
    intro hiδ c _ hAt B _ hFB
    have hiω := hω.transitive δ hδω i hiδ
    rcases natural_cases hM hBudget.omega hiω with hEmpty | ⟨p,_,hs⟩
    · have hcEmpty := fold_history_initial_d hM h hiδ hEmpty hAt
      have hc0 := hM.1.eq_of_same_members c zero (fun x => iff_of_false (hcEmpty x) (hBudget.zero_empty x))
      have hB1 : B=one := ((hBudget.rows i B).mp hFB).2.initial_d hM hEmpty
      rw [hc0,hB1]
      exact hBudget.one_successor.predecessor_mem
    · have hp := hs.predecessor_mem
      have hpδ := hδ.transitive i hiδ p hp
      have hpω := hω.transitive δ hδω p hpδ
      obtain ⟨b,hbV,hPrev⟩ := h.values.total p hpδ
      obtain ⟨Bp,hBpC,hFBp⟩ := hBudget.graph.total p hpω
      have hbBp := (foldBoundSchema_iff hM.1 H δ V F C p).mp (ih p hp) hpδ b hbV hPrev Bp hBpC hFBp
      have hbOrd := (hBudget.value_ordinal_d hM hFBp).mem hbBp
      have hpn : M.mem p n := by
        rcases (hsδ i).mp hiδ with hin | hSame
        · exact (hω.mem hnω).transitive i hin p hp
        · exact (hM.1.eq_of_same_members i n hSame) ▸ hp
      obtain ⟨a,ha,hSa⟩ := hS.total p hpn
      have hRect := fold_history_next_d hM hS hδ h hiδ hs hAt hPrev hSa hbOrd
      obtain ⟨P,hP⟩ := product_exists_d hM hBudget.stride (hBudget.value_ordinal_d hM hFBp)
      have hcP := rectangle_bounded_d hM hP hRect hbBp ha
      exact hBudget.product_bounded_d hM hs hFBp hFB hP c hcP)
  intro i hi c B hAt hFB
  exact (foldBoundSchema_iff hM.1 H δ V F C i).mp (hAll i (hδ.mem hi)) hi c (h.values.bounds hM.1 hAt).2 hAt
    B (hBudget.graph.bounds hM.1 hFB).2 hFB

theorem fold_bounded_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {κ ω zero one C F s c : M.Domain} (hBudget : Budget M κ ω zero one C F) (hFold : Fold M ω κ s c) : M.mem c C := by
  obtain ⟨n,δ,H,V,Q,hn,hδ,hS,hs,hH,hAt⟩ := hFold.history
  obtain ⟨B,hBC,hFB⟩ := hBudget.graph.total n hn
  have hcB := fold_history_bounded_d hM hBudget hS hs hδ hH n hs.predecessor_mem c B hAt hFB
  exact hBudget.ceiling.transitive B hBC c hcB

theorem fold_isOrdinal_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {κ ω zero one C F s c : M.Domain} (hBudget : Budget M κ ω zero one C F) (hFold : Fold M ω κ s c) : M.IsOrdinal c :=
  hBudget.ceiling.mem (fold_bounded_d hM hBudget hFold)

end KP1Y.WordRank
