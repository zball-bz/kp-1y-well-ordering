import KP1Y.SigmaHistory

/-! 集合值递归历史的唯一性：内部最小不同值处的两个前缀必须相等。 -/
namespace KP1Y.SigmaRecursion
open YesMetaZFC YesMetaZFC.SetTheory YesMetaZFC.SetTheory.Definitional
open KP1Y.Kuratowski KP1Y.Functions
universe u

def disagreeSchema : Project.Delta0UnarySchema 4 where
  body := Project.Formula.existsMem (.bound 1) (Project.Formula.existsMem (.bound 3)
    (.conj (memPairFormula (.bound 5) (.bound 2) (.bound 1))
      (.conj (memPairFormula (.bound 6) (.bound 2) (.bound 0))
        (.neg (Project.Formula.extensionalEq (.bound 1) (.bound 0))))))
  freeClosed := by
    simp [Project.Formula.existsMem, memPairFormula, codeFormula, pairFormula,
      Project.Formula.forallMem, Definitional.Formula.FreeClosed]
  delta0 := .existsMem _ (.existsMem _ (.conj (memPairFormula_delta0 _ _ _)
    (.conj (memPairFormula_delta0 _ _ _) (.neg (.atom _ _ _)))))

def disagreeEnv {M : SetTheory.Structure.{u}} (V W H J : M.Domain) : Env M 4 :=
  ⟨Fin.cases V (Fin.cases W (Fin.cases H (fun _ => J))),fun _ => V⟩

theorem disagreeSchema_iff {M : SetTheory.Structure.{u}} (he : Extensional M) (V W H J i : M.Domain) :
    Project.Formula.satisfies ((disagreeEnv V W H J).push i) disagreeSchema.body ↔
      ∃ v, M.mem v V ∧ ∃ w, M.mem w W ∧ MemPair M H i v ∧ MemPair M J i w ∧ v≠w := by
  simp only [disagreeSchema, Project.Formula.satisfies_existsMem_iff,
    Project.Formula.satisfies_conj_iff, Project.Formula.satisfies_neg_iff,
    Project.Formula.satisfies_extensionalEq_iff_eq he, memPairFormula_iff he]
  rfl

theorem history_values_equal {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {step : M.Domain → M.Domain → M.Domain → M.Domain → Prop}
    {Γ δ H J V W Q R : M.Domain} (hδ : M.IsOrdinal δ) (hδΓ : M.MemberSubset δ Γ)
    (hFun : Functional M Γ step) (hH : ValueHistory M step H δ V Q)
    (hJ : ValueHistory M step J δ W R) :
    ∀ i, M.mem i δ → ∀ v, M.mem v V → ∀ w, M.mem w W →
      MemPair M H i v → MemPair M J i w → v=w := by
  classical
  obtain ⟨D,hD⟩ := SetTheory.KP.separation_exists_d (KP1Y.models_weakKP hM)
    disagreeSchema (disagreeEnv V W H J) δ
  have hd (i : M.Domain) : M.mem i D ↔ M.mem i δ ∧
      ∃ v, M.mem v V ∧ ∃ w, M.mem w W ∧ MemPair M H i v ∧ MemPair M J i w ∧ v≠w :=
    (hD i).trans (and_congr Iff.rfl (disagreeSchema_iff hM.1 V W H J i))
  intro i hi v hv w hw hHv hJw
  apply Classical.byContradiction
  intro hne
  have hDne : ∃ i, M.mem i D := ⟨i,(hd i).mpr ⟨hi,v,hv,w,hw,hHv,hJw,hne⟩⟩
  obtain ⟨m,hm,hmin⟩ := hδ.wellOrder.least D (fun t ht => ((hd t).mp ht).1) hDne
  have hmδ := ((hd m).mp hm).1
  have hPast : ∀ t, M.mem t m → ∀ v, M.mem v V → ∀ w, M.mem w W →
      MemPair M H t v → MemPair M J t w → v=w := by
    intro t htm v hv w hw htv htw
    apply Classical.byContradiction
    intro hne
    have htδ := hδ.transitive m hmδ t htm
    have htD := (hd t).mpr ⟨htδ,v,hv,w,hw,htv,htw,hne⟩
    rcases hmin t htD with he | hmt
    · have heq := hM.1.eq_of_same_members m t he
      cases heq
      exact hδ.wellOrder.linear.irrefl m hmδ htm
    · exact hδ.wellOrder.linear.irrefl m hmδ
        (hδ.wellOrder.linear.trans m hmδ t htδ m hmδ hmt htm)
  have hPastRows : ∀ t, M.mem t m → ∀ a, MemPair M H t a ↔ MemPair M J t a := by
    intro t htm a
    have htδ := hδ.transitive m hmδ t htm
    constructor
    · intro hta
      obtain ⟨b,hb,htb⟩ := hJ.values.total t htδ
      have hab := hPast t htm a (hH.values.bounds hM.1 hta).2 b hb hta htb
      exact hab ▸ htb
    · intro hta
      obtain ⟨b,hb,htb⟩ := hH.values.total t htδ
      have hba := hPast t htm b hb a (hJ.values.bounds hM.1 hta).2 htb hta
      exact hba ▸ htb
  obtain ⟨a,ha,b,hb,hma,hmb,hab⟩ := ((hd m).mp hm).2
  obtain ⟨P,hP,hQP⟩ := hH.prefixes.total m hmδ
  obtain ⟨S,hS,hRS⟩ := hJ.prefixes.total m hmδ
  obtain ⟨hPref,wa,hwa,hStepA⟩ := hH.obeys m hmδ P hP a ha hQP hma
  obtain ⟨hPref',wb,hwb,hStepB⟩ := hJ.obeys m hmδ S hS b hb hRS hmb
  have hPS : P=S := Graph.ext hM.1 hPref.graph hPref'.graph (fun t htm y =>
    (hPref.all_rows hM.1 hH.values t htm y).trans
      ((hPastRows t htm y).trans (hPref'.all_rows hM.1 hJ.values t htm y).symm))
  cases hPS
  exact hab (hFun m (hδΓ m hmδ) P a b wa wb hStepA hStepB)

theorem history_rows_agree {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {step : M.Domain → M.Domain → M.Domain → M.Domain → Prop}
    {Γ δ H J V W Q R : M.Domain} (hδ : M.IsOrdinal δ) (hδΓ : M.MemberSubset δ Γ)
    (hFun : Functional M Γ step) (hH : ValueHistory M step H δ V Q)
    (hJ : ValueHistory M step J δ W R) :
    ∀ i, M.mem i δ → ∀ v, MemPair M H i v ↔ MemPair M J i v := by
  have h := history_values_equal hM hδ hδΓ hFun hH hJ
  intro i hi v
  constructor
  · intro hiv
    obtain ⟨w,hw,hiw⟩ := hJ.values.total i hi
    have hvw := h i hi v (hH.values.bounds hM.1 hiv).2 w hw hiv hiw
    exact hvw ▸ hiw
  · intro hiv
    obtain ⟨w,hw,hiw⟩ := hH.values.total i hi
    have hwv := h i hi w hw v (hJ.values.bounds hM.1 hiv).2 hiw hiv
    exact hwv ▸ hiw

theorem history_unique {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {step : M.Domain → M.Domain → M.Domain → M.Domain → Prop}
    {Γ δ H J V W Q R : M.Domain} (hδ : M.IsOrdinal δ) (hδΓ : M.MemberSubset δ Γ)
    (hFun : Functional M Γ step) (hH : ValueHistory M step H δ V Q)
    (hJ : ValueHistory M step J δ W R) : H=J :=
  Graph.ext hM.1 hH.values hJ.values (history_rows_agree hM hδ hδΓ hFun hH hJ)

theorem certificate_unique {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {step : M.Domain → M.Domain → M.Domain → M.Domain → Prop} {Γ δ H J B C : M.Domain}
    (hδ : M.IsOrdinal δ) (hδΓ : M.MemberSubset δ Γ) (hFun : Functional M Γ step)
    (hH : Certificate M step δ H B) (hJ : Certificate M step δ J C) : H=J := by
  obtain ⟨V,_,Q,_,hH⟩ := hH
  obtain ⟨W,_,R,_,hJ⟩ := hJ
  exact history_unique hM hδ hδΓ hFun hH hJ

end KP1Y.SigmaRecursion
