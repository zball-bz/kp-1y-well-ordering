import KP1Y.NaturalInduction

/-! 内部有界自然数集的最大元与反向归纳，供有限边界遍历证明使用。 -/
namespace KP1Y.Naturals
open YesMetaZFC YesMetaZFC.SetTheory YesMetaZFC.SetTheory.Definitional
universe u

theorem ordinal_subset_cases_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {a b : M.Domain} (ha : M.IsOrdinal a) (hb : M.IsOrdinal b) (hSub : M.MemberSubset a b) : a=b ∨ M.mem a b := by
  have hw := KP1Y.models_weakKP hM
  rcases Structure.IsOrdinal.trichotomy hM.1 ha hb (SetTheory.KP.difference_exists_d hw)
    (SetTheory.KP.intersection_exists_d hw a b) with he | hab | hba
  · exact Or.inl (hM.1.eq_of_same_members a b he)
  · exact Or.inr hab
  · exact False.elim (SetTheory.KP.mem_irrefl_d hw b (hSub b hba))

def boundedMaximumSchema : Project.UnarySchema 0 where
  body := .forallE (.imp (.conj (Project.Formula.subset (.bound 0) (.bound 1))
      (Project.Formula.existsMem (.bound 0) .truth))
    (Project.Formula.existsMem (.bound 0) (Project.Formula.forallMem (.bound 1)
      (.disj (Project.Formula.extensionalEq (.bound 0) (.bound 1)) (.mem (.bound 0) (.bound 1))))))
  freeClosed := by
    simp [Project.Formula.existsMem, Project.Formula.forallMem, Definitional.Formula.FreeClosed]

theorem boundedMaximumSchema_iff {M : SetTheory.Structure.{u}} (he : Extensional M) (env : Env M 0) (n : M.Domain) :
    Project.Formula.satisfies (env.push n) boundedMaximumSchema.body ↔
      ∀ B, M.MemberSubset B n → (∃ x, M.mem x B) → ∃ m, M.mem m B ∧ ∀ x, M.mem x B → (x=m ∨ M.mem x m) := by
  simp only [boundedMaximumSchema, Project.Formula.satisfies_forall_iff,
    Project.Formula.satisfies_imp_iff, Project.Formula.satisfies_conj_iff, Project.Formula.satisfies_subset_iff,
    Project.Formula.satisfies_existsMem_iff, Project.Formula.satisfies_forallMem_iff,
    Project.Formula.satisfies_truth_iff, Project.Formula.satisfies_disj_iff,
    Project.Formula.satisfies_extensionalEq_iff_eq he, Project.Formula.satisfies_mem_iff, and_true]
  exact ⟨fun h B hSub hNonempty => h B ⟨hSub,hNonempty⟩,fun h B hs => h B hs.1 hs.2⟩

theorem bounded_nat_max_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory) {ω : M.Domain} (hω : M.IsOmega ω)
    {n B : M.Domain} (hn : M.mem n ω) (hSub : M.MemberSubset B n) (hNonempty : ∃ x, M.mem x B) :
    ∃ m, M.mem m B ∧ ∀ x, M.mem x B → (x=m ∨ M.mem x m) := by
  classical
  let env : Env M 0 := ⟨Fin.elim0,fun _ => ω⟩
  have hAll := natural_induction_d hM boundedMaximumSchema env hω
    (fun e he => (boundedMaximumSchema_iff hM.1 env e).mpr (by
      intro B hB hNe
      obtain ⟨x,hx⟩ := hNe
      exact False.elim (he x (hB x hx))))
    (fun p _ ih s hs => (boundedMaximumSchema_iff hM.1 env s).mpr (by
      intro B hB hNe
      by_cases hpB : M.mem p B
      · refine ⟨p,hpB,?_⟩
        intro x hx
        rcases (hs x).mp (hB x hx) with hxp | he
        · exact Or.inr hxp
        · exact Or.inl (hM.1.eq_of_same_members x p he)
      · have hBp : M.MemberSubset B p := by
          intro x hx
          rcases (hs x).mp (hB x hx) with hxp | he
          · exact hxp
          · have hxp := hM.1.eq_of_same_members x p he
            exact False.elim (hpB (hxp ▸ hx))
        exact (boundedMaximumSchema_iff hM.1 env p).mp ih B hBp hNe))
  exact (boundedMaximumSchema_iff hM.1 env n).mp (hAll n hn) B hSub hNonempty

private def badSchema {n : Nat} (φ : Project.Delta0UnarySchema n) : Project.Delta0UnarySchema n where
  body := .neg φ.body
  freeClosed := by simpa only [Definitional.Formula.FreeClosed] using φ.freeClosed
  delta0 := .neg φ.delta0

theorem bounded_backward_induction_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {n : Nat} (φ : Project.Delta0UnarySchema n) (env : Env M n) {ω top : M.Domain} (hω : M.IsOmega ω)
    (hTopNat : M.mem top ω) (hTop : Project.Formula.satisfies (env.push top) φ.body)
    (hStep : ∀ p, M.mem p top → ∀ q, M.mem q ω → M.SuccessorOf q p → M.MemberSubset q top →
      Project.Formula.satisfies (env.push q) φ.body → Project.Formula.satisfies (env.push p) φ.body) :
    ∀ x, (x=top ∨ M.mem x top) → Project.Formula.satisfies (env.push x) φ.body := by
  classical
  have hOrdω := omega_isOrdinal_d hM hω
  have hOrdTop := hOrdω.mem hTopNat
  obtain ⟨N,hN,hNω⟩ := hω.1.2 top hTopNat
  obtain ⟨B,hB⟩ := SetTheory.KP.separation_exists_d (KP1Y.models_weakKP hM) (badSchema φ) env N
  have hBad (x : M.Domain) : M.mem x B ↔ M.mem x N ∧ ¬Project.Formula.satisfies (env.push x) φ.body := by
    simpa only [badSchema,Project.Formula.satisfies_neg_iff] using hB x
  intro x hx
  apply Classical.byContradiction
  intro hxBad
  have hxN : M.mem x N := by
    rcases hx with he | hx
    · subst x
      exact hN.predecessor_mem
    · exact (hN x).mpr (Or.inl hx)
  obtain ⟨m,hm,hMax⟩ := bounded_nat_max_d hM hω hNω (fun y hy => ((hBad y).mp hy).1)
    ⟨x,(hBad x).mpr ⟨hxN,hxBad⟩⟩
  have hmN := ((hBad m).mp hm).1
  have hmBad := ((hBad m).mp hm).2
  have hmω := hOrdω.transitive N hNω m hmN
  have hmTop : M.mem m top := by
    rcases (hN m).mp hmN with hmTop | he
    · exact hmTop
    · have hEq := hM.1.eq_of_same_members m top he
      exact False.elim (hmBad (hEq ▸ hTop))
  obtain ⟨q,hq,hqω⟩ := hω.1.2 m hmω
  have hqSub : M.MemberSubset q top := by
    intro y hy
    rcases (hq y).mp hy with hym | he
    · exact hOrdTop.transitive m hmTop y hym
    · exact (hM.1.eq_of_same_members y m he) ▸ hmTop
  have hqN : M.mem q N := by
    rcases ordinal_subset_cases_d hM (hOrdω.mem hqω) hOrdTop hqSub with he | hqt
    · subst q
      exact hN.predecessor_mem
    · exact (hN q).mpr (Or.inl hqt)
  have hqNotB : ¬M.mem q B := by
    intro hqB
    rcases hMax q hqB with he | hqm
    · have hmm : M.mem m m := he ▸ hq.predecessor_mem
      exact SetTheory.KP.mem_irrefl_d (KP1Y.models_weakKP hM) m hmm
    · exact (hOrdω.mem hmω).wellOrder.linear.irrefl m
        ((hOrdω.mem hmω).transitive q hqm m hq.predecessor_mem)
        ((hOrdω.mem hmω).transitive q hqm m hq.predecessor_mem)
  have hqGood : Project.Formula.satisfies (env.push q) φ.body := by
    apply Classical.byContradiction
    intro hNot
    exact hqNotB ((hBad q).mpr ⟨hqN,hNot⟩)
  exact hmBad (hStep m hmTop q hqω hq hqSub hqGood)

end KP1Y.Naturals
