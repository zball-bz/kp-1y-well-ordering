import KP1Y.CountableFunctions

/-! 模型内部有限自然数值函数的整个像有一个自然数界。 -/
namespace KP1Y.Naturals
open YesMetaZFC YesMetaZFC.SetTheory YesMetaZFC.SetTheory.Definitional
open KP1Y.Kuratowski KP1Y.Functions
universe u

theorem natural_common_bound_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory) {ω b a : M.Domain}
    (hω : M.IsOmega ω) (hb : M.mem b ω) (ha : M.mem a ω) :
    ∃ n, M.mem n ω ∧ M.MemberSubset b n ∧ M.mem a n := by
  have hOrd := omega_isOrdinal_d hM hω
  rcases hOrd.wellOrder.linear.compare b hb a ha with he | hba | hab
  · obtain ⟨n,hn,hnω⟩ := hω.1.2 b hb
    have hEq := hM.1.eq_of_same_members a b (fun x => (he x).symm)
    exact ⟨n,hnω,fun x hx => (hn x).mpr (Or.inl hx),hEq ▸ hn.predecessor_mem⟩
  · obtain ⟨n,hn,hnω⟩ := hω.1.2 a ha
    exact ⟨n,hnω,fun x hx => (hn x).mpr (Or.inl ((hOrd.mem ha).transitive b hba x hx)),hn.predecessor_mem⟩
  · obtain ⟨n,hn,hnω⟩ := hω.1.2 b hb
    exact ⟨n,hnω,fun x hx => (hn x).mpr (Or.inl hx),(hn a).mpr (Or.inl hab)⟩

private def finiteRangeSchema : Project.UnarySchema 1 where
  body := .forallE (.imp (graphFormula (.bound 0) (.bound 1) (.bound 2))
    (Project.Formula.existsMem (.bound 2) (Project.Formula.forallMem (.bound 2)
      (Project.Formula.forallMem (.bound 4) (.imp (memPairFormula (.bound 3) (.bound 1) (.bound 0))
        (.mem (.bound 0) (.bound 2)))))))
  freeClosed := by
    simp [graphFormula, memPairFormula, codeFormula, pairFormula,
      Project.Formula.forallMem, Project.Formula.existsMem, Definitional.Formula.FreeClosed]

private theorem finiteRangeSchema_iff {M : SetTheory.Structure.{u}} (he : Extensional M) (ω length : M.Domain) :
    Project.Formula.satisfies ((oneEnv ω).push length) finiteRangeSchema.body ↔
      ∀ f, Graph M f length ω → ∃ n, M.mem n ω ∧
        ∀ k, M.mem k length → ∀ a, M.mem a ω → MemPair M f k a → M.mem a n := by
  simp only [finiteRangeSchema, Project.Formula.satisfies_forall_iff, Project.Formula.satisfies_imp_iff,
    Project.Formula.satisfies_existsMem_iff, Project.Formula.satisfies_forallMem_iff,
    Project.Formula.satisfies_mem_iff, graphFormula_iff he, memPairFormula_iff he]
  rfl

theorem finite_natural_range_bounded_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {ω length f : M.Domain} (hω : M.IsOmega ω) (hLength : M.mem length ω) (hf : Graph M f length ω) :
    ∃ n, M.mem n ω ∧ ∀ k a, MemPair M f k a → M.mem a n := by
  have hAll := natural_induction_d hM finiteRangeSchema (oneEnv ω) hω
    (fun e he => (finiteRangeSchema_iff hM.1 ω e).mpr (by
      intro f _
      obtain ⟨zero,_,hZero⟩ := hω.1.1
      exact ⟨zero,hZero,fun k hk => False.elim (he k hk)⟩))
    (fun p _ ih next hSucc => (finiteRangeSchema_iff hM.1 ω next).mpr (by
      intro f hF
      obtain ⟨g,hG,hRows⟩ := restrict_graph_d hM hF (fun k hk => (hSucc k).mpr (Or.inl hk))
      obtain ⟨b,hb,hBound⟩ := (finiteRangeSchema_iff hM.1 ω p).mp ih g hG
      obtain ⟨a,ha,hAt⟩ := hF.total p hSucc.predecessor_mem
      obtain ⟨n,hn,hbn,han⟩ := natural_common_bound_d hM hω hb ha
      refine ⟨n,hn,?_⟩
      intro k hk x hx hFx
      rcases (hSucc k).mp hk with hkp | he
      · exact hbn x (hBound k hkp x hx ((hRows k x).mpr ⟨hkp,hFx⟩))
      · have hkp := hM.1.eq_of_same_members k p he
        subst k
        have hxa := hF.unique p x a hFx hAt
        exact hxa ▸ han))
  obtain ⟨n,hn,hBound⟩ := (finiteRangeSchema_iff hM.1 ω length).mp (hAll length hLength) f hf
  exact ⟨n,hn,fun k a hAt => hBound k (hf.bounds hM.1 hAt).1 a (hf.bounds hM.1 hAt).2 hAt⟩

end KP1Y.Naturals
