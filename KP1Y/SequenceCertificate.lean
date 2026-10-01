import KP1Y.SequenceSpaces

/-! 用历史、精确值域和并集给完整序列空间提供有界证书。 -/
namespace KP1Y.Sequences
open YesMetaZFC YesMetaZFC.SetTheory YesMetaZFC.SetTheory.Definitional
open KP1Y.Kuratowski KP1Y.Functions KP1Y.Bounded
universe u

def RangeBound (M : SetTheory.Structure.{u}) (D V H ω : M.Domain) : Prop :=
  M.MemberSubset D V ∧ ∀ T, M.mem T V → (M.mem T D ↔ ∃ n, M.mem n ω ∧ MemPair M H n T)

def rangeBoundFormula {n : Nat} (D V H ω : Project.Term n) : Project.Formula 1 n :=
  .conj (Project.Formula.subset D V) (Project.Formula.forallMem V
    (.iff (.mem (.bound 0) D.weaken) (Project.Formula.existsMem ω.weaken
      (memPairFormula H.weaken.weaken (.bound 0) (.bound 1)))))

theorem rangeBoundFormula_delta0 {n : Nat} (D V H ω : Project.Term n) : (rangeBoundFormula D V H ω).IsDelta0 :=
  .conj (.atom _ _ _) (.forallMem _ (.iff (.mem _ _) (.existsMem _ (memPairFormula_delta0 _ _ _))))

theorem rangeBoundFormula_iff {M : SetTheory.Structure.{u}} (he : Extensional M) {n : Nat}
    (env : Env M n) (D V H ω : Project.Term n) :
    Project.Formula.satisfies env (rangeBoundFormula D V H ω) ↔ RangeBound M (D.eval env) (V.eval env) (H.eval env) (ω.eval env) := by
  simp only [rangeBoundFormula, Project.Formula.satisfies_conj_iff, Project.Formula.satisfies_subset_iff,
    Project.Formula.satisfies_forallMem_iff, Project.Formula.satisfies_iff_iff, Project.Formula.satisfies_mem_iff,
    Project.Formula.satisfies_existsMem_iff, memPairFormula_iff he, Definitional.Term.eval_weaken]
  rfl

private def rangeSchema : Project.Delta0UnarySchema 2 where
  body := Project.Formula.existsMem (.bound 1) (memPairFormula (.bound 3) (.bound 0) (.bound 1))
  freeClosed := by
    simp [memPairFormula, codeFormula, pairFormula, Project.Formula.existsMem,
      Project.Formula.forallMem, Definitional.Formula.FreeClosed]
  delta0 := .existsMem _ (memPairFormula_delta0 _ _ _)

private theorem rangeSchema_iff {M : SetTheory.Structure.{u}} (he : Extensional M) (H ω T : M.Domain) :
    Project.Formula.satisfies (((oneEnv H).push ω).push T) rangeSchema.body ↔ ∃ n, M.mem n ω ∧ MemPair M H n T := by
  simp only [rangeSchema, Project.Formula.satisfies_existsMem_iff, memPairFormula_iff he]
  rfl

theorem range_bound_exists_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory) (V H ω : M.Domain) :
    ∃ D, RangeBound M D V H ω := by
  obtain ⟨D,hD⟩ := SetTheory.KP.separation_exists_d (KP1Y.models_weakKP hM) rangeSchema ((oneEnv H).push ω) V
  have hc (T : M.Domain) : M.mem T D ↔ M.mem T V ∧ ∃ n, M.mem n ω ∧ MemPair M H n T := by
    simpa only [rangeSchema_iff hM.1] using hD T
  exact ⟨D,fun T hT => ((hc T).mp hT).1,fun T hT => (hc T).trans ⟨And.right,fun h => ⟨hT,h⟩⟩⟩

theorem RangeBound.exact {M : SetTheory.Structure.{u}} (he : Extensional M) {D V H ω : M.Domain}
    (hR : RangeBound M D V H ω) (hH : Graph M H ω V) (T : M.Domain) :
    M.mem T D ↔ ∃ n, M.mem n ω ∧ MemPair M H n T := by
  constructor
  · intro hT
    exact (hR.2 T (hR.1 T hT)).mp hT
  · rintro ⟨n,hn,hAt⟩
    exact (hR.2 T (hH.bounds he hAt).2).mpr ⟨n,hn,hAt⟩

def SpaceCertificate (M : SetTheory.Structure.{u}) (ω A S B : M.Domain) : Prop :=
  ∃ H, M.mem H B ∧ ∃ V, M.mem V B ∧ ∃ Q, M.mem Q B ∧ ∃ D, M.mem D B ∧
    KP1Y.SigmaRecursion.ValueHistory M (spaceStep.denote (oneEnv A)) H ω V Q ∧ RangeBound M D V H ω ∧
      ∀ F, M.mem F S ↔ ∃ T, M.mem T D ∧ M.mem F T

theorem space_certificate_exists_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {ω : M.Domain} (hω : M.IsOmega ω) (A : M.Domain) : ∃ S B, SpaceCertificate M ω A S B := by
  have hw := KP1Y.models_weakKP hM
  obtain ⟨H,V,Q,hH⟩ := space_history_exists_d hM hω A
  obtain ⟨D,hD⟩ := range_bound_exists_d hM V H ω
  obtain ⟨S,hS⟩ := SetTheory.KP.exists_union hw D
  obtain ⟨B1,hB1⟩ := SetTheory.KP.exists_pair hw H V
  obtain ⟨B2,hB2⟩ := SetTheory.KP.exists_pair hw Q D
  obtain ⟨B,hB⟩ := SetTheory.KP.exists_unionOfTwo hw B1 B2
  exact ⟨S,B,H,(hB H).mpr (Or.inl ((hB1 H).mpr (Or.inl rfl))),
    V,(hB V).mpr (Or.inl ((hB1 V).mpr (Or.inr rfl))),
    Q,(hB Q).mpr (Or.inr ((hB2 Q).mpr (Or.inl rfl))),
    D,(hB D).mpr (Or.inr ((hB2 D).mpr (Or.inr rfl))),hH,hD,hS⟩

theorem space_certificate_exact_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {ω A S B : M.Domain} (hω : M.IsOmega ω) (h : SpaceCertificate M ω A S B) :
    ∀ F, M.mem F S ↔ ∃ n, M.mem n ω ∧ Graph M F n A := by
  obtain ⟨H,_,V,_,Q,_,D,_,hH,hD,hS⟩ := h
  have hExact := space_history_exact_d hM hω hH
  intro F
  constructor
  · intro hF
    obtain ⟨T,hT,hFT⟩ := (hS F).mp hF
    obtain ⟨n,hn,hAt⟩ := (hD.exact hM.1 hH.values T).mp hT
    exact ⟨n,hn,(hExact n hn T hAt F).mp hFT⟩
  · rintro ⟨n,hn,hF⟩
    obtain ⟨T,_,hAt⟩ := hH.values.total n hn
    exact (hS F).mpr ⟨T,(hD.exact hM.1 hH.values T).mpr ⟨n,hn,hAt⟩,(hExact n hn T hAt F).mpr hF⟩

theorem space_certificate_unique_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {ω A S T B D : M.Domain} (hω : M.IsOmega ω) (hS : SpaceCertificate M ω A S B) (hT : SpaceCertificate M ω A T D) : S=T :=
  hM.1.eq_of_same_members S T (fun F => (space_certificate_exact_d hM hω hS F).trans
    (space_certificate_exact_d hM hω hT F).symm)

end KP1Y.Sequences
