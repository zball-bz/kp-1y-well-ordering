import KP1Y.SatisfactionTruth

/-! 程序满意度集合的真实对象存在句，以及互补的两个字面 Σ₁ 定义。 -/
namespace KP1Y.Satisfaction
open YesMetaZFC YesMetaZFC.SetTheory YesMetaZFC.SetTheory.Definitional
open KP1Y.Kuratowski
universe u

def satisfactionCore : Project.Formula 1 13 :=
  .imp (Project.Formula.isOmega rootParameters.omega)
    (.existsE (.existsE (.conj
      (evaluationFormula rootParameters.weaken.weaken (.bound 1))
      (truthFormula rootParameters.weaken.weaken (.bound 1) (.bound 0)))))

def satisfactionSentence : Project.Sentence :=
  Project.Sentence.forallClosure satisfactionCore (by
    simp [satisfactionCore, evaluationFormula, truthFormula, finalTrueFormula,
      evalFormula, atomicFormula, negationFormula, implicationFormula, universalFormula,
      instructionAtFormula, Assignments.updatedFormula, Functions.graphFormula,
      Bounded.successorFormula, memPairFormula, codeFormula, pairFormula,
      Context.weaken, Context.map, rootParameters, Project.Formula.isOmega,
      Project.Formula.isInductive, Project.Formula.isEmpty, Project.Formula.isSuccessor,
      Project.Formula.forallMem, Project.Formula.existsMem, Definitional.Formula.FreeClosed])

theorem satisfactionCore_iff {M : SetTheory.Structure.{u}} (he : Extensional M) (env : Env M 13) :
    Project.Formula.satisfies env satisfactionCore ↔
      (M.IsOmega (env.bound 0) → ∃ H Sat,
        Evaluation M (rootParameters.eval env) H ∧ TruthSet M (rootParameters.eval env) H Sat) := by
  simp only [satisfactionCore, Project.Formula.satisfies_imp_iff,
    Project.Formula.satisfies_isOmega_iff, Project.Formula.satisfies_exists_iff,
    Project.Formula.satisfies_conj_iff, evaluationFormula_iff he, truthFormula_iff he,
    Context.eval_weaken]
  rfl

theorem satisfaction_derivable : KP1Y.Derives satisfactionSentence := by
  apply KP1Y.derives_of_all_models
  intro M hM free
  apply (Project.Formula.satisfies_forallClosure_iff free satisfactionCore).mpr
  intro bound
  let env : Env M 13 := ⟨bound,free⟩
  apply (satisfactionCore_iff hM.1 env).mpr
  intro hω
  obtain ⟨H,hH⟩ := evaluation_exists_d hM (rootParameters.eval env) hω
  obtain ⟨Sat,hSat⟩ := truth_set_exists_d hM (rootParameters.eval env) H
  exact ⟨H,Sat,hH,hSat⟩

private def valueParameters : Context (Project.Term 15) :=
  ⟨.bound 2,.bound 3,.bound 4,.bound 5,.bound 6,.bound 7,.bound 8,
    .bound 9,.bound 10,.bound 11,.bound 12,.bound 13,.bound 14⟩

/-- 存在一个经 Δ₀ 验证的完整求值表，并且指定末节点为真。 -/
def positiveTruthSchema : Project.Delta0BinarySchema 13 where
  body := .conj (evaluationFormula valueParameters (.bound 0))
    (finalTrueFormula valueParameters (.bound 0) (.bound 1))
  freeClosed := by
    simp [evaluationFormula, finalTrueFormula, evalFormula, atomicFormula, negationFormula,
      implicationFormula, universalFormula, instructionAtFormula, Assignments.updatedFormula,
      Functions.graphFormula, Bounded.successorFormula, memPairFormula, codeFormula, pairFormula,
      Context.weaken, Context.map, valueParameters, Project.Formula.forallMem,
      Project.Formula.existsMem, Definitional.Formula.FreeClosed]
  delta0 := .conj (evaluationFormula_delta0 _ _) (finalTrueFormula_delta0 _ _ _)

/-- 同一个规范求值问题的否定；唯一性保证不同证书不会给出矛盾真值。 -/
def negativeTruthSchema : Project.Delta0BinarySchema 13 where
  body := .conj (evaluationFormula valueParameters (.bound 0))
    (.neg (finalTrueFormula valueParameters (.bound 0) (.bound 1)))
  freeClosed := by
    simpa only [positiveTruthSchema, Definitional.Formula.FreeClosed] using positiveTruthSchema.freeClosed
  delta0 := .conj (evaluationFormula_delta0 _ _) (.neg (finalTrueFormula_delta0 _ _ _))

theorem positiveTruthSchema_iff {M : SetTheory.Structure.{u}} (he : Extensional M)
    (C : Context M.Domain) (c H : M.Domain) :
    Project.Formula.satisfies (((contextEnv C).push c).push H) positiveTruthSchema.body ↔
      Evaluation M C H ∧ FinalTrue M C H c := by
  simp only [positiveTruthSchema, Project.Formula.satisfies_conj_iff,
    evaluationFormula_iff he, finalTrueFormula_iff he]
  rfl

theorem negativeTruthSchema_iff {M : SetTheory.Structure.{u}} (he : Extensional M)
    (C : Context M.Domain) (c H : M.Domain) :
    Project.Formula.satisfies (((contextEnv C).push c).push H) negativeTruthSchema.body ↔
      Evaluation M C H ∧ ¬FinalTrue M C H c := by
  simp only [negativeTruthSchema, Project.Formula.satisfies_conj_iff,
    Project.Formula.satisfies_neg_iff, evaluationFormula_iff he, finalTrueFormula_iff he]
  rfl

theorem finalTrue_bounds {M : SetTheory.Structure.{u}} (he : Extensional M)
    {C : Context M.Domain} {H c : M.Domain} (hH : Evaluation M C H) (hTrue : FinalTrue M C H c) :
    M.mem c C.columns := by
  obtain ⟨_,_,_,_,_,i,_,_,_,_,_,hLookup⟩ := hTrue
  exact (KP1Y.Recursion.History.bounds he hH hLookup).2

theorem truth_positive_iff_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : Context M.Domain} (hω : M.IsOmega C.omega) {H Sat : M.Domain}
    (hH : Evaluation M C H) (hSat : TruthSet M C H Sat) (c : M.Domain) :
    M.mem c Sat ↔ ∃ G, Project.Formula.satisfies (((contextEnv C).push c).push G) positiveTruthSchema.body := by
  constructor
  · intro hc
    exact ⟨H,(positiveTruthSchema_iff hM.1 C c H).mpr ⟨hH,((hSat c).mp hc).2⟩⟩
  · rintro ⟨G,hG⟩
    obtain ⟨hGEval,hTrue⟩ := (positiveTruthSchema_iff hM.1 C c G).mp hG
    have hEq := evaluation_unique_d hM hω hGEval hH
    subst G
    exact (hSat c).mpr ⟨finalTrue_bounds hM.1 hH hTrue,hTrue⟩

theorem truth_negative_iff_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : Context M.Domain} (hω : M.IsOmega C.omega) {H Sat : M.Domain}
    (hH : Evaluation M C H) (hSat : TruthSet M C H Sat) (c : M.Domain) :
    ¬M.mem c Sat ↔ ∃ G, Project.Formula.satisfies (((contextEnv C).push c).push G) negativeTruthSchema.body := by
  constructor
  · intro hNot
    exact ⟨H,(negativeTruthSchema_iff hM.1 C c H).mpr
      ⟨hH,fun hTrue => hNot ((hSat c).mpr ⟨finalTrue_bounds hM.1 hH hTrue,hTrue⟩)⟩⟩
  · rintro ⟨G,hG⟩ hc
    obtain ⟨hGEval,hNot⟩ := (negativeTruthSchema_iff hM.1 C c G).mp hG
    have hEq := evaluation_unique_d hM hω hGEval hH
    subst G
    exact hNot ((hSat c).mp hc).2

end KP1Y.Satisfaction
