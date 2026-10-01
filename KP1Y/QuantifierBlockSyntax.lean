import KP1Y.FrameAgreement
import KP1Y.FormulaResult
import KP1Y.TypedSatisfaction
import KP1Y.ProgramInclusion

/-! 内部有限量词块的目标语义和有界编译结果验证。 -/
namespace KP1Y.Satisfaction
open YesMetaZFC YesMetaZFC.SetTheory YesMetaZFC.SetTheory.Definitional
open KP1Y.Kuratowski KP1Y.Functions KP1Y.Assignments
universe u

def Quantified (M : SetTheory.Structure.{u}) (C : Context M.Domain) (H original originalHead vars stage s bound : M.Domain) : Prop :=
  ∀ t, M.mem t C.assignments → AgreeOutside M vars stage s t bound C.carrier → NodeTrue M C H original originalHead t

def quantifiedFormula {n : Nat} (C : Context (Project.Term n)) (H original originalHead vars stage s bound : Project.Term n) :
    Project.Formula 1 n :=
  Project.Formula.forallMem C.assignments (.imp
    (agreeOutsideFormula vars.weaken stage.weaken s.weaken (.bound 0) bound.weaken C.carrier.weaken)
    (nodeTrueFormula C.weaken H.weaken original.weaken originalHead.weaken (.bound 0)))

theorem quantifiedFormula_delta0 {n : Nat} (C : Context (Project.Term n))
    (H original originalHead vars stage s bound : Project.Term n) : (quantifiedFormula C H original originalHead vars stage s bound).IsDelta0 :=
  .forallMem _ (.imp (agreeOutsideFormula_delta0 _ _ _ _ _ _) (nodeTrueFormula_delta0 _ _ _ _ _))

theorem quantifiedFormula_iff {M : SetTheory.Structure.{u}} (he : Extensional M) {n : Nat}
    (env : Env M n) (C : Context (Project.Term n)) (H original originalHead vars stage s bound : Project.Term n) :
    Project.Formula.satisfies env (quantifiedFormula C H original originalHead vars stage s bound) ↔
      Quantified M (C.eval env) (H.eval env) (original.eval env) (originalHead.eval env)
        (vars.eval env) (stage.eval env) (s.eval env) (bound.eval env) := by
  simp only [quantifiedFormula, Project.Formula.satisfies_forallMem_iff, Project.Formula.satisfies_imp_iff,
    agreeOutsideFormula_iff he, nodeTrueFormula_iff he, Context.eval_weaken, Definitional.Term.eval_weaken]
  rfl

theorem quantified_successor_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : Context M.Domain} {H original originalHead vars N stage next s bound v : M.Domain}
    (hVars : Graph M vars N bound) (hAt : MemPair M vars stage v) (hSucc : M.SuccessorOf next stage)
    (hS : Graph M s bound C.carrier) :
    (∀ x, M.mem x C.carrier → ∀ u, Updated M u s bound C.carrier v x →
      Quantified M C H original originalHead vars stage u bound) ↔
      Quantified M C H original originalHead vars next s bound := by
  constructor
  · intro h t ht hFrame
    obtain ⟨x,hx,u,hu,hOld⟩ := factor_frame_update_d hM hVars hAt hSucc hFrame
    exact h x hx u hu t ht hOld
  · intro h x _ u hu t ht hOld
    exact h t ht (merge_frame_update hM.1 hVars hAt hSucc hS hu hOld)

def QuantificationResult (M : SetTheory.Structure.{u}) (C : Context M.Domain) (D : RelationalData M.Domain)
    (H original originalHead vars stage bound : M.Domain) : Prop :=
  ∃ p, M.mem p C.programs ∧ ∃ length, M.mem length C.omega ∧ ∃ head, M.mem head C.omega ∧
    FormulaResult M C D p length head bound ∧ M.MemberSubset original p ∧
      ∀ s, M.mem s C.assignments → Graph M s bound C.carrier →
      (NodeTrue M C H p head s ↔ Quantified M C H original originalHead vars stage s bound)

def quantificationResultFormula {n : Nat} (C : Context (Project.Term n)) (D : RelationalData (Project.Term n))
    (H original originalHead vars stage bound : Project.Term n) : Project.Formula 1 n :=
  Project.Formula.existsMem C.programs (Project.Formula.existsMem C.omega.weaken
    (Project.Formula.existsMem C.omega.weaken.weaken
      (.conj (resultFormula C.weaken.weaken.weaken D.weaken.weaken.weaken
          (.bound 2) (.bound 1) (.bound 0) bound.weaken.weaken.weaken)
        (.conj (Project.Formula.subset original.weaken.weaken.weaken (.bound 2))
        (Project.Formula.forallMem C.assignments.weaken.weaken.weaken
          (.imp (graphFormula (.bound 0) bound.weaken.weaken.weaken.weaken C.carrier.weaken.weaken.weaken.weaken)
            (.iff (nodeTrueFormula C.weaken.weaken.weaken.weaken H.weaken.weaken.weaken.weaken (.bound 3) (.bound 1) (.bound 0))
              (quantifiedFormula C.weaken.weaken.weaken.weaken H.weaken.weaken.weaken.weaken
                original.weaken.weaken.weaken.weaken originalHead.weaken.weaken.weaken.weaken
                vars.weaken.weaken.weaken.weaken stage.weaken.weaken.weaken.weaken (.bound 0) bound.weaken.weaken.weaken.weaken))))))))

theorem quantificationResultFormula_delta0 {n : Nat} (C : Context (Project.Term n)) (D : RelationalData (Project.Term n))
    (H original originalHead vars stage bound : Project.Term n) :
    (quantificationResultFormula C D H original originalHead vars stage bound).IsDelta0 :=
  .existsMem _ (.existsMem _ (.existsMem _ (.conj (resultFormula_delta0 _ _ _ _ _ _)
    (.conj (.atom _ _ _) (.forallMem _ (.imp (graphFormula_delta0 _ _ _) (.iff (nodeTrueFormula_delta0 _ _ _ _ _)
      (quantifiedFormula_delta0 _ _ _ _ _ _ _ _))))))))

theorem quantificationResultFormula_iff {M : SetTheory.Structure.{u}} (he : Extensional M) {n : Nat}
    (env : Env M n) (C : Context (Project.Term n)) (D : RelationalData (Project.Term n))
    (H original originalHead vars stage bound : Project.Term n) :
    Project.Formula.satisfies env (quantificationResultFormula C D H original originalHead vars stage bound) ↔
      QuantificationResult M (C.eval env) (D.eval env) (H.eval env) (original.eval env) (originalHead.eval env)
        (vars.eval env) (stage.eval env) (bound.eval env) := by
  simp only [quantificationResultFormula, Project.Formula.satisfies_existsMem_iff,
    Project.Formula.satisfies_conj_iff, Project.Formula.satisfies_subset_iff, Project.Formula.satisfies_forallMem_iff,
    Project.Formula.satisfies_imp_iff, Project.Formula.satisfies_iff_iff, resultFormula_iff he,
    graphFormula_iff he, nodeTrueFormula_iff he, quantifiedFormula_iff he,
    Context.eval_weaken, RelationalData.eval_weaken, Definitional.Term.eval_weaken]
  rfl

private def quantificationContextParameters : Context (Project.Term 28) :=
  ⟨.bound 7,.bound 8,.bound 9,.bound 10,.bound 11,.bound 12,.bound 13,
    .bound 14,.bound 15,.bound 16,.bound 17,.bound 18,.bound 19⟩
private def quantificationDataParameters : RelationalData (Project.Term 28) :=
  ⟨.bound 20,.bound 21,.bound 22,.bound 23,.bound 24,.bound 25,.bound 26,.bound 27⟩

def quantificationGuard : Project.UnarySchema 27 where
  body := .imp (Project.Formula.subset (.bound 0) (.bound 1))
    (quantificationResultFormula quantificationContextParameters quantificationDataParameters
      (.bound 6) (.bound 5) (.bound 4) (.bound 3) (.bound 0) (.bound 2))
  freeClosed := by
    simp [quantificationResultFormula, quantifiedFormula, agreeOutsideFormula, touchedFormula,
      resultFormula, wellFormedProgramFormula, wellFormedAtFormula, scopedAtomFormula, instructionAtFormula,
      nodeTrueFormula, graphFormula, Bounded.successorFormula, memPairFormula, codeFormula, pairFormula,
      Context.weaken, Context.map, RelationalData.weaken, RelationalData.map,
      quantificationContextParameters, quantificationDataParameters, Project.Formula.existsMem,
      Project.Formula.forallMem, Definitional.Formula.FreeClosed]

theorem quantificationGuard_iff {M : SetTheory.Structure.{u}} (he : Extensional M)
    (C : Context M.Domain) (D : RelationalData M.Domain) (H original originalHead vars bound N stage : M.Domain) :
    Project.Formula.satisfies ((((((((syntaxEnv C D).push H).push original).push originalHead).push vars).push bound).push N).push stage)
        quantificationGuard.body ↔
      (M.MemberSubset stage N → QuantificationResult M C D H original originalHead vars stage bound) := by
  simp only [quantificationGuard, Project.Formula.satisfies_imp_iff, Project.Formula.satisfies_subset_iff,
    quantificationResultFormula_iff he]
  rfl

end KP1Y.Satisfaction
