import KP1Y.ConjunctionSyntax
import KP1Y.ProgramInclusion

/-! 保留已有程序的内部合取编译验证，供组合多个有限图条件使用。 -/
namespace KP1Y.Satisfaction
open YesMetaZFC YesMetaZFC.SetTheory YesMetaZFC.SetTheory.Definitional
open KP1Y.Kuratowski KP1Y.Functions
universe u

def ConjunctionFrom (M : SetTheory.Structure.{u}) (C : Context M.Domain) (D : RelationalData M.Domain)
    (H original seq stage bound : M.Domain) : Prop :=
  ∃ p, M.mem p C.programs ∧ ∃ length, M.mem length C.omega ∧ ∃ head, M.mem head C.omega ∧
    FormulaResult M C D p length head bound ∧ M.MemberSubset original p ∧
      ∀ s, M.mem s C.assignments → (NodeTrue M C H p head s ↔ AllAtoms M C D seq stage s)

def conjunctionFromFormula {n : Nat} (C : Context (Project.Term n)) (D : RelationalData (Project.Term n))
    (H original seq stage bound : Project.Term n) : Project.Formula 1 n :=
  Project.Formula.existsMem C.programs (Project.Formula.existsMem C.omega.weaken
    (Project.Formula.existsMem C.omega.weaken.weaken
      (.conj (resultFormula C.weaken.weaken.weaken D.weaken.weaken.weaken
          (.bound 2) (.bound 1) (.bound 0) bound.weaken.weaken.weaken)
        (.conj (Project.Formula.subset original.weaken.weaken.weaken (.bound 2))
          (Project.Formula.forallMem C.assignments.weaken.weaken.weaken
            (.iff (nodeTrueFormula C.weaken.weaken.weaken.weaken H.weaken.weaken.weaken.weaken (.bound 3) (.bound 1) (.bound 0))
              (allAtomsFormula C.weaken.weaken.weaken.weaken D.weaken.weaken.weaken.weaken
                seq.weaken.weaken.weaken.weaken stage.weaken.weaken.weaken.weaken (.bound 0))))))))

theorem conjunctionFromFormula_delta0 {n : Nat} (C : Context (Project.Term n)) (D : RelationalData (Project.Term n))
    (H original seq stage bound : Project.Term n) : (conjunctionFromFormula C D H original seq stage bound).IsDelta0 :=
  .existsMem _ (.existsMem _ (.existsMem _ (.conj (resultFormula_delta0 _ _ _ _ _ _)
    (.conj (.atom _ _ _) (.forallMem _ (.iff (nodeTrueFormula_delta0 _ _ _ _ _) (allAtomsFormula_delta0 _ _ _ _ _)))))))

theorem conjunctionFromFormula_iff {M : SetTheory.Structure.{u}} (he : Extensional M) {n : Nat}
    (env : Env M n) (C : Context (Project.Term n)) (D : RelationalData (Project.Term n))
    (H original seq stage bound : Project.Term n) :
    Project.Formula.satisfies env (conjunctionFromFormula C D H original seq stage bound) ↔
      ConjunctionFrom M (C.eval env) (D.eval env) (H.eval env) (original.eval env) (seq.eval env) (stage.eval env) (bound.eval env) := by
  simp only [conjunctionFromFormula, Project.Formula.satisfies_existsMem_iff,
    Project.Formula.satisfies_conj_iff, Project.Formula.satisfies_subset_iff,
    Project.Formula.satisfies_forallMem_iff, Project.Formula.satisfies_iff_iff,
    resultFormula_iff he, nodeTrueFormula_iff he, allAtomsFormula_iff he,
    Context.eval_weaken, RelationalData.eval_weaken, Definitional.Term.eval_weaken]
  rfl

private def fromContextParameters : Context (Project.Term 27) :=
  ⟨.bound 6,.bound 7,.bound 8,.bound 9,.bound 10,.bound 11,.bound 12,
    .bound 13,.bound 14,.bound 15,.bound 16,.bound 17,.bound 18⟩
private def fromDataParameters : RelationalData (Project.Term 27) :=
  ⟨.bound 19,.bound 20,.bound 21,.bound 22,.bound 23,.bound 24,.bound 25,.bound 26⟩

def conjunctionFromGuard : Project.UnarySchema 26 where
  body := .imp (Project.Formula.subset (.bound 0) (.bound 1))
    (conjunctionFromFormula fromContextParameters fromDataParameters (.bound 5) (.bound 4) (.bound 3) (.bound 0) (.bound 2))
  freeClosed := by
    simp [conjunctionFromFormula, resultFormula, wellFormedProgramFormula, wellFormedAtFormula,
      scopedAtomFormula, instructionAtFormula, nodeTrueFormula, allAtomsFormula, graphFormula,
      Bounded.successorFormula, memPairFormula, codeFormula, pairFormula,
      Context.weaken, Context.map, RelationalData.weaken, RelationalData.map,
      fromContextParameters, fromDataParameters, Project.Formula.existsMem,
      Project.Formula.forallMem, Definitional.Formula.FreeClosed]

theorem conjunctionFromGuard_iff {M : SetTheory.Structure.{u}} (he : Extensional M)
    (C : Context M.Domain) (D : RelationalData M.Domain) (H original seq bound N stage : M.Domain) :
    Project.Formula.satisfies (((((((syntaxEnv C D).push H).push original).push seq).push bound).push N).push stage)
        conjunctionFromGuard.body ↔
      (M.MemberSubset stage N → ConjunctionFrom M C D H original seq stage bound) := by
  simp only [conjunctionFromGuard, Project.Formula.satisfies_imp_iff, Project.Formula.satisfies_subset_iff,
    conjunctionFromFormula_iff he]
  rfl

end KP1Y.Satisfaction
