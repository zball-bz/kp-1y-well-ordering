import KP1Y.CompileDerived
import KP1Y.TypedSatisfaction

/-! 内部有限合取的语法及编译结果验证；全部量词有实际集合界。 -/
namespace KP1Y.Satisfaction
open YesMetaZFC YesMetaZFC.SetTheory YesMetaZFC.SetTheory.Definitional
open KP1Y.Kuratowski KP1Y.Functions
universe u

def AllAtoms (M : SetTheory.Structure.{u}) (C : Context M.Domain) (D : RelationalData M.Domain)
    (seq stage s : M.Domain) : Prop :=
  ∀ k, M.mem k stage → ∃ a, M.mem a D.codes ∧ MemPair M seq k a ∧ MemPair M C.atomic a s

def allAtomsFormula {n : Nat} (C : Context (Project.Term n)) (D : RelationalData (Project.Term n))
    (seq stage s : Project.Term n) : Project.Formula 1 n :=
  Project.Formula.forallMem stage (Project.Formula.existsMem D.codes.weaken
    (.conj (memPairFormula seq.weaken.weaken (.bound 1) (.bound 0))
      (memPairFormula C.atomic.weaken.weaken (.bound 0) s.weaken.weaken)))

theorem allAtomsFormula_delta0 {n : Nat} (C : Context (Project.Term n)) (D : RelationalData (Project.Term n))
    (seq stage s : Project.Term n) : (allAtomsFormula C D seq stage s).IsDelta0 :=
  .forallMem _ (.existsMem _ (.conj (memPairFormula_delta0 _ _ _) (memPairFormula_delta0 _ _ _)))

theorem allAtomsFormula_iff {M : SetTheory.Structure.{u}} (he : Extensional M) {n : Nat}
    (env : Env M n) (C : Context (Project.Term n)) (D : RelationalData (Project.Term n))
    (seq stage s : Project.Term n) :
    Project.Formula.satisfies env (allAtomsFormula C D seq stage s) ↔
      AllAtoms M (C.eval env) (D.eval env) (seq.eval env) (stage.eval env) (s.eval env) := by
  simp only [allAtomsFormula, Project.Formula.satisfies_forallMem_iff,
    Project.Formula.satisfies_existsMem_iff, Project.Formula.satisfies_conj_iff,
    memPairFormula_iff he, Definitional.Term.eval_weaken]
  rfl

theorem allAtoms_successor {M : SetTheory.Structure.{u}} (he : Extensional M)
    {C : Context M.Domain} {D : RelationalData M.Domain} {seq N stage next a s : M.Domain}
    (hSeq : Graph M seq N D.codes) (hAt : MemPair M seq stage a) (hSucc : M.SuccessorOf next stage) :
    AllAtoms M C D seq next s ↔ AllAtoms M C D seq stage s ∧ MemPair M C.atomic a s := by
  constructor
  · intro h
    refine ⟨fun k hk => h k ((hSucc k).mpr (Or.inl hk)),?_⟩
    obtain ⟨b,_,hAt',hTrue⟩ := h stage hSucc.predecessor_mem
    have hba := hSeq.unique stage b a hAt' hAt
    subst b
    exact hTrue
  · rintro ⟨hOld,hNow⟩ k hk
    rcases (hSucc k).mp hk with hk | hk
    · exact hOld k hk
    · have hEq := he.eq_of_same_members k stage hk
      subst k
      exact ⟨a,(hSeq.bounds he hAt).2,hAt,hNow⟩

def ConjunctionResult (M : SetTheory.Structure.{u}) (C : Context M.Domain) (D : RelationalData M.Domain)
    (H seq stage bound : M.Domain) : Prop :=
  ∃ p, M.mem p C.programs ∧ ∃ length, M.mem length C.omega ∧ ∃ head, M.mem head C.omega ∧
    FormulaResult M C D p length head bound ∧
      ∀ s, M.mem s C.assignments → (NodeTrue M C H p head s ↔ AllAtoms M C D seq stage s)

def conjunctionResultFormula {n : Nat} (C : Context (Project.Term n)) (D : RelationalData (Project.Term n))
    (H seq stage bound : Project.Term n) : Project.Formula 1 n :=
  Project.Formula.existsMem C.programs (Project.Formula.existsMem C.omega.weaken
    (Project.Formula.existsMem C.omega.weaken.weaken
      (.conj (resultFormula C.weaken.weaken.weaken D.weaken.weaken.weaken
          (.bound 2) (.bound 1) (.bound 0) bound.weaken.weaken.weaken)
        (Project.Formula.forallMem C.assignments.weaken.weaken.weaken
          (.iff (nodeTrueFormula C.weaken.weaken.weaken.weaken H.weaken.weaken.weaken.weaken (.bound 3) (.bound 1) (.bound 0))
            (allAtomsFormula C.weaken.weaken.weaken.weaken D.weaken.weaken.weaken.weaken
              seq.weaken.weaken.weaken.weaken stage.weaken.weaken.weaken.weaken (.bound 0)))))))

theorem conjunctionResultFormula_delta0 {n : Nat} (C : Context (Project.Term n)) (D : RelationalData (Project.Term n))
    (H seq stage bound : Project.Term n) : (conjunctionResultFormula C D H seq stage bound).IsDelta0 :=
  .existsMem _ (.existsMem _ (.existsMem _ (.conj (resultFormula_delta0 _ _ _ _ _ _)
    (.forallMem _ (.iff (nodeTrueFormula_delta0 _ _ _ _ _) (allAtomsFormula_delta0 _ _ _ _ _))))))

theorem conjunctionResultFormula_iff {M : SetTheory.Structure.{u}} (he : Extensional M) {n : Nat}
    (env : Env M n) (C : Context (Project.Term n)) (D : RelationalData (Project.Term n))
    (H seq stage bound : Project.Term n) :
    Project.Formula.satisfies env (conjunctionResultFormula C D H seq stage bound) ↔
      ConjunctionResult M (C.eval env) (D.eval env) (H.eval env) (seq.eval env) (stage.eval env) (bound.eval env) := by
  simp only [conjunctionResultFormula, Project.Formula.satisfies_existsMem_iff,
    Project.Formula.satisfies_conj_iff, Project.Formula.satisfies_forallMem_iff,
    Project.Formula.satisfies_iff_iff, resultFormula_iff he, nodeTrueFormula_iff he,
    allAtomsFormula_iff he, Context.eval_weaken, RelationalData.eval_weaken, Definitional.Term.eval_weaken]
  rfl

private def conjunctionContextParameters : Context (Project.Term 26) :=
  ⟨.bound 5,.bound 6,.bound 7,.bound 8,.bound 9,.bound 10,.bound 11,
    .bound 12,.bound 13,.bound 14,.bound 15,.bound 16,.bound 17⟩
private def conjunctionDataParameters : RelationalData (Project.Term 26) :=
  ⟨.bound 18,.bound 19,.bound 20,.bound 21,.bound 22,.bound 23,.bound 24,.bound 25⟩

def conjunctionGuard : Project.UnarySchema 25 where
  body := .imp (Project.Formula.subset (.bound 0) (.bound 1))
    (conjunctionResultFormula conjunctionContextParameters conjunctionDataParameters (.bound 4) (.bound 3) (.bound 0) (.bound 2))
  freeClosed := by
    simp [conjunctionResultFormula, resultFormula, wellFormedProgramFormula, wellFormedAtFormula,
      scopedAtomFormula, instructionAtFormula, nodeTrueFormula, allAtomsFormula, graphFormula,
      Bounded.successorFormula, memPairFormula, codeFormula, pairFormula,
      Context.weaken, Context.map, RelationalData.weaken, RelationalData.map,
      conjunctionContextParameters, conjunctionDataParameters, Project.Formula.existsMem,
      Project.Formula.forallMem, Definitional.Formula.FreeClosed]

theorem conjunctionGuard_iff {M : SetTheory.Structure.{u}} (he : Extensional M)
    (C : Context M.Domain) (D : RelationalData M.Domain) (H seq bound N stage : M.Domain) :
    Project.Formula.satisfies ((((((syntaxEnv C D).push H).push seq).push bound).push N).push stage) conjunctionGuard.body ↔
      (M.MemberSubset stage N → ConjunctionResult M C D H seq stage bound) := by
  simp only [conjunctionGuard, Project.Formula.satisfies_imp_iff, Project.Formula.satisfies_subset_iff,
    conjunctionResultFormula_iff he]
  rfl

end KP1Y.Satisfaction
