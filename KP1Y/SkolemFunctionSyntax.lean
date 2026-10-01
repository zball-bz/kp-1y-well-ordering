import KP1Y.SkolemKeys

/-! 最小见证选择及整个 Skolem 关系行的字面 Δ₀ 公式。 -/
namespace KP1Y.Satisfaction
open YesMetaZFC YesMetaZFC.SetTheory YesMetaZFC.SetTheory.Definitional
open KP1Y.Kuratowski
universe u

def chosenWitnessFormula {n : Nat} (C : Context (Project.Term n)) (I : EvaluationData (Project.Term n))
    (zero p j s bound v x : Project.Term n) : Project.Formula 1 n :=
  .conj (.mem x I.carrier)
    (.disj (.conj (falseWitnessFormula C I p j s bound v x)
        (Project.Formula.forallMem x (.neg (falseWitnessFormula C.weaken I.weaken p.weaken j.weaken s.weaken bound.weaken v.weaken (.bound 0)))))
      (.conj (Project.Formula.extensionalEq x zero)
        (Project.Formula.forallMem I.carrier (.neg (falseWitnessFormula C.weaken I.weaken p.weaken j.weaken s.weaken bound.weaken v.weaken (.bound 0))))))

theorem chosenWitnessFormula_delta0 {n : Nat} (C : Context (Project.Term n)) (I : EvaluationData (Project.Term n))
    (zero p j s bound v x : Project.Term n) : (chosenWitnessFormula C I zero p j s bound v x).IsDelta0 :=
  .conj (.mem _ _) (.disj
    (.conj (falseWitnessFormula_delta0 _ _ _ _ _ _ _ _) (.forallMem _ (.neg (falseWitnessFormula_delta0 _ _ _ _ _ _ _ _))))
    (.conj (.atom _ _ _) (.forallMem _ (.neg (falseWitnessFormula_delta0 _ _ _ _ _ _ _ _)))))

theorem chosenWitnessFormula_iff {M : SetTheory.Structure.{u}} (he : Extensional M) {n : Nat}
    (env : Env M n) (C : Context (Project.Term n)) (I : EvaluationData (Project.Term n)) (zero p j s bound v x : Project.Term n) :
    Project.Formula.satisfies env (chosenWitnessFormula C I zero p j s bound v x) ↔
      ChosenWitness M (C.eval env) (I.eval env) (zero.eval env) (p.eval env) (j.eval env) (s.eval env)
        (bound.eval env) (v.eval env) (x.eval env) := by
  simp only [chosenWitnessFormula, Project.Formula.satisfies_conj_iff, Project.Formula.satisfies_disj_iff,
    Project.Formula.satisfies_forallMem_iff, Project.Formula.satisfies_neg_iff, Project.Formula.satisfies_mem_iff,
    Project.Formula.satisfies_extensionalEq_iff_eq he, falseWitnessFormula_iff he,
    Context.eval_weaken, EvaluationData.eval_weaken, Definitional.Term.eval_weaken]
  rfl

def SkolemRow (M : SetTheory.Structure.{u}) (C : Context M.Domain) (I : EvaluationData M.Domain)
    (K : SkolemBounds M.Domain) (zero key x : M.Domain) : Prop :=
  ∃ p, M.mem p C.programs ∧ ∃ j, M.mem j C.omega ∧ ∃ s, M.mem s I.assignments ∧
    ∃ bound, M.mem bound C.omega ∧ ∃ v, M.mem v C.omega ∧
      KeyCode M K key p j s bound v ∧ ChosenWitness M C I zero p j s bound v x

def skolemRowFormula {n : Nat} (C : Context (Project.Term n)) (I : EvaluationData (Project.Term n))
    (K : SkolemBounds (Project.Term n)) (zero key x : Project.Term n) : Project.Formula 1 n :=
  Project.Formula.existsMem C.programs (Project.Formula.existsMem C.omega.weaken
    (Project.Formula.existsMem I.assignments.weaken.weaken (Project.Formula.existsMem C.omega.weaken.weaken.weaken
      (Project.Formula.existsMem C.omega.weaken.weaken.weaken.weaken
        (.conj (keyCodeFormula K.weaken.weaken.weaken.weaken.weaken key.weaken.weaken.weaken.weaken.weaken
            (.bound 4) (.bound 3) (.bound 2) (.bound 1) (.bound 0))
          (chosenWitnessFormula C.weaken.weaken.weaken.weaken.weaken I.weaken.weaken.weaken.weaken.weaken
            zero.weaken.weaken.weaken.weaken.weaken (.bound 4) (.bound 3) (.bound 2) (.bound 1) (.bound 0)
            x.weaken.weaken.weaken.weaken.weaken))))))

theorem skolemRowFormula_delta0 {n : Nat} (C : Context (Project.Term n)) (I : EvaluationData (Project.Term n))
    (K : SkolemBounds (Project.Term n)) (zero key x : Project.Term n) : (skolemRowFormula C I K zero key x).IsDelta0 :=
  .existsMem _ (.existsMem _ (.existsMem _ (.existsMem _ (.existsMem _
    (.conj (keyCodeFormula_delta0 _ _ _ _ _ _ _) (chosenWitnessFormula_delta0 _ _ _ _ _ _ _ _ _))))))

theorem skolemRowFormula_iff {M : SetTheory.Structure.{u}} (he : Extensional M) {n : Nat}
    (env : Env M n) (C : Context (Project.Term n)) (I : EvaluationData (Project.Term n)) (K : SkolemBounds (Project.Term n))
    (zero key x : Project.Term n) :
    Project.Formula.satisfies env (skolemRowFormula C I K zero key x) ↔
      SkolemRow M (C.eval env) (I.eval env) (K.eval env) (zero.eval env) (key.eval env) (x.eval env) := by
  simp only [skolemRowFormula, Project.Formula.satisfies_existsMem_iff, Project.Formula.satisfies_conj_iff,
    keyCodeFormula_iff he, chosenWitnessFormula_iff he, Context.eval_weaken,
    EvaluationData.eval_weaken, SkolemBounds.eval_weaken, Definitional.Term.eval_weaken]
  rfl

private def skolemContext : Context (Project.Term 25) :=
  ⟨.bound 2,.bound 3,.bound 4,.bound 5,.bound 6,.bound 7,.bound 8,
    .bound 9,.bound 10,.bound 11,.bound 12,.bound 13,.bound 14⟩
private def skolemInstance : EvaluationData (Project.Term 25) :=
  ⟨.bound 15,.bound 16,.bound 17,.bound 18,.bound 19⟩
private def skolemBounds : SkolemBounds (Project.Term 25) :=
  ⟨.bound 20,.bound 21,.bound 22,.bound 23⟩

def skolemRowSchema : Project.Delta0BinarySchema 23 where
  body := skolemRowFormula skolemContext skolemInstance skolemBounds (.bound 24) (.bound 1) (.bound 0)
  freeClosed := by
    simp [skolemRowFormula, chosenWitnessFormula, falseWitnessFormula, keyCodeFormula, Assignments.updatedFormula,
      nodeTrueFormula, Functions.graphFormula, memPairFormula, codeFormula, pairFormula, Context.weaken,
      Context.map, Context.withInterpretation, EvaluationData.context, EvaluationData.weaken, EvaluationData.map,
      SkolemBounds.weaken, SkolemBounds.map, skolemContext, skolemInstance, skolemBounds,
      Project.Formula.existsMem, Project.Formula.forallMem, Definitional.Formula.FreeClosed]
  delta0 := skolemRowFormula_delta0 _ _ _ _ _ _

def skolemEnv {M : SetTheory.Structure.{u}} (C : Context M.Domain) (I : EvaluationData M.Domain)
    (K : SkolemBounds M.Domain) (zero : M.Domain) : Env M 23 where
  bound k := match k.val with
    | 0 => C.omega | 1 => C.carrier | 2 => C.operands | 3 => C.pairs
    | 4 => C.instructions | 5 => C.programs | 6 => C.assignments | 7 => C.columns
    | 8 => C.atomic | 9 => C.atomTag | 10 => C.negTag | 11 => C.impTag | 12 => C.allTag
    | 13 => I.carrier | 14 => I.assignments | 15 => I.columns | 16 => I.atomic | 17 => I.table
    | 18 => K.programNodes | 19 => K.variableSlots | 20 => K.assignmentSlots | 21 => K.keys | _ => zero
  free _ := C.omega

theorem skolemRowSchema_iff {M : SetTheory.Structure.{u}} (he : Extensional M)
    (C : Context M.Domain) (I : EvaluationData M.Domain) (K : SkolemBounds M.Domain) (zero key x : M.Domain) :
    Project.Formula.satisfies (((skolemEnv C I K zero).push key).push x) skolemRowSchema.body ↔ SkolemRow M C I K zero key x := by
  simp only [skolemRowSchema, skolemRowFormula_iff he]
  rfl

end KP1Y.Satisfaction
