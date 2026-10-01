import KP1Y.SatisfactionInstruction

/-! 满意度递归的四个有界分支。全称分支的实际赋值更新仍在给定集合界内。 -/
namespace KP1Y.Satisfaction
open YesMetaZFC YesMetaZFC.SetTheory YesMetaZFC.SetTheory.Definitional
open KP1Y.Kuratowski KP1Y.Functions KP1Y.Assignments
universe u

def AtomicCase (M : SetTheory.Structure.{u}) (C : Context M.Domain) (p s i : M.Domain) : Prop :=
  ∃ a, M.mem a C.operands ∧ ∃ r, M.mem r C.operands ∧
    InstructionAt M C.instructions C.pairs p i C.atomTag a r ∧ MemPair M C.atomic a s

def NegationCase (M : SetTheory.Structure.{u}) (C : Context M.Domain) (p i c H : M.Domain) : Prop :=
  ∃ j, M.mem j i ∧ ∃ r, M.mem r C.operands ∧
    InstructionAt M C.instructions C.pairs p i C.negTag j r ∧ ¬MemPair M H j c

def ImplicationCase (M : SetTheory.Structure.{u}) (C : Context M.Domain) (p i c H : M.Domain) : Prop :=
  ∃ j, M.mem j i ∧ ∃ k, M.mem k i ∧
    InstructionAt M C.instructions C.pairs p i C.impTag j k ∧
      (MemPair M H j c → MemPair M H k c)

def UniversalCase (M : SetTheory.Structure.{u}) (C : Context M.Domain) (p s i H : M.Domain) : Prop :=
  ∃ j, M.mem j i ∧ ∃ v, M.mem v C.omega ∧ ∃ n, M.mem n C.omega ∧
    InstructionAt M C.instructions C.pairs p i C.allTag v j ∧
    Graph M s n C.carrier ∧ M.mem v n ∧
      ∀ x, M.mem x C.carrier → ∃ t, M.mem t C.assignments ∧ Updated M t s n C.carrier v x ∧
        ∃ b, M.mem b C.columns ∧ Codes M b p t ∧ MemPair M H j b

def atomicFormula {n : Nat} (C : Context (Project.Term n)) (p s i : Project.Term n) : Project.Formula 1 n :=
  Project.Formula.existsMem C.operands (Project.Formula.existsMem C.operands.weaken
    (.conj (instructionAtFormula C.instructions.weaken.weaken C.pairs.weaken.weaken
      p.weaken.weaken i.weaken.weaken C.atomTag.weaken.weaken (.bound 1) (.bound 0))
      (memPairFormula C.atomic.weaken.weaken (.bound 1) s.weaken.weaken)))

def negationFormula {n : Nat} (C : Context (Project.Term n)) (p i c H : Project.Term n) : Project.Formula 1 n :=
  Project.Formula.existsMem i (Project.Formula.existsMem C.operands.weaken
    (.conj (instructionAtFormula C.instructions.weaken.weaken C.pairs.weaken.weaken
      p.weaken.weaken i.weaken.weaken C.negTag.weaken.weaken (.bound 1) (.bound 0))
      (.neg (memPairFormula H.weaken.weaken (.bound 1) c.weaken.weaken))))

def implicationFormula {n : Nat} (C : Context (Project.Term n)) (p i c H : Project.Term n) : Project.Formula 1 n :=
  Project.Formula.existsMem i (Project.Formula.existsMem i.weaken
    (.conj (instructionAtFormula C.instructions.weaken.weaken C.pairs.weaken.weaken
      p.weaken.weaken i.weaken.weaken C.impTag.weaken.weaken (.bound 1) (.bound 0))
      (.imp (memPairFormula H.weaken.weaken (.bound 1) c.weaken.weaken)
        (memPairFormula H.weaken.weaken (.bound 0) c.weaken.weaken))))

def universalFormula {n : Nat} (C : Context (Project.Term n)) (p s i H : Project.Term n) : Project.Formula 1 n :=
  Project.Formula.existsMem i (Project.Formula.existsMem C.omega.weaken
    (Project.Formula.existsMem C.omega.weaken.weaken
      (.conj (instructionAtFormula C.instructions.weaken.weaken.weaken C.pairs.weaken.weaken.weaken
          p.weaken.weaken.weaken i.weaken.weaken.weaken C.allTag.weaken.weaken.weaken (.bound 1) (.bound 2))
        (.conj (graphFormula s.weaken.weaken.weaken (.bound 0) C.carrier.weaken.weaken.weaken)
          (.conj (.mem (.bound 1) (.bound 0))
            (Project.Formula.forallMem C.carrier.weaken.weaken.weaken
              (Project.Formula.existsMem C.assignments.weaken.weaken.weaken.weaken
                (.conj (updatedFormula (.bound 0) s.weaken.weaken.weaken.weaken.weaken (.bound 2)
                    C.carrier.weaken.weaken.weaken.weaken.weaken (.bound 3) (.bound 1))
                  (Project.Formula.existsMem C.columns.weaken.weaken.weaken.weaken.weaken
                    (.conj (codeFormula (.bound 0) p.weaken.weaken.weaken.weaken.weaken.weaken (.bound 1))
                      (memPairFormula H.weaken.weaken.weaken.weaken.weaken.weaken (.bound 5) (.bound 0))))))))))))

theorem atomicFormula_delta0 {n : Nat} (C : Context (Project.Term n)) (p s i : Project.Term n) :
    (atomicFormula C p s i).IsDelta0 :=
  .existsMem _ (.existsMem _ (.conj (instructionAtFormula_delta0 _ _ _ _ _ _ _) (memPairFormula_delta0 _ _ _)))

theorem negationFormula_delta0 {n : Nat} (C : Context (Project.Term n)) (p i c H : Project.Term n) :
    (negationFormula C p i c H).IsDelta0 :=
  .existsMem _ (.existsMem _ (.conj (instructionAtFormula_delta0 _ _ _ _ _ _ _) (.neg (memPairFormula_delta0 _ _ _))))

theorem implicationFormula_delta0 {n : Nat} (C : Context (Project.Term n)) (p i c H : Project.Term n) :
    (implicationFormula C p i c H).IsDelta0 :=
  .existsMem _ (.existsMem _ (.conj (instructionAtFormula_delta0 _ _ _ _ _ _ _)
    (.imp (memPairFormula_delta0 _ _ _) (memPairFormula_delta0 _ _ _))))

theorem universalFormula_delta0 {n : Nat} (C : Context (Project.Term n)) (p s i H : Project.Term n) :
    (universalFormula C p s i H).IsDelta0 :=
  .existsMem _ (.existsMem _ (.existsMem _ (.conj (instructionAtFormula_delta0 _ _ _ _ _ _ _)
    (.conj (graphFormula_delta0 _ _ _) (.conj (.mem _ _)
      (.forallMem _ (.existsMem _ (.conj (updatedFormula_delta0 _ _ _ _ _ _)
        (.existsMem _ (.conj (codeFormula_delta0 _ _ _) (memPairFormula_delta0 _ _ _)))))))))))

theorem atomicFormula_iff {M : SetTheory.Structure.{u}} (he : Extensional M) {n : Nat}
    (env : Env M n) (C : Context (Project.Term n)) (p s i : Project.Term n) :
    Project.Formula.satisfies env (atomicFormula C p s i) ↔
      AtomicCase M (C.eval env) (p.eval env) (s.eval env) (i.eval env) := by
  simp only [atomicFormula, Project.Formula.satisfies_existsMem_iff,
    Project.Formula.satisfies_conj_iff, instructionAtFormula_iff he,
    memPairFormula_iff he, Definitional.Term.eval_weaken]
  rfl

theorem negationFormula_iff {M : SetTheory.Structure.{u}} (he : Extensional M) {n : Nat}
    (env : Env M n) (C : Context (Project.Term n)) (p i c H : Project.Term n) :
    Project.Formula.satisfies env (negationFormula C p i c H) ↔
      NegationCase M (C.eval env) (p.eval env) (i.eval env) (c.eval env) (H.eval env) := by
  simp only [negationFormula, Project.Formula.satisfies_existsMem_iff,
    Project.Formula.satisfies_conj_iff, instructionAtFormula_iff he,
    Project.Formula.satisfies_neg_iff, memPairFormula_iff he, Definitional.Term.eval_weaken]
  rfl

theorem implicationFormula_iff {M : SetTheory.Structure.{u}} (he : Extensional M) {n : Nat}
    (env : Env M n) (C : Context (Project.Term n)) (p i c H : Project.Term n) :
    Project.Formula.satisfies env (implicationFormula C p i c H) ↔
      ImplicationCase M (C.eval env) (p.eval env) (i.eval env) (c.eval env) (H.eval env) := by
  simp only [implicationFormula, Project.Formula.satisfies_existsMem_iff,
    Project.Formula.satisfies_conj_iff, instructionAtFormula_iff he,
    Project.Formula.satisfies_imp_iff, memPairFormula_iff he, Definitional.Term.eval_weaken]
  rfl

theorem universalFormula_iff {M : SetTheory.Structure.{u}} (he : Extensional M) {n : Nat}
    (env : Env M n) (C : Context (Project.Term n)) (p s i H : Project.Term n) :
    Project.Formula.satisfies env (universalFormula C p s i H) ↔
      UniversalCase M (C.eval env) (p.eval env) (s.eval env) (i.eval env) (H.eval env) := by
  simp only [universalFormula, Project.Formula.satisfies_existsMem_iff,
    Project.Formula.satisfies_conj_iff, instructionAtFormula_iff he,
    Project.Formula.satisfies_forallMem_iff, graphFormula_iff he, updatedFormula_iff he,
    Project.Formula.satisfies_mem_iff, codeFormula_iff he, memPairFormula_iff he,
    Definitional.Term.eval_weaken]
  rfl

end KP1Y.Satisfaction
