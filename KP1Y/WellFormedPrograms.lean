import KP1Y.ScopedAtoms
import KP1Y.SatisfactionTruth

/-! 有限公式程序的实际 Δ₀ 合法性检查，不把原始程序的默认求值当成公式满意度。 -/
namespace KP1Y.Satisfaction
open YesMetaZFC YesMetaZFC.SetTheory YesMetaZFC.SetTheory.Definitional
open KP1Y.Kuratowski KP1Y.Functions
universe u

def WellFormedAt (M : SetTheory.Structure.{u}) (C : Context M.Domain) (D : RelationalData M.Domain)
    (p i bound : M.Domain) : Prop :=
  (∃ a, M.mem a D.codes ∧ ∃ r, M.mem r C.operands ∧
    InstructionAt M C.instructions C.pairs p i C.atomTag a r ∧ ScopedAtom M D a bound) ∨
  (∃ j, M.mem j i ∧ ∃ r, M.mem r C.operands ∧ InstructionAt M C.instructions C.pairs p i C.negTag j r) ∨
  (∃ j, M.mem j i ∧ ∃ k, M.mem k i ∧ InstructionAt M C.instructions C.pairs p i C.impTag j k) ∨
  (∃ j, M.mem j i ∧ ∃ v, M.mem v bound ∧ InstructionAt M C.instructions C.pairs p i C.allTag v j)

def wellFormedAtFormula {n : Nat} (C : Context (Project.Term n)) (D : RelationalData (Project.Term n))
    (p i bound : Project.Term n) : Project.Formula 1 n :=
  .disj
    (Project.Formula.existsMem D.codes (Project.Formula.existsMem C.operands.weaken
      (.conj (instructionAtFormula C.instructions.weaken.weaken C.pairs.weaken.weaken
          p.weaken.weaken i.weaken.weaken C.atomTag.weaken.weaken (.bound 1) (.bound 0))
        (scopedAtomFormula D.weaken.weaken (.bound 1) bound.weaken.weaken))))
    (.disj
      (Project.Formula.existsMem i (Project.Formula.existsMem C.operands.weaken
        (instructionAtFormula C.instructions.weaken.weaken C.pairs.weaken.weaken
          p.weaken.weaken i.weaken.weaken C.negTag.weaken.weaken (.bound 1) (.bound 0))))
      (.disj
        (Project.Formula.existsMem i (Project.Formula.existsMem i.weaken
          (instructionAtFormula C.instructions.weaken.weaken C.pairs.weaken.weaken
            p.weaken.weaken i.weaken.weaken C.impTag.weaken.weaken (.bound 1) (.bound 0))))
        (Project.Formula.existsMem i (Project.Formula.existsMem bound.weaken
          (instructionAtFormula C.instructions.weaken.weaken C.pairs.weaken.weaken
            p.weaken.weaken i.weaken.weaken C.allTag.weaken.weaken (.bound 0) (.bound 1))))))

theorem wellFormedAtFormula_delta0 {n : Nat} (C : Context (Project.Term n)) (D : RelationalData (Project.Term n))
    (p i bound : Project.Term n) : (wellFormedAtFormula C D p i bound).IsDelta0 :=
  .disj (.existsMem _ (.existsMem _ (.conj (instructionAtFormula_delta0 _ _ _ _ _ _ _) (scopedAtomFormula_delta0 _ _ _))))
    (.disj (.existsMem _ (.existsMem _ (instructionAtFormula_delta0 _ _ _ _ _ _ _)))
      (.disj (.existsMem _ (.existsMem _ (instructionAtFormula_delta0 _ _ _ _ _ _ _)))
        (.existsMem _ (.existsMem _ (instructionAtFormula_delta0 _ _ _ _ _ _ _)))))

theorem wellFormedAtFormula_iff {M : SetTheory.Structure.{u}} (he : Extensional M) {n : Nat}
    (env : Env M n) (C : Context (Project.Term n)) (D : RelationalData (Project.Term n)) (p i bound : Project.Term n) :
    Project.Formula.satisfies env (wellFormedAtFormula C D p i bound) ↔
      WellFormedAt M (C.eval env) (D.eval env) (p.eval env) (i.eval env) (bound.eval env) := by
  simp only [wellFormedAtFormula, Project.Formula.satisfies_disj_iff,
    Project.Formula.satisfies_existsMem_iff, Project.Formula.satisfies_conj_iff,
    instructionAtFormula_iff he, scopedAtomFormula_iff he,
    RelationalData.eval_weaken, Definitional.Term.eval_weaken]
  rfl

structure WellFormedProgram (M : SetTheory.Structure.{u}) (C : Context M.Domain) (D : RelationalData M.Domain)
    (p length bound : M.Domain) : Prop where
  graph : Graph M p length C.instructions
  length_nat : M.mem length C.omega
  bound_nat : M.mem bound C.omega
  nodes : ∀ i, M.mem i length → WellFormedAt M C D p i bound

def wellFormedProgramFormula {n : Nat} (C : Context (Project.Term n)) (D : RelationalData (Project.Term n))
    (p length bound : Project.Term n) : Project.Formula 1 n :=
  .conj (graphFormula p length C.instructions) (.conj (.mem length C.omega) (.conj (.mem bound C.omega)
    (Project.Formula.forallMem length (wellFormedAtFormula C.weaken D.weaken p.weaken (.bound 0) bound.weaken))))

theorem wellFormedProgramFormula_delta0 {n : Nat} (C : Context (Project.Term n)) (D : RelationalData (Project.Term n))
    (p length bound : Project.Term n) : (wellFormedProgramFormula C D p length bound).IsDelta0 :=
  .conj (graphFormula_delta0 _ _ _) (.conj (.mem _ _) (.conj (.mem _ _)
    (.forallMem _ (wellFormedAtFormula_delta0 _ _ _ _ _))))

theorem wellFormedProgramFormula_iff {M : SetTheory.Structure.{u}} (he : Extensional M) {n : Nat}
    (env : Env M n) (C : Context (Project.Term n)) (D : RelationalData (Project.Term n)) (p length bound : Project.Term n) :
    Project.Formula.satisfies env (wellFormedProgramFormula C D p length bound) ↔
      WellFormedProgram M (C.eval env) (D.eval env) (p.eval env) (length.eval env) (bound.eval env) := by
  simp only [wellFormedProgramFormula, Project.Formula.satisfies_conj_iff, graphFormula_iff he,
    Project.Formula.satisfies_mem_iff, Project.Formula.satisfies_forallMem_iff,
    wellFormedAtFormula_iff he, Context.eval_weaken, RelationalData.eval_weaken, Definitional.Term.eval_weaken]
  exact ⟨fun h => ⟨h.1,h.2.1,h.2.2.1,h.2.2.2⟩,fun h => ⟨h.graph,h.length_nat,h.bound_nat,h.nodes⟩⟩

def FormulaProgram (M : SetTheory.Structure.{u}) (C : Context M.Domain) (D : RelationalData M.Domain)
    (p length bound : M.Domain) : Prop :=
  WellFormedProgram M C D p length bound ∧ ∃ i, M.mem i length

def formulaProgramFormula {n : Nat} (C : Context (Project.Term n)) (D : RelationalData (Project.Term n))
    (p length bound : Project.Term n) : Project.Formula 1 n :=
  .conj (wellFormedProgramFormula C D p length bound) (Project.Formula.existsMem length .truth)

theorem formulaProgramFormula_delta0 {n : Nat} (C : Context (Project.Term n)) (D : RelationalData (Project.Term n))
    (p length bound : Project.Term n) : (formulaProgramFormula C D p length bound).IsDelta0 :=
  .conj (wellFormedProgramFormula_delta0 _ _ _ _ _) (.existsMem _ .truth)

theorem formulaProgramFormula_iff {M : SetTheory.Structure.{u}} (he : Extensional M) {n : Nat}
    (env : Env M n) (C : Context (Project.Term n)) (D : RelationalData (Project.Term n)) (p length bound : Project.Term n) :
    Project.Formula.satisfies env (formulaProgramFormula C D p length bound) ↔
      FormulaProgram M (C.eval env) (D.eval env) (p.eval env) (length.eval env) (bound.eval env) := by
  simp only [formulaProgramFormula, Project.Formula.satisfies_conj_iff,
    wellFormedProgramFormula_iff he, Project.Formula.satisfies_existsMem_iff, Project.Formula.satisfies_truth_iff,
    and_true]
  rfl

theorem wellFormedAt_transport {M : SetTheory.Structure.{u}} {C : Context M.Domain} {D : RelationalData M.Domain}
    {p q i bound : M.Domain}
    (hRows : ∀ instr, M.mem instr C.instructions → (MemPair M p i instr ↔ MemPair M q i instr)) :
    WellFormedAt M C D p i bound ↔ WellFormedAt M C D q i bound := by
  simp only [WellFormedAt, instruction_transport hRows]

theorem WellFormedAt.mono_scope {M : SetTheory.Structure.{u}} {C : Context M.Domain} {D : RelationalData M.Domain}
    {p i b b' : M.Domain} (h : WellFormedAt M C D p i b) (hbb' : M.MemberSubset b b') :
    WellFormedAt M C D p i b' := by
  rcases h with ⟨a,ha,r,hr,hInstr,hScope⟩ | hNeg | hImp | ⟨j,hj,v,hv,hInstr⟩
  · exact Or.inl ⟨a,ha,r,hr,hInstr,hScope.mono_scope hbb'⟩
  · exact Or.inr (Or.inl hNeg)
  · exact Or.inr (Or.inr (Or.inl hImp))
  · exact Or.inr (Or.inr (Or.inr ⟨j,hj,v,hbb' v hv,hInstr⟩))

theorem WellFormedProgram.mono_scope {M : SetTheory.Structure.{u}} {C : Context M.Domain} {D : RelationalData M.Domain}
    {p length b b' : M.Domain} (h : WellFormedProgram M C D p length b)
    (hb' : M.mem b' C.omega) (hbb' : M.MemberSubset b b') : WellFormedProgram M C D p length b' :=
  ⟨h.graph,h.length_nat,hb',fun i hi => (h.nodes i hi).mono_scope hbb'⟩

end KP1Y.Satisfaction
