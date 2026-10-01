import KP1Y.TypedSatisfactionSentence
import KP1Y.CompiledExtension

/-! 固定语法，改变载域和关系解释；为同一程序跨结构的编译正确性准备对象公式。 -/
namespace KP1Y.Satisfaction
open YesMetaZFC YesMetaZFC.SetTheory YesMetaZFC.SetTheory.Definitional
open KP1Y.Kuratowski KP1Y.Functions
universe u

def Context.withInterpretation {α : Type u} (C : Context α) (A assignments columns atomic : α) : Context α :=
  { C with carrier := A, assignments := assignments, columns := columns, atomic := atomic }

theorem Context.eval_withInterpretation {M : SetTheory.Structure.{u}} {n : Nat}
    (env : Env M n) (C : Context (Project.Term n)) (A assignments columns atomic : Project.Term n) :
    (C.withInterpretation A assignments columns atomic).eval env =
      (C.eval env).withInterpretation (A.eval env) (assignments.eval env) (columns.eval env) (atomic.eval env) := rfl

theorem wellFormedProgram_withInterpretation {M : SetTheory.Structure.{u}} {C : Context M.Domain}
    {D : RelationalData M.Domain} {p length bound A assignments columns atomic : M.Domain} :
    WellFormedProgram M (C.withInterpretation A assignments columns atomic) D p length bound ↔
      WellFormedProgram M C D p length bound :=
  ⟨fun h => ⟨h.graph,h.length_nat,h.bound_nat,h.nodes⟩,
    fun h => ⟨h.graph,h.length_nat,h.bound_nat,h.nodes⟩⟩

theorem CompiledExtension.withInterpretation {M : SetTheory.Structure.{u}} {C : Context M.Domain}
    {D : RelationalData M.Domain} {p n bound q length head : M.Domain}
    (h : CompiledExtension M C D p n bound q length head) (A assignments columns atomic : M.Domain) :
    CompiledExtension M (C.withInterpretation A assignments columns atomic) D p n bound q length head :=
  ⟨h.successor,h.head_nat,wellFormedProgram_withInterpretation.mpr h.wellFormed,h.prefixGraph⟩

structure EvaluationInstance (M : SetTheory.Structure.{u}) (C : Context M.Domain)
    (A assignments columns atomic H : M.Domain) : Prop where
  assignments_exact : ∀ s, M.mem s assignments ↔ ∃ n, M.mem n C.omega ∧ Graph M s n A
  columns_exact : IsProduct M columns C.programs assignments
  table : Evaluation M (C.withInterpretation A assignments columns atomic) H

theorem EvaluationInstance.contextSpaces {M : SetTheory.Structure.{u}} {C : Context M.Domain}
    (hC : ContextSpaces M C) {A assignments columns atomic H : M.Domain}
    (h : EvaluationInstance M C A assignments columns atomic H) :
    ContextSpaces M (C.withInterpretation A assignments columns atomic) :=
  ⟨hC.omega,hC.distinct,hC.tag_naturals,hC.omega_operands,hC.pairs,hC.instructions,hC.programs,
    h.assignments_exact,h.columns_exact⟩

def productExactFormula {n : Nat} (P X Y : Project.Term n) : Project.Formula 1 n :=
  .forallE (.iff (.mem (.bound 0) P.weaken)
    (Project.Formula.existsMem X.weaken (Project.Formula.existsMem Y.weaken.weaken
      (codeFormula (.bound 2) (.bound 1) (.bound 0)))))

theorem productExactFormula_iff {M : SetTheory.Structure.{u}} (he : Extensional M) {n : Nat}
    (env : Env M n) (P X Y : Project.Term n) :
    Project.Formula.satisfies env (productExactFormula P X Y) ↔ IsProduct M (P.eval env) (X.eval env) (Y.eval env) := by
  simp only [productExactFormula, Project.Formula.satisfies_forall_iff,
    Project.Formula.satisfies_iff_iff, Project.Formula.satisfies_mem_iff,
    Project.Formula.satisfies_existsMem_iff, codeFormula_iff he, Definitional.Term.eval_weaken]
  rfl

def evaluationInstanceFormula {n : Nat} (C : Context (Project.Term n))
    (A assignments columns atomic H : Project.Term n) : Project.Formula 1 n :=
  .conj (KP1Y.Sequences.finiteSequenceSpaceFormula assignments C.omega A)
    (.conj (productExactFormula columns C.programs assignments)
      (evaluationFormula (C.withInterpretation A assignments columns atomic) H))

theorem evaluationInstanceFormula_iff {M : SetTheory.Structure.{u}} (he : Extensional M) {n : Nat}
    (env : Env M n) (C : Context (Project.Term n)) (A assignments columns atomic H : Project.Term n) :
    Project.Formula.satisfies env (evaluationInstanceFormula C A assignments columns atomic H) ↔
      EvaluationInstance M (C.eval env) (A.eval env) (assignments.eval env) (columns.eval env) (atomic.eval env) (H.eval env) := by
  simp only [evaluationInstanceFormula, Project.Formula.satisfies_conj_iff,
    KP1Y.Sequences.finiteSequenceSpaceFormula_iff he, productExactFormula_iff he,
    evaluationFormula_iff he, Context.eval_withInterpretation]
  exact ⟨fun h => ⟨h.1,h.2.1,h.2.2⟩,fun h => ⟨h.assignments_exact,h.columns_exact,h.table⟩⟩

theorem evaluation_instance_exists_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : Context M.Domain} (hC : ContextSpaces M C) (A atomic : M.Domain) :
    ∃ assignments columns H, EvaluationInstance M C A assignments columns atomic H := by
  obtain ⟨assignments,hAssignments⟩ := KP1Y.Sequences.finite_sequences_exist_d hM hC.omega A
  obtain ⟨columns,hColumns⟩ := product_exists hM C.programs assignments
  obtain ⟨H,hH⟩ := evaluation_exists_d hM (C.withInterpretation A assignments columns atomic) hC.omega
  exact ⟨assignments,columns,H,hAssignments,hColumns,hH⟩

end KP1Y.Satisfaction
