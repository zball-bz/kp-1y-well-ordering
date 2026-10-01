import KP1Y.ProgramElementarity
import KP1Y.AssignmentCarriers

/-! Tarski–Vaught 论证中的节点归纳性质是实际对象公式。 -/
namespace KP1Y.Satisfaction
open YesMetaZFC YesMetaZFC.SetTheory YesMetaZFC.SetTheory.Definitional
open KP1Y.Kuratowski KP1Y.Functions KP1Y.Assignments
universe u v

def EvaluationData.map {α : Type u} {β : Type v} (I : EvaluationData α) (f : α → β) : EvaluationData β :=
  ⟨f I.carrier,f I.assignments,f I.columns,f I.atomic,f I.table⟩

def EvaluationData.eval {M : SetTheory.Structure.{u}} {n : Nat}
    (I : EvaluationData (Project.Term n)) (env : Env M n) : EvaluationData M.Domain := I.map (fun t => t.eval env)

theorem EvaluationData.eval_context {M : SetTheory.Structure.{u}} {n : Nat}
    (env : Env M n) (I : EvaluationData (Project.Term n)) (C : Context (Project.Term n)) :
    (I.context C).eval env = (I.eval env).context (C.eval env) := rfl

def AtomicAgreement (M : SetTheory.Structure.{u}) (C : Context M.Domain) (D : RelationalData M.Domain)
    (small large : EvaluationData M.Domain) : Prop :=
  ∀ a bound, ScopedAtom M D a bound → M.mem bound C.omega → ∀ s, Graph M s bound small.carrier →
    (MemPair M small.atomic a s ↔ MemPair M large.atomic a s)

def CounterWitnessClosed (M : SetTheory.Structure.{u}) (C : Context M.Domain) (D : RelationalData M.Domain)
    (small large : EvaluationData M.Domain) : Prop :=
  ∀ p length bound, WellFormedProgram M C D p length bound → ∀ j, M.mem j length →
    ∀ s, Graph M s bound small.carrier → ∀ v, M.mem v bound →
      (∃ x, M.mem x large.carrier ∧ ∃ t, Updated M t s bound large.carrier v x ∧
        ¬NodeTrue M (large.context C) large.table p j t) →
      ∃ x, M.mem x small.carrier ∧ ∃ t, Updated M t s bound small.carrier v x ∧
        ¬NodeTrue M (large.context C) large.table p j t

def NodeElementary (M : SetTheory.Structure.{u}) (C : Context M.Domain) (small large : EvaluationData M.Domain)
    (p i bound : M.Domain) : Prop :=
  ∀ s, M.mem s small.assignments → Graph M s bound small.carrier →
    (NodeTrue M (small.context C) small.table p i s ↔ NodeTrue M (large.context C) large.table p i s)

def nodeElementaryFormula {n : Nat} (C : Context (Project.Term n)) (small large : EvaluationData (Project.Term n))
    (p i bound : Project.Term n) : Project.Formula 1 n :=
  Project.Formula.forallMem small.assignments (.imp (graphFormula (.bound 0) bound.weaken small.carrier.weaken)
    (.iff (nodeTrueFormula (small.context C).weaken small.table.weaken p.weaken i.weaken (.bound 0))
      (nodeTrueFormula (large.context C).weaken large.table.weaken p.weaken i.weaken (.bound 0))))

theorem nodeElementaryFormula_iff {M : SetTheory.Structure.{u}} (he : Extensional M) {n : Nat}
    (env : Env M n) (C : Context (Project.Term n)) (small large : EvaluationData (Project.Term n)) (p i bound : Project.Term n) :
    Project.Formula.satisfies env (nodeElementaryFormula C small large p i bound) ↔
      NodeElementary M (C.eval env) (small.eval env) (large.eval env) (p.eval env) (i.eval env) (bound.eval env) := by
  simp only [nodeElementaryFormula, Project.Formula.satisfies_forallMem_iff,
    Project.Formula.satisfies_imp_iff, Project.Formula.satisfies_iff_iff, graphFormula_iff he,
    nodeTrueFormula_iff he, Context.eval_weaken, EvaluationData.eval_context, Definitional.Term.eval_weaken]
  rfl

def elementaryEnv {M : SetTheory.Structure.{u}} (C : Context M.Domain) (small large : EvaluationData M.Domain) : Env M 23 where
  bound k := match k.val with
    | 0 => C.omega | 1 => C.carrier | 2 => C.operands | 3 => C.pairs
    | 4 => C.instructions | 5 => C.programs | 6 => C.assignments | 7 => C.columns
    | 8 => C.atomic | 9 => C.atomTag | 10 => C.negTag | 11 => C.impTag | 12 => C.allTag
    | 13 => small.carrier | 14 => small.assignments | 15 => small.columns | 16 => small.atomic | 17 => small.table
    | 18 => large.carrier | 19 => large.assignments | 20 => large.columns | 21 => large.atomic | _ => large.table
  free _ := C.omega

private def elementaryContext : Context (Project.Term 27) :=
  ⟨.bound 4,.bound 5,.bound 6,.bound 7,.bound 8,.bound 9,.bound 10,
    .bound 11,.bound 12,.bound 13,.bound 14,.bound 15,.bound 16⟩
private def elementarySmall : EvaluationData (Project.Term 27) :=
  ⟨.bound 17,.bound 18,.bound 19,.bound 20,.bound 21⟩
private def elementaryLarge : EvaluationData (Project.Term 27) :=
  ⟨.bound 22,.bound 23,.bound 24,.bound 25,.bound 26⟩

def elementaryGuard : Project.UnarySchema 26 where
  body := .imp (.mem (.bound 0) (.bound 2))
    (nodeElementaryFormula elementaryContext elementarySmall elementaryLarge (.bound 3) (.bound 0) (.bound 1))
  freeClosed := by
    simp [nodeElementaryFormula, nodeTrueFormula, graphFormula, memPairFormula, codeFormula, pairFormula,
      Context.weaken, Context.map, Context.withInterpretation, EvaluationData.context,
      elementaryContext, elementarySmall, elementaryLarge, Project.Formula.existsMem,
      Project.Formula.forallMem, Definitional.Formula.FreeClosed]

theorem elementaryGuard_iff {M : SetTheory.Structure.{u}} (he : Extensional M)
    (C : Context M.Domain) (small large : EvaluationData M.Domain) (p length bound i : M.Domain) :
    Project.Formula.satisfies (((((elementaryEnv C small large).push p).push length).push bound).push i) elementaryGuard.body ↔
      (M.mem i length → NodeElementary M C small large p i bound) := by
  simp only [elementaryGuard, Project.Formula.satisfies_imp_iff, Project.Formula.satisfies_mem_iff,
    nodeElementaryFormula_iff he]
  rfl

end KP1Y.Satisfaction
