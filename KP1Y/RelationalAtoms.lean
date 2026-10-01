import KP1Y.AssignmentTuple

/-! 从实际关系解释集合构造原子真值表，包含参数元组的内部求值。 -/
namespace KP1Y.Satisfaction
open YesMetaZFC YesMetaZFC.SetTheory YesMetaZFC.SetTheory.Definitional
open KP1Y.Kuratowski KP1Y.Functions KP1Y.Assignments
universe u v

structure RelationalData (α : Type u) where
  omega : α
  carrier : α
  symbols : α
  arity : α
  interpretation : α
  variables : α
  values : α
  codes : α

def RelationalData.map {α : Type u} {β : Type v} (D : RelationalData α) (f : α → β) : RelationalData β :=
  ⟨f D.omega,f D.carrier,f D.symbols,f D.arity,f D.interpretation,f D.variables,f D.values,f D.codes⟩

def RelationalData.eval {M : SetTheory.Structure.{u}} {n : Nat}
    (D : RelationalData (Project.Term n)) (env : Env M n) : RelationalData M.Domain :=
  D.map (fun t => t.eval env)

def AtomValue (M : SetTheory.Structure.{u}) (D : RelationalData M.Domain) (a s : M.Domain) : Prop :=
  ∃ r, M.mem r D.symbols ∧ ∃ vars, M.mem vars D.variables ∧ Codes M a r vars ∧
    ∃ n, M.mem n D.omega ∧ ∃ m, M.mem m D.omega ∧ MemPair M D.arity r n ∧
      ∃ t, M.mem t D.values ∧ TupleValue M t vars s n m D.carrier ∧ MemPair M D.interpretation r t

def atomValueFormula {d : Nat} (D : RelationalData (Project.Term d)) (a s : Project.Term d) : Project.Formula 1 d :=
  Project.Formula.existsMem D.symbols (Project.Formula.existsMem D.variables.weaken
    (.conj (codeFormula a.weaken.weaken (.bound 1) (.bound 0))
      (Project.Formula.existsMem D.omega.weaken.weaken (Project.Formula.existsMem D.omega.weaken.weaken.weaken
        (.conj (memPairFormula D.arity.weaken.weaken.weaken.weaken (.bound 3) (.bound 1))
          (Project.Formula.existsMem D.values.weaken.weaken.weaken.weaken
            (.conj (tupleValueFormula (.bound 0) (.bound 3) s.weaken.weaken.weaken.weaken.weaken
                (.bound 2) (.bound 1) D.carrier.weaken.weaken.weaken.weaken.weaken)
              (memPairFormula D.interpretation.weaken.weaken.weaken.weaken.weaken (.bound 4) (.bound 0)))))))))

theorem atomValueFormula_delta0 {d : Nat} (D : RelationalData (Project.Term d)) (a s : Project.Term d) :
    (atomValueFormula D a s).IsDelta0 :=
  .existsMem _ (.existsMem _ (.conj (codeFormula_delta0 _ _ _)
    (.existsMem _ (.existsMem _ (.conj (memPairFormula_delta0 _ _ _)
      (.existsMem _ (.conj (tupleValueFormula_delta0 _ _ _ _ _ _) (memPairFormula_delta0 _ _ _))))))))

theorem atomValueFormula_iff {M : SetTheory.Structure.{u}} (he : Extensional M) {d : Nat}
    (env : Env M d) (D : RelationalData (Project.Term d)) (a s : Project.Term d) :
    Project.Formula.satisfies env (atomValueFormula D a s) ↔
      AtomValue M (D.eval env) (a.eval env) (s.eval env) := by
  simp only [atomValueFormula, Project.Formula.satisfies_existsMem_iff,
    Project.Formula.satisfies_conj_iff, codeFormula_iff he, memPairFormula_iff he,
    tupleValueFormula_iff he, Definitional.Term.eval_weaken]
  rfl

private def atomParameters : RelationalData (Project.Term 10) :=
  ⟨.bound 2,.bound 3,.bound 4,.bound 5,.bound 6,.bound 7,.bound 8,.bound 9⟩

private def atomSchema : Project.Delta0BinarySchema 8 where
  body := atomValueFormula atomParameters (.bound 1) (.bound 0)
  freeClosed := by
    simp [atomValueFormula, atomParameters, tupleValueFormula, graphFormula,
      memPairFormula, codeFormula, pairFormula, Project.Formula.existsMem,
      Project.Formula.forallMem, Definitional.Formula.FreeClosed]
  delta0 := atomValueFormula_delta0 _ _ _

private def atomEnv {M : SetTheory.Structure.{u}} (D : RelationalData M.Domain) : Env M 8 where
  bound k := match k.val with
    | 0 => D.omega | 1 => D.carrier | 2 => D.symbols | 3 => D.arity
    | 4 => D.interpretation | 5 => D.variables | 6 => D.values | _ => D.codes
  free _ := D.omega

private theorem atomSchema_iff {M : SetTheory.Structure.{u}} (he : Extensional M)
    (D : RelationalData M.Domain) (a s : M.Domain) :
    Project.Formula.satisfies (((atomEnv D).push a).push s) atomSchema.body ↔ AtomValue M D a s := by
  simp only [atomSchema, atomValueFormula_iff he]
  rfl

structure AtomicTable (M : SetTheory.Structure.{u}) (D : RelationalData M.Domain) (Atom : M.Domain) : Prop where
  support : ∀ q, M.mem q Atom → ∃ a, M.mem a D.codes ∧ ∃ s, M.mem s D.values ∧ Codes M q a s
  rows : ∀ a s, MemPair M Atom a s ↔ M.mem a D.codes ∧ M.mem s D.values ∧ AtomValue M D a s

theorem atomic_table_exists_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    (D : RelationalData M.Domain) : ∃ Atom, AtomicTable M D Atom := by
  obtain ⟨Atom,hSupport,hRows⟩ := relation_comprehension_d hM atomSchema (atomEnv D) D.codes D.values
  refine ⟨Atom,hSupport,?_⟩
  intro a s
  simpa only [atomSchema_iff hM.1] using hRows a s

end KP1Y.Satisfaction
