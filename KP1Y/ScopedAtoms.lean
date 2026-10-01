import KP1Y.RelationalSpaces

/-! 原子公式的合法性：关系符号、元数和每个变量号都有实际内部集合界。 -/
namespace KP1Y.Satisfaction
open YesMetaZFC YesMetaZFC.SetTheory YesMetaZFC.SetTheory.Definitional
open KP1Y.Kuratowski KP1Y.Functions KP1Y.Assignments
universe u

def RelationalData.weaken {n : Nat} (D : RelationalData (Project.Term n)) : RelationalData (Project.Term (n+1)) :=
  D.map (fun t => t.weaken)

theorem RelationalData.eval_weaken {M : SetTheory.Structure.{u}} {n : Nat}
    (D : RelationalData (Project.Term n)) (env : Env M n) (x : M.Domain) :
    D.weaken.eval (env.push x) = D.eval env := by
  cases D
  simp [RelationalData.weaken,RelationalData.eval,RelationalData.map,Definitional.Term.eval_weaken]

def ScopedAtom (M : SetTheory.Structure.{u}) (D : RelationalData M.Domain) (a bound : M.Domain) : Prop :=
  ∃ r, M.mem r D.symbols ∧ ∃ vars, M.mem vars D.variables ∧ Codes M a r vars ∧
    ∃ n, M.mem n D.omega ∧ MemPair M D.arity r n ∧ Graph M vars n bound

def scopedAtomFormula {d : Nat} (D : RelationalData (Project.Term d)) (a bound : Project.Term d) : Project.Formula 1 d :=
  Project.Formula.existsMem D.symbols (Project.Formula.existsMem D.variables.weaken
    (.conj (codeFormula a.weaken.weaken (.bound 1) (.bound 0))
      (Project.Formula.existsMem D.omega.weaken.weaken
        (.conj (memPairFormula D.arity.weaken.weaken.weaken (.bound 2) (.bound 0))
          (graphFormula (.bound 1) (.bound 0) bound.weaken.weaken.weaken)))))

theorem scopedAtomFormula_delta0 {d : Nat} (D : RelationalData (Project.Term d)) (a bound : Project.Term d) :
    (scopedAtomFormula D a bound).IsDelta0 :=
  .existsMem _ (.existsMem _ (.conj (codeFormula_delta0 _ _ _)
    (.existsMem _ (.conj (memPairFormula_delta0 _ _ _) (graphFormula_delta0 _ _ _)))))

theorem scopedAtomFormula_iff {M : SetTheory.Structure.{u}} (he : Extensional M) {d : Nat}
    (env : Env M d) (D : RelationalData (Project.Term d)) (a bound : Project.Term d) :
    Project.Formula.satisfies env (scopedAtomFormula D a bound) ↔
      ScopedAtom M (D.eval env) (a.eval env) (bound.eval env) := by
  simp only [scopedAtomFormula, Project.Formula.satisfies_existsMem_iff,
    Project.Formula.satisfies_conj_iff, codeFormula_iff he, memPairFormula_iff he,
    graphFormula_iff he, Definitional.Term.eval_weaken]
  rfl

theorem ScopedAtom.code_mem {M : SetTheory.Structure.{u}} {D : RelationalData M.Domain}
    (hD : DataSpaces M D) {a bound : M.Domain} (h : ScopedAtom M D a bound) : M.mem a D.codes := by
  obtain ⟨r,hr,vars,hVars,hCode,_⟩ := h
  exact (hD.codes a).mpr ⟨r,hr,vars,hVars,hCode⟩

theorem ScopedAtom.mono_scope {M : SetTheory.Structure.{u}} {D : RelationalData M.Domain}
    {a b c : M.Domain} (h : ScopedAtom M D a b) (hbc : M.MemberSubset b c) : ScopedAtom M D a c := by
  obtain ⟨r,hr,vars,hVars,hCode,n,hn,hArity,hGraph⟩ := h
  exact ⟨r,hr,vars,hVars,hCode,n,hn,hArity,hGraph.mono_values hbc⟩

theorem scoped_atom_evaluable_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {D : RelationalData M.Domain} {a bound s : M.Domain} (h : ScopedAtom M D a bound)
    (hS : Graph M s bound D.carrier) :
    ∃ r vars n t, M.mem r D.symbols ∧ Codes M a r vars ∧ M.mem n D.omega ∧
      MemPair M D.arity r n ∧ TupleValue M t vars s n bound D.carrier := by
  obtain ⟨r,hr,vars,_,hCode,n,hn,hArity,hVars⟩ := h
  obtain ⟨t,hValue⟩ := tuple_value_exists_d hM hVars hS
  exact ⟨r,vars,n,t,hr,hCode,hn,hArity,hValue⟩

theorem scoped_atom_correct_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {D : RelationalData M.Domain} (hD : DataSpaces M D) {Atom : M.Domain} (hAtom : AtomicTable M D Atom)
    {a bound s : M.Domain} (h : ScopedAtom M D a bound) (hb : M.mem bound D.omega)
    (hS : Graph M s bound D.carrier) :
    ∃ r vars n t, M.mem r D.symbols ∧ Codes M a r vars ∧ M.mem n D.omega ∧
      MemPair M D.arity r n ∧ TupleValue M t vars s n bound D.carrier ∧
      (MemPair M Atom a s ↔ MemPair M D.interpretation r t) := by
  obtain ⟨r,vars,n,t,hr,hCode,hn,hArity,hValue⟩ := scoped_atom_evaluable_d hM h hS
  exact ⟨r,vars,n,t,hr,hCode,hn,hArity,hValue,atomic_table_correct hM hD hAtom hr hCode hn hb hArity hValue⟩

end KP1Y.Satisfaction
