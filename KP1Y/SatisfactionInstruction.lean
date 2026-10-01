import KP1Y.AssignmentUpdate

/-! 内部公式程序的指令：操作码和两个字段均以实际 Kuratowski 对编码。 -/
namespace KP1Y.Satisfaction
open YesMetaZFC YesMetaZFC.SetTheory YesMetaZFC.SetTheory.Definitional
open KP1Y.Kuratowski KP1Y.Functions
universe u v

/-- 递归使用的全部集合界和四个操作码。各字段的构造义务在具体实例中证明。 -/
structure Context (α : Type u) where
  omega : α
  carrier : α
  operands : α
  pairs : α
  instructions : α
  programs : α
  assignments : α
  columns : α
  atomic : α
  atomTag : α
  negTag : α
  impTag : α
  allTag : α

def Context.map {α : Type u} {β : Type v} (C : Context α) (f : α → β) : Context β :=
  ⟨f C.omega,f C.carrier,f C.operands,f C.pairs,f C.instructions,f C.programs,
    f C.assignments,f C.columns,f C.atomic,f C.atomTag,f C.negTag,f C.impTag,f C.allTag⟩

def Context.weaken {n : Nat} (C : Context (Project.Term n)) : Context (Project.Term (n+1)) :=
  C.map (fun t => t.weaken)

def Context.eval {M : SetTheory.Structure.{u}} {n : Nat}
    (C : Context (Project.Term n)) (env : Env M n) : Context M.Domain :=
  C.map (fun t => t.eval env)

theorem Context.eval_weaken {M : SetTheory.Structure.{u}} {n : Nat}
    (C : Context (Project.Term n)) (env : Env M n) (x : M.Domain) :
    C.weaken.eval (env.push x) = C.eval env := by
  cases C
  simp [Context.weaken,Context.eval,Context.map,Definitional.Term.eval_weaken]

def InstructionAt (M : SetTheory.Structure.{u}) (I Q p i op x y : M.Domain) : Prop :=
  ∃ instr, M.mem instr I ∧ ∃ args, M.mem args Q ∧
    MemPair M p i instr ∧ Codes M instr op args ∧ Codes M args x y

def instructionAtFormula {n : Nat} (I Q p i op x y : Project.Term n) : Project.Formula 1 n :=
  Project.Formula.existsMem I (Project.Formula.existsMem Q.weaken
    (.conj (memPairFormula p.weaken.weaken i.weaken.weaken (.bound 1))
      (.conj (codeFormula (.bound 1) op.weaken.weaken (.bound 0))
        (codeFormula (.bound 0) x.weaken.weaken y.weaken.weaken))))

theorem instructionAtFormula_delta0 {n : Nat} (I Q p i op x y : Project.Term n) :
    (instructionAtFormula I Q p i op x y).IsDelta0 :=
  .existsMem _ (.existsMem _ (.conj (memPairFormula_delta0 _ _ _)
    (.conj (codeFormula_delta0 _ _ _) (codeFormula_delta0 _ _ _))))

theorem instructionAtFormula_iff {M : SetTheory.Structure.{u}} (he : Extensional M) {n : Nat}
    (env : Env M n) (I Q p i op x y : Project.Term n) :
    Project.Formula.satisfies env (instructionAtFormula I Q p i op x y) ↔
      InstructionAt M (I.eval env) (Q.eval env) (p.eval env) (i.eval env)
        (op.eval env) (x.eval env) (y.eval env) := by
  simp only [instructionAtFormula, Project.Formula.satisfies_existsMem_iff,
    Project.Formula.satisfies_conj_iff, memPairFormula_iff he, codeFormula_iff he,
    Definitional.Term.eval_weaken]
  rfl

/-- 函数图的同一位置不会有两个不同操作码或字段。 -/
theorem instruction_unique {M : SetTheory.Structure.{u}} (he : Extensional M)
    {I Q p i op x y op' x' y' m V : M.Domain} (hP : Graph M p m V)
    (h : InstructionAt M I Q p i op x y) (h' : InstructionAt M I Q p i op' x' y') :
    op=op' ∧ x=x' ∧ y=y' := by
  obtain ⟨instr,_,args,_,hPi,hCode,hArgs⟩ := h
  obtain ⟨instr',_,args',_,hPi',hCode',hArgs'⟩ := h'
  have hi := hP.unique i instr instr' hPi hPi'
  subst instr'
  obtain ⟨hop,ha⟩ := codes_injective he hCode hCode'
  subst args'
  exact ⟨hop,codes_injective he hArgs hArgs'⟩

theorem instruction_index {M : SetTheory.Structure.{u}} (he : Extensional M)
    {I Q p i op x y m V : M.Domain} (hP : Graph M p m V)
    (h : InstructionAt M I Q p i op x y) : M.mem i m := by
  obtain ⟨instr,_,_,_,hPi,_,_⟩ := h
  exact (hP.bounds he hPi).1

end KP1Y.Satisfaction
