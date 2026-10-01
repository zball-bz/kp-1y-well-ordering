import KP1Y.EnumeratorTupleOperation

/-! 给有限元组操作族附加全局枚举函数 e 的操作，所有分支保持字面 Δ₀。 -/
namespace KP1Y.Closure
open YesMetaZFC YesMetaZFC.SetTheory YesMetaZFC.SetTheory.Definitional
open KP1Y.Kuratowski KP1Y.Functions KP1Y.Bounded KP1Y.Satisfaction
universe u v

structure AugmentData (α : Type u) where
  omega : α
  carrier : α
  operations : α
  tuples : α
  oldKeys : α
  oldApply : α
  enumKeys : α
  enumerator : α
  indexZero : α
  default : α

def AugmentData.map {α : Type u} {β : Type v} (D : AugmentData α) (f : α → β) : AugmentData β :=
  ⟨f D.omega,f D.carrier,f D.operations,f D.tuples,f D.oldKeys,f D.oldApply,
    f D.enumKeys,f D.enumerator,f D.indexZero,f D.default⟩
def AugmentData.weaken {n : Nat} (D : AugmentData (Project.Term n)) : AugmentData (Project.Term (n+1)) := D.map (fun t => t.weaken)
def AugmentData.eval {M : SetTheory.Structure.{u}} {n : Nat} (D : AugmentData (Project.Term n)) (env : Env M n) : AugmentData M.Domain :=
  D.map (fun t => t.eval env)

theorem AugmentData.eval_weaken {M : SetTheory.Structure.{u}} {n : Nat}
    (D : AugmentData (Project.Term n)) (env : Env M n) (x : M.Domain) : D.weaken.eval (env.push x)=D.eval env := by
  cases D
  simp [AugmentData.weaken,AugmentData.eval,AugmentData.map,Definitional.Term.eval_weaken]

structure AugmentValid (M : SetTheory.Structure.{u}) (D : AugmentData M.Domain) : Prop where
  omega : M.IsOmega D.omega
  tuples : ∀ t, M.mem t D.tuples ↔ ∃ n, M.mem n D.omega ∧ Graph M t n D.carrier
  oldKeys : IsProduct M D.oldKeys D.operations D.tuples
  oldApply : Graph M D.oldApply D.oldKeys D.carrier
  enumKeys : IsProduct M D.enumKeys D.carrier D.omega
  enumerator : Graph M D.enumerator D.enumKeys D.carrier
  zero_nat : M.mem D.indexZero D.omega
  zero_empty : ∀ x, ¬M.mem x D.indexZero
  default_mem : M.mem D.default D.carrier

def AugmentCase (M : SetTheory.Structure.{u}) (D : AugmentData M.Domain) (op tag t x : M.Domain) : Prop :=
  ((∀ z, ¬M.mem z tag) ∧ ∃ key, M.mem key D.oldKeys ∧ Codes M key op t ∧ MemPair M D.oldApply key x) ∨
    ∃ n, M.mem n tag ∧ M.SuccessorOf tag n ∧ EnumTuple M D.carrier D.enumKeys D.enumerator D.indexZero D.default n t x

def augmentCaseFormula {n : Nat} (D : AugmentData (Project.Term n)) (op tag t x : Project.Term n) : Project.Formula 1 n :=
  .disj (.conj (emptyFormula tag) (Project.Formula.existsMem D.oldKeys
      (.conj (codeFormula (.bound 0) op.weaken t.weaken) (memPairFormula D.oldApply.weaken (.bound 0) x.weaken))))
    (Project.Formula.existsMem tag (.conj (successorFormula tag.weaken (.bound 0))
      (enumTupleFormula D.carrier.weaken D.enumKeys.weaken D.enumerator.weaken D.indexZero.weaken D.default.weaken
        (.bound 0) t.weaken x.weaken)))

theorem augmentCaseFormula_delta0 {n : Nat} (D : AugmentData (Project.Term n)) (op tag t x : Project.Term n) :
    (augmentCaseFormula D op tag t x).IsDelta0 :=
  .disj (.conj (emptyFormula_delta0 _) (.existsMem _ (.conj (codeFormula_delta0 _ _ _) (memPairFormula_delta0 _ _ _))))
    (.existsMem _ (.conj (successorFormula_delta0 _ _) (enumTupleFormula_delta0 _ _ _ _ _ _ _ _)))

theorem augmentCaseFormula_iff {M : SetTheory.Structure.{u}} (he : Extensional M) {n : Nat}
    (env : Env M n) (D : AugmentData (Project.Term n)) (op tag t x : Project.Term n) :
    Project.Formula.satisfies env (augmentCaseFormula D op tag t x) ↔
      AugmentCase M (D.eval env) (op.eval env) (tag.eval env) (t.eval env) (x.eval env) := by
  simp only [augmentCaseFormula, Project.Formula.satisfies_disj_iff, Project.Formula.satisfies_conj_iff,
    Project.Formula.satisfies_existsMem_iff, emptyFormula_iff, successorFormula_iff he,
    codeFormula_iff he, memPairFormula_iff he, enumTupleFormula_iff he, Definitional.Term.eval_weaken]
  rfl

def AugmentedApply (M : SetTheory.Structure.{u}) (D : AugmentData M.Domain) (Tagged key x : M.Domain) : Prop :=
  ∃ label, M.mem label Tagged ∧ ∃ t, M.mem t D.tuples ∧ Codes M key label t ∧
    ∃ op, M.mem op D.operations ∧ ∃ tag, M.mem tag D.omega ∧ Codes M label op tag ∧ AugmentCase M D op tag t x

def augmentedApplyFormula {n : Nat} (D : AugmentData (Project.Term n)) (Tagged key x : Project.Term n) : Project.Formula 1 n :=
  Project.Formula.existsMem Tagged (Project.Formula.existsMem D.tuples.weaken
    (.conj (codeFormula key.weaken.weaken (.bound 1) (.bound 0))
      (Project.Formula.existsMem D.operations.weaken.weaken (Project.Formula.existsMem D.omega.weaken.weaken.weaken
        (.conj (codeFormula (.bound 3) (.bound 1) (.bound 0))
          (augmentCaseFormula D.weaken.weaken.weaken.weaken (.bound 1) (.bound 0) (.bound 2) x.weaken.weaken.weaken.weaken))))))

theorem augmentedApplyFormula_delta0 {n : Nat} (D : AugmentData (Project.Term n)) (Tagged key x : Project.Term n) :
    (augmentedApplyFormula D Tagged key x).IsDelta0 :=
  .existsMem _ (.existsMem _ (.conj (codeFormula_delta0 _ _ _)
    (.existsMem _ (.existsMem _ (.conj (codeFormula_delta0 _ _ _) (augmentCaseFormula_delta0 _ _ _ _ _))))))

theorem augmentedApplyFormula_iff {M : SetTheory.Structure.{u}} (he : Extensional M) {n : Nat}
    (env : Env M n) (D : AugmentData (Project.Term n)) (Tagged key x : Project.Term n) :
    Project.Formula.satisfies env (augmentedApplyFormula D Tagged key x) ↔
      AugmentedApply M (D.eval env) (Tagged.eval env) (key.eval env) (x.eval env) := by
  simp only [augmentedApplyFormula, Project.Formula.satisfies_existsMem_iff,
    Project.Formula.satisfies_conj_iff, codeFormula_iff he, augmentCaseFormula_iff he,
    AugmentData.eval_weaken, Definitional.Term.eval_weaken]
  rfl

private def augmentContext : AugmentData (Project.Term 13) :=
  ⟨.bound 3,.bound 4,.bound 5,.bound 6,.bound 7,.bound 8,.bound 9,.bound 10,.bound 11,.bound 12⟩

def augmentedSchema : Project.Delta0BinarySchema 11 where
  body := augmentedApplyFormula augmentContext (.bound 2) (.bound 1) (.bound 0)
  freeClosed := by
    simp [augmentedApplyFormula, augmentCaseFormula, enumTupleFormula, emptyFormula, successorFormula,
      memPairFormula, codeFormula, pairFormula, AugmentData.weaken, AugmentData.map, augmentContext,
      Project.Formula.existsMem, Project.Formula.forallMem, Definitional.Formula.FreeClosed]
  delta0 := augmentedApplyFormula_delta0 _ _ _ _

def augmentEnv {M : SetTheory.Structure.{u}} (D : AugmentData M.Domain) : Env M 10 where
  bound k := match k.val with
    | 0 => D.omega | 1 => D.carrier | 2 => D.operations | 3 => D.tuples | 4 => D.oldKeys
    | 5 => D.oldApply | 6 => D.enumKeys | 7 => D.enumerator | 8 => D.indexZero | _ => D.default
  free _ := D.omega

theorem augmentedSchema_iff {M : SetTheory.Structure.{u}} (he : Extensional M) (D : AugmentData M.Domain) (Tagged key x : M.Domain) :
    Project.Formula.satisfies ((((augmentEnv D).push Tagged).push key).push x) augmentedSchema.body ↔ AugmentedApply M D Tagged key x := by
  rw [augmentedSchema,augmentedApplyFormula_iff he]
  rfl

end KP1Y.Closure
