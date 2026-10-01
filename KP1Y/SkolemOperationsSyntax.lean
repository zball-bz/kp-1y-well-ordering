import KP1Y.SkolemFunction
import KP1Y.CountableNamedSpaces

/-! 将 Skolem 参数分成可数元数据 (程序、节点、变量号) 与有限载域元组。 -/
namespace KP1Y.Satisfaction
open YesMetaZFC YesMetaZFC.SetTheory YesMetaZFC.SetTheory.Definitional
open KP1Y.Kuratowski KP1Y.Functions
universe u

def MetadataCode (M : SetTheory.Structure.{u}) (K : SkolemBounds M.Domain) (op p j v : M.Domain) : Prop :=
  ∃ pj, M.mem pj K.programNodes ∧ Codes M op pj v ∧ Codes M pj p j

def metadataCodeFormula {n : Nat} (K : SkolemBounds (Project.Term n)) (op p j v : Project.Term n) : Project.Formula 1 n :=
  Project.Formula.existsMem K.programNodes (.conj (codeFormula op.weaken (.bound 0) v.weaken)
    (codeFormula (.bound 0) p.weaken j.weaken))

theorem metadataCodeFormula_delta0 {n : Nat} (K : SkolemBounds (Project.Term n)) (op p j v : Project.Term n) :
    (metadataCodeFormula K op p j v).IsDelta0 := .existsMem _ (.conj (codeFormula_delta0 _ _ _) (codeFormula_delta0 _ _ _))

theorem metadataCodeFormula_iff {M : SetTheory.Structure.{u}} (he : Extensional M) {n : Nat}
    (env : Env M n) (K : SkolemBounds (Project.Term n)) (op p j v : Project.Term n) :
    Project.Formula.satisfies env (metadataCodeFormula K op p j v) ↔
      MetadataCode M (K.eval env) (op.eval env) (p.eval env) (j.eval env) (v.eval env) := by
  simp only [metadataCodeFormula, Project.Formula.satisfies_existsMem_iff,
    Project.Formula.satisfies_conj_iff, codeFormula_iff he, Definitional.Term.eval_weaken]
  rfl

theorem metadata_unique {M : SetTheory.Structure.{u}} (he : Extensional M) {K : SkolemBounds M.Domain}
    {op p j v p' j' v' : M.Domain} (h : MetadataCode M K op p j v) (h' : MetadataCode M K op p' j' v') :
    p=p' ∧ j=j' ∧ v=v' := by
  obtain ⟨pj,_,hOp,hPJ⟩ := h
  obtain ⟨pj',_,hOp',hPJ'⟩ := h'
  obtain ⟨hPjs,hVs⟩ := codes_injective he hOp hOp'
  subst pj'
  obtain ⟨hPs,hJs⟩ := codes_injective he hPJ hPJ'
  exact ⟨hPs,hJs,hVs⟩

theorem key_code_value_unique {M : SetTheory.Structure.{u}} (he : Extensional M) {K : SkolemBounds M.Domain}
    {key key' p j s bound v : M.Domain} (h : KeyCode M K key p j s bound v) (h' : KeyCode M K key' p j s bound v) : key=key' := by
  obtain ⟨pj,_,bv,_,sbv,_,hKey,hPJ,hSBV,hBV⟩ := h
  obtain ⟨pj',_,bv',_,sbv',_,hKey',hPJ',hSBV',hBV'⟩ := h'
  have hPjs := codes_unique he hPJ hPJ'
  have hBvs := codes_unique he hBV hBV'
  subst pj'
  subst bv'
  have hSbvs := codes_unique he hSBV hSBV'
  subst sbv'
  exact codes_unique he hKey hKey'

def SkolemApply (M : SetTheory.Structure.{u}) (C : Context M.Domain) (I : EvaluationData M.Domain)
    (K : SkolemBounds M.Domain) (Ops F key x : M.Domain) : Prop :=
  ∃ op, M.mem op Ops ∧ ∃ s, M.mem s I.assignments ∧ Codes M key op s ∧
    ∃ p, M.mem p C.programs ∧ ∃ j, M.mem j C.omega ∧ ∃ v, M.mem v C.omega ∧ MetadataCode M K op p j v ∧
      ∃ bound, M.mem bound C.omega ∧ Graph M s bound I.carrier ∧
        ∃ oldKey, M.mem oldKey K.keys ∧ KeyCode M K oldKey p j s bound v ∧ MemPair M F oldKey x

def skolemApplyFormula {n : Nat} (C : Context (Project.Term n)) (I : EvaluationData (Project.Term n))
    (K : SkolemBounds (Project.Term n)) (Ops F key x : Project.Term n) : Project.Formula 1 n :=
  Project.Formula.existsMem Ops (Project.Formula.existsMem I.assignments.weaken
    (.conj (codeFormula key.weaken.weaken (.bound 1) (.bound 0))
      (Project.Formula.existsMem C.programs.weaken.weaken (Project.Formula.existsMem C.omega.weaken.weaken.weaken
        (Project.Formula.existsMem C.omega.weaken.weaken.weaken.weaken
          (.conj (metadataCodeFormula K.weaken.weaken.weaken.weaken.weaken (.bound 4) (.bound 2) (.bound 1) (.bound 0))
            (Project.Formula.existsMem C.omega.weaken.weaken.weaken.weaken.weaken
              (.conj (graphFormula (.bound 4) (.bound 0) I.carrier.weaken.weaken.weaken.weaken.weaken.weaken)
                (Project.Formula.existsMem K.keys.weaken.weaken.weaken.weaken.weaken.weaken
                  (.conj (keyCodeFormula K.weaken.weaken.weaken.weaken.weaken.weaken.weaken
                      (.bound 0) (.bound 4) (.bound 3) (.bound 5) (.bound 1) (.bound 2))
                    (memPairFormula F.weaken.weaken.weaken.weaken.weaken.weaken.weaken (.bound 0)
                      x.weaken.weaken.weaken.weaken.weaken.weaken.weaken)))))))))))

theorem skolemApplyFormula_delta0 {n : Nat} (C : Context (Project.Term n)) (I : EvaluationData (Project.Term n))
    (K : SkolemBounds (Project.Term n)) (Ops F key x : Project.Term n) : (skolemApplyFormula C I K Ops F key x).IsDelta0 :=
  .existsMem _ (.existsMem _ (.conj (codeFormula_delta0 _ _ _)
    (.existsMem _ (.existsMem _ (.existsMem _ (.conj (metadataCodeFormula_delta0 _ _ _ _ _)
      (.existsMem _ (.conj (graphFormula_delta0 _ _ _) (.existsMem _
        (.conj (keyCodeFormula_delta0 _ _ _ _ _ _ _) (memPairFormula_delta0 _ _ _)))))))))))

theorem skolemApplyFormula_iff {M : SetTheory.Structure.{u}} (he : Extensional M) {n : Nat}
    (env : Env M n) (C : Context (Project.Term n)) (I : EvaluationData (Project.Term n))
    (K : SkolemBounds (Project.Term n)) (Ops F key x : Project.Term n) :
    Project.Formula.satisfies env (skolemApplyFormula C I K Ops F key x) ↔
      SkolemApply M (C.eval env) (I.eval env) (K.eval env) (Ops.eval env) (F.eval env) (key.eval env) (x.eval env) := by
  simp only [skolemApplyFormula, Project.Formula.satisfies_existsMem_iff, Project.Formula.satisfies_conj_iff,
    codeFormula_iff he, metadataCodeFormula_iff he, graphFormula_iff he, keyCodeFormula_iff he,
    memPairFormula_iff he, SkolemBounds.eval_weaken, Definitional.Term.eval_weaken]
  rfl

private def operationContext : Context (Project.Term 26) :=
  ⟨.bound 3,.bound 4,.bound 5,.bound 6,.bound 7,.bound 8,.bound 9,.bound 10,.bound 11,.bound 12,.bound 13,.bound 14,.bound 15⟩
private def operationInstance : EvaluationData (Project.Term 26) :=
  ⟨.bound 16,.bound 17,.bound 18,.bound 19,.bound 20⟩
private def operationBounds : SkolemBounds (Project.Term 26) :=
  ⟨.bound 21,.bound 22,.bound 23,.bound 24⟩

def skolemOperationSchema : Project.Delta0BinarySchema 24 where
  body := skolemApplyFormula operationContext operationInstance operationBounds (.bound 25) (.bound 2) (.bound 1) (.bound 0)
  freeClosed := by
    simp [skolemApplyFormula, metadataCodeFormula, keyCodeFormula, graphFormula, memPairFormula, codeFormula, pairFormula,
      SkolemBounds.weaken, SkolemBounds.map,
      operationContext, operationInstance, operationBounds, Project.Formula.existsMem,
      Project.Formula.forallMem, Definitional.Formula.FreeClosed]
  delta0 := skolemApplyFormula_delta0 _ _ _ _ _ _ _

theorem skolemOperationSchema_iff {M : SetTheory.Structure.{u}} (he : Extensional M)
    (C : Context M.Domain) (I : EvaluationData M.Domain) (K : SkolemBounds M.Domain) (Ops F key x : M.Domain) :
    Project.Formula.satisfies ((((skolemEnv C I K Ops).push F).push key).push x) skolemOperationSchema.body ↔
      SkolemApply M C I K Ops F key x := by
  rw [skolemOperationSchema,skolemApplyFormula_iff he]
  rfl

end KP1Y.Satisfaction
