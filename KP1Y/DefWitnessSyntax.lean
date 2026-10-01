import KP1Y.DefStageWitness

/-! Def后继的全部载域相关字段由一个字面Δ₀公式验证。 -/
namespace KP1Y.SetLanguage
open YesMetaZFC YesMetaZFC.SetTheory YesMetaZFC.SetTheory.Definitional
open KP1Y.Kuratowski KP1Y.Functions KP1Y.Sequences KP1Y.Satisfaction KP1Y.Definability
universe u

def stageWitnessFormula {n : Nat} (C : Context (Project.Term n)) (D : RelationalData (Project.Term n))
    (zero one two A Def : Project.Term n) (W : StageWitness (Project.Term n)) : Project.Formula 1 n :=
  .conj (spaceCertificateFormula D.omega A W.values W.sequences)
    (.conj (setRelationTableFormula A zero one two D.symbols W.values W.relation)
      (.conj (atomicTableFormula (W.data D A) W.atomic)
        (.conj (productBoundedFormula W.columns C.programs W.values)
          (.conj (evaluationFormula (W.context C A) W.table)
            (.conj (truthFormula (W.context C A) W.table W.raw)
              (.conj (typedTruthFormula (W.context C A) (W.data D A) W.raw W.typed)
                (defCertificateFormula (W.context C A) (W.data D A) W.typed zero Def W.definitions)))))))

theorem stageWitnessFormula_delta0 {n : Nat} (C : Context (Project.Term n)) (D : RelationalData (Project.Term n))
    (zero one two A Def : Project.Term n) (W : StageWitness (Project.Term n)) :
    (stageWitnessFormula C D zero one two A Def W).IsDelta0 :=
  .conj (spaceCertificateFormula_delta0 _ _ _ _)
    (.conj (setRelationTableFormula_delta0 _ _ _ _ _ _ _)
      (.conj (atomicTableFormula_delta0 _ _)
        (.conj (productBoundedFormula_delta0 _ _ _)
          (.conj (evaluationFormula_delta0 _ _)
            (.conj (truthFormula_delta0 _ _ _)
              (.conj (typedTruthFormula_delta0 _ _ _ _) (defCertificateFormula_delta0 _ _ _ _ _ _)))))))

theorem stageWitnessFormula_iff {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory) {n : Nat}
    (env : Env M n) (C : Context (Project.Term n)) (D : RelationalData (Project.Term n))
    (zero one two A Def : Project.Term n) (W : StageWitness (Project.Term n)) :
    Project.Formula.satisfies env (stageWitnessFormula C D zero one two A Def W) ↔
      StageWitness.Valid M (C.eval env) (D.eval env) (zero.eval env) (one.eval env) (two.eval env)
        (A.eval env) (Def.eval env) (W.eval env) := by
  simp only [stageWitnessFormula,Project.Formula.satisfies_conj_iff,spaceCertificateFormula_iff hM,
    setRelationTableFormula_iff hM.1,atomicTableFormula_iff hM.1,productBoundedFormula_iff hM,
    evaluationFormula_iff hM.1,truthFormula_iff hM.1,typedTruthFormula_iff hM.1,
    defCertificateFormula_iff hM.1,StageWitness.eval_context,StageWitness.eval_data]
  exact ⟨fun h => ⟨h.1,h.2.1,h.2.2.1,h.2.2.2.1,h.2.2.2.2.1,h.2.2.2.2.2.1,h.2.2.2.2.2.2.1,h.2.2.2.2.2.2.2⟩,
    fun h => ⟨h.sequences,h.relation,h.atomic,h.columns,h.evaluation,h.raw,h.typed,h.definitions⟩⟩

end KP1Y.SetLanguage
