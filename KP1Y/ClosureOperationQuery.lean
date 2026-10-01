import KP1Y.ClosureData

/-! 从可数操作索引和自然数字词解码出有限参数并实际应用操作函数。 -/
namespace KP1Y.Closure
open YesMetaZFC YesMetaZFC.SetTheory YesMetaZFC.SetTheory.Definitional
open KP1Y.Kuratowski KP1Y.Functions KP1Y.Assignments KP1Y.Cardinal
universe u

def OperationQuery (M : SetTheory.Structure.{u}) (C : Data M.Domain) (E i j x : M.Domain) : Prop :=
  ∃ op, M.mem op C.operations ∧ ∃ word, M.mem word C.words ∧
    MemPair M C.operationDecode i op ∧ MemPair M C.wordDecode j word ∧
      ∃ t, M.mem t C.tuples ∧ WordMap M C.omega C.carrier E word t ∧
        ∃ key, M.mem key C.keys ∧ Codes M key op t ∧ MemPair M C.applyOperation key x

def operationQueryFormula {n : Nat} (C : Data (Project.Term n)) (E i j x : Project.Term n) : Project.Formula 1 n :=
  Project.Formula.existsMem C.operations (Project.Formula.existsMem C.words.weaken
    (.conj (memPairFormula C.operationDecode.weaken.weaken i.weaken.weaken (.bound 1))
      (.conj (memPairFormula C.wordDecode.weaken.weaken j.weaken.weaken (.bound 0))
        (Project.Formula.existsMem C.tuples.weaken.weaken
          (.conj (wordMapFormula C.omega.weaken.weaken.weaken C.carrier.weaken.weaken.weaken
              E.weaken.weaken.weaken (.bound 1) (.bound 0))
            (Project.Formula.existsMem C.keys.weaken.weaken.weaken
              (.conj (codeFormula (.bound 0) (.bound 3) (.bound 1))
                (memPairFormula C.applyOperation.weaken.weaken.weaken.weaken (.bound 0) x.weaken.weaken.weaken.weaken))))))))

theorem operationQueryFormula_delta0 {n : Nat} (C : Data (Project.Term n)) (E i j x : Project.Term n) :
    (operationQueryFormula C E i j x).IsDelta0 :=
  .existsMem _ (.existsMem _ (.conj (memPairFormula_delta0 _ _ _) (.conj (memPairFormula_delta0 _ _ _)
    (.existsMem _ (.conj (wordMapFormula_delta0 _ _ _ _ _)
      (.existsMem _ (.conj (codeFormula_delta0 _ _ _) (memPairFormula_delta0 _ _ _))))))))

theorem operationQueryFormula_iff {M : SetTheory.Structure.{u}} (he : Extensional M) {n : Nat}
    (env : Env M n) (C : Data (Project.Term n)) (E i j x : Project.Term n) :
    Project.Formula.satisfies env (operationQueryFormula C E i j x) ↔
      OperationQuery M (C.eval env) (E.eval env) (i.eval env) (j.eval env) (x.eval env) := by
  simp only [operationQueryFormula, Project.Formula.satisfies_existsMem_iff, Project.Formula.satisfies_conj_iff,
    memPairFormula_iff he, wordMapFormula_iff he, codeFormula_iff he, Definitional.Term.eval_weaken]
  rfl

theorem operation_query_total_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : Data M.Domain} (hC : Valid M C) {E i j : M.Domain} (hE : Graph M E C.omega C.carrier)
    (hi : M.mem i C.omega) (hj : M.mem j C.omega) :
    ∃ x, M.mem x C.carrier ∧ OperationQuery M C E i j x := by
  obtain ⟨op,hOp,hOpAt⟩ := hC.operationDecode.2.1 i hi
  obtain ⟨word,hWord,hWordAt⟩ := hC.wordDecode.2.1 j hj
  obtain ⟨n,hn,hWordGraph⟩ := (hC.words word).mp hWord
  obtain ⟨t,hValue⟩ := tuple_value_exists_d hM hWordGraph hE
  have ht := (hC.tuples t).mpr ⟨n,hn,hValue.values⟩
  obtain ⟨key,hCode⟩ := codes_total hM op t
  have hKey := (hC.keys key).mpr ⟨op,hOp,t,ht,hCode⟩
  obtain ⟨x,hx,hAt⟩ := hC.operation.total key hKey
  exact ⟨x,hx,op,hOp,word,hWord,hOpAt,hWordAt,t,ht,⟨n,hn,hValue⟩,key,hKey,hCode,hAt⟩

theorem wordMap_unique {M : SetTheory.Structure.{u}} (he : Extensional M)
    {ω A E word t t' : M.Domain} (h : WordMap M ω A E word t) (h' : WordMap M ω A E word t') : t=t' := by
  obtain ⟨n,_,hValue⟩ := h
  obtain ⟨n',_,hValue'⟩ := h'
  have hnn' := domain_unique he hValue.variables hValue'.variables
  subst n'
  exact tuple_value_unique he hValue hValue'

theorem operation_query_unique {M : SetTheory.Structure.{u}} (he : Extensional M)
    {C : Data M.Domain} (hC : Valid M C) {E i j x y : M.Domain}
    (hx : OperationQuery M C E i j x) (hy : OperationQuery M C E i j y) : x=y := by
  obtain ⟨op,_,word,_,hOp,hWord,t,_,hMap,key,_,hCode,hX⟩ := hx
  obtain ⟨op',_,word',_,hOp',hWord',t',_,hMap',key',_,hCode',hY⟩ := hy
  have hOps := (hC.operationDecode.toGraph he).unique i op op' hOp hOp'
  have hWords := (hC.wordDecode.toGraph he).unique j word word' hWord hWord'
  subst op'
  subst word'
  have hTs := wordMap_unique he hMap hMap'
  subst t'
  have hKeys := codes_unique he hCode hCode'
  subst key'
  exact hC.operation.unique key x y hX hY

end KP1Y.Closure
