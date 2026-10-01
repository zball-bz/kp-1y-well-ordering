import KP1Y.AssignmentUpdate

/-! 关系原子的变量元组求值：在内部有限赋值图上作有界函数复合。 -/
namespace KP1Y.Assignments
open YesMetaZFC YesMetaZFC.SetTheory YesMetaZFC.SetTheory.Definitional
open KP1Y.Kuratowski KP1Y.Functions
universe u

structure TupleValue (M : SetTheory.Structure.{u}) (t vars s n m A : M.Domain) : Prop where
  variables : Graph M vars n m
  source : Graph M s m A
  values : Graph M t n A
  rows : ∀ k, M.mem k n → ∀ j, M.mem j m → ∀ a, M.mem a A →
    MemPair M vars k j → (MemPair M t k a ↔ MemPair M s j a)

def tupleValueFormula {d : Nat} (t vars s n m A : Project.Term d) : Project.Formula 1 d :=
  .conj (graphFormula vars n m) (.conj (graphFormula s m A) (.conj (graphFormula t n A)
    (Project.Formula.forallMem n (Project.Formula.forallMem m.weaken (Project.Formula.forallMem A.weaken.weaken
      (.imp (memPairFormula vars.weaken.weaken.weaken (.bound 2) (.bound 1))
        (.iff (memPairFormula t.weaken.weaken.weaken (.bound 2) (.bound 0))
          (memPairFormula s.weaken.weaken.weaken (.bound 1) (.bound 0)))))))))

theorem tupleValueFormula_delta0 {d : Nat} (t vars s n m A : Project.Term d) :
    (tupleValueFormula t vars s n m A).IsDelta0 :=
  .conj (graphFormula_delta0 _ _ _) (.conj (graphFormula_delta0 _ _ _) (.conj (graphFormula_delta0 _ _ _)
    (.forallMem _ (.forallMem _ (.forallMem _ (.imp (memPairFormula_delta0 _ _ _)
      (.iff (memPairFormula_delta0 _ _ _) (memPairFormula_delta0 _ _ _))))))))

theorem tupleValueFormula_iff {M : SetTheory.Structure.{u}} (he : Extensional M) {d : Nat}
    (env : Env M d) (t vars s n m A : Project.Term d) :
    Project.Formula.satisfies env (tupleValueFormula t vars s n m A) ↔
      TupleValue M (t.eval env) (vars.eval env) (s.eval env) (n.eval env) (m.eval env) (A.eval env) := by
  simp only [tupleValueFormula, Project.Formula.satisfies_conj_iff,
    Project.Formula.satisfies_forallMem_iff, Project.Formula.satisfies_imp_iff,
    Project.Formula.satisfies_iff_iff, graphFormula_iff he, memPairFormula_iff he,
    Definitional.Term.eval_weaken]
  exact ⟨fun h => ⟨h.1,h.2.1,h.2.2.1,h.2.2.2⟩,
    fun h => ⟨h.variables,h.source,h.values,h.rows⟩⟩

private def compositionSchema : Project.Delta0BinarySchema 3 where
  body := Project.Formula.existsMem (.bound 2)
    (.conj (memPairFormula (.bound 4) (.bound 2) (.bound 0))
      (memPairFormula (.bound 5) (.bound 0) (.bound 1)))
  freeClosed := by
    simp [memPairFormula, codeFormula, pairFormula, Project.Formula.existsMem,
      Project.Formula.forallMem, Definitional.Formula.FreeClosed]
  delta0 := .existsMem _ (.conj (memPairFormula_delta0 _ _ _) (memPairFormula_delta0 _ _ _))

private theorem compositionSchema_iff {M : SetTheory.Structure.{u}} (he : Extensional M)
    (s vars m k a : M.Domain) :
    Project.Formula.satisfies (((((oneEnv s).push vars).push m).push k).push a) compositionSchema.body ↔
      ∃ j, M.mem j m ∧ MemPair M vars k j ∧ MemPair M s j a := by
  simp only [compositionSchema, Project.Formula.satisfies_existsMem_iff,
    Project.Formula.satisfies_conj_iff, memPairFormula_iff he]
  rfl

theorem tuple_value_exists_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {vars s n m A : M.Domain} (hV : Graph M vars n m) (hS : Graph M s m A) :
    ∃ t, TupleValue M t vars s n m A := by
  obtain ⟨t,hSupport,hT⟩ := relation_comprehension_d hM compositionSchema (((oneEnv s).push vars).push m) n A
  have hRows (k a : M.Domain) : MemPair M t k a ↔
      M.mem k n ∧ M.mem a A ∧ ∃ j, M.mem j m ∧ MemPair M vars k j ∧ MemPair M s j a := by
    simpa only [compositionSchema_iff hM.1] using hT k a
  refine ⟨t,hV,hS,⟨hSupport,?_,?_⟩,?_⟩
  · intro k hk
    obtain ⟨j,hj,hVj⟩ := hV.total k hk
    obtain ⟨a,ha,hSa⟩ := hS.total j hj
    exact ⟨a,ha,(hRows k a).mpr ⟨hk,ha,j,hj,hVj,hSa⟩⟩
  · intro k a b hka hkb
    obtain ⟨_,_,j,_,hVj,hSa⟩ := (hRows k a).mp hka
    obtain ⟨_,_,j',_,hVj',hSb⟩ := (hRows k b).mp hkb
    have heq := hV.unique k j j' hVj hVj'
    subst j'
    exact hS.unique j a b hSa hSb
  · intro k hk j hj a ha hVj
    constructor
    · intro hka
      obtain ⟨_,_,j',_,hVj',hSa⟩ := (hRows k a).mp hka
      have heq := hV.unique k j' j hVj' hVj
      subst j'
      exact hSa
    · intro hSa
      exact (hRows k a).mpr ⟨hk,ha,j,hj,hVj,hSa⟩

theorem tuple_value_unique {M : SetTheory.Structure.{u}} (he : Extensional M)
    {t u vars s n m A : M.Domain} (ht : TupleValue M t vars s n m A) (hu : TupleValue M u vars s n m A) : t=u := by
  classical
  apply ht.values.ext he hu.values
  intro k hk a
  by_cases ha : M.mem a A
  · obtain ⟨j,hj,hVj⟩ := ht.variables.total k hk
    exact (ht.rows k hk j hj a ha hVj).trans (hu.rows k hk j hj a ha hVj).symm
  · exact iff_of_false (fun h => ha (ht.values.bounds he h).2) (fun h => ha (hu.values.bounds he h).2)

end KP1Y.Assignments
