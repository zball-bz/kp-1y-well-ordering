import KP1Y.SequenceSpaces

/-! 满意度量词步骤所需的内部赋值更新；修改指定位置，保留其余位置与实际长度。 -/
namespace KP1Y.Assignments
open YesMetaZFC YesMetaZFC.SetTheory YesMetaZFC.SetTheory.Definitional
open KP1Y.Kuratowski KP1Y.Functions
universe u

theorem domain_unique {M : SetTheory.Structure.{u}} (he : Extensional M)
    {F n m A B : M.Domain} (hF : Graph M F n A) (hG : Graph M F m B) : n=m := by
  apply he.eq_of_same_members
  intro i
  constructor
  · intro hi
    obtain ⟨v,_,hiv⟩ := hF.total i hi
    exact (hG.bounds he hiv).1
  · intro hi
    obtain ⟨v,_,hiv⟩ := hG.total i hi
    exact (hF.bounds he hiv).1

structure Updated (M : SetTheory.Structure.{u}) (T S n A i v : M.Domain) : Prop where
  graph : Graph M T n A
  rows : ∀ j, M.mem j n → ∀ y, M.mem y A →
    (MemPair M T j y ↔ (j=i ∧ y=v) ∨ (j≠i ∧ MemPair M S j y))

def updatedFormula {d : Nat} (T S n A i v : Project.Term d) : Project.Formula 1 d :=
  .conj (graphFormula T n A)
    (Project.Formula.forallMem n (Project.Formula.forallMem A.weaken
      (.iff (memPairFormula T.weaken.weaken (.bound 1) (.bound 0))
        (.disj
          (.conj (Project.Formula.extensionalEq (.bound 1) i.weaken.weaken)
            (Project.Formula.extensionalEq (.bound 0) v.weaken.weaken))
          (.conj (.neg (Project.Formula.extensionalEq (.bound 1) i.weaken.weaken))
            (memPairFormula S.weaken.weaken (.bound 1) (.bound 0)))))))

theorem updatedFormula_delta0 {d : Nat} (T S n A i v : Project.Term d) :
    (updatedFormula T S n A i v).IsDelta0 :=
  .conj (graphFormula_delta0 _ _ _) (.forallMem _ (.forallMem _
    (.iff (memPairFormula_delta0 _ _ _) (.disj (.conj (.atom _ _ _) (.atom _ _ _))
      (.conj (.neg (.atom _ _ _)) (memPairFormula_delta0 _ _ _))))))

theorem updatedFormula_iff {M : SetTheory.Structure.{u}} (he : Extensional M) {d : Nat}
    (env : Env M d) (T S n A i v : Project.Term d) :
    Project.Formula.satisfies env (updatedFormula T S n A i v) ↔
      Updated M (T.eval env) (S.eval env) (n.eval env) (A.eval env) (i.eval env) (v.eval env) := by
  simp only [updatedFormula, Project.Formula.satisfies_conj_iff, graphFormula_iff he,
    Project.Formula.satisfies_forallMem_iff, Project.Formula.satisfies_iff_iff,
    memPairFormula_iff he, Project.Formula.satisfies_disj_iff,
    Project.Formula.satisfies_neg_iff, Project.Formula.satisfies_extensionalEq_iff_eq he,
    Definitional.Term.eval_weaken]
  exact ⟨fun h => ⟨h.1,h.2⟩,fun h => ⟨h.graph,h.rows⟩⟩

private def updateSchema : Project.Delta0BinarySchema 3 where
  body := .disj
    (.conj (Project.Formula.extensionalEq (.bound 1) (.bound 3))
      (Project.Formula.extensionalEq (.bound 0) (.bound 2)))
    (.conj (.neg (Project.Formula.extensionalEq (.bound 1) (.bound 3)))
      (memPairFormula (.bound 4) (.bound 1) (.bound 0)))
  freeClosed := by
    simp [memPairFormula, codeFormula, pairFormula, Project.Formula.existsMem,
      Project.Formula.forallMem, Definitional.Formula.FreeClosed]
  delta0 := .disj (.conj (.atom _ _ _) (.atom _ _ _))
    (.conj (.neg (.atom _ _ _)) (memPairFormula_delta0 _ _ _))

private theorem updateSchema_iff {M : SetTheory.Structure.{u}} (he : Extensional M)
    (S i v j y : M.Domain) :
    Project.Formula.satisfies (((((oneEnv S).push i).push v).push j).push y) updateSchema.body ↔
      (j=i ∧ y=v) ∨ (j≠i ∧ MemPair M S j y) := by
  simp only [updateSchema, Project.Formula.satisfies_disj_iff, Project.Formula.satisfies_conj_iff,
    Project.Formula.satisfies_extensionalEq_iff_eq he, Project.Formula.satisfies_neg_iff,
    memPairFormula_iff he]
  rfl

theorem update_exists_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {S n A i v : M.Domain} (hS : Graph M S n A) (hv : M.mem v A) :
    ∃ T, Updated M T S n A i v := by
  classical
  obtain ⟨T,hSupport,hT⟩ := relation_comprehension_d hM updateSchema (((oneEnv S).push i).push v) n A
  have hRows (j y : M.Domain) : MemPair M T j y ↔ M.mem j n ∧ M.mem y A ∧
      ((j=i ∧ y=v) ∨ (j≠i ∧ MemPair M S j y)) := by
    simpa only [updateSchema_iff hM.1] using hT j y
  refine ⟨T,⟨hSupport,?_,?_⟩,?_⟩
  · intro j hj
    by_cases hji : j=i
    · exact ⟨v,hv,(hRows j v).mpr ⟨hj,hv,Or.inl ⟨hji,rfl⟩⟩⟩
    · obtain ⟨y,hy,hjy⟩ := hS.total j hj
      exact ⟨y,hy,(hRows j y).mpr ⟨hj,hy,Or.inr ⟨hji,hjy⟩⟩⟩
  · intro j y z hjy hjz
    rcases ((hRows j y).mp hjy).2.2 with hy | hy <;>
      rcases ((hRows j z).mp hjz).2.2 with hz | hz
    · exact hy.2.trans hz.2.symm
    · exact False.elim (hz.1 hy.1)
    · exact False.elim (hy.1 hz.1)
    · exact hS.unique j y z hy.2 hz.2
  · intro j hj y hy
    exact (hRows j y).trans ⟨fun h => h.2.2,fun h => ⟨hj,hy,h⟩⟩

theorem update_unique {M : SetTheory.Structure.{u}} (he : Extensional M)
    {T U S n A i v : M.Domain} (hT : Updated M T S n A i v) (hU : Updated M U S n A i v) : T=U := by
  classical
  apply hT.graph.ext he hU.graph
  intro j hj y
  by_cases hy : M.mem y A
  · exact (hT.rows j hj y hy).trans (hU.rows j hj y hy).symm
  · exact iff_of_false (fun h => hy (hT.graph.bounds he h).2) (fun h => hy (hU.graph.bounds he h).2)

theorem update_in_sequences_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {Seq S n ω A i v : M.Domain}
    (hSeq : ∀ F, M.mem F Seq ↔ ∃ k, M.mem k ω ∧ Graph M F k A)
    (hS : Graph M S n A) (hn : M.mem n ω) (hv : M.mem v A) :
    ∃ T, M.mem T Seq ∧ Updated M T S n A i v := by
  obtain ⟨T,hT⟩ := update_exists_d hM hS hv
  exact ⟨T,(hSeq T).mpr ⟨n,hn,hT.graph⟩,hT⟩

end KP1Y.Assignments
