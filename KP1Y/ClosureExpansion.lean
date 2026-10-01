import KP1Y.ClosureOperationQuery

/-! 可数闭包枚举器的一步扩张：保留旧像，并枚举全部可数操作的有限参数实例。 -/
namespace KP1Y.Closure
open YesMetaZFC YesMetaZFC.SetTheory YesMetaZFC.SetTheory.Definitional
open KP1Y.Kuratowski KP1Y.Functions KP1Y.Bounded
universe u

def NextPoint (M : SetTheory.Structure.{u}) (C : Data M.Domain) (E n x : M.Domain) : Prop :=
  ∃ tag, M.mem tag C.omega ∧ ∃ k, M.mem k C.omega ∧ Decodes M C n tag k ∧
    (((∀ z, ¬M.mem z tag) ∧ MemPair M E k x) ∨
      (¬(∀ z, ¬M.mem z tag) ∧ ∃ i, M.mem i C.omega ∧ ∃ j, M.mem j C.omega ∧
        Decodes M C k i j ∧ OperationQuery M C E i j x))

def nextPointFormula {d : Nat} (C : Data (Project.Term d)) (E n x : Project.Term d) : Project.Formula 1 d :=
  Project.Formula.existsMem C.omega (Project.Formula.existsMem C.omega.weaken
    (.conj (decodesFormula C.weaken.weaken n.weaken.weaken (.bound 1) (.bound 0))
      (.disj (.conj (emptyFormula (.bound 1)) (memPairFormula E.weaken.weaken (.bound 0) x.weaken.weaken))
        (.conj (.neg (emptyFormula (.bound 1)))
          (Project.Formula.existsMem C.omega.weaken.weaken (Project.Formula.existsMem C.omega.weaken.weaken.weaken
            (.conj (decodesFormula C.weaken.weaken.weaken.weaken (.bound 2) (.bound 1) (.bound 0))
              (operationQueryFormula C.weaken.weaken.weaken.weaken E.weaken.weaken.weaken.weaken
                (.bound 1) (.bound 0) x.weaken.weaken.weaken.weaken))))))))

theorem nextPointFormula_delta0 {d : Nat} (C : Data (Project.Term d)) (E n x : Project.Term d) :
    (nextPointFormula C E n x).IsDelta0 :=
  .existsMem _ (.existsMem _ (.conj (decodesFormula_delta0 _ _ _ _)
    (.disj (.conj (emptyFormula_delta0 _) (memPairFormula_delta0 _ _ _))
      (.conj (.neg (emptyFormula_delta0 _)) (.existsMem _ (.existsMem _
        (.conj (decodesFormula_delta0 _ _ _ _) (operationQueryFormula_delta0 _ _ _ _ _))))))))

theorem nextPointFormula_iff {M : SetTheory.Structure.{u}} (he : Extensional M) {d : Nat}
    (env : Env M d) (C : Data (Project.Term d)) (E n x : Project.Term d) :
    Project.Formula.satisfies env (nextPointFormula C E n x) ↔ NextPoint M (C.eval env) (E.eval env) (n.eval env) (x.eval env) := by
  simp only [nextPointFormula, Project.Formula.satisfies_existsMem_iff, Project.Formula.satisfies_conj_iff,
    Project.Formula.satisfies_disj_iff, Project.Formula.satisfies_neg_iff, emptyFormula_iff,
    decodesFormula_iff he, memPairFormula_iff he, operationQueryFormula_iff he,
    Data.eval_weaken, Definitional.Term.eval_weaken]
  rfl

theorem next_point_total_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : Data M.Domain} (hC : Valid M C) {E n : M.Domain} (hE : Graph M E C.omega C.carrier) (hn : M.mem n C.omega) :
    ∃ x, M.mem x C.carrier ∧ NextPoint M C E n x := by
  classical
  obtain ⟨tag,hTag,k,hk,hDecode⟩ := decode_total hC hn
  by_cases hEmpty : ∀ z, ¬M.mem z tag
  · obtain ⟨x,hx,hAt⟩ := hE.total k hk
    exact ⟨x,hx,tag,hTag,k,hk,hDecode,Or.inl ⟨hEmpty,hAt⟩⟩
  · obtain ⟨i,hi,j,hj,hDecode'⟩ := decode_total hC hk
    obtain ⟨x,hx,hQuery⟩ := operation_query_total_d hM hC hE hi hj
    exact ⟨x,hx,tag,hTag,k,hk,hDecode,Or.inr ⟨hEmpty,i,hi,j,hj,hDecode',hQuery⟩⟩

theorem next_point_unique {M : SetTheory.Structure.{u}} (he : Extensional M)
    {C : Data M.Domain} (hC : Valid M C) {E n x y : M.Domain} (hE : Graph M E C.omega C.carrier)
    (hx : NextPoint M C E n x) (hy : NextPoint M C E n y) : x=y := by
  obtain ⟨tag,_,k,_,hDecode,hCase⟩ := hx
  obtain ⟨tag',_,k',_,hDecode',hCase'⟩ := hy
  obtain ⟨hTags,hks⟩ := decode_unique he hC hDecode hDecode'
  subst tag'
  subst k'
  rcases hCase with ⟨hEmpty,hAt⟩ | ⟨hEmpty,i,_,j,_,hDec,hQuery⟩
  · rcases hCase' with ⟨_,hAt'⟩ | ⟨hNot,_⟩
    · exact hE.unique k x y hAt hAt'
    · exact False.elim (hNot hEmpty)
  · rcases hCase' with ⟨hYes,_⟩ | ⟨_,i',_,j',_,hDec',hQuery'⟩
    · exact False.elim (hEmpty hYes)
    · obtain ⟨his,hjs⟩ := decode_unique he hC hDec hDec'
      subst i'
      subst j'
      exact operation_query_unique he hC hQuery hQuery'

structure NextEnumerator (M : SetTheory.Structure.{u}) (C : Data M.Domain) (E F : M.Domain) : Prop where
  graph : Graph M F C.omega C.carrier
  rows : ∀ n, M.mem n C.omega → ∀ x, M.mem x C.carrier → (MemPair M F n x ↔ NextPoint M C E n x)

def nextEnumeratorFormula {n : Nat} (C : Data (Project.Term n)) (E F : Project.Term n) : Project.Formula 1 n :=
  .conj (graphFormula F C.omega C.carrier) (Project.Formula.forallMem C.omega
    (Project.Formula.forallMem C.carrier.weaken (.iff (memPairFormula F.weaken.weaken (.bound 1) (.bound 0))
      (nextPointFormula C.weaken.weaken E.weaken.weaken (.bound 1) (.bound 0)))))

theorem nextEnumeratorFormula_delta0 {n : Nat} (C : Data (Project.Term n)) (E F : Project.Term n) :
    (nextEnumeratorFormula C E F).IsDelta0 :=
  .conj (graphFormula_delta0 _ _ _) (.forallMem _ (.forallMem _
    (.iff (memPairFormula_delta0 _ _ _) (nextPointFormula_delta0 _ _ _ _))))

theorem nextEnumeratorFormula_iff {M : SetTheory.Structure.{u}} (he : Extensional M) {n : Nat}
    (env : Env M n) (C : Data (Project.Term n)) (E F : Project.Term n) :
    Project.Formula.satisfies env (nextEnumeratorFormula C E F) ↔ NextEnumerator M (C.eval env) (E.eval env) (F.eval env) := by
  simp only [nextEnumeratorFormula, Project.Formula.satisfies_conj_iff, graphFormula_iff he,
    Project.Formula.satisfies_forallMem_iff, Project.Formula.satisfies_iff_iff,
    memPairFormula_iff he, nextPointFormula_iff he, Data.eval_weaken, Definitional.Term.eval_weaken]
  exact ⟨fun h => ⟨h.1,h.2⟩,fun h => ⟨h.graph,h.rows⟩⟩

def dataEnv {M : SetTheory.Structure.{u}} (C : Data M.Domain) : Env M 12 where
  bound k := match k.val with
    | 0 => C.omega | 1 => C.carrier | 2 => C.pairs | 3 => C.pairDecode
    | 4 => C.words | 5 => C.wordDecode | 6 => C.operations | 7 => C.operationDecode
    | 8 => C.tuples | 9 => C.keys | 10 => C.applyOperation | _ => C.zero
  free _ := C.omega

private def pointContext : Data (Project.Term 15) :=
  ⟨.bound 3,.bound 4,.bound 5,.bound 6,.bound 7,.bound 8,.bound 9,.bound 10,.bound 11,.bound 12,.bound 13,.bound 14⟩
private def pointSchema : Project.Delta0BinarySchema 13 where
  body := nextPointFormula pointContext (.bound 2) (.bound 1) (.bound 0)
  freeClosed := by
    simp [nextPointFormula, operationQueryFormula, decodesFormula, Cardinal.wordMapFormula,
      Assignments.tupleValueFormula, graphFormula, emptyFormula, memPairFormula, codeFormula, pairFormula,
      Data.weaken, Data.map, pointContext, Project.Formula.existsMem,
      Project.Formula.forallMem, Definitional.Formula.FreeClosed]
  delta0 := nextPointFormula_delta0 _ _ _ _

private theorem pointSchema_iff {M : SetTheory.Structure.{u}} (he : Extensional M) (C : Data M.Domain) (E n x : M.Domain) :
    Project.Formula.satisfies ((((dataEnv C).push E).push n).push x) pointSchema.body ↔ NextPoint M C E n x := by
  rw [pointSchema,nextPointFormula_iff he]
  rfl

theorem next_enumerator_exists_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : Data M.Domain} (hC : Valid M C) {E : M.Domain} (hE : Graph M E C.omega C.carrier) :
    ∃ F, NextEnumerator M C E F := by
  obtain ⟨F,hSupport,hRaw⟩ := relation_comprehension_d hM pointSchema ((dataEnv C).push E) C.omega C.carrier
  have hRows (n x : M.Domain) : MemPair M F n x ↔ M.mem n C.omega ∧ M.mem x C.carrier ∧ NextPoint M C E n x := by
    simpa only [pointSchema_iff hM.1] using hRaw n x
  refine ⟨F,⟨hSupport,?_,?_⟩,?_⟩
  · intro n hn
    obtain ⟨x,hx,hPoint⟩ := next_point_total_d hM hC hE hn
    exact ⟨x,hx,(hRows n x).mpr ⟨hn,hx,hPoint⟩⟩
  · intro n x y hnx hny
    exact next_point_unique hM.1 hC hE ((hRows n x).mp hnx).2.2 ((hRows n y).mp hny).2.2
  · intro n hn x hx
    exact (hRows n x).trans ⟨fun h => h.2.2,fun h => ⟨hn,hx,h⟩⟩

theorem next_enumerator_unique {M : SetTheory.Structure.{u}} (he : Extensional M)
    {C : Data M.Domain} {E F G : M.Domain} (hF : NextEnumerator M C E F) (hG : NextEnumerator M C E G) : F=G := by
  classical
  apply hF.graph.ext he hG.graph
  intro n hn x
  by_cases hx : M.mem x C.carrier
  · exact (hF.rows n hn x hx).trans (hG.rows n hn x hx).symm
  · exact iff_of_false (fun h => hx (hF.graph.bounds he h).2) (fun h => hx (hG.graph.bounds he h).2)

end KP1Y.Closure
