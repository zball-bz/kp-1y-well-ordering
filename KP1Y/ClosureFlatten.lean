import KP1Y.ClosureFamily

/-! 用固定配对表展平实际枚举器族，产生闭包总像的真实 ω 满射。 -/
namespace KP1Y.Closure
open YesMetaZFC YesMetaZFC.SetTheory YesMetaZFC.SetTheory.Definitional
open KP1Y.Kuratowski KP1Y.Functions KP1Y.Iteration KP1Y.Cardinal
universe u

def FlattenPoint (M : SetTheory.Structure.{u}) (C : Data M.Domain) (R V n x : M.Domain) : Prop :=
  ∃ i, M.mem i C.omega ∧ ∃ j, M.mem j C.omega ∧ Decodes M C n i j ∧
    ∃ E, M.mem E V ∧ MemPair M R i E ∧ MemPair M E j x

def flattenPointFormula {d : Nat} (C : Data (Project.Term d)) (R V n x : Project.Term d) : Project.Formula 1 d :=
  Project.Formula.existsMem C.omega (Project.Formula.existsMem C.omega.weaken
    (.conj (decodesFormula C.weaken.weaken n.weaken.weaken (.bound 1) (.bound 0))
      (Project.Formula.existsMem V.weaken.weaken
        (.conj (memPairFormula R.weaken.weaken.weaken (.bound 2) (.bound 0))
          (memPairFormula (.bound 0) (.bound 1) x.weaken.weaken.weaken)))))

theorem flattenPointFormula_delta0 {d : Nat} (C : Data (Project.Term d)) (R V n x : Project.Term d) :
    (flattenPointFormula C R V n x).IsDelta0 :=
  .existsMem _ (.existsMem _ (.conj (decodesFormula_delta0 _ _ _ _)
    (.existsMem _ (.conj (memPairFormula_delta0 _ _ _) (memPairFormula_delta0 _ _ _)))))

theorem flattenPointFormula_iff {M : SetTheory.Structure.{u}} (he : Extensional M) {d : Nat}
    (env : Env M d) (C : Data (Project.Term d)) (R V n x : Project.Term d) :
    Project.Formula.satisfies env (flattenPointFormula C R V n x) ↔
      FlattenPoint M (C.eval env) (R.eval env) (V.eval env) (n.eval env) (x.eval env) := by
  simp only [flattenPointFormula, Project.Formula.satisfies_existsMem_iff,
    Project.Formula.satisfies_conj_iff, decodesFormula_iff he, memPairFormula_iff he,
    Data.eval_weaken, Definitional.Term.eval_weaken]
  rfl

def FamilyRange (M : SetTheory.Structure.{u}) (C : Data M.Domain) (R V x : M.Domain) : Prop :=
  ∃ i, M.mem i C.omega ∧ ∃ E, M.mem E V ∧ MemPair M R i E ∧ Reached M C.omega E x

structure Flattened (M : SetTheory.Structure.{u}) (C : Data M.Domain) (R V X f : M.Domain) : Prop where
  graph : Graph M f C.omega C.carrier
  onto : Onto M f C.omega X
  members : ∀ x, M.mem x X ↔ FamilyRange M C R V x
  rows : ∀ n, M.mem n C.omega → ∀ x, M.mem x C.carrier → (MemPair M f n x ↔ FlattenPoint M C R V n x)

private def flattenContext : Data (Project.Term 16) :=
  ⟨.bound 4,.bound 5,.bound 6,.bound 7,.bound 8,.bound 9,.bound 10,.bound 11,.bound 12,.bound 13,.bound 14,.bound 15⟩
private def flattenSchema : Project.Delta0BinarySchema 14 where
  body := flattenPointFormula flattenContext (.bound 3) (.bound 2) (.bound 1) (.bound 0)
  freeClosed := by
    simp [flattenPointFormula, decodesFormula, memPairFormula, codeFormula, pairFormula,
      Data.weaken, Data.map, flattenContext, Project.Formula.existsMem,
      Project.Formula.forallMem, Definitional.Formula.FreeClosed]
  delta0 := flattenPointFormula_delta0 _ _ _ _ _

private theorem flattenSchema_iff {M : SetTheory.Structure.{u}} (he : Extensional M)
    (C : Data M.Domain) (R V n x : M.Domain) :
    Project.Formula.satisfies (((((dataEnv C).push R).push V).push n).push x) flattenSchema.body ↔ FlattenPoint M C R V n x := by
  rw [flattenSchema,flattenPointFormula_iff he]
  rfl

theorem flatten_family_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : Data M.Domain} (hC : Valid M C) {base R V : M.Domain} (hFamily : EnumeratorFamily M C base R V) :
    ∃ X f, Flattened M C R V X f := by
  obtain ⟨f,hSupport,hRaw⟩ := relation_comprehension_d hM flattenSchema (((dataEnv C).push R).push V) C.omega C.carrier
  have hFull (n x : M.Domain) : MemPair M f n x ↔ M.mem n C.omega ∧ M.mem x C.carrier ∧ FlattenPoint M C R V n x := by
    simpa only [flattenSchema_iff hM.1] using hRaw n x
  have hGraph : Graph M f C.omega C.carrier := by
    refine ⟨hSupport,?_,?_⟩
    · intro n hn
      obtain ⟨i,hi,j,hj,hDecode⟩ := decode_total hC hn
      obtain ⟨E,hEV,hAt⟩ := hFamily.graph.total i hi
      obtain ⟨x,hx,hEx⟩ := (hFamily.values i hi E hAt).total j hj
      exact ⟨x,hx,(hFull n x).mpr ⟨hn,hx,i,hi,j,hj,hDecode,E,hEV,hAt,hEx⟩⟩
    · intro n x y hnx hny
      obtain ⟨_,_,i,hi,j,_,hDecode,E,_,hAt,hEx⟩ := (hFull n x).mp hnx
      obtain ⟨_,_,i',_,j',_,hDecode',E',_,hAt',hEy⟩ := (hFull n y).mp hny
      obtain ⟨his,hjs⟩ := decode_unique hM.1 hC hDecode hDecode'
      subst i'
      subst j'
      have hEs := hFamily.graph.unique i E E' hAt hAt'
      subst E'
      exact (hFamily.values i hi E hAt).unique j x y hEx hEy
  obtain ⟨X,hX,hOnto⟩ := function_range_countable_d hM hGraph
  refine ⟨X,f,hGraph,hOnto,?_,?_⟩
  · intro x
    rw [hX x]
    constructor
    · rintro ⟨n,hn,hnx⟩
      obtain ⟨_,_,i,hi,j,hj,_,E,hEV,hAt,hEx⟩ := (hFull n x).mp hnx
      exact ⟨i,hi,E,hEV,hAt,j,hj,hEx⟩
    · rintro ⟨i,hi,E,hEV,hAt,j,hj,hEx⟩
      obtain ⟨n,hn,hDecode⟩ := decode_onto_d hM hC hi hj
      have hx := ((hFamily.values i hi E hAt).bounds hM.1 hEx).2
      exact ⟨n,hn,(hFull n x).mpr ⟨hn,hx,i,hi,j,hj,hDecode,E,hEV,hAt,hEx⟩⟩
  · intro n hn x hx
    exact (hFull n x).trans ⟨fun h => h.2.2,fun h => ⟨hn,hx,h⟩⟩

end KP1Y.Closure
