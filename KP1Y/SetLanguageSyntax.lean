import KP1Y.RelationalSpaces
import KP1Y.BinaryTuples

/-! 纯集合语言的两个二元关系：对象模型中的等号与隶属。 -/
namespace KP1Y.SetLanguage
open YesMetaZFC YesMetaZFC.SetTheory YesMetaZFC.SetTheory.Definitional
open KP1Y.Kuratowski KP1Y.Functions KP1Y.Naturals KP1Y.Satisfaction
universe u

def SetAtom (M : SetTheory.Structure.{u}) (A zero one two r t : M.Domain) : Prop :=
  Graph M t two A ∧ ∃ x, M.mem x A ∧ ∃ y, M.mem y A ∧
    MemPair M t zero x ∧ MemPair M t one y ∧
      ((r=zero ∧ x=y) ∨ (r=one ∧ M.mem x y))

def setAtomFormula {n : Nat} (A zero one two r t : Project.Term n) : Project.Formula 1 n :=
  .conj (graphFormula t two A)
    (Project.Formula.existsMem A (Project.Formula.existsMem A.weaken
      (.conj (memPairFormula t.weaken.weaken zero.weaken.weaken (.bound 1))
        (.conj (memPairFormula t.weaken.weaken one.weaken.weaken (.bound 0))
          (.disj (.conj (Project.Formula.extensionalEq r.weaken.weaken zero.weaken.weaken)
              (Project.Formula.extensionalEq (.bound 1) (.bound 0)))
            (.conj (Project.Formula.extensionalEq r.weaken.weaken one.weaken.weaken)
              (.mem (.bound 1) (.bound 0))))))))

theorem setAtomFormula_delta0 {n : Nat} (A zero one two r t : Project.Term n) :
    (setAtomFormula A zero one two r t).IsDelta0 :=
  .conj (graphFormula_delta0 _ _ _) (.existsMem _ (.existsMem _
    (.conj (memPairFormula_delta0 _ _ _) (.conj (memPairFormula_delta0 _ _ _)
      (.disj (.conj (.atom _ _ _) (.atom _ _ _)) (.conj (.atom _ _ _) (.mem _ _)))))))

theorem setAtomFormula_iff {M : SetTheory.Structure.{u}} (he : Extensional M) {n : Nat}
    (env : Env M n) (A zero one two r t : Project.Term n) :
    Project.Formula.satisfies env (setAtomFormula A zero one two r t) ↔
      SetAtom M (A.eval env) (zero.eval env) (one.eval env) (two.eval env) (r.eval env) (t.eval env) := by
  simp only [setAtomFormula, Project.Formula.satisfies_conj_iff,
    Project.Formula.satisfies_existsMem_iff, Project.Formula.satisfies_disj_iff,
    Project.Formula.satisfies_extensionalEq_iff_eq he, Project.Formula.satisfies_mem_iff,
    graphFormula_iff he, memPairFormula_iff he, Definitional.Term.eval_weaken]
  rfl

theorem set_atom_iff {M : SetTheory.Structure.{u}} (he : Extensional M)
    {A zero one two r t x y : M.Domain} (ht : Graph M t two A)
    (h0 : MemPair M t zero x) (h1 : MemPair M t one y) :
    SetAtom M A zero one two r t ↔ (r=zero ∧ x=y) ∨ (r=one ∧ M.mem x y) := by
  constructor
  · rintro ⟨_,x',_,y',_,h0',h1',h⟩
    have hx := ht.unique zero x' x h0' h0
    have hy := ht.unique one y' y h1' h1
    subst x'
    subst y'
    exact h
  · intro h
    exact ⟨ht,x,(ht.bounds he h0).2,y,(ht.bounds he h1).2,h0,h1,h⟩

theorem equality_atom_iff {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {ω A zero one two t x y : M.Domain} (hN : SmallNaturals M ω zero one two)
    (ht : Graph M t two A) (h0 : MemPair M t zero x) (h1 : MemPair M t one y) :
    SetAtom M A zero one two zero t ↔ x=y := by
  rw [set_atom_iff hM.1 ht h0 h1]
  simp only [true_and, or_false, hN.zero_ne_one hM, false_and]

theorem membership_atom_iff {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {ω A zero one two t x y : M.Domain} (hN : SmallNaturals M ω zero one two)
    (ht : Graph M t two A) (h0 : MemPair M t zero x) (h1 : MemPair M t one y) :
    SetAtom M A zero one two one t ↔ M.mem x y := by
  rw [set_atom_iff hM.1 ht h0 h1]
  simp only [true_and, false_or, (hN.zero_ne_one hM).symm, false_and]

end KP1Y.SetLanguage
