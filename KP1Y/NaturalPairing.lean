import KP1Y.SquareBounds
import KP1Y.Countability

/-! KPω 内的实际 ω→ω² 满射，并保证解码坐标不大于输入编号。 -/
namespace KP1Y.Naturals
open YesMetaZFC YesMetaZFC.SetTheory YesMetaZFC.SetTheory.Definitional
open KP1Y.Kuratowski KP1Y.Functions KP1Y.Cardinal
universe u

structure NaturalPairing (M : SetTheory.Structure.{u}) (ω P f : M.Domain) : Prop where
  product : IsProduct M P ω ω
  graph : Graph M f ω P
  onto : Onto M f ω P
  bounds : ∀ n, M.mem n ω → ∀ p, M.mem p P → MemPair M f n p →
    ∀ x, M.mem x ω → ∀ y, M.mem y ω → Codes M p x y → M.MemberSubset x n ∧ M.MemberSubset y n

theorem natural_pairing_exists_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {ω : M.Domain} (hω : M.IsOmega ω) : ∃ P f, NaturalPairing M ω P f := by
  obtain ⟨zero,hEmpty,hZero⟩ := hω.1.1
  obtain ⟨P,base,H,hT⟩ := square_trace_exists_d hM hω hZero
  have hOnto : Onto M H ω P := by
    refine ⟨hT.iterator.graph.support,hT.iterator.graph.total,
      fun i _ x _ y _ hix hiy => hT.iterator.graph.unique i x y hix hiy,?_⟩
    intro p hp
    obtain ⟨x,hx,y,hy,hCode⟩ := (hT.pairs p).mp hp
    obtain ⟨q,_,hCode',i,hi,hAt⟩ := square_all_pairs_d hM hω hT hZero hEmpty x hx y hy
    have hpq := codes_unique hM.1 hCode hCode'
    subst q
    exact ⟨i,hi,hAt⟩
  exact ⟨P,H,hT.pairs,hT.iterator.graph,hOnto,square_coordinate_bounds_d hM hω hT hEmpty⟩

theorem NaturalPairing.decode_before {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {ω P f n next p x y : M.Domain} (hω : M.IsOmega ω) (hPair : NaturalPairing M ω P f)
    (hn : M.mem n ω) (hSucc : M.SuccessorOf next n) (hAt : MemPair M f n p) (hCode : Codes M p x y) : M.mem x next := by
  have hp := (hPair.graph.bounds hM.1 hAt).2
  obtain ⟨a,ha,b,hb,hCode'⟩ := (hPair.product p).mp hp
  obtain ⟨hxa,hyb⟩ := codes_injective hM.1 hCode hCode'
  subst a
  subst b
  have hωOrd := omega_isOrdinal_d hM hω
  exact ordinal_le_mem_successor_d hM (hωOrd.mem ha) (hωOrd.mem hn) (hPair.bounds n hn p hp hAt x ha y hb hCode).1 hSucc

def pairProductFormula {n : Nat} (P ω : Project.Term n) : Project.Formula 1 n :=
  .forallE (.iff (.mem (.bound 0) P.weaken) (Project.Formula.existsMem ω.weaken
    (Project.Formula.existsMem ω.weaken.weaken (codeFormula (.bound 2) (.bound 1) (.bound 0)))))

theorem pairProductFormula_iff {M : SetTheory.Structure.{u}} (he : Extensional M) {n : Nat}
    (env : Env M n) (P ω : Project.Term n) : Project.Formula.satisfies env (pairProductFormula P ω) ↔
      IsProduct M (P.eval env) (ω.eval env) (ω.eval env) := by
  simp only [pairProductFormula, Project.Formula.satisfies_forall_iff,
    Project.Formula.satisfies_iff_iff, Project.Formula.satisfies_mem_iff,
    Project.Formula.satisfies_existsMem_iff, codeFormula_iff he, Definitional.Term.eval_weaken]
  rfl

def pairBoundsFormula {n : Nat} (ω P f : Project.Term n) : Project.Formula 1 n :=
  Project.Formula.forallMem ω (Project.Formula.forallMem P.weaken
    (.imp (memPairFormula f.weaken.weaken (.bound 1) (.bound 0))
      (Project.Formula.forallMem ω.weaken.weaken (Project.Formula.forallMem ω.weaken.weaken.weaken
        (.imp (codeFormula (.bound 2) (.bound 1) (.bound 0))
          (.conj (Project.Formula.subset (.bound 1) (.bound 3)) (Project.Formula.subset (.bound 0) (.bound 3))))))))

theorem pairBoundsFormula_iff {M : SetTheory.Structure.{u}} (he : Extensional M) {n : Nat}
    (env : Env M n) (ω P f : Project.Term n) : Project.Formula.satisfies env (pairBoundsFormula ω P f) ↔
      ∀ k, M.mem k (ω.eval env) → ∀ p, M.mem p (P.eval env) → MemPair M (f.eval env) k p →
        ∀ x, M.mem x (ω.eval env) → ∀ y, M.mem y (ω.eval env) →
          Codes M p x y → M.MemberSubset x k ∧ M.MemberSubset y k := by
  simp only [pairBoundsFormula, Project.Formula.satisfies_forallMem_iff,
    Project.Formula.satisfies_imp_iff, Project.Formula.satisfies_conj_iff, Project.Formula.satisfies_subset_iff,
    memPairFormula_iff he, codeFormula_iff he, Definitional.Term.eval_weaken]
  rfl

def pairingCore : Project.Formula 1 1 :=
  .imp (Project.Formula.isOmega (.bound 0)) (.existsE (.existsE
    (.conj (pairProductFormula (.bound 1) (.bound 2))
      (.conj (graphFormula (.bound 0) (.bound 2) (.bound 1))
        (.conj (ontoFormula (.bound 0) (.bound 2) (.bound 1)) (pairBoundsFormula (.bound 2) (.bound 1) (.bound 0)))))))

def pairingSentence : Project.Sentence := Project.Sentence.forallClosure pairingCore (by
  simp [pairingCore, pairProductFormula, pairBoundsFormula, graphFormula, ontoFormula,
    memPairFormula, codeFormula, pairFormula, Project.Formula.isOmega, Project.Formula.isInductive,
    Project.Formula.isEmpty, Project.Formula.isSuccessor, Project.Formula.forallMem,
    Project.Formula.existsMem, Definitional.Formula.FreeClosed])

theorem natural_pairing_derivable : KP1Y.Derives pairingSentence := by
  apply KP1Y.derives_of_all_models
  intro M hM free
  apply (Project.Formula.satisfies_forallClosure_iff free pairingCore).mpr
  intro bound
  simp only [pairingCore, Project.Formula.satisfies_imp_iff, Project.Formula.satisfies_isOmega_iff,
    Project.Formula.satisfies_exists_iff, Project.Formula.satisfies_conj_iff,
    pairProductFormula_iff hM.1, graphFormula_iff hM.1, ontoFormula_iff hM.1, pairBoundsFormula_iff hM.1]
  intro hω
  obtain ⟨P,f,h⟩ := natural_pairing_exists_d hM hω
  exact ⟨P,f,h.product,h.graph,h.onto,h.bounds⟩

end KP1Y.Naturals
