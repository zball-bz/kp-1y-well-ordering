import KP1Y.IterationSyntax
import KP1Y.AssignmentCarriers

/-! 在任意 KPω 模型中形成真正的 ω 长迭代函数，供内部配对和闭包枚举使用。 -/
namespace KP1Y.Iteration
open YesMetaZFC YesMetaZFC.SetTheory YesMetaZFC.SetTheory.Definitional
open KP1Y.Kuratowski KP1Y.Functions
universe u

structure Iterator (M : SetTheory.Structure.{u}) (next : M.Domain → M.Domain → Prop)
    (ω S base H : M.Domain) : Prop where
  graph : Graph M H ω S
  initial : ∀ e, M.mem e ω → (∀ x, ¬M.mem x e) → MemPair M H e base
  transition : ∀ i j x y, M.SuccessorOf j i → MemPair M H i x → MemPair M H j y → next x y

theorem iterator_exists_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory) {n : Nat}
    (φ : Project.Delta0BinarySchema n) (env : Env M n) {ω S base : M.Domain} (hω : M.IsOmega ω)
    (hBase : M.mem base S) (hTotal : ∀ x, M.mem x S → ∃ y, M.mem y S ∧ nextDenote φ env x y)
    (hUnique : ∀ x, M.mem x S → ∀ y, M.mem y S → ∀ z, M.mem z S →
      nextDenote φ env x y → nextDenote φ env x z → y=z) :
    ∃ H, Iterator M (nextDenote φ env) ω S base H := by
  obtain ⟨H,V,Q,hH⟩ := KP1Y.SigmaRecursion.value_recursion_d hM (stateMatrix φ) ((env.push S).push base)
    (KP1Y.Naturals.omega_isOrdinal_d hM hω) (stateMatrix_total hM φ env hω hBase hTotal)
    (stateMatrix_functional hM φ env hω hUnique)
  have hStep : ∀ i, M.mem i ω → ∀ y, MemPair M H i y →
      ∃ P w, Prefix M P H i V ∧ StateStep M (nextDenote φ env) S base i P y w := by
    intro i hi y hiy
    obtain ⟨P,hPV,hQi⟩ := hH.prefixes.total i hi
    obtain ⟨hPref,w,_,hState⟩ := hH.obeys i hi P hPV y (hH.values.bounds hM.1 hiy).2 hQi hiy
    exact ⟨P,w,hPref,(stateMatrix_iff hM.1 φ env S base i P y w).mp hState⟩
  have hGraph : Graph M H ω S := KP1Y.Assignments.graph_tighten_values hH.values (by
    intro i y hiy
    obtain ⟨_,_,_,hState⟩ := hStep i (hH.values.bounds hM.1 hiy).1 y hiy
    exact hState.1)
  refine ⟨H,hGraph,?_,?_⟩
  · intro e heω hEmpty
    obtain ⟨y,_,hey⟩ := hGraph.total e heω
    obtain ⟨_,_,_,hState⟩ := hStep e heω y hey
    rcases hState.2.2 with ⟨_,hy⟩ | ⟨j,hj,_⟩
    · subst y
      exact hey
    · exact False.elim (hEmpty j hj)
  · intro i j x y hSucc hix hjy
    have hiω := (hGraph.bounds hM.1 hix).1
    have hjω := (hGraph.bounds hM.1 hjy).1
    have hxS := (hGraph.bounds hM.1 hix).2
    obtain ⟨P,w,hPref,hState⟩ := hStep j hjω y hjy
    rcases hState.2.2 with ⟨hEmpty,_⟩ | ⟨k,_,z,_,hSucc',hPz,hCase⟩
    · exact False.elim (hEmpty i hSucc.predecessor_mem)
    · have hik := Structure.SuccessorOf.predecessor_eq hM.1
        ((KP1Y.Naturals.omega_isOrdinal_d hM hω).mem hiω) hSucc hSucc'
      subst k
      have hiz := (hPref.all_rows hM.1 hH.values i hSucc.predecessor_mem z).mp hPz
      have hxz := hGraph.unique i x z hix hiz
      subst z
      rcases hCase with ⟨_,hNext⟩ | ⟨hNo,_⟩
      · exact hNext
      · exact False.elim (hNo hxS)

theorem iterator_next_d {M : SetTheory.Structure.{u}} (he : Extensional M)
    {next : M.Domain → M.Domain → Prop} {ω S base H i x y : M.Domain} (hω : M.IsOmega ω)
    (hH : Iterator M next ω S base H)
    (hUnique : ∀ a, M.mem a S → ∀ b, M.mem b S → ∀ c, M.mem c S → next a b → next a c → b=c)
    (hi : M.mem i ω) (hix : MemPair M H i x) (hy : M.mem y S) (hNext : next x y) :
    ∃ j, M.mem j ω ∧ M.SuccessorOf j i ∧ MemPair M H j y := by
  obtain ⟨j,hSucc,hj⟩ := hω.1.2 i hi
  obtain ⟨z,hz,hjz⟩ := hH.graph.total j hj
  have hyz := hUnique x (hH.graph.bounds he hix).2 y hy z hz hNext (hH.transition i j x z hSucc hix hjz)
  subst z
  exact ⟨j,hj,hSucc,hjz⟩

def Reached (M : SetTheory.Structure.{u}) (ω H x : M.Domain) : Prop := ∃ i, M.mem i ω ∧ MemPair M H i x

def reachedFormula {n : Nat} (ω H x : Project.Term n) : Project.Formula 1 n :=
  Project.Formula.existsMem ω (memPairFormula H.weaken (.bound 0) x.weaken)

theorem reachedFormula_delta0 {n : Nat} (ω H x : Project.Term n) : (reachedFormula ω H x).IsDelta0 :=
  .existsMem _ (memPairFormula_delta0 _ _ _)

theorem reachedFormula_iff {M : SetTheory.Structure.{u}} (he : Extensional M) {n : Nat}
    (env : Env M n) (ω H x : Project.Term n) :
    Project.Formula.satisfies env (reachedFormula ω H x) ↔ Reached M (ω.eval env) (H.eval env) (x.eval env) := by
  simp only [reachedFormula, Project.Formula.satisfies_existsMem_iff, memPairFormula_iff he, Definitional.Term.eval_weaken]
  rfl

theorem reached_next_d {M : SetTheory.Structure.{u}} (he : Extensional M)
    {next : M.Domain → M.Domain → Prop} {ω S base H x y : M.Domain} (hω : M.IsOmega ω)
    (hH : Iterator M next ω S base H)
    (hUnique : ∀ a, M.mem a S → ∀ b, M.mem b S → ∀ c, M.mem c S → next a b → next a c → b=c)
    (hx : Reached M ω H x) (hy : M.mem y S) (hNext : next x y) : Reached M ω H y := by
  obtain ⟨i,hi,hix⟩ := hx
  obtain ⟨j,hj,_,hjy⟩ := iterator_next_d he hω hH hUnique hi hix hy hNext
  exact ⟨j,hj,hjy⟩

end KP1Y.Iteration
