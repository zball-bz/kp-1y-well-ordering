import KP1Y.ReflectionNumerals
import KP1Y.FiniteSignatureFormulas

/-! 实际六符号签名：=、<、R、P、e的函数图、ω常量谓词，元数为2/2/4/3/3/1。 -/
namespace KP1Y.ReflectionModel
open YesMetaZFC YesMetaZFC.SetTheory YesMetaZFC.SetTheory.Definitional
open KP1Y.Kuratowski KP1Y.Functions KP1Y.Named KP1Y.Signature
universe u

def symbolArity (i : Fin 6) : Fin 7 := match i.val with
  | 0 => 2 | 1 => 2 | 2 => 4 | 3 => 3 | 4 => 3 | _ => 1

def Arity {α : Type u} (N : Numbers α) (r n : α) : Prop := ∃ i : Fin 6, r=N i.castSucc ∧ n=N (symbolArity i)

def arityFormula {d : Nat} (N : Numbers (Project.Term d)) (r n : Project.Term d) : Project.Formula 1 d :=
  finDisjunction (fun i : Fin 6 => .conj (Project.Formula.extensionalEq r (N i.castSucc)) (Project.Formula.extensionalEq n (N (symbolArity i))))

theorem arityFormula_delta0 {d : Nat} (N : Numbers (Project.Term d)) (r n : Project.Term d) : (arityFormula N r n).IsDelta0 :=
  finDisjunction_delta0 _ (fun _ => .conj (.atom _ _ _) (.atom _ _ _))

theorem arityFormula_freeClosed {d : Nat} (N : Numbers (Project.Term d)) (r n : Project.Term d)
    (hN : ∀ i, (N i).freeSupport=[]) (hr : r.freeSupport=[]) (hn : n.freeSupport=[]) : (arityFormula N r n).FreeClosed := by
  apply finDisjunction_freeClosed
  intro i
  simp [Definitional.Formula.FreeClosed,hN,hr,hn]

theorem arityFormula_iff {M : SetTheory.Structure.{u}} (he : Extensional M) {d : Nat} (env : Env M d)
    (N : Numbers (Project.Term d)) (r n : Project.Term d) : Project.Formula.satisfies env (arityFormula N r n) ↔
      Arity (fun i => (N i).eval env) (r.eval env) (n.eval env) := by
  simp only [arityFormula,finDisjunction_iff,Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_extensionalEq_iff_eq he]
  rfl

theorem arity_at_symbol_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory) {ω : M.Domain} {N : Numbers M.Domain}
    (hN : Numerals M ω N) (i : Fin 6) (n : M.Domain) : Arity N (N i.castSucc) n ↔ n=N (symbolArity i) := by
  constructor
  · rintro ⟨j,hij,hn⟩
    have hEq : i=j := Fin.ext (congrArg (fun x : Fin 7 => x.val) (hN.injective_d hM hij))
    subst j
    exact hn
  · intro hn
    exact ⟨i,rfl,hn⟩

theorem signature_arity_exists_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory) {ω : M.Domain} {N : Numbers M.Domain}
    (hN : Numerals M ω N) : ∃ A, Graph M A (N 6) ω ∧ ∀ r n, MemPair M A r n ↔ Arity N r n := by
  obtain ⟨A,hA,hRead⟩ := finite_assignment_exists_d hM hN.omega (fun i : Fin 6 => N (symbolArity i)) (fun i => hN.natural (symbolArity i))
  have hGraph : Graph M A (N 6) ω := by
    rw [hN.values 6]
    exact hA
  have hAt (i : Fin 6) : MemPair M A (N i.castSucc) (N (symbolArity i)) := by
    rw [hN.values i.castSucc]
    exact hRead i
  refine ⟨A,hGraph,?_⟩
  intro r n
  constructor
  · intro hRn
    obtain ⟨i,hi⟩ := (hN.symbols_iff hM.1 r).mp (hGraph.bounds hM.1 hRn).1
    subst r
    exact ⟨i,rfl,hGraph.unique (N i.castSucc) n (N (symbolArity i)) hRn (hAt i)⟩
  · rintro ⟨i,rfl,rfl⟩
    exact hAt i

end KP1Y.ReflectionModel
