import KP1Y.CountableSequences
import KP1Y.CountableUnions

/-! 可数闭包的一次性固定数据：配对、字词、操作索引及有限元组上的实际操作函数。 -/
namespace KP1Y.Closure
open YesMetaZFC YesMetaZFC.SetTheory YesMetaZFC.SetTheory.Definitional
open KP1Y.Kuratowski KP1Y.Functions KP1Y.Cardinal
universe u v

structure Data (α : Type u) where
  omega : α
  carrier : α
  pairs : α
  pairDecode : α
  words : α
  wordDecode : α
  operations : α
  operationDecode : α
  tuples : α
  keys : α
  applyOperation : α
  zero : α

def Data.map {α : Type u} {β : Type v} (C : Data α) (f : α → β) : Data β :=
  ⟨f C.omega,f C.carrier,f C.pairs,f C.pairDecode,f C.words,f C.wordDecode,
    f C.operations,f C.operationDecode,f C.tuples,f C.keys,f C.applyOperation,f C.zero⟩
def Data.weaken {n : Nat} (C : Data (Project.Term n)) : Data (Project.Term (n+1)) := C.map (fun t => t.weaken)
def Data.eval {M : SetTheory.Structure.{u}} {n : Nat} (C : Data (Project.Term n)) (env : Env M n) : Data M.Domain :=
  C.map (fun t => t.eval env)

theorem Data.eval_weaken {M : SetTheory.Structure.{u}} {n : Nat}
    (C : Data (Project.Term n)) (env : Env M n) (x : M.Domain) : C.weaken.eval (env.push x)=C.eval env := by
  cases C
  simp [Data.weaken,Data.eval,Data.map,Definitional.Term.eval_weaken]

structure Valid (M : SetTheory.Structure.{u}) (C : Data M.Domain) : Prop where
  omega : M.IsOmega C.omega
  pairing : KP1Y.Naturals.NaturalPairing M C.omega C.pairs C.pairDecode
  words : ∀ w, M.mem w C.words ↔ ∃ n, M.mem n C.omega ∧ Graph M w n C.omega
  wordDecode : Onto M C.wordDecode C.omega C.words
  operationDecode : Onto M C.operationDecode C.omega C.operations
  tuples : ∀ s, M.mem s C.tuples ↔ ∃ n, M.mem n C.omega ∧ Graph M s n C.carrier
  keys : IsProduct M C.keys C.operations C.tuples
  operation : Graph M C.applyOperation C.keys C.carrier
  zero_nat : M.mem C.zero C.omega
  zero_empty : ∀ x, ¬M.mem x C.zero

def Decodes (M : SetTheory.Structure.{u}) (C : Data M.Domain) (n i j : M.Domain) : Prop :=
  ∃ pair, M.mem pair C.pairs ∧ MemPair M C.pairDecode n pair ∧ Codes M pair i j

def decodesFormula {n : Nat} (C : Data (Project.Term n)) (index i j : Project.Term n) : Project.Formula 1 n :=
  Project.Formula.existsMem C.pairs (.conj (memPairFormula C.pairDecode.weaken index.weaken (.bound 0))
    (codeFormula (.bound 0) i.weaken j.weaken))

theorem decodesFormula_delta0 {n : Nat} (C : Data (Project.Term n)) (index i j : Project.Term n) :
    (decodesFormula C index i j).IsDelta0 :=
  .existsMem _ (.conj (memPairFormula_delta0 _ _ _) (codeFormula_delta0 _ _ _))

theorem decodesFormula_iff {M : SetTheory.Structure.{u}} (he : Extensional M) {n : Nat}
    (env : Env M n) (C : Data (Project.Term n)) (index i j : Project.Term n) :
    Project.Formula.satisfies env (decodesFormula C index i j) ↔
      Decodes M (C.eval env) (index.eval env) (i.eval env) (j.eval env) := by
  simp only [decodesFormula, Project.Formula.satisfies_existsMem_iff, Project.Formula.satisfies_conj_iff,
    memPairFormula_iff he, codeFormula_iff he, Definitional.Term.eval_weaken]
  rfl

theorem decode_total {M : SetTheory.Structure.{u}} {C : Data M.Domain} (hC : Valid M C)
    {n : M.Domain} (hn : M.mem n C.omega) : ∃ i, M.mem i C.omega ∧ ∃ j, M.mem j C.omega ∧ Decodes M C n i j := by
  obtain ⟨pair,hPair,hAt⟩ := hC.pairing.graph.total n hn
  obtain ⟨i,hi,j,hj,hCode⟩ := (hC.pairing.product pair).mp hPair
  exact ⟨i,hi,j,hj,pair,hPair,hAt,hCode⟩

theorem decode_unique {M : SetTheory.Structure.{u}} (he : Extensional M) {C : Data M.Domain} (hC : Valid M C)
    {n i j i' j' : M.Domain} (h : Decodes M C n i j) (h' : Decodes M C n i' j') : i=i' ∧ j=j' := by
  obtain ⟨pair,_,hAt,hCode⟩ := h
  obtain ⟨pair',_,hAt',hCode'⟩ := h'
  have hEq := hC.pairing.graph.unique n pair pair' hAt hAt'
  subst pair'
  exact codes_injective he hCode hCode'

theorem decode_onto_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory) {C : Data M.Domain} (hC : Valid M C)
    {i j : M.Domain} (hi : M.mem i C.omega) (hj : M.mem j C.omega) :
    ∃ n, M.mem n C.omega ∧ Decodes M C n i j := by
  obtain ⟨pair,hCode⟩ := codes_total hM i j
  have hPair := (hC.pairing.product pair).mpr ⟨i,hi,j,hj,hCode⟩
  obtain ⟨n,hn,hAt⟩ := hC.pairing.onto.2.2.2 pair hPair
  exact ⟨n,hn,pair,hPair,hAt,hCode⟩

end KP1Y.Closure
