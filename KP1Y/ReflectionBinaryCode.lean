import KP1Y.ReflectionAtomEvaluation

/-! 等号/严格序原子的小型代码接口，只保留实际相关的0/1/2及变量空间参数。 -/
namespace KP1Y.ReflectionModel
open YesMetaZFC YesMetaZFC.SetTheory YesMetaZFC.SetTheory.Definitional
open KP1Y.Kuratowski KP1Y.Functions KP1Y.Satisfaction
universe u

def binaryKind (strict : Bool) : Fin 6 := if strict then 1 else 0

def pairValues {α : Type u} {n : Nat} (x y : α) (i : Fin n) : α := if i.val=0 then x else y

def BinaryCode (strict : Bool) (M : SetTheory.Structure.{u}) (zero one two Variables bound x y a : M.Domain) : Prop :=
  ∃ vars, M.mem vars Variables ∧ Codes M a (if strict then one else zero) vars ∧ Graph M vars two bound ∧
    MemPair M vars zero x ∧ MemPair M vars one y

def binaryCodeFormula {d : Nat} (strict : Bool) (zero one two Variables bound x y a : Project.Term d) : Project.Formula 1 d :=
  Project.Formula.existsMem Variables
    (.conj (codeFormula a.weaken (if strict then one.weaken else zero.weaken) (.bound 0))
      (.conj (graphFormula (.bound 0) two.weaken bound.weaken)
        (.conj (memPairFormula (.bound 0) zero.weaken x.weaken) (memPairFormula (.bound 0) one.weaken y.weaken))))

theorem binaryCodeFormula_delta0 {d : Nat} (strict : Bool) (zero one two Variables bound x y a : Project.Term d) :
    (binaryCodeFormula strict zero one two Variables bound x y a).IsDelta0 :=
  .existsMem _ (.conj (codeFormula_delta0 _ _ _) (.conj (graphFormula_delta0 _ _ _)
    (.conj (memPairFormula_delta0 _ _ _) (memPairFormula_delta0 _ _ _))))

theorem binaryCodeFormula_freeClosed {d : Nat} (strict : Bool) (zero one two Variables bound x y a : Project.Term d)
    (hz : zero.freeSupport=[]) (ho : one.freeSupport=[]) (ht : two.freeSupport=[]) (hv : Variables.freeSupport=[])
    (hb : bound.freeSupport=[]) (hx : x.freeSupport=[]) (hy : y.freeSupport=[]) (ha : a.freeSupport=[]) :
    (binaryCodeFormula strict zero one two Variables bound x y a).FreeClosed := by
  cases strict <;> simp [binaryCodeFormula,codeFormula,pairFormula,graphFormula,memPairFormula,
    Project.Formula.existsMem,Project.Formula.forallMem,Definitional.Formula.FreeClosed,hz,ho,ht,hv,hb,hx,hy,ha]

theorem binaryCodeFormula_iff {M : SetTheory.Structure.{u}} (he : Extensional M) {d : Nat} (e : Env M d)
    (strict : Bool) (zero one two Variables bound x y a : Project.Term d) :
    Project.Formula.satisfies e (binaryCodeFormula strict zero one two Variables bound x y a) ↔
      BinaryCode strict M (zero.eval e) (one.eval e) (two.eval e) (Variables.eval e) (bound.eval e) (x.eval e) (y.eval e) (a.eval e) := by
  cases strict <;> simp only [binaryCodeFormula,BinaryCode,Bool.false_eq_true,↓reduceIte,
    Project.Formula.satisfies_existsMem_iff,Project.Formula.satisfies_conj_iff,codeFormula_iff he,graphFormula_iff he,memPairFormula_iff he,Term.eval_weaken] <;> rfl

theorem binaryCode_iff_atomCode {M : SetTheory.Structure.{u}} (strict : Bool) (C : ArticleData M.Domain) (D : RelationalData M.Domain)
    (bound x y a : M.Domain) :
    BinaryCode strict M (C.numbers 0) (C.numbers 1) (C.numbers 2) D.variables bound x y a ↔
      AtomCode M C D (binaryKind strict) bound (pairValues x y) a := by
  cases strict <;> constructor
  · rintro ⟨vars,hv,hCode,hG,h0,h1⟩
    refine ⟨vars,hv,hCode,hG,?_⟩
    change ∀ i : Fin 2, MemPair M vars (C.numbers (tupleName (symbolArity 0) i)) (pairValues x y i)
    intro i
    have hi : i=0 ∨ i=1 := by omega
    rcases hi with rfl | rfl <;> assumption
  · rintro ⟨vars,hv,hCode,hG,hRows⟩
    exact ⟨vars,hv,hCode,hG,hRows (0 : Fin 2),hRows (1 : Fin 2)⟩
  · rintro ⟨vars,hv,hCode,hG,h0,h1⟩
    refine ⟨vars,hv,hCode,hG,?_⟩
    change ∀ i : Fin 2, MemPair M vars (C.numbers (tupleName (symbolArity 1) i)) (pairValues x y i)
    intro i
    have hi : i=0 ∨ i=1 := by omega
    rcases hi with rfl | rfl <;> assumption
  · rintro ⟨vars,hv,hCode,hG,hRows⟩
    exact ⟨vars,hv,hCode,hG,hRows (0 : Fin 2),hRows (1 : Fin 2)⟩

theorem binary_code_exists_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory) {C : ArticleData M.Domain} (hC : C.Valid M)
    {A : M.Domain} {D : RelationalData M.Domain} (hD : ArticleInterpretation M C A D) (strict : Bool) {bound x y : M.Domain}
    (hb : M.mem bound D.omega) (hx : M.mem x bound) (hy : M.mem y bound) :
    ∃ a, BinaryCode strict M (C.numbers 0) (C.numbers 1) (C.numbers 2) D.variables bound x y a := by
  obtain ⟨a,ha⟩ := atom_code_exists_d hM hC hD (binaryKind strict) hb (pairValues x y) (by
    intro i
    unfold pairValues
    split <;> assumption)
  exact ⟨a,(binaryCode_iff_atomCode strict C D bound x y a).mpr ha⟩

theorem BinaryCode.unique_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory) {C : ArticleData M.Domain} (hC : C.Valid M)
    {D : RelationalData M.Domain} {strict : Bool} {bound x y a b : M.Domain}
    (h : BinaryCode strict M (C.numbers 0) (C.numbers 1) (C.numbers 2) D.variables bound x y a)
    (h' : BinaryCode strict M (C.numbers 0) (C.numbers 1) (C.numbers 2) D.variables bound x y b) : a=b :=
  ((binaryCode_iff_atomCode strict C D bound x y a).mp h).unique hM.1 hC.numerals ((binaryCode_iff_atomCode strict C D bound x y b).mp h')

theorem BinaryCode.scoped_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory) {C : ArticleData M.Domain} (hC : C.Valid M)
    {A : M.Domain} {D : RelationalData M.Domain} (hD : ArticleInterpretation M C A D) {strict : Bool} {bound x y a : M.Domain}
    (hb : M.mem bound D.omega) (h : BinaryCode strict M (C.numbers 0) (C.numbers 1) (C.numbers 2) D.variables bound x y a) :
    ScopedAtom M D a bound := ((binaryCode_iff_atomCode strict C D bound x y a).mp h).scoped_d hM hC hD hb

theorem BinaryCode.code_mem_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory) {C : ArticleData M.Domain} (hC : C.Valid M)
    {A : M.Domain} {D : RelationalData M.Domain} (hD : ArticleInterpretation M C A D) {strict : Bool} {bound x y a : M.Domain}
    (hb : M.mem bound D.omega) (h : BinaryCode strict M (C.numbers 0) (C.numbers 1) (C.numbers 2) D.variables bound x y a) : M.mem a D.codes :=
  (h.scoped_d hM hC hD hb).code_mem hD.spaces

end KP1Y.ReflectionModel
