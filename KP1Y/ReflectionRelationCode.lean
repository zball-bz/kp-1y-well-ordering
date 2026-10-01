import KP1Y.ReflectionAtomEvaluation

/-! R/P 的紧凑原子码。这里四元/三元参数均为变量名，实际语义值由赋值读取。 -/
namespace KP1Y.ReflectionModel
open YesMetaZFC YesMetaZFC.SetTheory YesMetaZFC.SetTheory.Definitional
open KP1Y.Kuratowski KP1Y.Functions KP1Y.Satisfaction
universe u

def relationNames {α : Type u} (k η a b : α) (i : Fin 4) : α :=
  if i.val=0 then k else if i.val=1 then η else if i.val=2 then a else b

def topNames {α : Type u} (k η a : α) (i : Fin 3) : α :=
  if i.val=0 then k else if i.val=1 then η else a

def RelationCode (M : SetTheory.Structure.{u}) (zero one two three four Variables scope k η a b code : M.Domain) : Prop :=
  ∃ vars, M.mem vars Variables ∧ Codes M code two vars ∧ Graph M vars four scope ∧
    MemPair M vars zero k ∧ MemPair M vars one η ∧ MemPair M vars two a ∧ MemPair M vars three b

def TopCode (M : SetTheory.Structure.{u}) (zero one two three Variables scope k η a code : M.Domain) : Prop :=
  ∃ vars, M.mem vars Variables ∧ Codes M code three vars ∧ Graph M vars three scope ∧
    MemPair M vars zero k ∧ MemPair M vars one η ∧ MemPair M vars two a

def relationCodeFormula {d : Nat} (zero one two three four Variables scope k η a b code : Project.Term d) : Project.Formula 1 d :=
  Project.Formula.existsMem Variables
    (.conj (codeFormula code.weaken two.weaken (.bound 0))
      (.conj (graphFormula (.bound 0) four.weaken scope.weaken)
        (.conj (memPairFormula (.bound 0) zero.weaken k.weaken)
          (.conj (memPairFormula (.bound 0) one.weaken η.weaken)
            (.conj (memPairFormula (.bound 0) two.weaken a.weaken) (memPairFormula (.bound 0) three.weaken b.weaken))))))

def topCodeFormula {d : Nat} (zero one two three Variables scope k η a code : Project.Term d) : Project.Formula 1 d :=
  Project.Formula.existsMem Variables
    (.conj (codeFormula code.weaken three.weaken (.bound 0))
      (.conj (graphFormula (.bound 0) three.weaken scope.weaken)
        (.conj (memPairFormula (.bound 0) zero.weaken k.weaken)
          (.conj (memPairFormula (.bound 0) one.weaken η.weaken) (memPairFormula (.bound 0) two.weaken a.weaken)))))

theorem relationCodeFormula_delta0 {d : Nat} (zero one two three four Variables scope k η a b code : Project.Term d) :
    (relationCodeFormula zero one two three four Variables scope k η a b code).IsDelta0 :=
  .existsMem _ (.conj (codeFormula_delta0 _ _ _) (.conj (graphFormula_delta0 _ _ _)
    (.conj (memPairFormula_delta0 _ _ _) (.conj (memPairFormula_delta0 _ _ _)
      (.conj (memPairFormula_delta0 _ _ _) (memPairFormula_delta0 _ _ _))))))

theorem topCodeFormula_delta0 {d : Nat} (zero one two three Variables scope k η a code : Project.Term d) :
    (topCodeFormula zero one two three Variables scope k η a code).IsDelta0 :=
  .existsMem _ (.conj (codeFormula_delta0 _ _ _) (.conj (graphFormula_delta0 _ _ _)
    (.conj (memPairFormula_delta0 _ _ _) (.conj (memPairFormula_delta0 _ _ _) (memPairFormula_delta0 _ _ _)))))

theorem relationCodeFormula_freeClosed {d : Nat} (zero one two three four Variables scope k η a b code : Project.Term d)
    (hz : zero.freeSupport=[]) (ho : one.freeSupport=[]) (ht : two.freeSupport=[]) (hth : three.freeSupport=[])
    (hf : four.freeSupport=[]) (hv : Variables.freeSupport=[]) (hs : scope.freeSupport=[])
    (hk : k.freeSupport=[]) (hη : η.freeSupport=[]) (ha : a.freeSupport=[]) (hb : b.freeSupport=[]) (hc : code.freeSupport=[]) :
    (relationCodeFormula zero one two three four Variables scope k η a b code).FreeClosed := by
  simp [relationCodeFormula,codeFormula,pairFormula,graphFormula,memPairFormula,
    Project.Formula.existsMem,Project.Formula.forallMem,Definitional.Formula.FreeClosed,hz,ho,ht,hth,hf,hv,hs,hk,hη,ha,hb,hc]

theorem topCodeFormula_freeClosed {d : Nat} (zero one two three Variables scope k η a code : Project.Term d)
    (hz : zero.freeSupport=[]) (ho : one.freeSupport=[]) (ht : two.freeSupport=[]) (hth : three.freeSupport=[])
    (hv : Variables.freeSupport=[]) (hs : scope.freeSupport=[])
    (hk : k.freeSupport=[]) (hη : η.freeSupport=[]) (ha : a.freeSupport=[]) (hc : code.freeSupport=[]) :
    (topCodeFormula zero one two three Variables scope k η a code).FreeClosed := by
  simp [topCodeFormula,codeFormula,pairFormula,graphFormula,memPairFormula,
    Project.Formula.existsMem,Project.Formula.forallMem,Definitional.Formula.FreeClosed,hz,ho,ht,hth,hv,hs,hk,hη,ha,hc]

theorem relationCodeFormula_iff {M : SetTheory.Structure.{u}} (he : Extensional M) {d : Nat} (e : Env M d)
    (zero one two three four Variables scope k η a b code : Project.Term d) :
    Project.Formula.satisfies e (relationCodeFormula zero one two three four Variables scope k η a b code) ↔
      RelationCode M (zero.eval e) (one.eval e) (two.eval e) (three.eval e) (four.eval e) (Variables.eval e)
        (scope.eval e) (k.eval e) (η.eval e) (a.eval e) (b.eval e) (code.eval e) := by
  simp only [relationCodeFormula,RelationCode,Project.Formula.satisfies_existsMem_iff,
    Project.Formula.satisfies_conj_iff,codeFormula_iff he,graphFormula_iff he,memPairFormula_iff he,Term.eval_weaken]
  rfl

theorem topCodeFormula_iff {M : SetTheory.Structure.{u}} (he : Extensional M) {d : Nat} (e : Env M d)
    (zero one two three Variables scope k η a code : Project.Term d) :
    Project.Formula.satisfies e (topCodeFormula zero one two three Variables scope k η a code) ↔
      TopCode M (zero.eval e) (one.eval e) (two.eval e) (three.eval e) (Variables.eval e)
        (scope.eval e) (k.eval e) (η.eval e) (a.eval e) (code.eval e) := by
  simp only [topCodeFormula,TopCode,Project.Formula.satisfies_existsMem_iff,
    Project.Formula.satisfies_conj_iff,codeFormula_iff he,graphFormula_iff he,memPairFormula_iff he,Term.eval_weaken]
  rfl

theorem relationCode_iff_atomCode {M : SetTheory.Structure.{u}} (C : ArticleData M.Domain) (D : RelationalData M.Domain)
    (scope k η a b code : M.Domain) :
    RelationCode M (C.numbers 0) (C.numbers 1) (C.numbers 2) (C.numbers 3) (C.numbers 4) D.variables scope k η a b code ↔
      AtomCode M C D 2 scope (relationNames k η a b) code := by
  constructor
  · rintro ⟨vars,hv,hCode,hG,h0,h1,h2,h3⟩
    refine ⟨vars,hv,hCode,hG,?_⟩
    change ∀ i : Fin 4, MemPair M vars (C.numbers (tupleName (symbolArity 2) i)) (relationNames k η a b i)
    intro i
    have hi : i=0 ∨ i=1 ∨ i=2 ∨ i=3 := by omega
    rcases hi with rfl | rfl | rfl | rfl <;> assumption
  · rintro ⟨vars,hv,hCode,hG,hRows⟩
    exact ⟨vars,hv,hCode,hG,hRows (0 : Fin 4),hRows (1 : Fin 4),hRows (2 : Fin 4),hRows (3 : Fin 4)⟩

theorem topCode_iff_atomCode {M : SetTheory.Structure.{u}} (C : ArticleData M.Domain) (D : RelationalData M.Domain)
    (scope k η a code : M.Domain) :
    TopCode M (C.numbers 0) (C.numbers 1) (C.numbers 2) (C.numbers 3) D.variables scope k η a code ↔
      AtomCode M C D 3 scope (topNames k η a) code := by
  constructor
  · rintro ⟨vars,hv,hCode,hG,h0,h1,h2⟩
    refine ⟨vars,hv,hCode,hG,?_⟩
    change ∀ i : Fin 3, MemPair M vars (C.numbers (tupleName (symbolArity 3) i)) (topNames k η a i)
    intro i
    have hi : i=0 ∨ i=1 ∨ i=2 := by omega
    rcases hi with rfl | rfl | rfl <;> assumption
  · rintro ⟨vars,hv,hCode,hG,hRows⟩
    exact ⟨vars,hv,hCode,hG,hRows (0 : Fin 3),hRows (1 : Fin 3),hRows (2 : Fin 3)⟩

theorem relation_code_exists_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory) {C : ArticleData M.Domain} (hC : C.Valid M)
    {A : M.Domain} {D : RelationalData M.Domain} (hD : ArticleInterpretation M C A D) {scope k η a b : M.Domain}
    (hs : M.mem scope D.omega) (hk : M.mem k scope) (hη : M.mem η scope) (ha : M.mem a scope) (hb : M.mem b scope) :
    ∃ code, RelationCode M (C.numbers 0) (C.numbers 1) (C.numbers 2) (C.numbers 3) (C.numbers 4) D.variables scope k η a b code := by
  obtain ⟨code,hCode⟩ := atom_code_exists_d hM hC hD 2 hs (relationNames k η a b) (by
    intro i
    simp only [relationNames]
    split <;> first | assumption | (split <;> first | assumption | (split <;> assumption)))
  exact ⟨code,(relationCode_iff_atomCode C D scope k η a b code).mpr hCode⟩

theorem top_code_exists_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory) {C : ArticleData M.Domain} (hC : C.Valid M)
    {A : M.Domain} {D : RelationalData M.Domain} (hD : ArticleInterpretation M C A D) {scope k η a : M.Domain}
    (hs : M.mem scope D.omega) (hk : M.mem k scope) (hη : M.mem η scope) (ha : M.mem a scope) :
    ∃ code, TopCode M (C.numbers 0) (C.numbers 1) (C.numbers 2) (C.numbers 3) D.variables scope k η a code := by
  obtain ⟨code,hCode⟩ := atom_code_exists_d hM hC hD 3 hs (topNames k η a) (by
    intro i
    simp only [topNames]
    split <;> first | assumption | (split <;> assumption))
  exact ⟨code,(topCode_iff_atomCode C D scope k η a code).mpr hCode⟩

theorem RelationCode.unique_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory) {C : ArticleData M.Domain} (hC : C.Valid M)
    {D D' : RelationalData M.Domain} {scope scope' k η a b code code' : M.Domain}
    (h : RelationCode M (C.numbers 0) (C.numbers 1) (C.numbers 2) (C.numbers 3) (C.numbers 4) D.variables scope k η a b code)
    (h' : RelationCode M (C.numbers 0) (C.numbers 1) (C.numbers 2) (C.numbers 3) (C.numbers 4) D'.variables scope' k η a b code') : code=code' :=
  ((relationCode_iff_atomCode C D scope k η a b code).mp h).unique hM.1 hC.numerals
    ((relationCode_iff_atomCode C D' scope' k η a b code').mp h')

theorem TopCode.unique_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory) {C : ArticleData M.Domain} (hC : C.Valid M)
    {D D' : RelationalData M.Domain} {scope scope' k η a code code' : M.Domain}
    (h : TopCode M (C.numbers 0) (C.numbers 1) (C.numbers 2) (C.numbers 3) D.variables scope k η a code)
    (h' : TopCode M (C.numbers 0) (C.numbers 1) (C.numbers 2) (C.numbers 3) D'.variables scope' k η a code') : code=code' :=
  ((topCode_iff_atomCode C D scope k η a code).mp h).unique hM.1 hC.numerals
    ((topCode_iff_atomCode C D' scope' k η a code').mp h')

theorem RelationCode.scoped_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory) {C : ArticleData M.Domain} (hC : C.Valid M)
    {A : M.Domain} {D : RelationalData M.Domain} (hD : ArticleInterpretation M C A D) {scope k η a b code : M.Domain}
    (hs : M.mem scope D.omega)
    (h : RelationCode M (C.numbers 0) (C.numbers 1) (C.numbers 2) (C.numbers 3) (C.numbers 4) D.variables scope k η a b code) :
    ScopedAtom M D code scope := ((relationCode_iff_atomCode C D scope k η a b code).mp h).scoped_d hM hC hD hs

theorem TopCode.scoped_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory) {C : ArticleData M.Domain} (hC : C.Valid M)
    {A : M.Domain} {D : RelationalData M.Domain} (hD : ArticleInterpretation M C A D) {scope k η a code : M.Domain}
    (hs : M.mem scope D.omega)
    (h : TopCode M (C.numbers 0) (C.numbers 1) (C.numbers 2) (C.numbers 3) D.variables scope k η a code) :
    ScopedAtom M D code scope := ((topCode_iff_atomCode C D scope k η a code).mp h).scoped_d hM hC hD hs

theorem RelationCode.code_mem_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory) {C : ArticleData M.Domain} (hC : C.Valid M)
    {A : M.Domain} {D : RelationalData M.Domain} (hD : ArticleInterpretation M C A D) {scope k η a b code : M.Domain}
    (hs : M.mem scope D.omega)
    (h : RelationCode M (C.numbers 0) (C.numbers 1) (C.numbers 2) (C.numbers 3) (C.numbers 4) D.variables scope k η a b code) : M.mem code D.codes :=
  (h.scoped_d hM hC hD hs).code_mem hD.spaces

theorem TopCode.code_mem_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory) {C : ArticleData M.Domain} (hC : C.Valid M)
    {A : M.Domain} {D : RelationalData M.Domain} (hD : ArticleInterpretation M C A D) {scope k η a code : M.Domain}
    (hs : M.mem scope D.omega)
    (h : TopCode M (C.numbers 0) (C.numbers 1) (C.numbers 2) (C.numbers 3) D.variables scope k η a code) : M.mem code D.codes :=
  (h.scoped_d hM hC hD hs).code_mem hD.spaces

end KP1Y.ReflectionModel
