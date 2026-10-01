import KP1Y.ReflectionAtomicBridge

/-! 给定有限元数的变量名，实际形成唯一原子码并验证作用域；构造关系字面Δ₀。 -/
namespace KP1Y.ReflectionModel
open YesMetaZFC YesMetaZFC.SetTheory YesMetaZFC.SetTheory.Definitional
open KP1Y.Kuratowski KP1Y.Functions KP1Y.Assignments KP1Y.Satisfaction KP1Y.Signature
universe u

def AtomCode (M : SetTheory.Structure.{u}) (C : ArticleData M.Domain) (D : RelationalData M.Domain) (kind : Fin 6)
    (bound : M.Domain) (values : Fin (symbolArity kind).val → M.Domain) (a : M.Domain) : Prop :=
  ∃ vars, M.mem vars D.variables ∧ Codes M a (C.numbers kind.castSucc) vars ∧
    Graph M vars (C.numbers (symbolArity kind)) bound ∧
      ∀ i, MemPair M vars (C.numbers (tupleName (symbolArity kind) i)) (values i)

def atomCodeFormula {d : Nat} (C : ArticleData (Project.Term d)) (D : RelationalData (Project.Term d)) (kind : Fin 6)
    (bound : Project.Term d) (values : Fin (symbolArity kind).val → Project.Term d) (a : Project.Term d) : Project.Formula 1 d :=
  Project.Formula.existsMem D.variables
    (.conj (codeFormula a.weaken (C.numbers kind.castSucc).weaken (.bound 0))
      (.conj (graphFormula (.bound 0) (C.numbers (symbolArity kind)).weaken bound.weaken)
        (finConjunction (fun i => memPairFormula (.bound 0) (C.numbers (tupleName (symbolArity kind) i)).weaken (values i).weaken))))

theorem atomCodeFormula_delta0 {d : Nat} (C : ArticleData (Project.Term d)) (D : RelationalData (Project.Term d)) (kind : Fin 6)
    (bound : Project.Term d) (values : Fin (symbolArity kind).val → Project.Term d) (a : Project.Term d) :
    (atomCodeFormula C D kind bound values a).IsDelta0 := .existsMem _ (.conj (codeFormula_delta0 _ _ _)
      (.conj (graphFormula_delta0 _ _ _) (finConjunction_delta0 _ (fun _ => memPairFormula_delta0 _ _ _))))

theorem atomCodeFormula_freeClosed {d : Nat} {C : ArticleData (Project.Term d)} (hC : C.Closed)
    (D : RelationalData (Project.Term d)) (kind : Fin 6) (bound : Project.Term d)
    (values : Fin (symbolArity kind).val → Project.Term d) (a : Project.Term d)
    (hD : D.variables.freeSupport=[]) (hb : bound.freeSupport=[]) (hv : ∀ i, (values i).freeSupport=[]) (ha : a.freeSupport=[]) :
    (atomCodeFormula C D kind bound values a).FreeClosed := by
  have hRows := finConjunction_freeClosed (fun i => memPairFormula (Project.Term.bound (depth := d+1) 0)
    (C.numbers (tupleName (symbolArity kind) i)).weaken (values i).weaken) (by
      intro i
      simp [memPairFormula,codeFormula,pairFormula,Project.Formula.existsMem,Project.Formula.forallMem,
        Definitional.Formula.FreeClosed,hC.numbers,hv])
  simp only [atomCodeFormula,Project.Formula.existsMem,Definitional.Formula.FreeClosed]
  refine ⟨by simp [hD],?_,?_,hRows⟩ <;>
    simp [graphFormula,memPairFormula,codeFormula,pairFormula,Project.Formula.existsMem,Project.Formula.forallMem,
      Definitional.Formula.FreeClosed,hb,ha,hC.numbers]

theorem atomCodeFormula_iff {M : SetTheory.Structure.{u}} (he : Extensional M) {d : Nat} (e : Env M d)
    (C : ArticleData (Project.Term d)) (D : RelationalData (Project.Term d)) (kind : Fin 6) (bound : Project.Term d)
    (values : Fin (symbolArity kind).val → Project.Term d) (a : Project.Term d) :
    Project.Formula.satisfies e (atomCodeFormula C D kind bound values a) ↔
      AtomCode M (C.eval e) (D.eval e) kind (bound.eval e) (fun i => (values i).eval e) (a.eval e) := by
  simp only [atomCodeFormula,Project.Formula.satisfies_existsMem_iff,Project.Formula.satisfies_conj_iff,
    codeFormula_iff he,graphFormula_iff he,finConjunction_iff,memPairFormula_iff he,Term.eval_weaken]
  rfl

theorem atom_code_exists_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory) {C : ArticleData M.Domain} (hC : C.Valid M)
    {A : M.Domain} {D : RelationalData M.Domain} (hD : ArticleInterpretation M C A D) (kind : Fin 6) {bound : M.Domain}
    (hb : M.mem bound D.omega) (values : Fin (symbolArity kind).val → M.Domain) (hValues : ∀ i, M.mem (values i) bound) :
    ∃ a, AtomCode M C D kind bound values a := by
  obtain ⟨vars,hVars,hRows⟩ := fixed_tuple_exists_d hM hC.numerals (symbolArity kind) values hValues
  obtain ⟨a,hCode⟩ := codes_total hM (C.numbers kind.castSucc) vars
  have hn : M.mem (C.numbers (symbolArity kind)) D.omega := by
    rw [hD.omega]
    exact hC.numerals.natural (symbolArity kind)
  have hv : M.mem vars D.variables := (hD.spaces.variables vars).mpr ⟨C.numbers (symbolArity kind),hn,
    hVars.mono_values ((KP1Y.Naturals.omega_isOrdinal_d hM hD.spaces.omega).transitive bound hb)⟩
  exact ⟨a,vars,hv,hCode,hVars,hRows⟩

theorem AtomCode.unique {M : SetTheory.Structure.{u}} (he : Extensional M) {C : ArticleData M.Domain}
    (hN : Numerals M C.reflection.omega C.numbers) {D D' : RelationalData M.Domain} {kind : Fin 6} {bound bound' a b : M.Domain}
    {values : Fin (symbolArity kind).val → M.Domain} (h : AtomCode M C D kind bound values a) (h' : AtomCode M C D' kind bound' values b) : a=b := by
  obtain ⟨vars,_,hCode,hVars,hRows⟩ := h
  obtain ⟨vars',_,hCode',hVars',hRows'⟩ := h'
  have hvv' := fixed_tuple_unique he hN (symbolArity kind) values hVars hVars' hRows hRows'
  subst vars'
  exact codes_unique he hCode hCode'

theorem AtomCode.scoped_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory) {C : ArticleData M.Domain} (hC : C.Valid M)
    {A : M.Domain} {D : RelationalData M.Domain} (hD : ArticleInterpretation M C A D) {kind : Fin 6} {bound a : M.Domain}
    {values : Fin (symbolArity kind).val → M.Domain} (hb : M.mem bound D.omega) (h : AtomCode M C D kind bound values a) :
    ScopedAtom M D a bound := by
  obtain ⟨vars,_,hCode,hVars,_⟩ := h
  exact hD.scoped_code_d hM hC kind hb hVars hCode

theorem AtomCode.code_mem_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory) {C : ArticleData M.Domain} (hC : C.Valid M)
    {A : M.Domain} {D : RelationalData M.Domain} (hD : ArticleInterpretation M C A D) {kind : Fin 6} {bound a : M.Domain}
    {values : Fin (symbolArity kind).val → M.Domain} (hb : M.mem bound D.omega) (h : AtomCode M C D kind bound values a) : M.mem a D.codes :=
  (h.scoped_d hM hC hD hb).code_mem hD.spaces

end KP1Y.ReflectionModel
