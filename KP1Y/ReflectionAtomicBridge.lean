import KP1Y.ReflectionModelHeight
import KP1Y.ElementaryAtomicAgreement

/-! 实际原子代码/变量元组到数学关系的桥，含初等小结构的同一原子解释。 -/
namespace KP1Y.ReflectionModel
open YesMetaZFC YesMetaZFC.SetTheory
open KP1Y.Kuratowski KP1Y.Functions KP1Y.Assignments KP1Y.Satisfaction
universe u

theorem ArticleInterpretation.scoped_code_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory) {C : ArticleData M.Domain}
    (hC : C.Valid M) {A : M.Domain} {D : RelationalData M.Domain} (h : ArticleInterpretation M C A D)
    (i : Fin 6) {a vars bound : M.Domain} (hb : M.mem bound D.omega)
    (hVars : Graph M vars (C.numbers (symbolArity i)) bound) (hCode : Codes M a (C.numbers i.castSucc) vars) :
    ScopedAtom M D a bound := by
  have hr : M.mem (C.numbers i.castSucc) D.symbols := by
    rw [h.symbols]
    exact hC.numerals.symbol_mem i
  have hn : M.mem (C.numbers (symbolArity i)) D.omega := by
    rw [h.omega]
    exact hC.numerals.natural (symbolArity i)
  have hVarMem : M.mem vars D.variables := (h.spaces.variables vars).mpr
    ⟨C.numbers (symbolArity i),hn,hVars.mono_values ((KP1Y.Naturals.omega_isOrdinal_d hM h.spaces.omega).transitive bound hb)⟩
  exact ⟨C.numbers i.castSucc,hr,vars,hVarMem,hCode,C.numbers (symbolArity i),hn,(h.arity_at_d hM hC i _).mpr rfl,hVars⟩

theorem ArticleInterpretation.atom_body_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory) {C : ArticleData M.Domain}
    (hC : C.Valid M) {A : M.Domain} {D : RelationalData M.Domain} (h : ArticleInterpretation M C A D)
    {Atom : M.Domain} (hAtom : AtomicTable M D Atom) (i : Fin 6) {a vars s bound t : M.Domain}
    (hb : M.mem bound D.omega) (hCode : Codes M a (C.numbers i.castSucc) vars)
    (hValue : TupleValue M t vars s (C.numbers (symbolArity i)) bound A) :
    MemPair M Atom a s ↔ Body M C i t := by
  have hr : M.mem (C.numbers i.castSucc) D.symbols := by
    rw [h.symbols]
    exact hC.numerals.symbol_mem i
  have hn : M.mem (C.numbers (symbolArity i)) D.omega := by
    rw [h.omega]
    exact hC.numerals.natural (symbolArity i)
  have hArity := (h.arity_at_d hM hC i (C.numbers (symbolArity i))).mpr rfl
  have hValueD : TupleValue M t vars s (C.numbers (symbolArity i)) bound D.carrier :=
    Eq.mpr (congrArg (fun X => TupleValue M t vars s (C.numbers (symbolArity i)) bound X) h.carrier) hValue
  exact (atomic_table_correct hM h.spaces hAtom hr hCode hn hb hArity hValueD).trans (h.body_iff_d hM hC i hValue.values)

theorem Height.atomic_agreement_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory) {C : ArticleData M.Domain}
    {S : ArticleStructure M.Domain} (hS : S.Valid M C) {δ : M.Domain} {small : EvaluationData M.Domain}
    (h : Height M C S δ small) : AtomicAgreement M S.context S.relations small S.large :=
  h.elementary.atomic_agreement_d hM hS.context hS.interpretation.spaces h.valid hS.large hS.link.codes_bound

theorem Height.atom_body_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory) {C : ArticleData M.Domain}
    (hC : C.Valid M) {S : ArticleStructure M.Domain} (hS : S.Valid M C) {δ : M.Domain} {small : EvaluationData M.Domain}
    (h : Height M C S δ small) (i : Fin 6) {a vars s bound t : M.Domain}
    (hb : M.mem bound S.context.omega) (hCode : Codes M a (C.numbers i.castSucc) vars)
    (hValue : TupleValue M t vars s (C.numbers (symbolArity i)) bound small.carrier) :
    MemPair M small.atomic a s ↔ Body M C i t := by
  have hbD := Eq.mp (congrArg (M.mem bound) hS.link.omega_eq) hb
  have hScope := hS.interpretation.scoped_code_d hM hC i hbD hValue.variables hCode
  have hAgree := h.atomic_agreement_d hM hS a bound hScope hb s hValue.source
  have hSub : M.MemberSubset small.carrier C.top := by
    intro x hx
    exact Eq.mp (congrArg (M.mem x) hS.carrier) (h.elementary.carrier_subset x hx)
  exact hAgree.trans (hS.interpretation.atom_body_d hM hC hS.atomic i hbD hCode (tuple_value_enlarge hM.1 hSub hValue))

end KP1Y.ReflectionModel
