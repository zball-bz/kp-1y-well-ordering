import KP1Y.ReflectionAtomCode

/-! 原子码在赋值上的求值：实际合成参数元组，并连接大/小结构的数学谓词。 -/
namespace KP1Y.ReflectionModel
open YesMetaZFC YesMetaZFC.SetTheory
open KP1Y.Kuratowski KP1Y.Functions KP1Y.Assignments KP1Y.Satisfaction
universe u

theorem AtomCode.evaluate_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory) {C : ArticleData M.Domain} (hC : C.Valid M)
    {A : M.Domain} {D : RelationalData M.Domain} (hD : ArticleInterpretation M C A D) {Atom : M.Domain} (hAtom : AtomicTable M D Atom)
    {kind : Fin 6} {bound a s : M.Domain} {values : Fin (symbolArity kind).val → M.Domain}
    (hb : M.mem bound D.omega) (hCode : AtomCode M C D kind bound values a) (hS : Graph M s bound A) :
    ∃ t, Graph M t (C.numbers (symbolArity kind)) A ∧
      (∀ i x, M.mem x A → (MemPair M t (C.numbers (tupleName (symbolArity kind) i)) x ↔ MemPair M s (values i) x)) ∧
      (MemPair M Atom a s ↔ Body M C kind t) := by
  obtain ⟨vars,_,hPair,hVars,hRows⟩ := hCode
  obtain ⟨t,hValue⟩ := tuple_value_exists_d hM hVars hS
  refine ⟨t,hValue.values,?_,hD.atom_body_d hM hC hAtom kind hb hPair hValue⟩
  intro i x hx
  have hi : M.mem (C.numbers (tupleName (symbolArity kind) i)) (C.numbers (symbolArity kind)) := hC.numerals.lt i.isLt
  exact hValue.rows _ hi (values i) (hVars.bounds hM.1 (hRows i)).2 x hx (hRows i)

theorem Height.evaluate_atom_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory) {C : ArticleData M.Domain} (hC : C.Valid M)
    {S : ArticleStructure M.Domain} (hS : S.Valid M C) {δ : M.Domain} {small : EvaluationData M.Domain} (h : Height M C S δ small)
    {kind : Fin 6} {bound a s : M.Domain} {values : Fin (symbolArity kind).val → M.Domain}
    (hb : M.mem bound S.context.omega) (hCode : AtomCode M C S.relations kind bound values a) (hAssign : Graph M s bound small.carrier) :
    ∃ t, Graph M t (C.numbers (symbolArity kind)) small.carrier ∧
      (∀ i x, M.mem x small.carrier → (MemPair M t (C.numbers (tupleName (symbolArity kind) i)) x ↔ MemPair M s (values i) x)) ∧
      (MemPair M small.atomic a s ↔ Body M C kind t) := by
  obtain ⟨vars,_,hPair,hVars,hRows⟩ := hCode
  obtain ⟨t,hValue⟩ := tuple_value_exists_d hM hVars hAssign
  refine ⟨t,hValue.values,?_,h.atom_body_d hM hC hS kind hb hPair hValue⟩
  intro i x hx
  have hi : M.mem (C.numbers (tupleName (symbolArity kind) i)) (C.numbers (symbolArity kind)) := hC.numerals.lt i.isLt
  exact hValue.rows _ hi (values i) (hVars.bounds hM.1 (hRows i)).2 x hx (hRows i)

end KP1Y.ReflectionModel
