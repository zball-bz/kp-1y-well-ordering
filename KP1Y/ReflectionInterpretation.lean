import KP1Y.ReflectionInterpretationSyntax
import KP1Y.RelationalSpaces
import KP1Y.CountableSegments
import KP1Y.RelationTables

/-! 构造实际解释集合和全部元数据，不把R/P/e的语义作为额外关系公理。 -/
namespace KP1Y.ReflectionModel
open YesMetaZFC YesMetaZFC.SetTheory YesMetaZFC.SetTheory.Definitional
open KP1Y.Kuratowski KP1Y.Functions KP1Y.Satisfaction KP1Y.Cardinal
universe u

structure ArticleInterpretation (M : SetTheory.Structure.{u}) (C : ArticleData M.Domain) (A : M.Domain)
    (D : RelationalData M.Domain) : Prop where
  omega : D.omega=C.reflection.omega
  carrier : D.carrier=A
  symbols : D.symbols=C.numbers 6
  spaces : DataSpaces M D
  arity : Graph M D.arity D.symbols D.omega
  arity_rows : ∀ r n, MemPair M D.arity r n ↔ Arity C.numbers r n
  support : RelationSupport M D.interpretation D.symbols D.values
  rows : ∀ r t, MemPair M D.interpretation r t ↔ Interprets M C A r t

theorem article_interpretation_exists_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory) {C : ArticleData M.Domain}
    (hC : C.Valid M) (A : M.Domain) : ∃ D, ArticleInterpretation M C A D := by
  obtain ⟨arity,hArity,hArityRows⟩ := signature_arity_exists_d hM hC.numerals
  obtain ⟨variables,values,codes,hSpaces⟩ := data_spaces_exists_d hM hC.numerals.omega A (C.numbers 6) arity (C.numbers 0)
  obtain ⟨interp,hSupport,hRaw⟩ := relation_comprehension_d hM relationSchema ((articleEnv C).push A) (C.numbers 6) values
  have hRows (r t : M.Domain) : MemPair M interp r t ↔ M.mem r (C.numbers 6) ∧ M.mem t values ∧ Interprets M C A r t := by
    simpa only [relationSchema_iff hM.1] using hRaw r t
  refine ⟨⟨C.reflection.omega,A,C.numbers 6,arity,interp,variables,values,codes⟩,rfl,rfl,rfl,
    ⟨hSpaces.omega,hSpaces.variables,hSpaces.values,hSpaces.codes⟩,hArity,hArityRows,hSupport,?_⟩
  intro r t
  constructor
  · intro hAt
    exact ((hRows r t).mp hAt).2.2
  · rintro ⟨i,hr,hMeaning⟩
    have hSymbol : M.mem r (C.numbers 6) := by
      rw [hr]
      exact hC.numerals.symbol_mem i
    have ht : M.mem t values := (hSpaces.values t).mpr ⟨C.numbers (symbolArity i),hC.numerals.natural (symbolArity i),hMeaning.1⟩
    exact (hRows r t).mpr ⟨hSymbol,ht,i,hr,hMeaning⟩

theorem ArticleInterpretation.kind_iff_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory) {C : ArticleData M.Domain}
    (hC : C.Valid M) {A : M.Domain} {D : RelationalData M.Domain} (h : ArticleInterpretation M C A D) (i : Fin 6) (t : M.Domain) :
    MemPair M D.interpretation (C.numbers i.castSucc) t ↔ Meaning M C A i t := by
  rw [h.rows]
  constructor
  · rintro ⟨j,hij,hBody⟩
    have hEq : i=j := Fin.ext (congrArg (fun x : Fin 7 => x.val) (hC.numerals.injective_d hM hij))
    subst j
    exact hBody
  · intro hBody
    exact ⟨i,rfl,hBody⟩

theorem ArticleInterpretation.arity_at_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory) {C : ArticleData M.Domain}
    (hC : C.Valid M) {A : M.Domain} {D : RelationalData M.Domain} (h : ArticleInterpretation M C A D) (i : Fin 6) (n : M.Domain) :
    MemPair M D.arity (C.numbers i.castSucc) n ↔ n=C.numbers (symbolArity i) :=
  (h.arity_rows _ n).trans (arity_at_symbol_d hM hC.numerals i n)

theorem ArticleInterpretation.symbols_countable_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory) {C : ArticleData M.Domain}
    (hC : C.Valid M) {A : M.Domain} {D : RelationalData M.Domain} (h : ArticleInterpretation M C A D) :
    ∃ E, Onto M E D.omega D.symbols := by
  have hSub : M.MemberSubset D.symbols D.omega := by
    rw [h.symbols,h.omega]
    intro r hr
    obtain ⟨i,hi⟩ := (hC.numerals.symbols_iff hM.1 r).mp hr
    exact hi ▸ hC.numerals.natural i.castSucc
  have hZero : M.mem (C.numbers 0) D.symbols := by
    rw [h.symbols]
    exact hC.numerals.symbol_mem 0
  exact subset_surjection_d hM hSub hZero

end KP1Y.ReflectionModel
