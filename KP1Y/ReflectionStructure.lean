import KP1Y.ReflectionInterpretationSemantics
import KP1Y.CountableSyntax
import KP1Y.ElementaryHeight

/-! 将具体六符号解释装配为实际语法、满意度、程序枚举和最小见证Skolem函数。 -/
namespace KP1Y.ReflectionModel
open YesMetaZFC YesMetaZFC.SetTheory YesMetaZFC.SetTheory.Definitional
open KP1Y.Kuratowski KP1Y.Functions KP1Y.Satisfaction KP1Y.Cardinal
universe u

structure ArticleStructure (α : Type u) where
  relations : RelationalData α
  context : Context α
  large : EvaluationData α
  bounds : SkolemBounds α
  skolem : α
  programs : α

structure ArticleStructure.Valid (M : SetTheory.Structure.{u}) (C : ArticleData M.Domain) (S : ArticleStructure M.Domain) : Prop where
  interpretation : ArticleInterpretation M C C.top S.relations
  context : ContextSpaces M S.context
  link : RelationalContext M S.relations S.large.atomic S.context
  large : S.large.Valid S.context
  carrier : S.large.carrier=C.top
  atomic : AtomicTable M S.relations S.large.atomic
  bounds : SkolemBoundsValid M S.context S.large S.bounds
  skolem : SkolemFunction M S.context S.large S.bounds (C.numbers 0) S.skolem
  programs : Onto M S.programs S.context.omega S.context.programs

theorem ArticleStructure.Valid.omega {M : SetTheory.Structure.{u}} {C : ArticleData M.Domain} {S : ArticleStructure M.Domain}
    (h : S.Valid M C) : S.context.omega=C.reflection.omega := h.link.omega_eq.trans h.interpretation.omega

theorem ArticleStructure.Valid.relational_carrier {M : SetTheory.Structure.{u}} {C : ArticleData M.Domain} {S : ArticleStructure M.Domain}
    (h : S.Valid M C) : S.large.carrier=S.relations.carrier := h.carrier.trans h.interpretation.carrier.symm

theorem article_structure_exists_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory) {C : ArticleData M.Domain}
    (hC : C.Valid M) : ∃ S : ArticleStructure M.Domain, S.Valid M C := by
  obtain ⟨D,hD⟩ := article_interpretation_exists_d hM hC C.top
  obtain ⟨Atom,hAtom⟩ := atomic_table_exists_d hM D
  obtain ⟨ESymbols,hESymbols⟩ := hD.symbols_countable_d hM hC
  obtain ⟨context,EPrograms,hLink,hSyntax,hPrograms⟩ := countable_context_exists_d hM hD.spaces hESymbols Atom
  obtain ⟨table,hTable⟩ := evaluation_exists_d hM context hSyntax.omega
  let large : EvaluationData M.Domain := ⟨context.carrier,context.assignments,context.columns,context.atomic,table⟩
  have hLarge : large.Valid context := by
    refine ⟨hSyntax.assignments,hSyntax.columns,?_⟩
    exact hTable
  have hCarrier : large.carrier=C.top := hLink.carrier_eq.trans hD.carrier
  have hLargeAtom : AtomicTable M D large.atomic := Eq.mpr (congrArg (AtomicTable M D) hLink.atomic_eq) hAtom
  have hOrd : M.IsOrdinal large.carrier := Eq.mpr (congrArg M.IsOrdinal hCarrier) hC.top
  have hZero : M.mem (C.numbers 0) large.carrier := Eq.mpr (congrArg (M.mem (C.numbers 0)) hCarrier) (hC.number_top 0)
  obtain ⟨K,hK⟩ := skolem_bounds_exist_d hM context large
  obtain ⟨F,hF⟩ := skolem_function_exists_d hM context large hK hOrd hZero
  exact ⟨⟨D,context,large,K,F,EPrograms⟩,hD,hSyntax,
    ⟨hLink.omega_eq,hLink.carrier_eq,hLink.assignments_eq,rfl,hLink.codes_bound⟩,
    hLarge,hCarrier,hLargeAtom,hK,hF,hPrograms⟩

end KP1Y.ReflectionModel
