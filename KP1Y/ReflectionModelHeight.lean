import KP1Y.ReflectionStructure

/-! 实际R/P/e结构的初等高度，实例化已核验的可数Skolem闭包构造。 -/
namespace KP1Y.ReflectionModel
open YesMetaZFC YesMetaZFC.SetTheory
open KP1Y.Kuratowski KP1Y.Functions KP1Y.Satisfaction KP1Y.Cardinal KP1Y.Closure
universe u

structure Height (M : SetTheory.Structure.{u}) (C : ArticleData M.Domain) (S : ArticleStructure M.Domain)
    (δ : M.Domain) (small : EvaluationData M.Domain) : Prop where
  ordinal : M.IsOrdinal δ
  below : M.mem δ C.top
  omega : M.mem C.reflection.omega δ
  carrier : small.carrier=δ
  valid : small.Valid S.context
  elementary : ProgramElementary M S.context S.relations small S.large
  countable : ∃ E, Onto M E C.reflection.omega δ

theorem ArticleStructure.Valid.height_exists_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ArticleData M.Domain} (hC : C.Valid M) {S : ArticleStructure M.Domain} (hS : S.Valid M C)
    (hκ : UncountableOrdinal M C.reflection.omega C.top) {γ : M.Domain} (hγ : M.mem γ C.top) :
    ∃ δ small, M.mem γ δ ∧ Height M C S δ small := by
  have hUncountable : UncountableOrdinal M S.context.omega S.large.carrier := by
    rw [hS.omega,hS.carrier]
    exact hκ
  have hEnumeration : UniformEnumeration M S.context.omega S.large.carrier C.enumKeys C.enumeration := by
    rw [hS.omega,hS.carrier]
    exact hC.enumeration
  have hγLarge : M.mem γ S.large.carrier := Eq.mpr (congrArg (M.mem γ) hS.carrier) hγ
  obtain ⟨δ,E,small,hOrd,hδκ,hγδ,hωδ,hCarrier,hSmall,hElementary,hCount⟩ := elementary_height_given_enumeration_d hM
    hS.context hS.interpretation.spaces hS.large hS.relational_carrier hS.atomic hS.bounds hS.skolem hS.programs
    hUncountable hEnumeration hγLarge
  refine ⟨δ,small,hγδ,hOrd,?_,?_,hCarrier,hSmall,hElementary,E,?_⟩
  · exact Eq.mp (congrArg (M.mem δ) hS.carrier) hδκ
  · exact Eq.mp (congrArg (fun w => M.mem w δ) hS.omega) hωδ
  · exact Eq.mp (congrArg (fun w => Onto M E w δ) hS.omega) hCount

theorem Height.natural_mem {M : SetTheory.Structure.{u}} {C : ArticleData M.Domain} {S : ArticleStructure M.Domain}
    {δ : M.Domain} {small : EvaluationData M.Domain} (h : Height M C S δ small) {n : M.Domain}
    (hn : M.mem n C.reflection.omega) : M.mem n δ := h.ordinal.transitive C.reflection.omega h.omega n hn

theorem Height.number_mem {M : SetTheory.Structure.{u}} {C : ArticleData M.Domain} (hC : C.Valid M) {S : ArticleStructure M.Domain}
    {δ : M.Domain} {small : EvaluationData M.Domain} (h : Height M C S δ small) (i : Fin 7) : M.mem (C.numbers i) δ :=
  h.natural_mem (hC.numerals.natural i)

end KP1Y.ReflectionModel
