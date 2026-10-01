import KP1Y.EnumerationInitialSegment

/-! 给定全局初段枚举 e 后，实际构造高于任意 γ 的可数初等序数初始段。 -/
namespace KP1Y.Satisfaction
open YesMetaZFC YesMetaZFC.SetTheory
open KP1Y.Kuratowski KP1Y.Functions KP1Y.Cardinal KP1Y.Iteration KP1Y.Closure
universe u

theorem e_closed_skolem_hull_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : Context M.Domain} (hC : ContextSpaces M C) {I : EvaluationData M.Domain} (hI : I.Valid C)
    {K : SkolemBounds M.Domain} (hK : SkolemBoundsValid M C I K)
    {zero F EPrograms base EKeys e default : M.Domain} (hF : SkolemFunction M C I K zero F)
    (hPrograms : Onto M EPrograms C.omega C.programs) (hBase : Graph M base C.omega I.carrier)
    (hEnum : UniformEnumeration M C.omega I.carrier EKeys e) (hDefault : M.mem default I.carrier) :
    ∃ X E, M.MemberSubset X I.carrier ∧ Onto M E C.omega X ∧
      (∀ x, Reached M C.omega base x → M.mem x X) ∧ SkolemClosed M C K F X ∧ EnumerationClosed M C.omega e X := by
  obtain ⟨Ops,EOps,Keys,G,hOps,hEOps,hG⟩ := skolem_operations_countable_d hM hC hI hK hF.graph hPrograms
  obtain ⟨indexZero,hEmpty,hIndexZero⟩ := hC.omega.1.1
  let D : AugmentData M.Domain := ⟨C.omega,I.carrier,Ops,I.assignments,Keys,G,EKeys,e,indexZero,default⟩
  have hD : AugmentValid M D :=
    ⟨hC.omega,hI.assignments_exact,hG.keys,hG.graph,hEnum.keys,hEnum.graph,hIndexZero,hEmpty,hDefault⟩
  obtain ⟨X,E,hSub,hCount,hSeed,hOldClosed,hEnumClosed⟩ := countable_augmented_hull_d hM hD hEOps hBase
  exact ⟨X,E,hSub,hCount,hSeed,operation_closed_skolem_d hM hI hK hF.graph hOps hG hSub hOldClosed,hEnumClosed⟩

theorem elementary_height_given_enumeration_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : Context M.Domain} (hC : ContextSpaces M C) {D : RelationalData M.Domain} (hD : DataSpaces M D)
    {large : EvaluationData M.Domain} (hLarge : large.Valid C) (hCarrier : large.carrier=D.carrier)
    (hAtom : AtomicTable M D large.atomic) {K : SkolemBounds M.Domain} (hK : SkolemBoundsValid M C large K)
    {zero F EPrograms EKeys e γ : M.Domain} (hF : SkolemFunction M C large K zero F)
    (hPrograms : Onto M EPrograms C.omega C.programs) (hκ : UncountableOrdinal M C.omega large.carrier)
    (hEnum : UniformEnumeration M C.omega large.carrier EKeys e) (hγ : M.mem γ large.carrier) :
    ∃ δ E small, M.IsOrdinal δ ∧ M.mem δ large.carrier ∧ M.mem γ δ ∧ M.mem C.omega δ ∧
      small.carrier=δ ∧ small.Valid C ∧ ProgramElementary M C D small large ∧ Onto M E C.omega δ := by
  obtain ⟨base,hSeed⟩ := height_seed_exists_d hM hC.omega hκ.1 hκ.2.1 hγ
  obtain ⟨empty,_,hEmptyNat⟩ := hC.omega.1.1
  have hDefault := hκ.1.transitive C.omega hκ.2.1 empty hEmptyNat
  obtain ⟨δ,E,hSub,hCount,hSeedIn,hSkolemClosed,hEnumClosed⟩ :=
    e_closed_skolem_hull_d hM hC hLarge hK hF hPrograms hSeed.graph hEnum hDefault
  obtain ⟨hOrd,hδκ⟩ := countable_initial_segment_d hM hκ hEnum hSub hCount hEnumClosed
  obtain ⟨small,hSmallCarrier,hSmall,hElem⟩ :=
    closed_substructure_exists_d hM hC hD hLarge hCarrier hAtom hK hF hSub hSkolemClosed
  exact ⟨δ,E,small,hOrd,hδκ,hSeedIn γ hSeed.point,hSeedIn C.omega hSeed.omega,
    hSmallCarrier,hSmall,hElem,hCount⟩

end KP1Y.Satisfaction
