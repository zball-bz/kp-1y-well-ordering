import KP1Y.SkolemOperations
import KP1Y.CountableOperationsClosure
import KP1Y.RestrictedAtoms

/-! 对实际 Skolem 操作族构造可数闭包，并得到实际可数初等子结构。 -/
namespace KP1Y.Satisfaction
open YesMetaZFC YesMetaZFC.SetTheory
open KP1Y.Kuratowski KP1Y.Functions KP1Y.Cardinal KP1Y.Iteration
universe u

theorem countable_skolem_hull_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : Context M.Domain} (hC : ContextSpaces M C) {I : EvaluationData M.Domain} (hI : I.Valid C)
    {K : SkolemBounds M.Domain} (hK : SkolemBoundsValid M C I K) {zero F EPrograms base : M.Domain}
    (hF : SkolemFunction M C I K zero F) (hPrograms : Onto M EPrograms C.omega C.programs)
    (hBase : Graph M base C.omega I.carrier) :
    ∃ X E, M.MemberSubset X I.carrier ∧ Onto M E C.omega X ∧
      (∀ x, Reached M C.omega base x → M.mem x X) ∧ SkolemClosed M C K F X := by
  obtain ⟨Ops,EOps,Keys,G,hOps,hEOps,hG⟩ := skolem_operations_countable_d hM hC hI hK hF.graph hPrograms
  obtain ⟨X,E,hSub,hEnum,hSeed,hClosed⟩ := KP1Y.Closure.countable_operation_hull_d hM hC.omega hEOps
    hI.assignments_exact hG.keys hG.graph hBase
  exact ⟨X,E,hSub,hEnum,hSeed,operation_closed_skolem_d hM hI hK hF.graph hOps hG hSub hClosed⟩

theorem countable_elementary_substructure_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : Context M.Domain} (hC : ContextSpaces M C) {D : RelationalData M.Domain} (hD : DataSpaces M D)
    {large : EvaluationData M.Domain} (hLarge : large.Valid C) (hCarrier : large.carrier=D.carrier)
    (hAtom : AtomicTable M D large.atomic) {K : SkolemBounds M.Domain} (hK : SkolemBoundsValid M C large K)
    {zero F EPrograms base : M.Domain} (hF : SkolemFunction M C large K zero F)
    (hPrograms : Onto M EPrograms C.omega C.programs) (hBase : Graph M base C.omega large.carrier) :
    ∃ small E, small.Valid C ∧ ProgramElementary M C D small large ∧ Onto M E C.omega small.carrier ∧
      ∀ x, Reached M C.omega base x → M.mem x small.carrier := by
  obtain ⟨X,E,hSub,hEnum,hSeed,hClosed⟩ := countable_skolem_hull_d hM hC hLarge hK hF hPrograms hBase
  obtain ⟨small,hX,hSmall,hElem⟩ := closed_substructure_exists_d hM hC hD hLarge hCarrier hAtom hK hF hSub hClosed
  refine ⟨small,E,hSmall,hElem,?_,?_⟩
  · simpa only [hX] using hEnum
  · intro x hx
    simpa only [hX] using hSeed x hx

end KP1Y.Satisfaction
