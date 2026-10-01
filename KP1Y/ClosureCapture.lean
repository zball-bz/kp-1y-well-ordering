import KP1Y.ClosureFlatten
import KP1Y.ClosureMonotone
import KP1Y.FiniteNaturalRange

/-! 总像中的内部有限参数元组必落入某一共同层，不能用外部有限性代替。 -/
namespace KP1Y.Closure
open YesMetaZFC YesMetaZFC.SetTheory
open KP1Y.Kuratowski KP1Y.Functions KP1Y.Assignments KP1Y.Cardinal KP1Y.Iteration
universe u

theorem Flattened.subset {M : SetTheory.Structure.{u}} (he : Extensional M) {C : Data M.Domain}
    {R V X f : M.Domain} (h : Flattened M C R V X f) : M.MemberSubset X C.carrier := by
  intro x hx
  obtain ⟨n,_,hAt⟩ := h.onto.2.2.2 x hx
  exact (h.graph.bounds he hAt).2

theorem finite_tuple_captured_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : Data M.Domain} (hC : Valid M C) {base R V X f t length : M.Domain}
    (hFamily : EnumeratorFamily M C base R V) (hFlat : Flattened M C R V X f)
    (hT : Graph M t length X) (hLength : M.mem length C.omega) :
    ∃ N, M.mem N C.omega ∧ ∃ E, M.mem E V ∧ MemPair M R N E ∧
      ∀ k x, MemPair M t k x → Reached M C.omega E x := by
  obtain ⟨inv,hInv,hSection⟩ := least_section_exists_d hM hC.omega hFlat.onto
  obtain ⟨indices,hIndices⟩ := tuple_value_exists_d hM hT hInv
  obtain ⟨N,hN,hBound⟩ := KP1Y.Naturals.finite_natural_range_bounded_d hM hC.omega hLength hIndices.values
  obtain ⟨E,hEV,hNE⟩ := hFamily.graph.total N hN
  refine ⟨N,hN,E,hEV,hNE,?_⟩
  intro k x hAt
  have hk := (hT.bounds hM.1 hAt).1
  have hxX := (hT.bounds hM.1 hAt).2
  obtain ⟨index,hIndex,hIndexAt⟩ := hIndices.values.total k hk
  have hInvAt := (hIndices.rows k hk x hxX index hIndex hAt).mp hIndexAt
  have hFlatAt := hSection x index hInvAt
  have hxA := (hFlat.graph.bounds hM.1 hFlatAt).2
  obtain ⟨i,hi,j,hj,hDecode,G,_,hIG,hGx⟩ := (hFlat.rows index hIndex x hxA).mp hFlatAt
  obtain ⟨pair,hPair,hDecodeAt,hCode⟩ := hDecode
  have hiBound := (hC.pairing.bounds index hIndex pair hPair hDecodeAt i hi j hj hCode).1
  have hIndexN := hBound k index hIndexAt
  have hOrd := KP1Y.Naturals.omega_isOrdinal_d hM hC.omega
  have hiN : M.mem i N := by
    rcases KP1Y.Naturals.ordinal_subset_cases_d hM (hOrd.mem hi) (hOrd.mem hIndex) hiBound with he | him
    · exact he ▸ hIndexN
    · exact (hOrd.mem hN).transitive index hIndexN i him
  exact family_monotone_d hM hC hFamily N hN i hi (Or.inr hiN) G E hIG hNE x hxA ⟨j,hj,hGx⟩

end KP1Y.Closure
