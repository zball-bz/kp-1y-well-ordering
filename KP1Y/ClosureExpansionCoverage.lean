import KP1Y.ClosureExpansion

/-! 一步扩张确实保留旧像，并覆盖旧像中全部内部有限参数上的操作值。 -/
namespace KP1Y.Closure
open YesMetaZFC YesMetaZFC.SetTheory
open KP1Y.Kuratowski KP1Y.Functions KP1Y.Assignments KP1Y.Cardinal KP1Y.Iteration
universe u

theorem word_preimage_from_range_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : Data M.Domain} (hC : Valid M C) {E t n : M.Domain} (hE : Graph M E C.omega C.carrier)
    (hT : Graph M t n C.carrier) (hn : M.mem n C.omega)
    (hRange : ∀ k x, MemPair M t k x → Reached M C.omega E x) :
    ∃ word, M.mem word C.words ∧ WordMap M C.omega C.carrier E word t := by
  obtain ⟨X,hX,hOnto⟩ := function_range_countable_d hM hE
  have hTX : Graph M t n X := graph_tighten_values hT (fun k x hAt => (hX x).mpr (hRange k x hAt))
  obtain ⟨inv,hInv,hSection⟩ := least_section_exists_d hM hC.omega hOnto
  obtain ⟨word,hIndex⟩ := tuple_value_exists_d hM hTX hInv
  have hWord := (hC.words word).mpr ⟨n,hn,hIndex.values⟩
  have hValue : TupleValue M t word E n C.omega C.carrier := by
    refine ⟨hIndex.values,hE,hT,?_⟩
    intro k hk j hj a _ hWordAt
    obtain ⟨b,hb,hTkb⟩ := hTX.total k hk
    have hInvbj := (hIndex.rows k hk b hb j hj hTkb).mp hWordAt
    have hEjb := hSection b j hInvbj
    constructor
    · intro hTka
      have hab := hT.unique k a b hTka hTkb
      subst a
      exact hEjb
    · intro hEja
      have hab := hE.unique j a b hEja hEjb
      subst a
      exact hTkb
  exact ⟨word,hWord,n,hn,hValue⟩

theorem next_enumerator_preserves_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : Data M.Domain} (hC : Valid M C) {E F : M.Domain} (hE : Graph M E C.omega C.carrier)
    (hF : NextEnumerator M C E F) : ∀ x, Reached M C.omega E x → Reached M C.omega F x := by
  intro x hOld
  obtain ⟨k,hk,hAt⟩ := hOld
  obtain ⟨n,hn,hDecode⟩ := decode_onto_d hM hC hC.zero_nat hk
  have hx := (hE.bounds hM.1 hAt).2
  exact ⟨n,hn,(hF.rows n hn x hx).mpr ⟨C.zero,hC.zero_nat,k,hk,hDecode,Or.inl ⟨hC.zero_empty,hAt⟩⟩⟩

theorem next_enumerator_covers_operations_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : Data M.Domain} (hC : Valid M C) {E F op t n key x : M.Domain}
    (hE : Graph M E C.omega C.carrier) (hF : NextEnumerator M C E F)
    (hOp : M.mem op C.operations) (hT : Graph M t n C.carrier) (hn : M.mem n C.omega)
    (hRange : ∀ k y, MemPair M t k y → Reached M C.omega E y)
    (hCode : Codes M key op t) (hAt : MemPair M C.applyOperation key x) : Reached M C.omega F x := by
  obtain ⟨i,hi,hOpAt⟩ := hC.operationDecode.2.2.2 op hOp
  obtain ⟨word,hWord,hMap⟩ := word_preimage_from_range_d hM hC hE hT hn hRange
  obtain ⟨j,hj,hWordAt⟩ := hC.wordDecode.2.2.2 word hWord
  obtain ⟨k,hk,hDecode⟩ := decode_onto_d hM hC hi hj
  obtain ⟨one,hOneSucc,hOne⟩ := hC.omega.1.2 C.zero hC.zero_nat
  have hNotEmpty : ¬(∀ z, ¬M.mem z one) := fun h => h C.zero hOneSucc.predecessor_mem
  obtain ⟨index,hIndex,hOuter⟩ := decode_onto_d hM hC hOne hk
  have ht := (hC.tuples t).mpr ⟨n,hn,hT⟩
  have hKey := (hC.keys key).mpr ⟨op,hOp,t,ht,hCode⟩
  have hx := (hC.operation.bounds hM.1 hAt).2
  have hQuery : OperationQuery M C E i j x := ⟨op,hOp,word,hWord,hOpAt,hWordAt,t,ht,hMap,key,hKey,hCode,hAt⟩
  exact ⟨index,hIndex,(hF.rows index hIndex x hx).mpr
    ⟨one,hOne,k,hk,hOuter,Or.inr ⟨hNotEmpty,i,hi,j,hj,hDecode,hQuery⟩⟩⟩

end KP1Y.Closure
