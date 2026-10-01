import KP1Y.AugmentedOperationsSyntax

/-! 实际构造同时供应原操作与全局枚举 e 的可数操作图。 -/
namespace KP1Y.Closure
open YesMetaZFC YesMetaZFC.SetTheory
open KP1Y.Kuratowski KP1Y.Functions KP1Y.Cardinal KP1Y.Satisfaction
universe u

theorem augment_case_total_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {D : AugmentData M.Domain} (hD : AugmentValid M D) {op tag t : M.Domain}
    (hOp : M.mem op D.operations) (hTag : M.mem tag D.omega) (ht : M.mem t D.tuples) :
    ∃ x, M.mem x D.carrier ∧ AugmentCase M D op tag t x := by
  rcases KP1Y.Naturals.natural_cases hM hD.omega hTag with hEmpty | ⟨n,hn,hSucc⟩
  · obtain ⟨key,hCode⟩ := codes_total hM op t
    have hKey := (hD.oldKeys key).mpr ⟨op,hOp,t,ht,hCode⟩
    obtain ⟨x,hx,hAt⟩ := hD.oldApply.total key hKey
    exact ⟨x,hx,Or.inl ⟨hEmpty,key,hKey,hCode,hAt⟩⟩
  · obtain ⟨x,hx,hEnum⟩ := enum_tuple_total_d hM hD.enumKeys hD.enumerator hD.default_mem hn
    exact ⟨x,hx,Or.inr ⟨n,hSucc.predecessor_mem,hSucc,hEnum⟩⟩

theorem augment_case_unique {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {D : AugmentData M.Domain} (hD : AugmentValid M D) {op tag t x y : M.Domain}
    (hTag : M.mem tag D.omega) (ht : M.mem t D.tuples)
    (hx : AugmentCase M D op tag t x) (hy : AugmentCase M D op tag t y) : x=y := by
  rcases hx with ⟨hEmpty,key,_,hCode,hAt⟩ | ⟨n,hn,hSucc,hEnum⟩
  · rcases hy with ⟨_,key',_,hCode',hAt'⟩ | ⟨n,hn,_⟩
    · have hKeys := codes_unique hM.1 hCode hCode'
      subst key'
      exact hD.oldApply.unique key x y hAt hAt'
    · exact False.elim (hEmpty n hn)
  · rcases hy with ⟨hEmpty,_⟩ | ⟨n',_,hSucc',hEnum'⟩
    · exact False.elim (hEmpty n hn)
    · have hNs := Structure.SuccessorOf.predecessor_eq hM.1
        (((KP1Y.Naturals.omega_isOrdinal_d hM hD.omega).mem hTag).mem hn) hSucc hSucc'
      subst n'
      obtain ⟨length,_,hT⟩ := (hD.tuples t).mp ht
      exact enum_tuple_unique hM.1 hD.enumerator hT hEnum hEnum'

structure AugmentedFamily (M : SetTheory.Structure.{u}) (D : AugmentData M.Domain) (Tagged Keys G : M.Domain) : Prop where
  tagged : IsProduct M Tagged D.operations D.omega
  keys : IsProduct M Keys Tagged D.tuples
  graph : Graph M G Keys D.carrier
  rows : ∀ key x, MemPair M G key x ↔ M.mem key Keys ∧ M.mem x D.carrier ∧ AugmentedApply M D Tagged key x

theorem augmented_family_exists_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {D : AugmentData M.Domain} (hD : AugmentValid M D) {Tagged : M.Domain}
    (hTagged : IsProduct M Tagged D.operations D.omega) : ∃ Keys G, AugmentedFamily M D Tagged Keys G := by
  obtain ⟨Keys,hKeys⟩ := product_exists hM Tagged D.tuples
  obtain ⟨G,hSupport,hRaw⟩ := relation_comprehension_d hM augmentedSchema ((augmentEnv D).push Tagged) Keys D.carrier
  have hRows (key x : M.Domain) : MemPair M G key x ↔ M.mem key Keys ∧ M.mem x D.carrier ∧ AugmentedApply M D Tagged key x := by
    simpa only [augmentedSchema_iff hM.1] using hRaw key x
  refine ⟨Keys,G,hTagged,hKeys,⟨hSupport,?_,?_⟩,hRows⟩
  · intro key hKey
    obtain ⟨label,hLabel,t,ht,hCode⟩ := (hKeys key).mp hKey
    obtain ⟨op,hOp,tag,hTag,hLabelCode⟩ := (hTagged label).mp hLabel
    obtain ⟨x,hx,hCase⟩ := augment_case_total_d hM hD hOp hTag ht
    exact ⟨x,hx,(hRows key x).mpr ⟨hKey,hx,label,hLabel,t,ht,hCode,op,hOp,tag,hTag,hLabelCode,hCase⟩⟩
  · intro key x y hX hY
    obtain ⟨_,_,label,_,t,ht,hCode,op,_,tag,hTag,hLabelCode,hCase⟩ := (hRows key x).mp hX
    obtain ⟨_,_,label',_,t',_,hCode',op',_,tag',_,hLabelCode',hCase'⟩ := (hRows key y).mp hY
    obtain ⟨hLabels,hTs⟩ := codes_injective hM.1 hCode hCode'
    subst label'
    subst t'
    obtain ⟨hOps,hTags⟩ := codes_injective hM.1 hLabelCode hLabelCode'
    subst op'
    subst tag'
    exact augment_case_unique hM hD hTag ht hCase hCase'

theorem countable_augmented_family_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {D : AugmentData M.Domain} (hD : AugmentValid M D) {EOps : M.Domain} (hOps : Onto M EOps D.omega D.operations) :
    ∃ Tagged ETagged Keys G, Onto M ETagged D.omega Tagged ∧ AugmentedFamily M D Tagged Keys G := by
  obtain ⟨EOmega,hEOmega⟩ := identity_onto_d hM D.omega
  obtain ⟨Tagged,ETagged,hTagged,hEnum⟩ := countable_product_d hM hD.omega hOps hEOmega
  obtain ⟨Keys,G,hG⟩ := augmented_family_exists_d hM hD hTagged
  exact ⟨Tagged,ETagged,Keys,G,hEnum,hG⟩

end KP1Y.Closure
