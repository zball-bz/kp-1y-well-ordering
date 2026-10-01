import KP1Y.AugmentedOperations

/-! 扩充操作闭包同时保留 Skolem 操作，并对全局 e 的每个自然数输入封闭。 -/
namespace KP1Y.Closure
open YesMetaZFC YesMetaZFC.SetTheory
open KP1Y.Kuratowski KP1Y.Functions KP1Y.Cardinal KP1Y.Iteration KP1Y.Sequences
universe u

def FamilyClosed (M : SetTheory.Structure.{u}) (ω Ops G X : M.Domain) : Prop :=
  ∀ op, M.mem op Ops → ∀ n, M.mem n ω → ∀ t, Graph M t n X →
    ∀ key, Codes M key op t → ∀ x, MemPair M G key x → M.mem x X

def EnumerationClosed (M : SetTheory.Structure.{u}) (ω e X : M.Domain) : Prop :=
  ∀ a, M.mem a X → ∀ n, M.mem n ω → ∀ key, Codes M key a n → ∀ x, MemPair M e key x → M.mem x X

theorem augmented_closed_old_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {D : AugmentData M.Domain} (hD : AugmentValid M D) {Tagged Keys G X : M.Domain}
    (hG : AugmentedFamily M D Tagged Keys G) (hSub : M.MemberSubset X D.carrier)
    (hClosed : FamilyClosed M D.omega Tagged G X) : FamilyClosed M D.omega D.operations D.oldApply X := by
  intro op hOp n hn t hT oldKey hOldCode x hAt
  have ht := (hD.tuples t).mpr ⟨n,hn,hT.mono_values hSub⟩
  obtain ⟨label,hLabelCode⟩ := codes_total hM op D.indexZero
  have hLabel := (hG.tagged label).mpr ⟨op,hOp,D.indexZero,hD.zero_nat,hLabelCode⟩
  obtain ⟨key,hCode⟩ := codes_total hM label t
  have hKey := (hG.keys key).mpr ⟨label,hLabel,t,ht,hCode⟩
  have hOldKey := (hD.oldKeys oldKey).mpr ⟨op,hOp,t,ht,hOldCode⟩
  have hCase : AugmentCase M D op D.indexZero t x := Or.inl ⟨hD.zero_empty,oldKey,hOldKey,hOldCode,hAt⟩
  have hApply : AugmentedApply M D Tagged key x := ⟨label,hLabel,t,ht,hCode,op,hOp,D.indexZero,hD.zero_nat,hLabelCode,hCase⟩
  have hGAt := (hG.rows key x).mpr ⟨hKey,(hD.oldApply.bounds hM.1 hAt).2,hApply⟩
  exact hClosed label hLabel n hn t hT key hCode x hGAt

theorem augmented_closed_enum_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {D : AugmentData M.Domain} (hD : AugmentValid M D) {Tagged Keys G X op : M.Domain}
    (hG : AugmentedFamily M D Tagged Keys G) (hSub : M.MemberSubset X D.carrier)
    (hOp : M.mem op D.operations) (hClosed : FamilyClosed M D.omega Tagged G X) : EnumerationClosed M D.omega D.enumerator X := by
  intro a ha n hn enumKey hEnumCode x heAt
  obtain ⟨one,hOneSucc,hOne⟩ := hD.omega.1.2 D.indexZero hD.zero_nat
  obtain ⟨t,hAppend⟩ := append_exists_d hM D.indexZero D.indexZero a
  have hT : Graph M t one X := graph_append_d hM (empty_graph (V := X) hD.zero_empty) hOneSucc ha hAppend
  have hFirst : MemPair M t D.indexZero a := (append_rows hM.1 hAppend D.indexZero a).mpr (Or.inr ⟨rfl,rfl⟩)
  have ht := (hD.tuples t).mpr ⟨one,hOne,hT.mono_values hSub⟩
  obtain ⟨tag,hTagSucc,hTag⟩ := hD.omega.1.2 n hn
  obtain ⟨label,hLabelCode⟩ := codes_total hM op tag
  have hLabel := (hG.tagged label).mpr ⟨op,hOp,tag,hTag,hLabelCode⟩
  obtain ⟨key,hCode⟩ := codes_total hM label t
  have hKey := (hG.keys key).mpr ⟨label,hLabel,t,ht,hCode⟩
  have hEnumKey := (hD.enumKeys enumKey).mpr ⟨a,hSub a ha,n,hn,hEnumCode⟩
  have hEnum : Satisfaction.EnumTuple M D.carrier D.enumKeys D.enumerator D.indexZero D.default n t x :=
    Or.inl ⟨a,hSub a ha,hFirst,enumKey,hEnumKey,hEnumCode,heAt⟩
  have hCase : AugmentCase M D op tag t x := Or.inr ⟨n,hTagSucc.predecessor_mem,hTagSucc,hEnum⟩
  have hApply : AugmentedApply M D Tagged key x := ⟨label,hLabel,t,ht,hCode,op,hOp,tag,hTag,hLabelCode,hCase⟩
  have hGAt := (hG.rows key x).mpr ⟨hKey,(hD.enumerator.bounds hM.1 heAt).2,hApply⟩
  exact hClosed label hLabel one hOne t hT key hCode x hGAt

theorem countable_augmented_hull_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {D : AugmentData M.Domain} (hD : AugmentValid M D) {EOps base : M.Domain}
    (hOps : Onto M EOps D.omega D.operations) (hBase : Graph M base D.omega D.carrier) :
    ∃ X E, M.MemberSubset X D.carrier ∧ Onto M E D.omega X ∧ (∀ x, Reached M D.omega base x → M.mem x X) ∧
      FamilyClosed M D.omega D.operations D.oldApply X ∧ EnumerationClosed M D.omega D.enumerator X := by
  obtain ⟨Tagged,ETagged,Keys,G,hTaggedEnum,hG⟩ := countable_augmented_family_d hM hD hOps
  obtain ⟨X,E,hSub,hEnum,hSeed,hClosed⟩ := countable_operation_hull_d hM hD.omega hTaggedEnum hD.tuples hG.keys hG.graph hBase
  obtain ⟨op,hOp,_⟩ := hOps.2.1 D.indexZero hD.zero_nat
  exact ⟨X,E,hSub,hEnum,hSeed,augmented_closed_old_d hM hD hG hSub hClosed,
    augmented_closed_enum_d hM hD hG hSub hOp hClosed⟩

end KP1Y.Closure
