import KP1Y.OneYMatrixCopyForest
import KP1Y.OneYMatrixCopySelection

/-! 继承候选森林的实际水平复制：复用BM4低行图，raw源区间为(root,last]。 -/
namespace KP1Y.OneYFinite.FrameCopy
open YesMetaZFC YesMetaZFC.SetTheory YesMetaZFC.SetTheory.Definitional
open KP1Y.Kuratowski KP1Y.Functions KP1Y.Naturals KP1Y.Bounded
open CopyCoordinates
universe u

/-- index为1-Y宽度参数，BM4实际副本数恰为index+1；low行0<1固定。 -/
def Copies (M : SetTheory.Structure.{u}) (C : ExpressionData M.Domain) (T : MatrixArithmetic M.Domain)
    (A : Context M.Domain) (P index width Q : M.Domain) : Prop :=
  ∃ count, M.SuccessorOf count index ∧ MatrixCopy.CopyForest M C T A P C.zero C.one count width Q

theorem Copies.forest {M : SetTheory.Structure.{u}} {C : ExpressionData M.Domain} {T : MatrixArithmetic M.Domain}
    {A : Context M.Domain} {P index width Q : M.Domain} (h : Copies M C T A P index width Q) : Forest M C.omega width Q := by
  obtain ⟨_,_,hQ⟩ := h
  exact hQ.forest

theorem copies_exists_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {A : Context M.Domain} (hA : A.Valid M C) {m P index width : M.Domain}
    (hP : Forest M C.omega m P) (hWidth : Width M C T A index width) : ∃ Q, Copies M C T A P index width Q := by
  obtain ⟨count,hCount,hSucc,total,_,hTotal,hSum⟩ := width_as_bms_d hM hC hT hA hWidth
  obtain ⟨Q,hQ⟩ := MatrixCopy.copy_forest_exists_d (row := C.zero) (maximal := C.one) hM hC hT hA hP hCount hTotal hSum
  exact ⟨Q,count,hSucc,hQ⟩

theorem Copies.unique {M : SetTheory.Structure.{u}} (he : Extensional M)
    {C : ExpressionData M.Domain} {T : MatrixArithmetic M.Domain} {A : Context M.Domain} {P index width Q R : M.Domain}
    (hQ : Copies M C T A P index width Q) (hR : Copies M C T A P index width R) : Q=R := by
  obtain ⟨count,hCount,hQ⟩ := hQ
  obtain ⟨count',hCount',hR⟩ := hR
  have hc := Structure.SuccessorOf.eq he hCount hCount'
  subst count'
  exact hQ.forest.ext he hR.forest (fun c p => (hQ.parents c p).trans (hR.parents c p).symm)

theorem Copies.encoded_parent_iff_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {A : Context M.Domain} (hA : A.Valid M C) {m P index width Q source block child : M.Domain}
    (_hP : Forest M C.omega m P) (hQ : Copies M C T A P index width Q)
    (hSource : Source M A source) (hEncode : Encode M C T A source block child) (hChild : M.mem child width) :
    ∀ target, MemPair M Q child target ↔ ∃ p, M.mem p A.last ∧ MemPair M P source p ∧ ParentCopy M C T A block p target := by
  obtain ⟨count,_,hQ⟩ := hQ
  obtain ⟨total,hTotal,hWidth⟩ := hQ.width_geometry
  rcases hSource.2 with he | hBefore
  · subst source
    obtain ⟨next,hNext,hSucc,hPos⟩ := encode_seam_bms_d hM hC hT hA hEncode
    have hNextCount := (copy_position_lt_width_iff_d hM hC hT hA.root (hA.length_nat hM.1) hQ.count_nat hNext
      hTotal hWidth (hA.length_positive_d hM hC) hPos).mp hChild
    exact hQ.root_low_parent_iff_d hM hC hT hA hQ.count_nat hNextCount hEncode.2.1 hSucc hC.one_succ.predecessor_mem hPos
  · obtain ⟨slot,hSlot,hSlotPos,hSourceAdd,hPos⟩ := encode_nonseam_bms_d hM hC hT hA hSource.1 hBefore hEncode
    have hBlockCount := (copy_position_lt_width_iff_d hM hC hT hA.root (hA.length_nat hM.1) hQ.count_nat hEncode.2.1
      hTotal hWidth hSlot hPos).mp hChild
    exact hQ.nonroot_parent_iff_d hM hC hT hA hQ.count_nat hBlockCount hSlot
      (fun he => hC.zero_empty C.zero (he ▸ hSlotPos)) hBefore hSourceAdd hPos

theorem Copies.original_parent_iff_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {A : Context M.Domain} (hA : A.Valid M C) {m P index width Q child : M.Domain}
    (hP : Forest M C.omega m P) (hQ : Copies M C T A P index width Q)
    (hOld : child=A.last ∨ M.mem child A.last) (hChild : M.mem child width) :
    ∀ target, MemPair M Q child target ↔ MemPair M P child target := by
  have hCopies := hQ
  obtain ⟨count,hCount,hQ⟩ := hQ
  rcases hOld with he | hlt
  · subst child
    have hRows := hCopies.encoded_parent_iff_d hM hC hT hA hP ⟨hA.below,Or.inl rfl⟩ (encode_zero_d hM hC hT hA hA.last) hChild
    intro target
    rw [hRows target]
    constructor
    · rintro ⟨p,hp,hP,hMap⟩
      obtain ⟨J,hJ,hRowsJ⟩ := parent_copy_graph_exists_d hM hC hT hA hC.zero_nat
      have he := hJ.graph.unique p target p ((hRowsJ p target).mpr hMap)
        ((hRowsJ p p).mpr (parent_copy_zero_d hM hC hT hA hMap.1))
      exact he.symm ▸ hP
    · intro hParent
      have hp := hP.left A.last target hParent
      exact ⟨target,hp,hParent,parent_copy_zero_d hM hC hT hA ((omega_isOrdinal_d hM hC.omega).transitive A.last hA.last target hp)⟩
  · have hCountPos : M.mem C.zero count := (hC.zero_mem_iff hM hQ.count_nat).mpr (by
      intro he
      exact hC.zero_empty index (he ▸ hCount.predecessor_mem))
    exact fun target => (hQ.parent_prefix_d hM hC hT hA hP hQ.count_nat hCountPos child hlt target).symm

theorem Copies.nonroot_parent_iff_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {A : Context M.Domain} (hA : A.Valid M C) {m P index width Q source block child : M.Domain}
    (hP : Forest M C.omega m P) (hQ : Copies M C T A P index width Q)
    (hSource : M.mem source A.last) (hNonroot : source≠A.root) (hMap : ParentCopy M C T A block source child)
    (hChild : M.mem child width) :
    ∀ target, MemPair M Q child target ↔ ∃ p, M.mem p A.last ∧ MemPair M P source p ∧ ParentCopy M C T A block p target := by
  classical
  by_cases hGood : M.mem source A.root
  · have he := (parent_copy_good_iff hMap.2.1 hMap.1 hGood).mp hMap
    subst child
    intro target
    rw [hQ.original_parent_iff_d hM hC hT hA hP (Or.inr hSource) hChild]
    constructor
    · intro hParent
      have hp := (hP.bounds hM.1 hParent).2
      have hTargetGood := ((omega_isOrdinal_d hM hC.omega).mem hA.root).transitive source hGood target (hP.left source target hParent)
      have hTargetLast := ((omega_isOrdinal_d hM hC.omega).mem hA.last).transitive A.root hA.below target hTargetGood
      exact ⟨target,hTargetLast,hParent,(parent_copy_good_iff hMap.2.1
        ((omega_isOrdinal_d hM hC.omega).transitive m hP.width target hp) hTargetGood).mpr rfl⟩
    · rintro ⟨p,_,hParent,hMapP⟩
      have hpGood := ((omega_isOrdinal_d hM hC.omega).mem hA.root).transitive source hGood p (hP.left source p hParent)
      exact ((parent_copy_good_iff hMapP.2.1 hMapP.1 hpGood).mp hMapP).symm ▸ hParent
  · have hAfter : M.mem A.root source := by
      rcases (omega_isOrdinal_d hM hC.omega).wellOrder.linear.compare source hMap.1 A.root hA.root with he | hlt | hgt
      · exact False.elim (hNonroot (hM.1.eq_of_same_members source A.root he))
      · exact False.elim (hGood hlt)
      · exact hgt
    exact hQ.encoded_parent_iff_d hM hC hT hA hP ⟨hAfter,Or.inr hSource⟩ ((parent_copy_bad_iff hGood).mp hMap) hChild

/-- 与原FrameCopy一致的raw规则：保留列≤last，新列读取(root,last]来源。 -/
def RawParent (M : SetTheory.Structure.{u}) (C : ExpressionData M.Domain) (T : MatrixArithmetic M.Domain)
    (A : Context M.Domain) (P child target : M.Domain) : Prop :=
  ((child=A.last ∨ M.mem child A.last) ∧ MemPair M P child target) ∨
    (M.mem A.last child ∧ ∃ source, M.mem source C.omega ∧ ∃ block, M.mem block C.omega ∧
      RawDecoded M C T A child source block ∧ ∃ p, M.mem p A.last ∧ MemPair M P source p ∧ ParentCopy M C T A block p target)

theorem Copies.raw_parent_iff_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {A : Context M.Domain} (hA : A.Valid M C) {m P index width Q child target : M.Domain}
    (hP : Forest M C.omega m P) (hQ : Copies M C T A P index width Q) (hc : M.mem child width) :
    MemPair M Q child target ↔ RawParent M C T A P child target := by
  have hw := omega_isOrdinal_d hM hC.omega
  have hcNat := hw.transitive width hQ.forest.width child hc
  classical
  by_cases hNew : M.mem A.last child
  · have hAfter := (hw.mem hcNat).transitive A.last hNew A.root hA.below
    obtain ⟨source,block,hRaw⟩ := raw_decode_exists_d hM hC hT hA hcNat
    have hs := hRaw.1
    have hb := hRaw.2.1
    obtain ⟨hSource,hEncode⟩ := (raw_decoded_active_iff hAfter).mp hRaw
    rw [hQ.encoded_parent_iff_d hM hC hT hA hP hSource hEncode hc]
    constructor
    · intro h
      exact Or.inr ⟨hNew,source,hs,block,hb,hRaw,h⟩
    · rintro (⟨hOld,_⟩ | ⟨_,source',_,block',_,hRaw',hCase⟩)
      · rcases hOld with he | hlt
        · exact False.elim (SetTheory.KP.mem_irrefl_d (KP1Y.models_weakKP hM) A.last (he ▸ hNew))
        · exact False.elim (SetTheory.KP.mem_irrefl_d (KP1Y.models_weakKP hM) A.last ((hw.mem hA.last).transitive child hlt A.last hNew))
      · obtain ⟨heS,heB⟩ := raw_decode_unique_d hM hC hT hA hRaw' hRaw
        subst source'
        subst block'
        exact hCase
  · have hOld : child=A.last ∨ M.mem child A.last := by
      rcases hw.wellOrder.linear.compare child hcNat A.last hA.last with he | hlt | hgt
      · exact Or.inl (hM.1.eq_of_same_members child A.last he)
      · exact Or.inr hlt
      · exact False.elim (hNew hgt)
    rw [hQ.original_parent_iff_d hM hC hT hA hP hOld hc]
    exact ⟨fun h => Or.inl ⟨hOld,h⟩,fun h => h.elim And.right (fun h => False.elim (hNew h.1))⟩

theorem Copies.linear_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {A : Context M.Domain} (hA : A.Valid M C) {m P index width Q : M.Domain}
    (hP : LinearForest M C.omega m P) (hLast : M.mem A.last m) (hQ : Copies M C T A P index width Q) :
    LinearForest M C.omega width Q := by
  obtain ⟨_,_,hQ⟩ := hQ
  exact hQ.linear_d hM hC hT hA hP hLast hC.one_succ.predecessor_mem

end KP1Y.OneYFinite.FrameCopy
