import KP1Y.OneYOrdinaryCopy
import KP1Y.OneYBadRoot

/-! 活跃层的实际复制山形；高接缝读取原 root 的父项，不对该父项平移。 -/
namespace KP1Y.OneYFinite.CopiedMountain.Terminal
open YesMetaZFC YesMetaZFC.SetTheory YesMetaZFC.SetTheory.Definitional
open KP1Y.Kuratowski KP1Y.Functions KP1Y.Naturals KP1Y.Bounded
open KP1Y.OneYFinite.CopyCoordinates
universe u

abbrev Height (M : SetTheory.Structure.{u}) (C : ExpressionData M.Domain) (T : MatrixArithmetic M.Domain)
    (A : Context M.Domain) (X : Data M.Domain) (c h : M.Domain) : Prop := Ordinary.Height M C T A X c h

def HighSeam (M : SetTheory.Structure.{u}) (last level r s : M.Domain) : Prop := s=last ∧ (level=r ∨ M.mem level r)

def MappedParent (M : SetTheory.Structure.{u}) (C : ExpressionData M.Domain) (T : MatrixArithmetic M.Domain)
    (A : Context M.Domain) (X : Data M.Domain) (b r s q : M.Domain) : Prop :=
  ∃ p, M.mem p C.omega ∧ ParentAt M X r s p ∧ ParentCopy M C T A b p q

def Parent (M : SetTheory.Structure.{u}) (C : ExpressionData M.Domain) (T : MatrixArithmetic M.Domain)
    (A : Context M.Domain) (X : Data M.Domain) (level r c q : M.Domain) : Prop :=
  M.mem c C.omega ∧ ((M.mem c A.last ∧ ParentAt M X r c q) ∨ (¬M.mem c A.last ∧
    ∃ s, M.mem s C.omega ∧ ∃ b, M.mem b C.omega ∧ RawDecoded M C T A c s b ∧
      ((HighSeam M A.last level r s ∧ ParentAt M X r A.root q) ∨
        (¬HighSeam M A.last level r s ∧ MappedParent M C T A X b r s q))))

def highSeamFormula {n : Nat} (last level r s : Project.Term n) : Project.Formula 1 n :=
  .conj (Project.Formula.extensionalEq s last) (.disj (Project.Formula.extensionalEq level r) (.mem level r))

def mappedParentFormula {n : Nat} (C : ExpressionData (Project.Term n)) (T : MatrixArithmetic (Project.Term n))
    (A : Context (Project.Term n)) (X : Data (Project.Term n)) (b r s q : Project.Term n) : Project.Formula 1 n :=
  Project.Formula.existsMem C.omega (.conj (parentAtFormula X.weaken r.weaken s.weaken (.bound 0))
    (parentCopyFormula C.weaken T.weaken A.weaken b.weaken (.bound 0) q.weaken))

def parentFormula {n : Nat} (C : ExpressionData (Project.Term n)) (T : MatrixArithmetic (Project.Term n))
    (A : Context (Project.Term n)) (X : Data (Project.Term n)) (level r c q : Project.Term n) : Project.Formula 1 n :=
  .conj (.mem c C.omega) (.disj (.conj (.mem c A.last) (parentAtFormula X r c q))
    (.conj (.neg (.mem c A.last)) (Project.Formula.existsMem C.omega (Project.Formula.existsMem C.omega.weaken
      (.conj (rawDecodedFormula C.weaken.weaken T.weaken.weaken A.weaken.weaken c.weaken.weaken (.bound 1) (.bound 0))
        (.disj (.conj (highSeamFormula A.last.weaken.weaken level.weaken.weaken r.weaken.weaken (.bound 1))
          (parentAtFormula X.weaken.weaken r.weaken.weaken A.root.weaken.weaken q.weaken.weaken))
          (.conj (.neg (highSeamFormula A.last.weaken.weaken level.weaken.weaken r.weaken.weaken (.bound 1)))
            (mappedParentFormula C.weaken.weaken T.weaken.weaken A.weaken.weaken X.weaken.weaken
              (.bound 0) r.weaken.weaken (.bound 1) q.weaken.weaken))))))))

theorem highSeamFormula_delta0 {n : Nat} (last level r s : Project.Term n) : (highSeamFormula last level r s).IsDelta0 :=
  .conj (.atom _ _ _) (.disj (.atom _ _ _) (.mem _ _))

theorem mappedParentFormula_delta0 {n : Nat} (C : ExpressionData (Project.Term n)) (T : MatrixArithmetic (Project.Term n))
    (A : Context (Project.Term n)) (X : Data (Project.Term n)) (b r s q : Project.Term n) : (mappedParentFormula C T A X b r s q).IsDelta0 :=
  .existsMem _ (.conj (parentAtFormula_delta0 _ _ _ _) (parentCopyFormula_delta0 _ _ _ _ _ _))

theorem parentFormula_delta0 {n : Nat} (C : ExpressionData (Project.Term n)) (T : MatrixArithmetic (Project.Term n))
    (A : Context (Project.Term n)) (X : Data (Project.Term n)) (level r c q : Project.Term n) : (parentFormula C T A X level r c q).IsDelta0 :=
  .conj (.mem _ _) (.disj (.conj (.mem _ _) (parentAtFormula_delta0 _ _ _ _)) (.conj (.neg (.mem _ _))
    (.existsMem _ (.existsMem _ (.conj (rawDecodedFormula_delta0 _ _ _ _ _ _)
      (.disj (.conj (highSeamFormula_delta0 _ _ _ _) (parentAtFormula_delta0 _ _ _ _))
        (.conj (.neg (highSeamFormula_delta0 _ _ _ _)) (mappedParentFormula_delta0 _ _ _ _ _ _ _ _))))))))

theorem mappedParentFormula_freeClosed {n : Nat} {C : ExpressionData (Project.Term n)} (hC : C.Closed)
    {T : MatrixArithmetic (Project.Term n)} (hT : ArithmeticClosed T) {A : Context (Project.Term n)} (hA : A.Closed)
    {X : Data (Project.Term n)} (hX : X.Closed) (b r s q : Project.Term n)
    (hb : b.freeSupport=[]) (hr : r.freeSupport=[]) (hs : s.freeSupport=[]) (hq : q.freeSupport=[]) :
    (mappedParentFormula C T A X b r s q).FreeClosed := by
  have hParent := parentAtFormula_freeClosed hX.weaken r.weaken s.weaken (.bound 0) (by simpa using hr) (by simpa using hs) rfl
  have hCopy := parentCopyFormula_freeClosed hC.weaken hT.weaken hA.weaken b.weaken (.bound 0) q.weaken (by simpa using hb) rfl (by simpa using hq)
  simp [mappedParentFormula,Project.Formula.existsMem,Definitional.Formula.FreeClosed,hC.omega,hParent,hCopy]

theorem parentFormula_freeClosed {n : Nat} {C : ExpressionData (Project.Term n)} (hC : C.Closed)
    {T : MatrixArithmetic (Project.Term n)} (hT : ArithmeticClosed T) {A : Context (Project.Term n)} (hA : A.Closed)
    {X : Data (Project.Term n)} (hX : X.Closed) (level r c q : Project.Term n)
    (hd : level.freeSupport=[]) (hr : r.freeSupport=[]) (hc : c.freeSupport=[]) (hq : q.freeSupport=[]) : (parentFormula C T A X level r c q).FreeClosed := by
  have hOld := parentAtFormula_freeClosed hX r c q hr hc hq
  have hRaw := rawDecodedFormula_freeClosed hC.weaken.weaken hT.weaken.weaken hA.weaken.weaken c.weaken.weaken (.bound 1) (.bound 0)
    (by simpa using hc) rfl rfl
  have hRoot := parentAtFormula_freeClosed hX.weaken.weaken r.weaken.weaken A.root.weaken.weaken q.weaken.weaken
    (by simpa using hr) (by simpa using hA.root) (by simpa using hq)
  have hMapped := mappedParentFormula_freeClosed hC.weaken.weaken hT.weaken.weaken hA.weaken.weaken hX.weaken.weaken
    (.bound 0) r.weaken.weaken (.bound 1) q.weaken.weaken rfl (by simpa using hr) rfl (by simpa using hq)
  simp [parentFormula,highSeamFormula,Project.Formula.existsMem,Definitional.Formula.FreeClosed,hC.omega,hA.last,hd,hr,hc,hOld,hRaw,hRoot,hMapped]

theorem highSeamFormula_iff {M : SetTheory.Structure.{u}} (he : Extensional M) {n : Nat} (e : Env M n) (last level r s : Project.Term n) :
    Project.Formula.satisfies e (highSeamFormula last level r s) ↔ HighSeam M (last.eval e) (level.eval e) (r.eval e) (s.eval e) := by
  simp only [highSeamFormula,Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_disj_iff,
    Project.Formula.satisfies_extensionalEq_iff_eq he,Project.Formula.satisfies_mem_iff]
  rfl

theorem mappedParentFormula_iff {M : SetTheory.Structure.{u}} (he : Extensional M) {n : Nat} (e : Env M n)
    (C : ExpressionData (Project.Term n)) (T : MatrixArithmetic (Project.Term n)) (A : Context (Project.Term n))
    (X : Data (Project.Term n)) (b r s q : Project.Term n) : Project.Formula.satisfies e (mappedParentFormula C T A X b r s q) ↔
      MappedParent M (C.eval e) (T.eval e) (A.eval e) (X.eval e) (b.eval e) (r.eval e) (s.eval e) (q.eval e) := by
  simp only [mappedParentFormula,Project.Formula.satisfies_existsMem_iff,Project.Formula.satisfies_conj_iff,
    parentAtFormula_iff he,parentCopyFormula_iff he,ExpressionData.eval_weaken,MatrixArithmetic.eval_weaken,Context.eval_weaken,Data.eval_weaken,Term.eval_weaken]
  rfl

theorem parentFormula_iff {M : SetTheory.Structure.{u}} (he : Extensional M) {n : Nat} (e : Env M n)
    (C : ExpressionData (Project.Term n)) (T : MatrixArithmetic (Project.Term n)) (A : Context (Project.Term n))
    (X : Data (Project.Term n)) (level r c q : Project.Term n) : Project.Formula.satisfies e (parentFormula C T A X level r c q) ↔
      Parent M (C.eval e) (T.eval e) (A.eval e) (X.eval e) (level.eval e) (r.eval e) (c.eval e) (q.eval e) := by
  simp only [parentFormula,Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_mem_iff,Project.Formula.satisfies_disj_iff,
    Project.Formula.satisfies_neg_iff,Project.Formula.satisfies_existsMem_iff,parentAtFormula_iff he,rawDecodedFormula_iff he,
    highSeamFormula_iff he,mappedParentFormula_iff he,ExpressionData.eval_weaken,MatrixArithmetic.eval_weaken,Context.eval_weaken,Data.eval_weaken,Term.eval_weaken]
  rfl

structure Active (M : SetTheory.Structure.{u}) (X : Data M.Domain) (A : Context M.Domain) (level : M.Domain) : Prop where
  parent : ParentAt M X level A.last A.root
  lastHeight : ∃ height, MemPair M X.heights A.last height ∧ M.SuccessorOf height level

private theorem root_lt_of_not_old_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {A : Context M.Domain} (hA : A.Valid M C)
    {c : M.Domain} (hc : M.mem c C.omega) (hNot : ¬M.mem c A.last) : M.mem A.root c := by
  rcases (omega_isOrdinal_d hM hC.omega).wellOrder.linear.compare c hc A.last hA.last with he | hLess | hMore
  · exact (hM.1.eq_of_same_members c A.last he).symm ▸ hA.below
  · exact False.elim (hNot hLess)
  · exact ((omega_isOrdinal_d hM hC.omega).mem hc).transitive A.last hMore A.root hA.below

theorem height_at_decoded_iff_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {A : Context M.Domain} (hA : A.Valid M C) {X : Data M.Domain} {c s b h : M.Domain}
    (hDec : OrdinaryCoordinates.Decoded M C T A c s b) : Height M C T A X c h ↔ MemPair M X.heights s h := by
  constructor
  · rintro ⟨s',_,b',_,hDec',hHeight⟩
    have hss := (hDec'.unique_d hM hC hT hA hDec).1
    subst s'
    exact hHeight
  · intro hHeight
    exact ⟨s,hDec.2.1,b,hDec.2.2.1,hDec,hHeight⟩

theorem height_original_iff_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {A : Context M.Domain} (hA : A.Valid M C) {X : Data M.Domain} {c h : M.Domain} (hc : M.mem c A.last) :
    Height M C T A X c h ↔ MemPair M X.heights c h :=
  height_at_decoded_iff_d hM hC hT hA (OrdinaryCoordinates.decoded_original_d hM hC hT hA hc)

theorem height_parent_copy_iff_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {A : Context M.Domain} (hA : A.Valid M C) {X : Data M.Domain} {p b q h : M.Domain}
    (hp : M.mem p A.last) (hCopy : ParentCopy M C T A b p q) : Height M C T A X q h ↔ MemPair M X.heights p h := by
  obtain ⟨block,hDec⟩ := OrdinaryCoordinates.decoded_parent_copy_d hM hC hT hA hp hCopy
  exact height_at_decoded_iff_d hM hC hT hA hDec

theorem height_raw_seam_iff_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {A : Context M.Domain} (hA : A.Valid M C) {X : Data M.Domain} {c b h : M.Domain}
    (hc : M.mem c C.omega) (hNot : ¬M.mem c A.last) (hRaw : RawDecoded M C T A c A.last b) :
    Height M C T A X c h ↔ MemPair M X.heights A.root h := by
  obtain ⟨block,_,hDec⟩ := OrdinaryCoordinates.raw_seam_decoded_d hM hC hT hA hc (root_lt_of_not_old_d hM hC hA hc hNot) hRaw
  exact height_at_decoded_iff_d hM hC hT hA hDec

theorem height_raw_nonseam_iff_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {A : Context M.Domain} (hA : A.Valid M C) {X : Data M.Domain} {c s b h : M.Domain}
    (hc : M.mem c C.omega) (hNot : ¬M.mem c A.last) (hRaw : RawDecoded M C T A c s b) (hs : s≠A.last) :
    Height M C T A X c h ↔ MemPair M X.heights s h := by
  have hsLast := (raw_decoded_source_bounds_d hM hC hA hRaw).2.resolve_left hs
  exact height_at_decoded_iff_d hM hC hT hA
    (OrdinaryCoordinates.raw_nonseam_decoded_d hM hC hT hA hc (root_lt_of_not_old_d hM hC hA hc hNot) hRaw hsLast)

theorem MappedParent.unique_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {A : Context M.Domain} (hA : A.Valid M C) {X : Data M.Domain} (hX : X.Valid M C) {b r s q q' : M.Domain}
    (h : MappedParent M C T A X b r s q) (h' : MappedParent M C T A X b r s q') : q=q' := by
  obtain ⟨p,_,hP,hCopy⟩ := h
  obtain ⟨p',_,hP',hCopy'⟩ := h'
  have hpp := hP.unique hX hP'
  subst p'
  obtain ⟨J,hJ,hRows⟩ := parent_copy_graph_exists_d hM hC hT hA hCopy.2.1
  exact hJ.graph.unique p q q' ((hRows p q).mpr hCopy) ((hRows p q').mpr hCopy')

theorem Parent.row_natural {M : SetTheory.Structure.{u}} (he : Extensional M) {C : ExpressionData M.Domain}
    {T : MatrixArithmetic M.Domain} {A : Context M.Domain} {X : Data M.Domain} (hX : X.Valid M C)
    {level r c q : M.Domain} (h : Parent M C T A X level r c q) : M.mem r C.omega := by
  rcases h.2 with ⟨_,hOld⟩ | ⟨_,_,_,_,_,_,hHigh | hMapped⟩
  · exact (hOld.bounds he hX).1
  · exact (hHigh.2.bounds he hX).1
  · obtain ⟨_,_,hOld,_⟩ := hMapped.2
    exact (hOld.bounds he hX).1

theorem Parent.left_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {A : Context M.Domain} (hA : A.Valid M C) {X : Data M.Domain} (hX : X.Valid M C) {level r c q : M.Domain}
    (h : Parent M C T A X level r c q) : M.mem q c := by
  rcases h with ⟨hc,hOld | ⟨hNot,s,_,b,_,hRaw,hHigh | hMapped⟩⟩
  · exact (hOld.2.bounds hM.1 hX).2.2.2
  · exact ((omega_isOrdinal_d hM hC.omega).mem hc).transitive A.root (root_lt_of_not_old_d hM hC hA hc hNot) q
      (hHigh.2.bounds hM.1 hX).2.2.2
  · obtain ⟨p,_,hP,hCopy⟩ := hMapped.2
    have hActive := (raw_decoded_active_iff (root_lt_of_not_old_d hM hC hA hc hNot)).mp hRaw
    exact parent_copy_below_encode_d hM hC hT hA hActive.1.1 (hP.bounds hM.1 hX).2.2.2 hCopy hActive.2

theorem Parent.unique_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {A : Context M.Domain} (hA : A.Valid M C) {X : Data M.Domain} (hX : X.Valid M C) {level r c q q' : M.Domain}
    (h : Parent M C T A X level r c q) (h' : Parent M C T A X level r c q') : q=q' := by
  rcases h.2 with ⟨hOld,hP⟩ | ⟨hNot,s,_,b,_,hRaw,hCase⟩ <;> rcases h'.2 with ⟨hOld',hP'⟩ | ⟨hNot',s',_,b',_,hRaw',hCase'⟩
  · exact hP.unique hX hP'
  · exact False.elim (hNot' hOld)
  · exact False.elim (hNot hOld')
  · obtain ⟨hss,hbb⟩ := raw_decode_unique_d hM hC hT hA hRaw hRaw'
    subst s'
    subst b'
    rcases hCase with ⟨hHigh,hP⟩ | ⟨hLow,hP⟩ <;> rcases hCase' with ⟨hHigh',hP'⟩ | ⟨hLow',hP'⟩
    · exact hP.unique hX hP'
    · exact False.elim (hLow' hHigh)
    · exact False.elim (hLow hHigh')
    · exact hP.unique_d hM hC hT hA hX hP'

private theorem below_of_not_ge_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {r d : M.Domain}
    (hr : M.mem r C.omega) (hd : M.mem d C.omega) (hNot : ¬(d=r ∨ M.mem d r)) : M.mem r d := by
  rcases (omega_isOrdinal_d hM hC.omega).wellOrder.linear.compare r hr d hd with he | hlt | hgt
  · exact False.elim (hNot (.inl (hM.1.eq_of_same_members r d he).symm))
  · exact hlt
  · exact False.elim (hNot (.inr hgt))

theorem source_iff_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {A : Context M.Domain} (hA : A.Valid M C) {X : Data M.Domain} (hX : X.Valid M C)
    {level r c h : M.Domain} (hActive : Active M X A level) (hHeight : Height M C T A X c h) :
    (∃q, Parent M C T A X level r c q) ↔ M.mem r h := by
  have hd := (hActive.parent.bounds hM.1 hX).1
  have hc : M.mem c C.omega := by
    obtain ⟨_,_,_,_,hDec,_⟩ := hHeight
    exact hDec.1
  have hh : M.mem h C.omega := by
    obtain ⟨_,_,_,_,_,hAt⟩ := hHeight
    exact (hX.heights.bounds hM.1 hAt).2
  have hOrd := omega_isOrdinal_d hM hC.omega
  have hRoot (hAt : MemPair M X.heights A.root h) (hrd : M.mem r level) : M.mem r h := by
    rcases hX.endpoint level A.last A.root h hActive.parent hAt with he | hlt
    · exact he ▸ hrd
    · exact (hOrd.mem hh).transitive level hlt r hrd
  have hMapped (s b : M.Domain) (hb : M.mem b C.omega) (hP : ∃p, ParentAt M X r s p) :
      ∃q, MappedParent M C T A X b r s q := by
    obtain ⟨p,hP⟩ := hP
    have hp := hOrd.transitive X.width hX.width p (hP.bounds hM.1 hX).2.2.1
    obtain ⟨J,hJ,hRows⟩ := parent_copy_graph_exists_d hM hC hT hA hb
    obtain ⟨q,_,hQ⟩ := hJ.graph.total p hp
    exact ⟨q,p,hp,hP,(hRows p q).mp hQ⟩
  constructor
  · rintro ⟨q,hParent⟩
    have hr := hParent.row_natural hM.1 hX
    rcases hParent.2 with ⟨hOld,hP⟩ | ⟨hNot,s,_,b,_,hRaw,hHigh | hLow⟩
    · exact (hX.source r c h ((height_original_iff_d hM hC hT hA hOld).mp hHeight)).mp ⟨q,hP⟩
    · obtain ⟨⟨rfl,_⟩,hP⟩ := hHigh
      exact (hX.source r A.root h ((height_raw_seam_iff_d hM hC hT hA hc hNot hRaw).mp hHeight)).mp ⟨q,hP⟩
    · by_cases hs : s=A.last
      · subst s
        exact hRoot ((height_raw_seam_iff_d hM hC hT hA hc hNot hRaw).mp hHeight)
          (below_of_not_ge_d hM hC hr hd (fun hge => hLow.1 ⟨rfl,hge⟩))
      · obtain ⟨p,_,hP,_⟩ := hLow.2
        exact (hX.source r s h ((height_raw_nonseam_iff_d hM hC hT hA hc hNot hRaw hs).mp hHeight)).mp ⟨p,hP⟩
  · intro hrh
    have hr := hOrd.transitive h hh r hrh
    by_cases hOld : M.mem c A.last
    · obtain ⟨q,hP⟩ := (hX.source r c h ((height_original_iff_d hM hC hT hA hOld).mp hHeight)).mpr hrh
      exact ⟨q,hc,.inl ⟨hOld,hP⟩⟩
    · obtain ⟨s,b,hRaw⟩ := raw_decode_exists_d hM hC hT hA hc
      have hs := hRaw.1
      have hb := hRaw.2.1
      by_cases hHigh : HighSeam M A.last level r s
      · have hsLast := hHigh.1
        subst s
        obtain ⟨q,hP⟩ := (hX.source r A.root h ((height_raw_seam_iff_d hM hC hT hA hc hOld hRaw).mp hHeight)).mpr hrh
        exact ⟨q,hc,.inr ⟨hOld,A.last,hs,b,hb,hRaw,.inl ⟨hHigh,hP⟩⟩⟩
      · have hP : ∃p, ParentAt M X r s p := by
          by_cases hsLast : s=A.last
          · subst s
            obtain ⟨lastHeight,hLast,hSucc⟩ := hActive.lastHeight
            have hrd := below_of_not_ge_d hM hC hr hd (fun hge => hHigh ⟨rfl,hge⟩)
            exact (hX.source r A.last lastHeight hLast).mpr ((hSucc r).mpr (.inl hrd))
          · exact (hX.source r s h ((height_raw_nonseam_iff_d hM hC hT hA hc hOld hRaw hsLast).mp hHeight)).mpr hrh
        obtain ⟨q,hP⟩ := hMapped s b hb hP
        exact ⟨q,hc,.inr ⟨hOld,s,hs,b,hb,hRaw,.inr ⟨hHigh,hP⟩⟩⟩

theorem endpoint_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {A : Context M.Domain} (hA : A.Valid M C) {X : Data M.Domain} (hX : X.Valid M C)
    {level r c q h : M.Domain} (hParent : Parent M C T A X level r c q) (hHeight : Height M C T A X q h) :
    r=h ∨ M.mem r h := by
  have hLastOrd := (omega_isOrdinal_d hM hC.omega).mem hA.last
  rcases hParent.2 with ⟨hOld,hP⟩ | ⟨_,s,_,b,_,hRaw,hHigh | hLow⟩
  · have hq := hLastOrd.transitive c hOld q (hP.bounds hM.1 hX).2.2.2
    exact hX.endpoint r c q h hP ((height_original_iff_d hM hC hT hA hq).mp hHeight)
  · have hq := hLastOrd.transitive A.root hA.below q (hHigh.2.bounds hM.1 hX).2.2.2
    exact hX.endpoint r A.root q h hHigh.2 ((height_original_iff_d hM hC hT hA hq).mp hHeight)
  · obtain ⟨p,_,hP,hCopy⟩ := hLow.2
    have hp : M.mem p A.last := by
      rcases (raw_decoded_source_bounds_d hM hC hA hRaw).2 with he | hlt
      · exact he ▸ (hP.bounds hM.1 hX).2.2.2
      · exact hLastOrd.transitive s hlt p (hP.bounds hM.1 hX).2.2.2
    exact hX.endpoint r s p h hP ((height_parent_copy_iff_d hM hC hT hA hp hCopy).mp hHeight)

private def copyEnv {M : SetTheory.Structure.{u}} (C : ExpressionData M.Domain) (T : MatrixArithmetic M.Domain)
    (A : Context M.Domain) (X : Data M.Domain) (level : M.Domain) : Env M 20 :=
  ((((((((((((((((((((oneEnv C.omega).push C.zero).push C.one).push C.sequences).push C.expressions).push T.addPairs).push T.plus).push T.mulPairs).push T.times).push T.diffPairs).push T.difference).push A.last).push A.root).push A.length).push A.first).push X.width).push X.heights).push X.forests).push X.parents).push level)

private def parentSchema : Project.Delta0BinarySchema 21 where
  body := parentFormula ⟨.bound 22,.bound 21,.bound 20,.bound 19,.bound 18⟩ ⟨.bound 17,.bound 16,.bound 15,.bound 14,.bound 13,.bound 12⟩
    ⟨.bound 11,.bound 10,.bound 9,.bound 8⟩ ⟨.bound 7,.bound 6,.bound 5,.bound 4⟩ (.bound 3) (.bound 2) (.bound 1) (.bound 0)
  freeClosed := parentFormula_freeClosed ⟨rfl,rfl,rfl,rfl,rfl⟩ ⟨rfl,rfl,rfl,rfl,rfl,rfl⟩ ⟨rfl,rfl,rfl,rfl⟩ ⟨rfl,rfl,rfl,rfl⟩ _ _ _ _ rfl rfl rfl rfl
  delta0 := parentFormula_delta0 _ _ _ _ _ _ _ _

private theorem parentSchema_iff {M : SetTheory.Structure.{u}} (he : Extensional M)
    (C : ExpressionData M.Domain) (T : MatrixArithmetic M.Domain) (A : Context M.Domain) (X : Data M.Domain) (level r c p : M.Domain) :
    Project.Formula.satisfies ((((copyEnv C T A X level).push r).push c).push p) parentSchema.body ↔ Parent M C T A X level r c p :=
  parentFormula_iff he _ _ _ _ _ _ _ _ _

structure Copies (M : SetTheory.Structure.{u}) (C : ExpressionData M.Domain) (T : MatrixArithmetic M.Domain)
    (A : Context M.Domain) (X : Data M.Domain) (level n : M.Domain) (Y : Data M.Domain) : Prop where
  width : Y.width=n
  forests : ∀ F, M.mem F Y.forests ↔ Forest M C.omega n F
  heights : ∀ c h, MemPair M Y.heights c h ↔ M.mem c n ∧ Height M C T A X c h
  parents : ∀ r c p, ParentAt M Y r c p ↔ M.mem c n ∧ Parent M C T A X level r c p

theorem copy_exists_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {A : Context M.Domain} (hA : A.Valid M C) {X : Data M.Domain} (hX : X.Valid M C)
    {level n : M.Domain} (hActive : Active M X A level) (hn : M.mem n C.omega) :
    ∃ Y, Y.Valid M C ∧ Copies M C T A X level n Y := by
  obtain ⟨Heights,hHeights,hHeightRows⟩ := Ordinary.height_graph_exists_d hM hC hT hA hX (hActive.parent.bounds hM.1 hX).2.1 hn
  obtain ⟨Forests,Parents,hParents,hForests,hParentRows⟩ := forest_family_exists_d hM hC parentSchema (copyEnv C T A X level) hn
    (fun r _ c _ p _ hφ => ((parentSchema_iff hM.1 C T A X level r c p).mp hφ).left_d hM hC hT hA hX)
    (fun r _ c _ p _ q _ hφ hφ' => ((parentSchema_iff hM.1 C T A X level r c p).mp hφ).unique_d hM hC hT hA hX
      ((parentSchema_iff hM.1 C T A X level r c q).mp hφ'))
  let Y : Data M.Domain := ⟨n,Heights,Forests,Parents⟩
  have hForest (r F : M.Domain) (hRow : MemPair M Parents r F) : Forest M C.omega n F := ((hParentRows r F).mp hRow).2.1
  have hRows (r c p : M.Domain) : ParentAt M Y r c p ↔ M.mem c n ∧ Parent M C T A X level r c p := by
    constructor
    · rintro ⟨F,_,hF,hAt⟩
      obtain ⟨hc,hp⟩ := (hForest r F hF).bounds hM.1 hAt
      exact ⟨hc,(parentSchema_iff hM.1 C T A X level r c p).mp ((((hParentRows r F).mp hF).2.2 c hc p hp).mp hAt)⟩
    · rintro ⟨hc,hParent⟩
      have hr := hParent.row_natural hM.1 hX
      have hp := ((omega_isOrdinal_d hM hC.omega).mem hn).transitive c hc p (hParent.left_d hM hC hT hA hX)
      obtain ⟨F,hF,hRow⟩ := hParents.total r hr
      exact ⟨F,hF,hRow,(((hParentRows r F).mp hRow).2.2 c hc p hp).mpr ((parentSchema_iff hM.1 C T A X level r c p).mpr hParent)⟩
  refine ⟨Y,⟨hn,hHeights,hParents,hForest,?_,?_⟩,rfl,hForests,hHeightRows,hRows⟩
  · intro r c h hAt
    obtain ⟨hc,hHeight⟩ := (hHeightRows c h).mp hAt
    refine Iff.trans ?_ (source_iff_d hM hC hT hA hX hActive hHeight)
    exact ⟨fun ⟨p,hp⟩ => ⟨p,((hRows r c p).mp hp).2⟩,fun ⟨p,hp⟩ => ⟨p,(hRows r c p).mpr ⟨hc,hp⟩⟩⟩
  · intro r c p h hParent hAt
    exact endpoint_d hM hC hT hA hX ((hRows r c p).mp hParent).2 ((hHeightRows p h).mp hAt).2

theorem Copies.unique {M : SetTheory.Structure.{u}} (he : Extensional M)
    {C : ExpressionData M.Domain} {T : MatrixArithmetic M.Domain} {A : Context M.Domain} {X Y Z : Data M.Domain} {level n : M.Domain}
    (hY : Y.Valid M C) (hZ : Z.Valid M C) (h : Copies M C T A X level n Y) (h' : Copies M C T A X level n Z) : Y=Z :=
  Ordinary.data_ext he hY hZ (h.width.trans h'.width.symm)
    (he.eq_of_same_members _ _ (fun F => (h.forests F).trans (h'.forests F).symm))
    (fun c v => (h.heights c v).trans (h'.heights c v).symm)
    (fun r c p => (h.parents r c p).trans (h'.parents r c p).symm)

theorem parent_original_iff_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain}
    {A : Context M.Domain} (hA : A.Valid M C) {X : Data M.Domain} {level r c q : M.Domain}
    (hc : M.mem c A.last) : Parent M C T A X level r c q ↔ ParentAt M X r c q := by
  constructor
  · rintro ⟨_,⟨_,hP⟩ | ⟨hNot,_⟩⟩
    · exact hP
    · exact False.elim (hNot hc)
  · intro hP
    exact ⟨(omega_isOrdinal_d hM hC.omega).transitive A.last hA.last c hc,.inl ⟨hc,hP⟩⟩

theorem Copies.original_heights_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {A : Context M.Domain} (hA : A.Valid M C) {X Y : Data M.Domain} {level n c height : M.Domain}
    (h : Copies M C T A X level n Y) (hc : M.mem c n) (hLast : M.mem c A.last) :
    MemPair M Y.heights c height ↔ MemPair M X.heights c height := by
  rw [h.heights c height,height_original_iff_d hM hC hT hA hLast]
  exact ⟨And.right,fun h => ⟨hc,h⟩⟩

theorem Copies.original_parents_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain}
    {A : Context M.Domain} (hA : A.Valid M C) {X Y : Data M.Domain} {level n r c p : M.Domain}
    (h : Copies M C T A X level n Y) (hc : M.mem c n) (hLast : M.mem c A.last) : ParentAt M Y r c p ↔ ParentAt M X r c p := by
  rw [h.parents r c p,parent_original_iff_d hM hC hA hLast]
  exact ⟨And.right,fun h => ⟨hc,h⟩⟩

/-- 活跃层的两个几何条件由实际坏根及同一行运行读取。 -/
theorem active_from_bad_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {A : Context M.Domain}
    {m : M.Domain} {L : LayerStateSpace M.Domain} {V P H k level W Q J : M.Domain} {X : Data M.Domain}
    (hLayers : LayerRun M C m L V P H) (hBad : BadAt M C m L H k level A.last A.root)
    (hLayer : RowAt M L.states H k W Q) (hRun : RowRun M C m L.rows W Q J)
    (hX : X.Valid M C) (hFrom : FromRun M C m L.rows W J X) : Active M X A level := by
  have hRowBad := hBad.in_run_d hM hC hLayers hLayer hRun
  obtain ⟨U,_,F,_,hRow,hParent,_⟩ := hRowBad
  have hP := (hFrom.parent_iff hM.1 hX level A.last A.root).mpr ⟨U,F,hRow,hParent⟩
  obtain ⟨height,_,hHeight⟩ := hX.heights.total A.last (hP.bounds hM.1 hX).2.1
  exact ⟨hP,height,hHeight,hBad.height_step_d hM hC hLayers hLayer hRun hFrom.heights hHeight⟩

/-- 对实际坏根层复制；父源条件和端点界不是额外输入。 -/
theorem copy_from_bad_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {A : Context M.Domain} (hA : A.Valid M C) {m : M.Domain} {L : LayerStateSpace M.Domain}
    {V P H k level W Q J n : M.Domain} {X : Data M.Domain}
    (hLayers : LayerRun M C m L V P H) (hBad : BadAt M C m L H k level A.last A.root)
    (hLayer : RowAt M L.states H k W Q) (hRun : RowRun M C m L.rows W Q J)
    (hX : X.Valid M C) (hFrom : FromRun M C m L.rows W J X) (hn : M.mem n C.omega) :
    ∃Y, Y.Valid M C ∧ Copies M C T A X level n Y :=
  copy_exists_d hM hC hT hA hX (active_from_bad_d hM hC hLayers hBad hLayer hRun hX hFrom) hn

/-- 从实际层入口构造原始行运行、原山形及活跃复制山形。 -/
theorem copied_run_from_bad_exists_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {A : Context M.Domain} (hA : A.Valid M C) {m : M.Domain} {L : LayerStateSpace M.Domain}
    {V P H k level W Q n : M.Domain}
    (hLayers : LayerRun M C m L V P H) (hBad : BadAt M C m L H k level A.last A.root)
    (hLayer : RowAt M L.states H k W Q) (hn : M.mem n C.omega) :
    ∃J X Y, RowRun M C m L.rows W Q J ∧ X.Valid M C ∧ FromRun M C m L.rows W J X ∧
      Y.Valid M C ∧ Copies M C T A X level n Y := by
  have hRooted := hLayers.at_rooted hM.1 hLayer
  obtain ⟨J,hRun⟩ := row_run_exists_d hM hC hLayers.space.rows hRooted.row
  obtain ⟨X,hX,hFrom⟩ := from_run_exists_d hM hC hRun hRooted.positive
  obtain ⟨Y,hY,hCopy⟩ := copy_from_bad_d hM hC hT hA hLayers hBad hLayer hRun hX hFrom hn
  exact ⟨J,X,Y,hRun,hX,hFrom,hY,hCopy⟩

theorem parent_raw_iff_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {A : Context M.Domain} (hA : A.Valid M C) {X : Data M.Domain} {level r c s b q : M.Domain}
    (hc : M.mem c C.omega) (hNot : ¬M.mem c A.last) (hRaw : RawDecoded M C T A c s b) :
    Parent M C T A X level r c q ↔
      (HighSeam M A.last level r s ∧ ParentAt M X r A.root q) ∨
      (¬HighSeam M A.last level r s ∧ MappedParent M C T A X b r s q) := by
  constructor
  · rintro ⟨_,⟨hOld,_⟩ | ⟨_,s',_,b',_,hRaw',hCase⟩⟩
    · exact False.elim (hNot hOld)
    · obtain ⟨hss,hbb⟩ := raw_decode_unique_d hM hC hT hA hRaw' hRaw
      subst s'
      subst b'
      exact hCase
  · intro hCase
    exact ⟨hc,.inr ⟨hNot,s,hRaw.1,b,hRaw.2.1,hRaw,hCase⟩⟩

/-- 高接缝的父项就是原根的父项，目标列没有平移。 -/
theorem parent_raw_high_iff_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {A : Context M.Domain} (hA : A.Valid M C) {X : Data M.Domain} {level r c b q : M.Domain}
    (hc : M.mem c C.omega) (hNot : ¬M.mem c A.last) (hRaw : RawDecoded M C T A c A.last b)
    (hHigh : level=r ∨ M.mem level r) : Parent M C T A X level r c q ↔ ParentAt M X r A.root q := by
  rw [parent_raw_iff_d hM hC hT hA hc hNot hRaw]
  have hh : HighSeam M A.last level r A.last := ⟨rfl,hHigh⟩
  exact ⟨fun h => h.elim And.right (fun h => False.elim (h.1 hh)),fun h => .inl ⟨hh,h⟩⟩

theorem parent_raw_low_iff_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {A : Context M.Domain} (hA : A.Valid M C) {X : Data M.Domain} {level r c s b q : M.Domain}
    (hc : M.mem c C.omega) (hNot : ¬M.mem c A.last) (hRaw : RawDecoded M C T A c s b)
    (hLow : ¬HighSeam M A.last level r s) : Parent M C T A X level r c q ↔ MappedParent M C T A X b r s q := by
  rw [parent_raw_iff_d hM hC hT hA hc hNot hRaw]
  exact ⟨fun h => h.elim (fun h => False.elim (hLow h.1)) And.right,fun h => .inr ⟨hLow,h⟩⟩

theorem Active.root_height_ge {M : SetTheory.Structure.{u}} {C : ExpressionData M.Domain}
    {A : Context M.Domain} {X : Data M.Domain} (hX : X.Valid M C) {level height : M.Domain}
    (h : Active M X A level) (hHeight : MemPair M X.heights A.root height) : level=height ∨ M.mem level height :=
  hX.endpoint level A.last A.root height h.parent hHeight

theorem Copies.seam_heights_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {A : Context M.Domain} (hA : A.Valid M C) {X Y : Data M.Domain} {level n c b height : M.Domain}
    (h : Copies M C T A X level n Y) (hn : M.mem n C.omega) (hc : M.mem c n)
    (hNot : ¬M.mem c A.last) (hRaw : RawDecoded M C T A c A.last b) :
    MemPair M Y.heights c height ↔ MemPair M X.heights A.root height := by
  rw [h.heights c height,height_raw_seam_iff_d hM hC hT hA ((omega_isOrdinal_d hM hC.omega).transitive n hn c hc) hNot hRaw]
  exact ⟨And.right,fun h => ⟨hc,h⟩⟩

theorem Copies.high_seam_parents_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {A : Context M.Domain} (hA : A.Valid M C) {X Y : Data M.Domain} {level n r c b p : M.Domain}
    (h : Copies M C T A X level n Y) (hn : M.mem n C.omega) (hc : M.mem c n)
    (hNot : ¬M.mem c A.last) (hRaw : RawDecoded M C T A c A.last b) (hHigh : level=r ∨ M.mem level r) :
    ParentAt M Y r c p ↔ ParentAt M X r A.root p := by
  rw [h.parents r c p,parent_raw_high_iff_d hM hC hT hA ((omega_isOrdinal_d hM hC.omega).transitive n hn c hc) hNot hRaw hHigh]
  exact ⟨And.right,fun h => ⟨hc,h⟩⟩

end KP1Y.OneYFinite.CopiedMountain.Terminal
