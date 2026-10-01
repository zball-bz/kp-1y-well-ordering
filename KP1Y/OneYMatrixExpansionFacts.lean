import KP1Y.OneYMatrixExpansion
import KP1Y.OneYForestClosure
import KP1Y.OneYMatrixParents

/-! 已构造的真实矩阵展开之副本、前缀及后续父图后果。 -/
namespace KP1Y.OneYFinite
open YesMetaZFC YesMetaZFC.SetTheory YesMetaZFC.SetTheory.Definitional
open KP1Y.Kuratowski KP1Y.Functions KP1Y.Naturals KP1Y.Bounded
universe u

theorem lifted_entry_zero_iff_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {A : FiniteMatrix M.Domain} (hA : A.Valid M C.omega)
    {T : MatrixArithmetic M.Domain} (hT : T.Valid M C) {Forests Rows last maximal root source r y : M.Domain}
    (hLast : M.mem last A.width) (hRoot : M.mem root A.width) :
    LiftedEntry M C A T Forests Rows last maximal root C.zero source r y ↔ MatrixEntry M A r source y := by
  classical
  constructor
  · rintro ⟨a,ha,hEntry,hCase⟩
    rcases hCase with ⟨_,d,hd,t,_,_,hTimes,hPlus⟩ | ⟨_,he⟩
    · have ht := natural_product_zero_left_d hM hC hd ((hT.mul.mul_iff_product hM hC.zero_nat hd).mp hTimes)
      subst t
      have hy := ((hT.add.add_iff_sum hM ha hC.zero_nat).mp hPlus).zero_value_d hM hC.zero_empty
      exact hy.symm ▸ hEntry
    · exact he ▸ hEntry
  · intro hEntry
    have hBounds := hEntry.bounds hM.1 hA
    by_cases hAsc : Ascending M C A.width Forests Rows maximal root source r
    · obtain ⟨Inc,hInc,hRows⟩ := row_increment_graph_exists_d hM hA hT.diff hLast hRoot
      obtain ⟨d,hd,hAt⟩ := hInc.total r hBounds.1
      obtain ⟨t,_,hTimes⟩ := hT.mul.mul_exists_d hM hC hC.zero_nat hd
      have ht := natural_product_zero_left_d hM hC hd ((hT.mul.mul_iff_product hM hC.zero_nat hd).mp hTimes)
      subst t
      have hPlus := (hT.add.add_iff_sum hM hBounds.2.2 hC.zero_nat).mpr (KP1Y.Arithmetic.sum_zero_d hM y hC.zero_empty)
      exact ⟨y,hBounds.2.2,hEntry,Or.inl ⟨hAsc,d,hd,C.zero,hC.zero_nat,(hRows r d).mp hAt,hTimes,hPlus⟩⟩
    · exact ⟨y,hBounds.2.2,hEntry,Or.inr ⟨hAsc,rfl⟩⟩

theorem copy_position_zero_iff_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {root L slot target : M.Domain} (hRoot : M.mem root C.omega) (hL : M.mem L C.omega) :
    CopyPosition M C.omega T.addPairs T.plus T.mulPairs T.times root L C.zero slot target ↔ AddAt M T.addPairs T.plus root slot target := by
  constructor
  · rintro ⟨offset,_,start,_,hTimes,hStart,hTarget⟩
    have ho := natural_product_zero_left_d hM hC hL ((hT.mul.mul_iff_product hM hC.zero_nat hL).mp hTimes)
    subst offset
    have hs := ((hT.add.add_iff_sum hM hRoot hC.zero_nat).mp hStart).zero_value_d hM hC.zero_empty
    subst start
    exact hTarget
  · intro hTarget
    obtain ⟨offset,_,hTimes⟩ := hT.mul.mul_exists_d hM hC hC.zero_nat hL
    have ho := natural_product_zero_left_d hM hC hL ((hT.mul.mul_iff_product hM hC.zero_nat hL).mp hTimes)
    subst offset
    exact ⟨C.zero,hC.zero_nat,root,hRoot,hTimes,
      (hT.add.add_iff_sum hM hRoot hC.zero_nat).mpr (KP1Y.Arithmetic.sum_zero_d hM root hC.zero_empty),hTarget⟩

theorem RawMatrixExpansion.zero_width_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {A B : FiniteMatrix M.Domain} {T : MatrixArithmetic M.Domain}
    {Forests Rows last maximal root count L total : M.Domain}
    (h : RawMatrixExpansion M C A T Forests Rows last maximal root C.zero count L total B)
    (hRootLast : M.mem root last) : B.width=last := by
  have hCount := Structure.SuccessorOf.eq hM.1 h.copies hC.one_succ
  subst count
  have hL := truncated_difference_natural hM.1 h.difference
  have hTotal := natural_product_one_left_d hM hC hL h.product
  subst total
  exact KP1Y.Arithmetic.sum_unique_d hM h.width (truncated_difference_add_inverse_d hM hC h.difference (Or.inr hRootLast))

theorem RawMatrixExpansion.prefix_width_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {A B : FiniteMatrix M.Domain} {T : MatrixArithmetic M.Domain}
    {Forests Rows last maximal root index count L total : M.Domain}
    (h : RawMatrixExpansion M C A T Forests Rows last maximal root index count L total B)
    (hIndex : M.mem index C.omega) (hRootLast : M.mem root last) : M.MemberSubset last B.width := by
  have hw := omega_isOrdinal_d hM hC.omega
  have hCountNat := natural_successor_mem_d hM hC hIndex h.copies
  have hCountPos : M.mem C.zero count := by
    apply (hC.zero_mem_iff hM hCountNat).mpr
    intro he
    exact hC.zero_empty index (he ▸ h.copies.predecessor_mem)
  have hOneSub : M.MemberSubset C.one count := by
    intro x hx
    rcases (hC.one_succ x).mp hx with hx | he
    · exact False.elim (hC.zero_empty x hx)
    · exact (hM.1.eq_of_same_members x C.zero he) ▸ hCountPos
  have hL := truncated_difference_natural hM.1 h.difference
  obtain ⟨z,_,hOne⟩ := natural_product_exists_d hM hC hC.one_nat hL
  have hz := natural_product_one_left_d hM hC hL hOne
  subst z
  have hLT := natural_product_mono_left_d hM hC hC.one_nat hCountNat hL hOne h.product hOneSub
  exact KP1Y.Arithmetic.sum_mono_right_d hM (hw.mem h.difference.2.1)
    (truncated_difference_add_inverse_d hM hC h.difference (Or.inr hRootLast)) h.width hLT

/-- 任意复制次数都保留原末列之前的整个前缀，包括第0坏块。 -/
theorem RawMatrixExpansion.prefix_entry_iff_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {A B : FiniteMatrix M.Domain} (hA : A.Valid M C.omega)
    {T : MatrixArithmetic M.Domain} (hT : T.Valid M C) {Forests Rows last maximal root index count L total : M.Domain}
    (h : RawMatrixExpansion M C A T Forests Rows last maximal root index count L total B)
    (hLast : M.mem last A.width) (hRootLast : M.mem root last) (hIndex : M.mem index C.omega)
    {r c y : M.Domain} (hc : M.mem c last) : MatrixEntry M B r c y ↔ MatrixEntry M A r c y := by
  have hw := omega_isOrdinal_d hM hC.omega
  have hRoot := (hw.mem hA.width).transitive last hLast root hRootLast
  have hRootNat := h.difference.2.1
  have hL := truncated_difference_natural hM.1 h.difference
  have hCountNat := natural_successor_mem_d hM hC hIndex h.copies
  have hRootL := truncated_difference_add_inverse_d hM hC h.difference (Or.inr hRootLast)
  obtain ⟨oneProduct,_,hOneProduct⟩ := natural_product_exists_d hM hC hC.one_nat hL
  have hOneEq := natural_product_one_left_d hM hC hL hOneProduct
  subst oneProduct
  have hForward : ∀ r c y, M.mem c last → MatrixEntry M B r c y → MatrixEntry M A r c y := by
    intro r c y hc hEntry
    obtain ⟨_,_,hRaw⟩ := (h.entries r c y).mp hEntry
    rcases hRaw with ⟨_,hOld⟩ | ⟨hNot,copy,hCopy,slot,hSlot,source,_,hSource,hPos,hLift⟩
    · exact hOld
    · have hcNat := hw.transitive last h.difference.1 c hc
      have hAfter : root=c ∨ M.mem root c := by
        rcases hw.wellOrder.linear.compare root hRootNat c hcNat with he | hlt | hgt
        · exact Or.inl (hM.1.eq_of_same_members root c he)
        · exact Or.inr hlt
        · exact False.elim (hNot hgt)
      obtain ⟨copy0,hCopy0,slot0,hSlot0,hPos0⟩ := copy_interval_coverage_d hM hC hT.add hT.mul hRootNat hL hC.one_nat
        hOneProduct hRootL hc hAfter
      have hCopyZero : copy0=C.zero := by
        rcases (hC.one_succ copy0).mp hCopy0 with he | he
        · exact False.elim (hC.zero_empty copy0 he)
        · exact hM.1.eq_of_same_members copy0 C.zero he
      subst copy0
      obtain ⟨hCopyEq,_⟩ := copy_position_injective_d hM hC hT.add hT.mul hRootNat hL
        (hw.transitive count hCountNat copy hCopy) hC.zero_nat hSlot hSlot0 hPos hPos0
      subst copy
      have hRootSlot := (copy_position_zero_iff_d hM hC hT hRootNat hL).mp hPos
      have hSourceEq := hT.add.add_unique hM.1 hSource hRootSlot
      subst source
      exact (lifted_entry_zero_iff_d hM hC hA hT hLast hRoot).mp hLift
  constructor
  · exact hForward r c y hc
  · intro hEntry
    have hrA := (hEntry.bounds hM.1 hA).1
    have hrB : M.mem r B.height := Eq.mpr (congrArg (M.mem r) h.height) hrA
    have hcB := h.prefix_width_d hM hC hIndex hRootLast c hc
    obtain ⟨z,_,hZ⟩ := h.matrix.entry_total_d hM hrB hcB
    have hzy := hA.entry_unique hM.1 (hForward r c z hc hZ) hEntry
    exact hzy ▸ hZ

private def rowAncestorEnv {M : SetTheory.Structure.{u}} (C : ExpressionData M.Domain) (m Forests Rows : M.Domain) : Env M 8 :=
  (((((((oneEnv C.omega).push C.zero).push C.one).push C.sequences).push C.expressions).push m).push Forests).push Rows

private def rowAncestorSchema : Project.UnarySchema 8 where
  body := Project.Formula.forallMem (.bound 0) (Project.Formula.forallMem (.bound 3)
    (Project.Formula.forallMem (.bound 4) (Project.Formula.forallMem (.bound 6) (Project.Formula.forallMem (.bound 7)
      (.imp (.conj (memPairFormula (.bound 6) (.bound 4) (.bound 3))
        (.conj (memPairFormula (.bound 6) (.bound 5) (.bound 2))
          (ancestorFormula ⟨.bound 13,.bound 12,.bound 11,.bound 10,.bound 9⟩ (.bound 8) (.bound 2) (.bound 1) (.bound 0))))
        (ancestorFormula ⟨.bound 13,.bound 12,.bound 11,.bound 10,.bound 9⟩ (.bound 8) (.bound 3) (.bound 1) (.bound 0)))))))
  freeClosed := by
    have hC : (⟨.bound 13,.bound 12,.bound 11,.bound 10,.bound 9⟩ : ExpressionData (Project.Term 14)).Closed := ⟨rfl,rfl,rfl,rfl,rfl⟩
    have hA := ancestorFormula_freeClosed hC (.bound 8) (.bound 2) (.bound 1) (.bound 0) rfl rfl rfl rfl
    have hB := ancestorFormula_freeClosed hC (.bound 8) (.bound 3) (.bound 1) (.bound 0) rfl rfl rfl rfl
    simp [memPairFormula,codeFormula,pairFormula,Project.Formula.forallMem,Project.Formula.existsMem,Definitional.Formula.FreeClosed,hA,hB]

private theorem rowAncestorSchema_iff {M : SetTheory.Structure.{u}} (he : Extensional M)
    (C : ExpressionData M.Domain) (m Forests Rows s : M.Domain) :
    Project.Formula.satisfies ((rowAncestorEnv C m Forests Rows).push s) rowAncestorSchema.body ↔
      ∀ r, M.mem r s → ∀ P, M.mem P Forests → ∀ Q, M.mem Q Forests → ∀ a, M.mem a m → ∀ c, M.mem c m →
        MemPair M Rows r P ∧ MemPair M Rows s Q ∧ Ancestor M C m Q a c → Ancestor M C m P a c := by
  simp only [rowAncestorSchema,Project.Formula.satisfies_forallMem_iff,Project.Formula.satisfies_imp_iff,
    Project.Formula.satisfies_conj_iff,memPairFormula_iff he,ancestorFormula_iff he]
  rfl

/-- 真实逐行父算法的高行祖先关系在所有较低行仍成立。 -/
theorem MatrixParentRun.ancestor_below_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {m height Cells Values Forests Rows L : M.Domain}
    (h : MatrixParentRun M C m height Cells Values Forests Rows L) {r s P Q a c : M.Domain}
    (hrs : M.mem r s) (hP : MemPair M Rows r P) (hQ : MemPair M Rows s Q) (hAnc : Ancestor M C m Q a c) :
    Ancestor M C m P a c := by
  have hw := omega_isOrdinal_d hM hC.omega
  have hAll := natural_induction_d hM rowAncestorSchema (rowAncestorEnv C m Forests Rows) hC.omega
    (fun zero hEmpty => (rowAncestorSchema_iff hM.1 C m Forests Rows zero).mpr (by
      intro r hr
      exact False.elim (hEmpty r hr)))
    (fun prev _ ih s hs => (rowAncestorSchema_iff hM.1 C m Forests Rows s).mpr (by
      intro r hrs P hPMem Q _ a ha c hc hAnte
      obtain ⟨hP,hQ,hAnc⟩ := hAnte
      have hsH := (h.graph.bounds hM.1 hQ).1
      have hPrevH := (hw.mem h.height_nat).transitive s hsH prev hs.predecessor_mem
      obtain ⟨R,hRMem,hR⟩ := h.graph.total prev hPrevH
      obtain ⟨V,hV⟩ := h.values_exist s hsH
      have hLower := (h.step prev s R Q V hs hR hQ hV).ancestor_inherited_d hM hC hAnc
      rcases (hs r).mp hrs with hrPrev | he
      · exact (rowAncestorSchema_iff hM.1 C m Forests Rows prev).mp ih r hrPrev P hPMem R hRMem a ha c hc ⟨hP,hR,hLower⟩
      · have hEq := hM.1.eq_of_same_members r prev he
        subst r
        have hPR := h.graph.unique prev P R hP hR
        subst P
        exact hLower))
  exact (rowAncestorSchema_iff hM.1 C m Forests Rows s).mp
    (hAll s (hw.transitive height h.height_nat s (h.graph.bounds hM.1 hQ).1))
    r hrs P (h.graph.bounds hM.1 hP).2 Q (h.graph.bounds hM.1 hQ).2
      a (hAnc.bounds hM.1).1 c (hAnc.bounds hM.1).2 ⟨hP,hQ,hAnc⟩

theorem MatrixParentRun.selection_at_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {m height Cells Values Forests Rows L : M.Domain}
    (h : MatrixParentRun M C m height Cells Values Forests Rows L) {r P V : M.Domain}
    (hAt : MemPair M Rows r P) (hV : MatrixRowValues M C.omega m Cells Values r V) :
    ∃ inherited, Selects false M C m inherited V P := by
  have hw := omega_isOrdinal_d hM hC.omega
  have hr := (h.graph.bounds hM.1 hAt).1
  rcases natural_cases hM hC.omega (hw.transitive height h.height_nat r hr) with hEmpty | ⟨prev,_,hs⟩
  · have hz := hM.1.eq_of_same_members r C.zero (fun x => iff_of_false (hEmpty x) (hC.zero_empty x))
    subst r
    exact ⟨L,h.initial P V hAt hV⟩
  · have hp := (hw.mem h.height_nat).transitive r hr prev hs.predecessor_mem
    obtain ⟨Q,_,hQ⟩ := h.graph.total prev hp
    exact ⟨Q,h.step prev r Q P V hs hQ hAt hV⟩

theorem matrix_row_view_entry_iff_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {w : M.Domain} {A : FiniteMatrix M.Domain} (hA : A.Valid M w) {r V : M.Domain}
    (hr : M.mem r A.height) (hV : MatrixRowValues M w A.width A.cells A.values r V) (c d : M.Domain) :
    MemPair M V c d ↔ MatrixEntry M A r c d := by
  constructor
  · intro hAt
    obtain ⟨hc,hd⟩ := hV.graph.bounds hM.1 hAt
    obtain ⟨key,hCode⟩ := codes_total hM r c
    have hk := (hA.cells key).mpr ⟨r,hr,c,hc,hCode⟩
    exact ⟨key,hk,hCode,(hV.entries c hc key hk hCode d hd).mpr hAt⟩
  · intro hEntry
    have hBounds := hEntry.bounds hM.1 hA
    obtain ⟨key,hk,hCode,hAt⟩ := hEntry
    exact (hV.entries c hBounds.2.1 key hk hCode d hBounds.2.2).mp hAt

private def pathValueEnv {M : SetTheory.Structure.{u}} (C : ExpressionData M.Domain) (m P V : M.Domain) : Env M 8 :=
  (((((((oneEnv C.omega).push C.zero).push C.one).push C.sequences).push C.expressions).push m).push P).push V

private def pathValueSchema : Project.UnarySchema 8 where
  body := .forallE (.forallE (.forallE (Project.Formula.forallMem (.bound 11)
    (Project.Formula.forallMem (.bound 12) (.imp
      (.conj (parentPathFormula ⟨.bound 13,.bound 12,.bound 11,.bound 10,.bound 9⟩ (.bound 8) (.bound 7)
        (.bound 4) (.bound 5) (.bound 3) (.bound 2))
        (.conj (memPairFormula (.bound 6) (.bound 3) (.bound 1)) (memPairFormula (.bound 6) (.bound 2) (.bound 0))))
      (.disj (Project.Formula.extensionalEq (.bound 3) (.bound 2)) (.mem (.bound 1) (.bound 0))))))))
  freeClosed := by
    have hP := parentPathFormula_freeClosed
      (show (⟨.bound 13,.bound 12,.bound 11,.bound 10,.bound 9⟩ : ExpressionData (Project.Term 14)).Closed from ⟨rfl,rfl,rfl,rfl,rfl⟩)
      (.bound 8) (.bound 7) (.bound 4) (.bound 5) (.bound 3) (.bound 2) rfl rfl rfl rfl rfl rfl
    simp [Project.Formula.forallMem,Project.Formula.existsMem,Definitional.Formula.FreeClosed,memPairFormula,codeFormula,pairFormula,hP]

private theorem pathValueSchema_iff {M : SetTheory.Structure.{u}} (he : Extensional M)
    (C : ExpressionData M.Domain) (m P V len : M.Domain) :
    Project.Formula.satisfies ((pathValueEnv C m P V).push len) pathValueSchema.body ↔
      ∀ f a c, ∀ x, M.mem x C.omega → ∀ y, M.mem y C.omega →
        ParentPath M C m P f len a c ∧ MemPair M V a x ∧ MemPair M V c y → a=c ∨ M.mem x y := by
  simp only [pathValueSchema,Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_forallMem_iff,
    Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_disj_iff,
    Project.Formula.satisfies_extensionalEq_iff_eq he,Project.Formula.satisfies_mem_iff,
    parentPathFormula_iff he,memPairFormula_iff he]
  rfl

private theorem ancestor_values_lt_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {m P V a c x y : M.Domain}
    (hV : Graph M V m C.omega)
    (hParent : ∀ c p x y, MemPair M P c p → MemPair M V p x → MemPair M V c y → M.mem x y)
    (hAnc : Ancestor M C m P a c) (hAx : MemPair M V a x) (hCy : MemPair M V c y) : M.mem x y := by
  have hw := omega_isOrdinal_d hM hC.omega
  have hAll := natural_induction_d hM pathValueSchema (pathValueEnv C m P V) hC.omega
    (fun zero hEmpty => (pathValueSchema_iff hM.1 C m P V zero).mpr (by
      intro f a c x _ y _ hAnte
      exact False.elim (hEmpty C.zero (hAnte.1.zero_in_length hM.1))))
    (fun len hLen ih next hs => (pathValueSchema_iff hM.1 C m P V next).mpr (by
      intro f a c x hx y hy hAnte
      obtain ⟨hPath,hAx,hCy⟩ := hAnte
      rcases hPath.peel_d hM hC with ⟨_,he,_⟩ | ⟨prev,g,b,hPrev,_,_,hOld,hCb⟩
      · exact Or.inl he
      · have hLenPrev := Structure.SuccessorOf.predecessor_eq hM.1 (hw.mem hLen) hs hPrev
        subst prev
        obtain ⟨z,hz,hBz⟩ := hV.total b (hOld.end_bound hM.1)
        have hzy := hParent c b z y hCb hBz hCy
        rcases (pathValueSchema_iff hM.1 C m P V len).mp ih g a b x hx z hz ⟨hOld,hAx,hBz⟩ with he | hxz
        · subst b
          have hxz := hV.unique a x z hAx hBz
          exact Or.inr (hxz.symm ▸ hzy)
        · exact Or.inr (hw.wellOrder.linear.trans x hx z hz y hy hxz hzy)))
  obtain ⟨hac,len,_,f,_,hPath⟩ := hAnc
  rcases (pathValueSchema_iff hM.1 C m P V len).mp (hAll len hPath.length) f a c x (hV.bounds hM.1 hAx).2 y
      (hV.bounds hM.1 hCy).2 ⟨hPath,hAx,hCy⟩ with he | hxy
  · exact False.elim (SetTheory.KP.mem_irrefl_d (KP1Y.models_weakKP hM) c (he ▸ hac))
  · exact hxy

theorem MatrixParentRun.ancestor_entry_lt_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {A : FiniteMatrix M.Domain} (hA : A.Valid M C.omega)
    {Forests Rows L : M.Domain} (h : MatrixParentRun M C A.width A.height A.cells A.values Forests Rows L)
    {r P a c x y : M.Domain} (hAt : MemPair M Rows r P) (hAnc : Ancestor M C A.width P a c)
    (hAx : MatrixEntry M A r a x) (hCy : MatrixEntry M A r c y) : M.mem x y := by
  have hr := (h.graph.bounds hM.1 hAt).1
  obtain ⟨V,hV⟩ := hA.row_view_d hM hr
  obtain ⟨inherited,hSel⟩ := h.selection_at_d hM hC hAt hV
  have hParent : ∀ c p x y, MemPair M P c p → MemPair M V p x → MemPair M V c y → M.mem x y := by
    intro c p x y hCp hPx hCy
    obtain ⟨u,_,v,_,hPu,hCv,huv,_⟩ := hSel.parent_values hCp
    have hxu := hV.graph.unique p x u hPx hPu
    have hyv := hV.graph.unique c y v hCy hCv
    exact hxu.symm ▸ hyv.symm ▸ huv
  exact ancestor_values_lt_d hM hC hV.graph hParent hAnc
    ((matrix_row_view_entry_iff_d hM hA hr hV a x).mpr hAx) ((matrix_row_view_entry_iff_d hM hA hr hV c y).mpr hCy)

theorem MatrixExpansionContext.increment_positive_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {A : FiniteMatrix M.Domain} (hA : A.Valid M C.omega)
    {Forests Rows L last maximal root DiffPairs Diff r d : M.Domain}
    (hRun : MatrixParentRun M C A.width A.height A.cells A.values Forests Rows L)
    (h : MatrixExpansionContext M C A Forests Rows last maximal root) (hDiff : DifferenceTable M C DiffPairs Diff)
    (hr : M.mem r maximal) (hInc : RowIncrement M C.omega A DiffPairs Diff last root r d) : M.mem C.zero d := by
  obtain ⟨P,_,hP,hParent⟩ := h.parent
  have hTopAncestor := ancestor_direct_d hM hC (hRun.forests maximal P hP) hParent
  have hw := omega_isOrdinal_d hM hC.omega
  have hrH := (hw.mem hA.height).transitive maximal h.row r hr
  obtain ⟨Q,_,hQ⟩ := hRun.graph.total r hrH
  have hAncestor := hRun.ancestor_below_d hM hC hr hQ hP hTopAncestor
  obtain ⟨x,hx,y,hy,key,_,hCode,hLast,hRoot,hAt⟩ := hInc
  have hyx := hRun.ancestor_entry_lt_d hM hC hA hQ hAncestor hRoot hLast
  have hD := (hDiff.rows x hx y hy key hCode d).mp hAt
  exact (truncated_difference_positive_iff_d hM hC hD).mpr hyx

theorem lifted_entry_unascending_iff {M : SetTheory.Structure.{u}} (he : Extensional M)
    {C : ExpressionData M.Domain} {A : FiniteMatrix M.Domain} (hA : A.Valid M C.omega) {T : MatrixArithmetic M.Domain}
    {Forests Rows last maximal root copy source r y : M.Domain}
    (hNot : ¬Ascending M C A.width Forests Rows maximal root source r) :
    LiftedEntry M C A T Forests Rows last maximal root copy source r y ↔ MatrixEntry M A r source y := by
  constructor
  · rintro ⟨a,_,hEntry,hCase⟩
    rcases hCase with ⟨hAsc,_⟩ | ⟨_,hy⟩
    · exact False.elim (hNot hAsc)
    · exact hy ▸ hEntry
  · intro hEntry
    exact ⟨y,(hEntry.bounds he hA).2.2,hEntry,Or.inr ⟨hNot,rfl⟩⟩

theorem copy_position_not_good_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {root L copy slot c : M.Domain} (hRoot : M.mem root C.omega) (hSlot : M.mem slot C.omega)
    (hPos : CopyPosition M C.omega T.addPairs T.plus T.mulPairs T.times root L copy slot c) : ¬M.mem c root := by
  obtain ⟨offset,hOffset,start,hStart,_,hRootStart,hStartC⟩ := hPos
  have hw := omega_isOrdinal_d hM hC.omega
  have hRS := KP1Y.Arithmetic.sum_base_subset_d hM (hw.mem hRoot) ((hT.add.add_iff_sum hM hRoot hOffset).mp hRootStart)
  have hSC := KP1Y.Arithmetic.sum_base_subset_d hM (hw.mem hStart) ((hT.add.add_iff_sum hM hStart hSlot).mp hStartC)
  intro hc
  exact SetTheory.KP.mem_irrefl_d (KP1Y.models_weakKP hM) c (hSC c (hRS c hc))

/-- 真实二维输出在任一有效副本坐标上，恰等于精确 ascending 加量公式。 -/
theorem RawMatrixExpansion.copied_entry_iff_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {A B : FiniteMatrix M.Domain} (hA : A.Valid M C.omega)
    {T : MatrixArithmetic M.Domain} (hT : T.Valid M C) {Forests Rows last maximal root index count L total : M.Domain}
    (h : RawMatrixExpansion M C A T Forests Rows last maximal root index count L total B)
    (hLast : M.mem last A.width) (hRootLast : M.mem root last) (hIndex : M.mem index C.omega)
    {copy slot source c r y : M.Domain} (hCopy : copy=index ∨ M.mem copy index) (hSlot : M.mem slot L)
    (hSource : AddAt M T.addPairs T.plus root slot source)
    (hPos : CopyPosition M C.omega T.addPairs T.plus T.mulPairs T.times root L copy slot c) :
    MatrixEntry M B r c y ↔ LiftedEntry M C A T Forests Rows last maximal root copy source r y := by
  have hw := omega_isOrdinal_d hM hC.omega
  have hRootNat := h.difference.2.1
  have hL := truncated_difference_natural hM.1 h.difference
  have hCountNat := natural_successor_mem_d hM hC hIndex h.copies
  have hCopyCount : M.mem copy count := by
    rcases hCopy with he | hci
    · exact he ▸ h.copies.predecessor_mem
    · exact (h.copies copy).mpr (Or.inl hci)
  have hCopyNat := hw.transitive count hCountNat copy hCopyCount
  have hSlotNat := hw.transitive L hL slot hSlot
  have hNotGood := copy_position_not_good_d hM hC hT hRootNat hSlotNat hPos
  have hCWidth := copy_position_bounded_d hM hC hT.add hT.mul hRootNat hL hCountNat h.product h.width hCopyCount hSlot hPos
  have hSourceLast := KP1Y.Arithmetic.sum_strict_right_d hM (hw.mem hRootNat)
    ((hT.add.add_iff_sum hM hRootNat hSlotNat).mp hSource)
    (truncated_difference_add_inverse_d hM hC h.difference (Or.inr hRootLast)) hSlot
  have hSourceWidth := (hw.mem hA.width).transitive last hLast source hSourceLast
  constructor
  · intro hEntry
    obtain ⟨_,_,hRaw⟩ := (h.entries r c y).mp hEntry
    rcases hRaw with ⟨hGood,_⟩ | ⟨_,copy',hCopy',slot',hSlot',source',_,hSource',hPos',hLift⟩
    · exact False.elim (hNotGood hGood)
    · obtain ⟨hCopies,hSlots⟩ := copy_position_injective_d hM hC hT.add hT.mul hRootNat hL hCopyNat
        (hw.transitive count hCountNat copy' hCopy') hSlot hSlot' hPos hPos'
      subst copy'
      subst slot'
      have hSources := hT.add.add_unique hM.1 hSource hSource'
      subst source'
      exact hLift
  · intro hLift
    have hr : M.mem r A.height := by
      obtain ⟨_,_,hEntry,_⟩ := hLift
      exact (hEntry.bounds hM.1 hA).1
    exact (h.entries r c y).mpr ⟨hr,hCWidth,Or.inr ⟨hNotGood,copy,hCopyCount,slot,hSlot,source,hSourceWidth,hSource,hPos,hLift⟩⟩

theorem RawMatrixExpansion.copied_unascending_iff_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {A B : FiniteMatrix M.Domain} (hA : A.Valid M C.omega)
    {T : MatrixArithmetic M.Domain} (hT : T.Valid M C) {Forests Rows last maximal root index count L total : M.Domain}
    (h : RawMatrixExpansion M C A T Forests Rows last maximal root index count L total B)
    (hLast : M.mem last A.width) (hRootLast : M.mem root last) (hIndex : M.mem index C.omega)
    {copy slot source c r y : M.Domain} (hCopy : copy=index ∨ M.mem copy index) (hSlot : M.mem slot L)
    (hSource : AddAt M T.addPairs T.plus root slot source)
    (hPos : CopyPosition M C.omega T.addPairs T.plus T.mulPairs T.times root L copy slot c)
    (hNot : ¬Ascending M C A.width Forests Rows maximal root source r) : MatrixEntry M B r c y ↔ MatrixEntry M A r source y :=
  (h.copied_entry_iff_d hM hC hA hT hLast hRootLast hIndex hCopy hSlot hSource hPos).trans (lifted_entry_unascending_iff hM.1 hA hNot)

theorem MatrixParentRun.not_ascending_above_good_parent_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {m height Cells Values Forests Rows Linear : M.Domain}
    (hRun : MatrixParentRun M C m height Cells Values Forests Rows Linear) {r s P source p root maximal : M.Domain}
    (hP : MemPair M Rows r P) (hParent : MemPair M P source p) (hGood : M.mem p root) (hNonroot : source≠root)
    (hrs : M.mem r s) : ¬Ascending M C m Forests Rows maximal root source s := by
  rintro ⟨_,hAsc⟩
  rcases hAsc with he | ⟨Q,_,hQ,hAncestor⟩
  · exact hNonroot he
  · have hBelow := hRun.ancestor_below_d hM hC hrs hP hQ hAncestor
    have hRootNat := (omega_isOrdinal_d hM hC.omega).transitive m hRun.linear.1.width root (hBelow.bounds hM.1).1
    rcases ancestor_le_parent_d hM hC (hRun.forests r P hP) hParent hBelow with he | hrp
    · exact SetTheory.KP.mem_irrefl_d (KP1Y.models_weakKP hM) p (he ▸ hGood)
    · exact SetTheory.KP.mem_irrefl_d (KP1Y.models_weakKP hM) root
        (((omega_isOrdinal_d hM hC.omega).mem hRootNat).transitive p hGood root hrp)

theorem MatrixExpansionContext.last_ascending_below_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {A : FiniteMatrix M.Domain} {Forests Rows Linear last maximal root r : M.Domain}
    (hRun : MatrixParentRun M C A.width A.height A.cells A.values Forests Rows Linear)
    (h : MatrixExpansionContext M C A Forests Rows last maximal root) (hr : M.mem r maximal) :
    Ascending M C A.width Forests Rows maximal root last r := by
  obtain ⟨P,_,hP,hParent⟩ := h.parent
  have hTop := ancestor_direct_d hM hC (hRun.forests maximal P hP) hParent
  have hrH := ((omega_isOrdinal_d hM hC.omega).mem hRun.height_nat).transitive maximal h.row r hr
  obtain ⟨Q,hQMem,hQ⟩ := hRun.graph.total r hrH
  exact ⟨hr,Or.inr ⟨Q,hQMem,hQ,hRun.ancestor_below_d hM hC hr hQ hP hTop⟩⟩

/-- 低行的新复制根与前一副本的虚拟末列相等，按真实值公式和行增量反解证明。 -/
theorem MatrixExpansionContext.lifted_root_succ_eq_last_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {A : FiniteMatrix M.Domain} (hA : A.Valid M C.omega)
    {T : MatrixArithmetic M.Domain} (hT : T.Valid M C) {Forests Rows Linear last maximal root r copy next x y : M.Domain}
    (hRun : MatrixParentRun M C A.width A.height A.cells A.values Forests Rows Linear)
    (h : MatrixExpansionContext M C A Forests Rows last maximal root)
    (hr : M.mem r maximal) (hCopy : M.mem copy C.omega) (hNext : M.SuccessorOf next copy)
    (hNew : LiftedEntry M C A T Forests Rows last maximal root next root r x)
    (hOld : LiftedEntry M C A T Forests Rows last maximal root copy last r y) : x=y := by
  have hAscRoot : Ascending M C A.width Forests Rows maximal root root r := ⟨hr,Or.inl rfl⟩
  have hAscLast := h.last_ascending_below_d hM hC hRun hr
  obtain ⟨a,ha,hRootEntry,hNewCases⟩ := hNew
  obtain ⟨b,hb,hLastEntry,hOldCases⟩ := hOld
  rcases hNewCases with ⟨_,d,hd,t,ht,hInc,hTimes,hPlus⟩ | ⟨hNot,_⟩
  · rcases hOldCases with ⟨_,d',_,u,hu,hInc',hTimes',hPlus'⟩ | ⟨hNot,_⟩
    · have hdd' := row_increment_unique_d hM hA hT.diff hInc hInc'
      subst d'
      have hPositive := h.increment_positive_d hM hC hA hRun hT.diff hr hInc
      obtain ⟨b',hb',a',ha',key,_,hCode,hLast',hRoot',hDiff⟩ := hInc
      have hbb := hA.entry_unique hM.1 hLastEntry hLast'
      have haa := hA.entry_unique hM.1 hRootEntry hRoot'
      subst b'
      subst a'
      have hDifference := (hT.diff.rows b hb' a ha' key hCode d).mp hDiff
      have hab := (truncated_difference_positive_iff_d hM hC hDifference).mp hPositive
      have hRootDelta := truncated_difference_add_inverse_d hM hC hDifference (Or.inr hab)
      have hNextNat := natural_successor_mem_d hM hC hCopy hNext
      have hProductStep := natural_product_left_successor_d hM hC hCopy hd hNext
        ((hT.mul.mul_iff_product hM hCopy hd).mp hTimes') ((hT.mul.mul_iff_product hM hNextNat hd).mp hTimes)
      have hNewSum := (hT.add.add_iff_sum hM ha ht).mp hPlus
      have hOldSum := (hT.add.add_iff_sum hM hb hu).mp hPlus'
      obtain ⟨base,hBase,hBaseSum⟩ := natural_sum_exists_d hM hC.omega ha hu
      obtain ⟨z,_,hZ⟩ := natural_sum_exists_d hM hC.omega hBase hd
      have hZX := natural_sum_assoc_d hM hC hu hd hBaseSum hZ hProductStep hNewSum
      have hYZ := natural_sum_shuffle_d hM hC hd hu hRootDelta hOldSum hBaseSum hZ
      exact hZX.symm.trans hYZ.symm
    · exact False.elim (hNot hAscLast)
  · exact False.elim (hNot hAscRoot)

/-- 最大父行处，新复制根严格小于虚拟末列；不依赖副本编号。 -/
theorem MatrixExpansionContext.lifted_root_lt_last_at_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {A : FiniteMatrix M.Domain} (hA : A.Valid M C.omega)
    {T : MatrixArithmetic M.Domain} {Forests Rows Linear last maximal root copy copy' x y : M.Domain}
    (hRun : MatrixParentRun M C A.width A.height A.cells A.values Forests Rows Linear)
    (h : MatrixExpansionContext M C A Forests Rows last maximal root)
    (hRoot : LiftedEntry M C A T Forests Rows last maximal root copy root maximal x)
    (hLast : LiftedEntry M C A T Forests Rows last maximal root copy' last maximal y) : M.mem x y := by
  have hNot (source : M.Domain) : ¬Ascending M C A.width Forests Rows maximal root source maximal :=
    fun h => SetTheory.KP.mem_irrefl_d (KP1Y.models_weakKP hM) maximal h.1
  have hRootEntry := (lifted_entry_unascending_iff hM.1 hA (hNot root)).mp hRoot
  have hLastEntry := (lifted_entry_unascending_iff hM.1 hA (hNot last)).mp hLast
  obtain ⟨P,_,hP,hParent⟩ := h.parent
  exact hRun.ancestor_entry_lt_d hM hC hA hP (ancestor_direct_d hM hC (hRun.forests maximal P hP) hParent) hRootEntry hLastEntry

theorem selects_common_prefix_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {positive : Bool} {m n cut F G V W P Q : M.Domain}
    (hP : Selects positive M C m F V P) (hQ : Selects positive M C n G W Q)
    (hCut : M.mem cut C.omega) (hSubM : M.MemberSubset cut m) (hSubN : M.MemberSubset cut n)
    (hParents : RowsAgreeOn M F G cut) (hValues : RowsAgreeOn M V W cut) : RowsAgreeOn M P Q cut := by
  obtain ⟨S,hS,hFS⟩ := hP.inherited.restrict_d hM hC.omega hCut
  obtain ⟨VS,hVS,hVSRows⟩ := restrict_graph_d hM hP.values hSubM
  have hVVS : RowsAgreeOn M V VS cut := fun c hc x => ((hVSRows c x).trans ⟨And.right,fun h => ⟨hc,h⟩⟩).symm
  obtain ⟨R,hR⟩ := select_forest_exists_d hM positive hC hS hVS
  have hPR := hP.prefix_rows_d hM hC hR hSubM hFS hVVS
  have hQR := hQ.prefix_rows_d hM hC hR hSubN
    (fun c hc p => (hParents c hc p).symm.trans (hFS c hc p))
    (fun c hc x => (hValues c hc x).symm.trans (hVVS c hc x))
  exact fun c hc p => (hPR c hc p).trans (hQR c hc p).symm

private def parentPrefixEnv {M : SetTheory.Structure.{u}} (Rows Other Forests OtherForests cut : M.Domain) : Env M 5 :=
  ((((oneEnv Rows).push Other).push Forests).push OtherForests).push cut

private def parentPrefixSchema : Project.UnarySchema 5 where
  body := Project.Formula.forallMem (.bound 3) (Project.Formula.forallMem (.bound 3)
    (.imp (.conj (memPairFormula (.bound 7) (.bound 2) (.bound 1)) (memPairFormula (.bound 6) (.bound 2) (.bound 0)))
      (Project.Formula.forallMem (.bound 3) (.forallE
        (.iff (memPairFormula (.bound 3) (.bound 1) (.bound 0)) (memPairFormula (.bound 2) (.bound 1) (.bound 0)))))))
  freeClosed := by
    simp [memPairFormula,codeFormula,pairFormula,Project.Formula.forallMem,Project.Formula.existsMem,Definitional.Formula.FreeClosed]

private theorem parentPrefixSchema_iff {M : SetTheory.Structure.{u}} (he : Extensional M)
    (Rows Other Forests OtherForests cut r : M.Domain) :
    Project.Formula.satisfies ((parentPrefixEnv Rows Other Forests OtherForests cut).push r) parentPrefixSchema.body ↔
      ∀ P, M.mem P Forests → ∀ Q, M.mem Q OtherForests → MemPair M Rows r P ∧ MemPair M Other r Q → RowsAgreeOn M P Q cut := by
  simp only [parentPrefixSchema,RowsAgreeOn,Project.Formula.satisfies_forallMem_iff,Project.Formula.satisfies_forall_iff,
    Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_iff_iff,memPairFormula_iff he]
  rfl

/-- 两个实际父运行在数值共同前缀上相同，即使两个矩阵宽度不同。 -/
theorem matrix_parent_common_prefix_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {A B : FiniteMatrix M.Domain}
    (hA : A.Valid M C.omega) (hB : B.Valid M C.omega) {Forests Rows L OtherForests Other OtherL cut : M.Domain}
    (hRun : MatrixParentRun M C A.width A.height A.cells A.values Forests Rows L)
    (hOther : MatrixParentRun M C B.width B.height B.cells B.values OtherForests Other OtherL)
    (hCut : M.mem cut C.omega) (hCutA : M.MemberSubset cut A.width) (hCutB : M.MemberSubset cut B.width)
    (hEntries : ∀ r c d, M.mem r A.height → M.mem r B.height → M.mem c cut →
      (MatrixEntry M A r c d ↔ MatrixEntry M B r c d)) :
    ∀ r P Q, MemPair M Rows r P → MemPair M Other r Q → RowsAgreeOn M P Q cut := by
  have hValues (r V W : M.Domain) (hrA : M.mem r A.height) (hrB : M.mem r B.height)
      (hV : MatrixRowValues M C.omega A.width A.cells A.values r V)
      (hW : MatrixRowValues M C.omega B.width B.cells B.values r W) : RowsAgreeOn M V W cut := by
    intro c hc d
    exact (matrix_row_view_entry_iff_d hM hA hrA hV c d).trans
      ((hEntries r c d hrA hrB hc).trans (matrix_row_view_entry_iff_d hM hB hrB hW c d).symm)
  have hAll := natural_induction_d hM parentPrefixSchema (parentPrefixEnv Rows Other Forests OtherForests cut) hC.omega
    (fun zero hEmpty => (parentPrefixSchema_iff hM.1 Rows Other Forests OtherForests cut zero).mpr (by
      have hz := hM.1.eq_of_same_members zero C.zero (fun x => iff_of_false (hEmpty x) (hC.zero_empty x))
      subst zero
      intro P _ Q _ hAnte
      obtain ⟨hP,hQ⟩ := hAnte
      have hzA := (hRun.graph.bounds hM.1 hP).1
      have hzB := (hOther.graph.bounds hM.1 hQ).1
      obtain ⟨V,hV⟩ := hRun.values_exist C.zero hzA
      obtain ⟨W,hW⟩ := hOther.values_exist C.zero hzB
      have hLinear : RowsAgreeOn M L OtherL cut := by
        intro c hc p
        rw [hRun.linear.2 c p,hOther.linear.2 c p]
        simp only [hCutA c hc,hCutB c hc,true_and]
      exact selects_common_prefix_d hM hC (hRun.initial P V hP hV) (hOther.initial Q W hQ hW)
        hCut hCutA hCutB hLinear (hValues C.zero V W hzA hzB hV hW)))
    (fun prev _ ih r hs => (parentPrefixSchema_iff hM.1 Rows Other Forests OtherForests cut r).mpr (by
      intro P _ Q _ hAnte
      obtain ⟨hP,hQ⟩ := hAnte
      have hrA := (hRun.graph.bounds hM.1 hP).1
      have hrB := (hOther.graph.bounds hM.1 hQ).1
      have hw := omega_isOrdinal_d hM hC.omega
      have hpA := (hw.mem hA.height).transitive r hrA prev hs.predecessor_mem
      have hpB := (hw.mem hB.height).transitive r hrB prev hs.predecessor_mem
      obtain ⟨P0,hP0Mem,hP0⟩ := hRun.graph.total prev hpA
      obtain ⟨Q0,hQ0Mem,hQ0⟩ := hOther.graph.total prev hpB
      have hParents := (parentPrefixSchema_iff hM.1 Rows Other Forests OtherForests cut prev).mp ih P0 hP0Mem Q0 hQ0Mem ⟨hP0,hQ0⟩
      obtain ⟨V,hV⟩ := hRun.values_exist r hrA
      obtain ⟨W,hW⟩ := hOther.values_exist r hrB
      exact selects_common_prefix_d hM hC (hRun.step prev r P0 P V hs hP0 hP hV) (hOther.step prev r Q0 Q W hs hQ0 hQ hW)
        hCut hCutA hCutB hParents (hValues r V W hrA hrB hV hW)))
  intro r P Q hP hQ
  have hrω := (omega_isOrdinal_d hM hC.omega).transitive A.height hA.height r (hRun.graph.bounds hM.1 hP).1
  exact (parentPrefixSchema_iff hM.1 Rows Other Forests OtherForests cut r).mp (hAll r hrω)
    P (hRun.graph.bounds hM.1 hP).2 Q (hOther.graph.bounds hM.1 hQ).2 ⟨hP,hQ⟩

theorem RawMatrixExpansion.parent_prefix_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {A B : FiniteMatrix M.Domain} (hA : A.Valid M C.omega)
    {T : MatrixArithmetic M.Domain} (hT : T.Valid M C) {Forests Rows L OtherForests Other OtherL last maximal root index count len total : M.Domain}
    (hRun : MatrixParentRun M C A.width A.height A.cells A.values Forests Rows L)
    (h : RawMatrixExpansion M C A T Forests Rows last maximal root index count len total B)
    (hOther : MatrixParentRun M C B.width B.height B.cells B.values OtherForests Other OtherL)
    (hLast : M.mem last A.width) (hRootLast : M.mem root last) (hIndex : M.mem index C.omega) :
    ∀ r P Q, MemPair M Rows r P → MemPair M Other r Q → RowsAgreeOn M P Q last := by
  have hw := omega_isOrdinal_d hM hC.omega
  exact matrix_parent_common_prefix_d hM hC hA h.matrix hRun hOther
    (hw.transitive A.width hA.width last hLast) ((hw.mem hA.width).transitive last hLast)
    (h.prefix_width_d hM hC hIndex hRootLast)
    (fun r c d _ _ hc => (h.prefix_entry_iff_d hM hC hA hT hLast hRootLast hIndex (r := r) (y := d) hc).symm)

theorem matrix_prefix_run_exists_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {A : FiniteMatrix M.Domain} (hA : A.Valid M C.omega)
    {Forests Rows L n : M.Domain} (hRun : MatrixParentRun M C A.width A.height A.cells A.values Forests Rows L)
    (hn : M.mem n C.omega) (hSub : M.MemberSubset n A.width) :
    ∃ B OtherForests Other OtherL, B.Valid M C.omega ∧ B.height=A.height ∧ B.width=n ∧
      MatrixParentRun M C B.width B.height B.cells B.values OtherForests Other OtherL ∧
      (∀ r c d, M.mem c n → (MatrixEntry M B r c d ↔ MatrixEntry M A r c d)) ∧
      ∀ r P Q, MemPair M Rows r P → MemPair M Other r Q → RowsAgreeOn M P Q n := by
  obtain ⟨B,hB,hHeight,hWidth,hEntries⟩ := hA.prefix_exists_d hM hn hSub
  obtain ⟨OtherForests,Other,OtherL,hOther⟩ := matrix_parent_run_exists_d hM hC hB
  have hToB : M.MemberSubset n B.width := hWidth ▸ fun _ h => h
  have hParents := matrix_parent_common_prefix_d hM hC hA hB hRun hOther hn hSub hToB
    (fun r c d _ _ hc => (hEntries r c d hc).symm)
  exact ⟨B,OtherForests,Other,OtherL,hB,hHeight,hWidth,hOther,hEntries,hParents⟩

theorem ancestor_common_prefix_iff_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {m n cut P Q a c : M.Domain}
    (hP : Forest M C.omega m P) (hQ : Forest M C.omega n Q) (hCut : M.mem cut C.omega)
    (hCutM : M.MemberSubset cut m) (hCutN : M.MemberSubset cut n) (hc : M.mem c cut)
    (hRows : RowsAgreeOn M P Q cut) : Ancestor M C m P a c ↔ Ancestor M C n Q a c :=
  (ancestor_prefix_iff_d hM hC hP hCut hCutM hc hRows).trans
    (ancestor_prefix_iff_d hM hC hQ hCut hCutN hc (fun _ _ _ => Iff.rfl)).symm

theorem RawMatrixExpansion.ancestor_prefix_iff_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {A B : FiniteMatrix M.Domain} (hA : A.Valid M C.omega)
    {T : MatrixArithmetic M.Domain} (hT : T.Valid M C) {Forests Rows L OtherForests Other OtherL last maximal root index count len total : M.Domain}
    (hRun : MatrixParentRun M C A.width A.height A.cells A.values Forests Rows L)
    (h : RawMatrixExpansion M C A T Forests Rows last maximal root index count len total B)
    (hOther : MatrixParentRun M C B.width B.height B.cells B.values OtherForests Other OtherL)
    (hLast : M.mem last A.width) (hRootLast : M.mem root last) (hIndex : M.mem index C.omega)
    {r P Q a c : M.Domain} (hP : MemPair M Rows r P) (hQ : MemPair M Other r Q) (hc : M.mem c last) :
    Ancestor M C A.width P a c ↔ Ancestor M C B.width Q a c := by
  have hw := omega_isOrdinal_d hM hC.omega
  exact ancestor_common_prefix_iff_d hM hC (hRun.forests r P hP) (hOther.forests r Q hQ)
    (hw.transitive A.width hA.width last hLast) ((hw.mem hA.width).transitive last hLast)
    (h.prefix_width_d hM hC hIndex hRootLast) hc (h.parent_prefix_d hM hC hA hT hRun hOther hLast hRootLast hIndex r P Q hP hQ)

end KP1Y.OneYFinite
