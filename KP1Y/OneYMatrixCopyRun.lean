import KP1Y.OneYMatrixCopyLowSelection

/-! 将逐行的真实父选择闭合为整个实际有限矩阵父运行的复制定理。 -/
namespace KP1Y.OneYFinite.MatrixCopy
open YesMetaZFC YesMetaZFC.SetTheory YesMetaZFC.SetTheory.Definitional
open KP1Y.Kuratowski KP1Y.Functions KP1Y.Naturals KP1Y.Bounded
open KP1Y.OneYFinite KP1Y.Arithmetic
universe u

/-- 已知上一行的实际复制图，逐个好部/非root/root分支识别当前实际选择行。 -/
theorem selected_row_is_copy_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {A B : FiniteMatrix M.Domain} (hA : A.Valid M C.omega)
    {T : MatrixArithmetic M.Domain} (hT : T.Valid M C) {X : CopyCoordinates.Context M.Domain} (hX : X.Valid M C)
    {Forests Rows L maximal index count total r F P previous previousMax QF V VB Q : M.Domain}
    (hRun : MatrixParentRun M C A.width A.height A.cells A.values Forests Rows L)
    (hContext : MatrixExpansionContext M C A Forests Rows X.last maximal X.root)
    (hExp : RawMatrixExpansion M C A T Forests Rows X.last maximal X.root index count X.length total B)
    (hIndex : M.mem index C.omega)
    (hPrevious : PreviousMatrixForest M C A.height Forests Rows L r F) (hP : MemPair M Rows r P)
    (hV : MatrixRowValues M C.omega A.width A.cells A.values r V)
    (hVB : MatrixRowValues M C.omega B.width B.cells B.values r VB) (hNew : Selects false M C B.width QF VB Q)
    (hCF : CopyForest M C T X F previous previousMax count B.width QF)
    (hPreviousHigh : ¬M.mem previous previousMax → ¬M.mem r maximal)
    (hRootLast : M.mem previous previousMax → Ancestor M C A.width P X.root X.last)
    (hPrefix : RowsAgreeOn M P Q X.last) : CopyForest M C T X P r maximal count B.width Q := by
  have hw := omega_isOrdinal_d hM hC.omega
  have hLast := hContext.width_successor.predecessor_mem
  have hr := (hRun.graph.bounds hM.1 hP).1
  have hSel := hRun.selects_previous_d hPrevious hP hV
  obtain ⟨Qc,hQc⟩ := copy_forest_exists_d hM hC hT hX hSel.forest hCF.count_nat hExp.product hExp.width
    (row := r) (maximal := maximal)
  have hEqual : Q=Qc := hNew.forest.ext hM.1 hQc.forest (by
    intro child target
    classical
    by_cases hChild : M.mem child B.width
    · rcases hCF.column_cases_d hM hC hT hX hChild with hGood | ⟨copy,hCopy,slot,hSlot,source,hSource,hAdd,hPos⟩
      · have hcLast := (hw.mem hX.last).transitive X.root hX.below child hGood
        exact (hPrefix child hcLast target).symm.trans (hQc.good_parent_iff_d hM hC hT hX hGood).symm
      · have hCopyNat := hw.transitive count hCF.count_nat copy hCopy
        have hSlotNat := hw.transitive X.length (hX.length_nat hM.1) slot hSlot
        have hSourceNat := hw.transitive X.last hX.last source hSource
        have hSourceAfter : X.root=source ∨ M.mem X.root source :=
          ordinal_subset_cases_d hM (hw.mem hX.root) (hw.mem hSourceNat)
            (sum_base_subset_d hM (hw.mem hX.root) ((hT.add.add_iff_sum hM hX.root hSlotNat).mp hAdd))
        have hNotGood : ¬M.mem source X.root := by
          intro hGood
          rcases hSourceAfter with he | hlt
          · exact SetTheory.KP.mem_irrefl_d (KP1Y.models_weakKP hM) X.root (he.symm ▸ hGood)
          · exact SetTheory.KP.mem_irrefl_d (KP1Y.models_weakKP hM) X.root ((hw.mem hX.root).transitive source hGood X.root hlt)
        have hMap := (CopyCoordinates.parent_copy_bad_iff hNotGood).mpr
          ((CopyCoordinates.encode_at_base_iff_d hM hC hT hX.root hSlotNat hCopyNat hAdd).mpr hPos)
        by_cases hPrevLow : M.mem previous previousMax
        · by_cases hNonroot : source≠X.root
          · exact (low_nonroot_selected_parent_iff_d hM hC hA hT hX hRun hExp hLast hIndex hPrevious hP hCF hPrevLow
              (hRootLast hPrevLow) hVB hNew hCopy hSource hNonroot hMap target).trans
              (hQc.source_parent_nonroot_d hM hC hT hX hSel.forest hCF.count_nat hCopy hSource hNonroot hMap target).symm
          · have hEq : source=X.root := Classical.byContradiction hNonroot
            subst source
            have hRootZero := (hT.add.add_iff_sum hM hX.root hC.zero_nat).mpr (sum_zero_d hM X.root hC.zero_empty)
            have hEncode := (CopyCoordinates.parent_copy_bad_iff (SetTheory.KP.mem_irrefl_d (KP1Y.models_weakKP hM) X.root)).mp hMap
            have hRootPos := (CopyCoordinates.encode_at_base_iff_d hM hC hT hX.root hC.zero_nat hCopyNat hRootZero).mp hEncode
            by_cases hFixed : copy=C.zero ∨ ¬M.mem r maximal
            · exact (fixed_root_selected_parent_iff_d hM hC hA hT hX hExp hLast hIndex hr hSel (hRootLast hPrevLow) hCF hPrevLow
                hFixed hV hVB hNew hCopy hMap target).trans
                (hQc.root_high_parent_iff_d hM hC hT hX hCF.count_nat hCopy hFixed hRootPos target).symm
            · have hLow : M.mem r maximal := Classical.byContradiction (fun h => hFixed (Or.inr h))
              have hCopyNonzero : copy≠C.zero := fun h => hFixed (Or.inl h)
              obtain ⟨prev,hPrev,hs⟩ : ∃ prev, M.mem prev C.omega ∧ M.SuccessorOf copy prev := by
                rcases natural_cases hM hC.omega hCopyNat with he | hSucc
                · exact False.elim (hCopyNonzero (hM.1.eq_of_same_members copy C.zero (fun t => iff_of_false (he t) (hC.zero_empty t))))
                · exact hSucc
              exact (seam_selected_parent_iff_d hM hC hA hT hX hRun hContext hExp hIndex hLow hPrevious hP hV hVB hNew
                hCF hPrevLow hPrev hs hCopy hMap target).trans
                (hQc.root_low_parent_iff_d hM hC hT hX hCF.count_nat hCopy hPrev hs hLow hRootPos target).symm
        · have hHigh := hPreviousHigh hPrevLow
          exact (high_selected_parent_iff_d hM hC hA hT hX hExp hLast hIndex hr hSel hCF hPrevLow hHigh hV hVB hNew
            hCopy hSource hMap target).trans
            (hQc.source_parent_high_d hM hC hT hX hSel.forest hCF.count_nat hCopy hSource hHigh hMap target).symm
    · exact iff_of_false (fun h => hChild (hNew.forest.bounds hM.1 h).1) (fun h => hChild (hQc.forest.bounds hM.1 h).1))
  exact hEqual.symm ▸ hQc

private theorem context_root_ancestor_at_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {A : FiniteMatrix M.Domain}
    {Forests Rows L last maximal root r P : M.Domain}
    (hRun : MatrixParentRun M C A.width A.height A.cells A.values Forests Rows L)
    (hContext : MatrixExpansionContext M C A Forests Rows last maximal root) (hP : MemPair M Rows r P)
    (hLe : r=maximal ∨ M.mem r maximal) : Ancestor M C A.width P root last := by
  have hRootLt := hContext.root_lt_last hRun
  rcases hLe with he | hlt
  · subst r
    obtain ⟨Q,_,hQ,hParent⟩ := hContext.parent
    have he := hRun.graph.unique maximal Q P hQ hP
    subst Q
    exact ancestor_direct_d hM hC (hRun.forests maximal P hP) hParent
  · obtain ⟨_,he | ⟨Q,_,hQ,hAncestor⟩⟩ := hContext.last_ascending_below_d hM hC hRun hlt
    · exact False.elim (SetTheory.KP.mem_irrefl_d (KP1Y.models_weakKP hM) root (he ▸ hRootLt))
    · exact hRun.graph.unique r Q P hQ hP ▸ hAncestor

private def copyRowsEnv {M : SetTheory.Structure.{u}} (C : ExpressionData M.Domain) (T : MatrixArithmetic M.Domain)
    (X : CopyCoordinates.Context M.Domain) (Rows Other maximal count : M.Domain) : Env M 19 :=
  ((((((((((((((((((oneEnv C.omega).push C.zero).push C.one).push C.sequences).push C.expressions).push T.addPairs).push T.plus).push T.mulPairs).push T.times).push T.diffPairs).push T.difference).push X.last).push X.root).push X.length).push X.first).push Rows).push Other).push maximal).push count

private def copyRowsSchema : Project.UnarySchema 19 where
  body := .forallE (.forallE (.forallE (.forallE (.imp
    (.conj (memPairFormula (.bound 8) (.bound 4) (.bound 3)) (memPairFormula (.bound 7) (.bound 4) (.bound 2)))
    (.iff (memPairFormula (.bound 2) (.bound 1) (.bound 0))
      (copiedParentFormula ⟨.bound 23,.bound 22,.bound 21,.bound 20,.bound 19⟩
        ⟨.bound 18,.bound 17,.bound 16,.bound 15,.bound 14,.bound 13⟩ ⟨.bound 12,.bound 11,.bound 10,.bound 9⟩
        (.bound 3) (.bound 4) (.bound 6) (.bound 5) (.bound 1) (.bound 0)))))))
  freeClosed := by
    simp [copiedParentFormula,copyBranchFormula,CopyCoordinates.parentCopyFormula,CopyCoordinates.encodeFormula,
      copyPositionFormula,ExpressionData.weaken,ExpressionData.map,MatrixArithmetic.weaken,MatrixArithmetic.map,
      CopyCoordinates.Context.weaken,CopyCoordinates.Context.map,mulAtFormula,addAtFormula,successorFormula,
      memPairFormula,codeFormula,pairFormula,Project.Formula.forallMem,Project.Formula.existsMem,Definitional.Formula.FreeClosed]

private theorem copyRowsSchema_iff {M : SetTheory.Structure.{u}} (he : Extensional M)
    (C : ExpressionData M.Domain) (T : MatrixArithmetic M.Domain) (X : CopyCoordinates.Context M.Domain)
    (Rows Other maximal count r : M.Domain) :
    Project.Formula.satisfies ((copyRowsEnv C T X Rows Other maximal count).push r) copyRowsSchema.body ↔
      ∀ P Q child target, MemPair M Rows r P → MemPair M Other r Q →
        (MemPair M Q child target ↔ CopiedParent M C T X P r maximal count child target) := by
  simp only [copyRowsSchema,Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_imp_iff,
    Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_iff_iff,memPairFormula_iff he,copiedParentFormula_iff he,and_imp]
  rfl

/-- 任意真实B父运行的每一行都是精确的复制父图；全部内部行以字面对象公式归纳。 -/
theorem _root_.KP1Y.OneYFinite.RawMatrixExpansion.parent_copy_rows_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {A B : FiniteMatrix M.Domain} (hA : A.Valid M C.omega)
    {T : MatrixArithmetic M.Domain} (hT : T.Valid M C) {X : CopyCoordinates.Context M.Domain} (hX : X.Valid M C)
    {Forests Rows L OtherForests Other OtherL maximal index count total : M.Domain}
    (hRun : MatrixParentRun M C A.width A.height A.cells A.values Forests Rows L)
    (hContext : MatrixExpansionContext M C A Forests Rows X.last maximal X.root)
    (hExp : RawMatrixExpansion M C A T Forests Rows X.last maximal X.root index count X.length total B)
    (hOther : MatrixParentRun M C B.width B.height B.cells B.values OtherForests Other OtherL)
    (hIndex : M.mem index C.omega) :
    ∀ r P Q, MemPair M Rows r P → MemPair M Other r Q → CopyForest M C T X P r maximal count B.width Q := by
  have hw := omega_isOrdinal_d hM hC.omega
  have hLast := hContext.width_successor.predecessor_mem
  have hMaxNat := hw.transitive A.height hA.height maximal hContext.row
  have hCountNat := natural_successor_mem_d hM hC hIndex hExp.copies
  have hPrefix := hExp.parent_prefix_d hM hC hA hT hRun hOther hLast hX.below hIndex
  have hAll := natural_induction_d hM copyRowsSchema (copyRowsEnv C T X Rows Other maximal count) hC.omega
    (fun zero hEmpty => (copyRowsSchema_iff hM.1 C T X Rows Other maximal count zero).mpr (by
      have hz := hM.1.eq_of_same_members zero C.zero (fun x => iff_of_false (hEmpty x) (hC.zero_empty x))
      subst zero
      intro P Q child target hP hQ
      have hr := (hRun.graph.bounds hM.1 hP).1
      have hrB := (hOther.graph.bounds hM.1 hQ).1
      obtain ⟨V,hV⟩ := hRun.values_exist C.zero hr
      obtain ⟨VB,hVB⟩ := hOther.values_exist C.zero hrB
      obtain ⟨F,hF⟩ := copy_forest_exists_d hM hC hT hX hRun.linear.1 hCountNat hExp.product hExp.width
        (row := C.zero) (maximal := C.one)
      have hLow := hC.one_succ.predecessor_mem
      have hLinear := hF.linear_d hM hC hT hX hRun.linear hLast hLow
      have hEqual := linear_forest_unique hM.1 hLinear hOther.linear
      subst F
      have hRootLast : M.mem C.zero C.one → Ancestor M C A.width P X.root X.last := by
        intro _
        apply context_root_ancestor_at_d hM hC hRun hContext hP
        rcases hw.wellOrder.linear.compare C.zero hC.zero_nat maximal hMaxNat with he | hlt | hgt
        · exact Or.inl (hM.1.eq_of_same_members C.zero maximal he)
        · exact Or.inr hlt
        · exact False.elim (hC.zero_empty maximal hgt)
      have hCopy := selected_row_is_copy_d hM hC hA hT hX hRun hContext hExp hIndex (Or.inl ⟨rfl,rfl⟩) hP hV hVB
        (hOther.initial Q VB hQ hVB) hF (fun h => False.elim (h hLow)) hRootLast (hPrefix C.zero P Q hP hQ)
      exact hCopy.parents child target))
    (fun prev hPrev ih r hs => (copyRowsSchema_iff hM.1 C T X Rows Other maximal count r).mpr (by
      intro P Q child target hP hQ
      have hr := (hRun.graph.bounds hM.1 hP).1
      have hrB := (hOther.graph.bounds hM.1 hQ).1
      have hPrevA := (hw.mem hA.height).transitive r hr prev hs.predecessor_mem
      have hPrevB := (hw.mem hExp.matrix.height).transitive r hrB prev hs.predecessor_mem
      obtain ⟨F,hFF,hF⟩ := hRun.graph.total prev hPrevA
      obtain ⟨QF,_,hQF⟩ := hOther.graph.total prev hPrevB
      obtain ⟨V,hV⟩ := hRun.values_exist r hr
      obtain ⟨VB,hVB⟩ := hOther.values_exist r hrB
      have hCF : CopyForest M C T X F prev maximal count B.width QF :=
        ⟨hOther.forests prev QF hQF,fun c t => (copyRowsSchema_iff hM.1 C T X Rows Other maximal count prev).mp ih F QF c t hF hQF,
          hCountNat,total,hExp.product,hExp.width⟩
      have hPreviousHigh : ¬M.mem prev maximal → ¬M.mem r maximal :=
        fun hNot hLow => hNot ((hw.mem hMaxNat).transitive r hLow prev hs.predecessor_mem)
      have hRootLast : M.mem prev maximal → Ancestor M C A.width P X.root X.last := by
        intro hPrevLow
        have hrNat := natural_successor_mem_d hM hC hPrev hs
        have hSub : M.MemberSubset r maximal := by
          intro x hx
          rcases (hs x).mp hx with hxp | he
          · exact (hw.mem hMaxNat).transitive prev hPrevLow x hxp
          · exact (hM.1.eq_of_same_members x prev he).symm ▸ hPrevLow
        exact context_root_ancestor_at_d hM hC hRun hContext hP
          (ordinal_subset_cases_d hM (hw.mem hrNat) (hw.mem hMaxNat) hSub)
      have hCopy := selected_row_is_copy_d hM hC hA hT hX hRun hContext hExp hIndex
        (Or.inr ⟨prev,hPrevA,hs,hFF,hF⟩) hP hV hVB (hOther.step prev r QF Q VB hs hQF hQ hVB)
        hCF hPreviousHigh hRootLast (hPrefix r P Q hP hQ)
      exact hCopy.parents child target))
  intro r P Q hP hQ
  have hrNat := hw.transitive A.height hA.height r (hRun.graph.bounds hM.1 hP).1
  exact ⟨hOther.forests r Q hQ,fun c t => (copyRowsSchema_iff hM.1 C T X Rows Other maximal count r).mp (hAll r hrNat) P Q c t hP hQ,
    hCountNat,total,hExp.product,hExp.width⟩

/-- 真正构造B父运行及其整个复制行族证书；无行族存在性或逐行一致性前提。 -/
theorem _root_.KP1Y.OneYFinite.RawMatrixExpansion.copy_parent_run_exists_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {A B : FiniteMatrix M.Domain} (hA : A.Valid M C.omega)
    {T : MatrixArithmetic M.Domain} (hT : T.Valid M C) {X : CopyCoordinates.Context M.Domain} (hX : X.Valid M C)
    {Forests Rows L maximal index count total : M.Domain}
    (hRun : MatrixParentRun M C A.width A.height A.cells A.values Forests Rows L)
    (hContext : MatrixExpansionContext M C A Forests Rows X.last maximal X.root)
    (hExp : RawMatrixExpansion M C A T Forests Rows X.last maximal X.root index count X.length total B)
    (hIndex : M.mem index C.omega) :
    ∃ OtherForests Other OtherL, MatrixParentRun M C B.width B.height B.cells B.values OtherForests Other OtherL ∧
      ∀ r P Q, MemPair M Rows r P → MemPair M Other r Q → CopyForest M C T X P r maximal count B.width Q := by
  obtain ⟨OtherForests,Other,OtherL,hOther⟩ := matrix_parent_run_exists_d hM hC hExp.matrix
  exact ⟨OtherForests,Other,OtherL,hOther,hExp.parent_copy_rows_d hM hC hA hT hX hRun hContext hOther hIndex⟩

/-- 从实际非退化展开上下文出发，同时构造raw矩阵、实际父运行和每行复制证明。 -/
theorem matrix_expand_raw_with_parent_copy_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {A : FiniteMatrix M.Domain} (hA : A.Valid M C.omega)
    {T : MatrixArithmetic M.Domain} (hT : T.Valid M C) {Forests Rows L last maximal root index : M.Domain}
    (hRun : MatrixParentRun M C A.width A.height A.cells A.values Forests Rows L)
    (hContext : MatrixExpansionContext M C A Forests Rows last maximal root) (hIndex : M.mem index C.omega) :
    ∃ count len total B first OtherForests Other OtherL,
      let X : CopyCoordinates.Context M.Domain := ⟨last,root,len,first⟩
      X.Valid M C ∧ RawMatrixExpansion M C A T Forests Rows last maximal root index count len total B ∧
      MatrixParentRun M C B.width B.height B.cells B.values OtherForests Other OtherL ∧
      ∀ r P Q, MemPair M Rows r P → MemPair M Other r Q → CopyForest M C T X P r maximal count B.width Q := by
  obtain ⟨count,len,total,B,hExp⟩ := matrix_expand_raw_context_d hM hC hA hT hRun hContext hIndex
  obtain ⟨first,hFirst,_⟩ := hC.omega.1.2 root hExp.difference.2.1
  let X : CopyCoordinates.Context M.Domain := ⟨last,root,len,first⟩
  have hX : X.Valid M C := ⟨hExp.difference.1,hExp.difference.2.1,hContext.root_lt_last hRun,hExp.difference,hFirst⟩
  obtain ⟨OtherForests,Other,OtherL,hOther,hCopy⟩ := hExp.copy_parent_run_exists_d hM hC hA hT hX hRun hContext hIndex
  exact ⟨count,len,total,B,first,OtherForests,Other,OtherL,hX,hExp,hOther,hCopy⟩

end KP1Y.OneYFinite.MatrixCopy
