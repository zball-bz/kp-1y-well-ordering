import KP1Y.OneYMatrixCopySelection
import KP1Y.OneYSelectionAncestorValues

/-! 低行及临界行的实际父选择；所有跨副本归纳都作用于字面对象公式。 -/
namespace KP1Y.OneYFinite.MatrixCopy
open YesMetaZFC YesMetaZFC.SetTheory YesMetaZFC.SetTheory.Definitional
open KP1Y.Kuratowski KP1Y.Functions KP1Y.Naturals KP1Y.Bounded
open KP1Y.OneYFinite KP1Y.Arithmetic
universe u

private theorem le_trans_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {a b c : M.Domain} (hc : M.mem c C.omega)
    (hab : a=b ∨ M.mem a b) (hbc : b=c ∨ M.mem b c) : a=c ∨ M.mem a c := by
  rcases hab with he | hlt <;> rcases hbc with he' | hlt'
  · exact Or.inl (he.trans he')
  · exact Or.inr (he.symm ▸ hlt')
  · exact Or.inr (he' ▸ hlt)
  · exact Or.inr (((omega_isOrdinal_d hM hC.omega).mem hc).transitive b hlt' a hlt)

private theorem not_lt_of_le_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {a b : M.Domain} (ha : M.mem a C.omega)
    (hab : a=b ∨ M.mem a b) : ¬M.mem b a := by
  intro hba
  rcases hab with he | hab
  · exact SetTheory.KP.mem_irrefl_d (KP1Y.models_weakKP hM) a (he.symm ▸ hba)
  · exact SetTheory.KP.mem_irrefl_d (KP1Y.models_weakKP hM) a
      (((omega_isOrdinal_d hM hC.omega).mem ha).transitive b hba a hab)

/-- 每个真实提升值至少为源值；此处不需要正加量或ascending假设。 -/
theorem lifted_entry_base_le_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {A : FiniteMatrix M.Domain} (hA : A.Valid M C.omega)
    {T : MatrixArithmetic M.Domain} (hT : T.Valid M C) {Forests Rows last maximal root copy source r a y : M.Domain}
    (hEntry : MatrixEntry M A r source a)
    (hLift : LiftedEntry M C A T Forests Rows last maximal root copy source r y) : a=y ∨ M.mem a y := by
  obtain ⟨b,hb,hB,hCase⟩ := hLift
  have he := hA.entry_unique hM.1 hB hEntry
  subst b
  rcases hCase with ⟨_,_,_,t,ht,_,_,hPlus⟩ | ⟨_,he⟩
  · have hw := omega_isOrdinal_d hM hC.omega
    have hSum := (hT.add.add_iff_sum hM hb ht).mp hPlus
    exact ordinal_subset_cases_d hM (hw.mem hb) (hw.mem (hPlus.bounds hM.1 hT.add).2.2)
      (sum_base_subset_d hM (hw.mem hb) hSum)
  · exact Or.inl he.symm

/-- 旧root是last的当前行祖先时，旧候选链坏部各源列的实际复制值≥原root值。 -/
theorem copied_last_ancestor_value_ge_root_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {A B : FiniteMatrix M.Domain} (hA : A.Valid M C.omega)
    {T : MatrixArithmetic M.Domain} (hT : T.Valid M C) {X : CopyCoordinates.Context M.Domain} (hX : X.Valid M C)
    {Forests Rows maximal index count total r F P V VB copy q target a y : M.Domain}
    (hExp : RawMatrixExpansion M C A T Forests Rows X.last maximal X.root index count X.length total B)
    (hLast : M.mem X.last A.width) (hIndex : M.mem index C.omega) (hr : M.mem r A.height)
    (hSel : Selects false M C A.width F V P) (hRootLast : Ancestor M C A.width P X.root X.last)
    (hV : MatrixRowValues M C.omega A.width A.cells A.values r V)
    (hVB : MatrixRowValues M C.omega B.width B.cells B.values r VB)
    (hRootValue : MatrixEntry M A r X.root a) (hCopy : M.mem copy count) (hq : M.mem q X.last)
    (hMap : CopyCoordinates.ParentCopy M C T X copy q target) (hAncestor : Ancestor M C A.width F q X.last)
    (hAfter : X.root=target ∨ M.mem X.root target) (hValue : MemPair M VB target y) : a=y ∨ M.mem a y := by
  have hw := omega_isOrdinal_d hM hC.omega
  have hAfterQ : X.root=q ∨ M.mem X.root q := by
    rcases hw.wellOrder.linear.compare X.root hX.root q hMap.1 with he | hlt | hgt
    · exact Or.inl (hM.1.eq_of_same_members X.root q he)
    · exact Or.inr hlt
    · have he := (CopyCoordinates.parent_copy_good_iff hMap.2.1 hMap.1 hgt).mp hMap
      exact False.elim (not_lt_of_le_d hM hC hX.root hAfter (he.symm ▸ hgt))
  obtain ⟨b,hb,hBValue⟩ := hV.graph.total q (hAncestor.bounds hM.1).1
  have hRootAt := (matrix_row_view_entry_iff_d hM hA hr hV X.root a).mpr hRootValue
  have hAB : a=b ∨ M.mem a b := by
    rcases hAfterQ with he | hlt
    · subst q
      exact Or.inl (hV.graph.unique X.root a b hRootAt hBValue)
    · exact Or.inr (hSel.ancestor_value_lt_after_d hM hC hRootLast hAncestor hlt hRootAt hBValue)
  have hrB : M.mem r B.height := hExp.height.symm ▸ hr
  have hLift := (hExp.parent_copy_entry_iff_d hM hC hA hT hX hLast hIndex hCopy hq hMap).mp
    ((matrix_row_view_entry_iff_d hM hExp.matrix hrB hVB target y).mp hValue)
  have hBY := lifted_entry_base_le_d hM hC hA hT ((matrix_row_view_entry_iff_d hM hA hr hV q b).mp hBValue) hLift
  exact le_trans_d hM hC (hVB.graph.bounds hM.1 hValue).2 hAB hBY

private def rootBoundEnv {M : SetTheory.Structure.{u}} (C : ExpressionData M.Domain) (T : MatrixArithmetic M.Domain)
    (X : CopyCoordinates.Context M.Domain) (count width Q V a : M.Domain) : Env M 20 :=
  (((((((((((((((((((oneEnv C.omega).push C.zero).push C.one).push C.sequences).push C.expressions).push T.addPairs).push T.plus).push T.mulPairs).push T.times).push T.diffPairs).push T.difference).push X.last).push X.root).push X.length).push X.first).push count).push width).push Q).push V).push a

private def rootBoundSchema : Project.UnarySchema 20 where
  body := .forallE (.forallE (.forallE (.imp
    (.conj (.mem (.bound 2) (.bound 8))
      (.conj (CopyCoordinates.parentCopyFormula ⟨.bound 23,.bound 22,.bound 21,.bound 20,.bound 19⟩
        ⟨.bound 18,.bound 17,.bound 16,.bound 15,.bound 14,.bound 13⟩ ⟨.bound 12,.bound 11,.bound 10,.bound 9⟩ (.bound 2) (.bound 11) (.bound 3))
        (.conj (.disj (Project.Formula.extensionalEq (.bound 11) (.bound 1)) (.mem (.bound 11) (.bound 1)))
          (.conj (ancestorFormula ⟨.bound 23,.bound 22,.bound 21,.bound 20,.bound 19⟩ (.bound 7) (.bound 6) (.bound 1) (.bound 3))
            (memPairFormula (.bound 5) (.bound 1) (.bound 0))))))
    (.disj (Project.Formula.extensionalEq (.bound 4) (.bound 0)) (.mem (.bound 4) (.bound 0))))))
  freeClosed := by
    have hC : (⟨.bound 23,.bound 22,.bound 21,.bound 20,.bound 19⟩ : ExpressionData (Project.Term 24)).Closed := ⟨rfl,rfl,rfl,rfl,rfl⟩
    have hT : CopyCoordinates.ArithmeticClosed (⟨.bound 18,.bound 17,.bound 16,.bound 15,.bound 14,.bound 13⟩ : MatrixArithmetic (Project.Term 24)) := ⟨rfl,rfl,rfl,rfl,rfl,rfl⟩
    have hX : (⟨.bound 12,.bound 11,.bound 10,.bound 9⟩ : CopyCoordinates.Context (Project.Term 24)).Closed := ⟨rfl,rfl,rfl,rfl⟩
    have hMap := CopyCoordinates.parentCopyFormula_freeClosed hC hT hX (.bound 2) (.bound 11) (.bound 3) rfl rfl rfl
    have hAnc := ancestorFormula_freeClosed hC (.bound 7) (.bound 6) (.bound 1) (.bound 3) rfl rfl rfl rfl
    simp [Definitional.Formula.FreeClosed,memPairFormula,codeFormula,pairFormula,Project.Formula.forallMem,
      Project.Formula.existsMem,hMap,hAnc]

private theorem rootBoundSchema_iff {M : SetTheory.Structure.{u}} (he : Extensional M)
    (C : ExpressionData M.Domain) (T : MatrixArithmetic M.Domain) (X : CopyCoordinates.Context M.Domain)
    (count width Q V a child : M.Domain) :
    Project.Formula.satisfies ((rootBoundEnv C T X count width Q V a).push child) rootBoundSchema.body ↔
      ∀ copy x y, M.mem copy count → CopyCoordinates.ParentCopy M C T X copy X.root child →
        (X.root=x ∨ M.mem X.root x) → Ancestor M C width Q x child → MemPair M V x y → (a=y ∨ M.mem a y) := by
  simp only [rootBoundSchema,Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_imp_iff,
    Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_disj_iff,Project.Formula.satisfies_mem_iff,
    Project.Formula.satisfies_extensionalEq_iff_eq he,CopyCoordinates.parentCopyFormula_iff he,
    ancestorFormula_iff he,memPairFormula_iff he,and_imp]
  rfl

/-- 在低的上一行中，任何块根的坏部祖先，其真实新行值≥原root值。
这包括任意多个更早副本，证明使用目标根列上的一次字面对象集合归纳。
-/
theorem copied_root_bad_ancestor_value_ge_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {A B : FiniteMatrix M.Domain} (hA : A.Valid M C.omega)
    {T : MatrixArithmetic M.Domain} (hT : T.Valid M C) {X : CopyCoordinates.Context M.Domain} (hX : X.Valid M C)
    {Forests Rows maximal index count total r F P V VB previous previousMax QF copy child x a y : M.Domain}
    (hExp : RawMatrixExpansion M C A T Forests Rows X.last maximal X.root index count X.length total B)
    (hLast : M.mem X.last A.width) (hIndex : M.mem index C.omega) (hr : M.mem r A.height)
    (hSel : Selects false M C A.width F V P) (hRootLast : Ancestor M C A.width P X.root X.last)
    (hCF : CopyForest M C T X F previous previousMax count B.width QF) (hPreviousLow : M.mem previous previousMax)
    (hV : MatrixRowValues M C.omega A.width A.cells A.values r V)
    (hVB : MatrixRowValues M C.omega B.width B.cells B.values r VB)
    (hRootValue : MatrixEntry M A r X.root a) (hCopy : M.mem copy count)
    (hRootMap : CopyCoordinates.ParentCopy M C T X copy X.root child)
    (hAfter : X.root=x ∨ M.mem X.root x) (hAncestor : Ancestor M C B.width QF x child)
    (hValue : MemPair M VB x y) : a=y ∨ M.mem a y := by
  have hw := omega_isOrdinal_d hM hC.omega
  have hInheritedRootLast := hSel.ancestor_inherited_d hM hC hRootLast
  have hAll := KP1Y.induction_d hM rootBoundSchema (rootBoundEnv C T X count B.width QF VB a) (by
    intro child ih
    apply (rootBoundSchema_iff hM.1 C T X count B.width QF VB a child).mpr
    intro b x y hb hRootMap hAfter hAncestor hValue
    have hbNat := hw.transitive count hCF.count_nat b hb
    classical
    by_cases hbZero : b=C.zero
    · subst b
      obtain ⟨J,hJ,hRows⟩ := hCF.copy_embedding_d hM hC hT hX hb
      have hJRoot := (hRows X.root child).mpr ⟨hX.below,hRootMap⟩
      have hJZero := (hRows X.root X.root).mpr ⟨hX.below,CopyCoordinates.parent_copy_zero_d hM hC hT hX hX.root⟩
      have hChildRoot := hJ.graph.unique X.root child X.root hJRoot hJZero
      exact False.elim (not_lt_of_le_d hM hC hX.root hAfter (hChildRoot ▸ hAncestor.1))
    · obtain ⟨prev,hPrev,hs⟩ : ∃ prev, M.mem prev C.omega ∧ M.SuccessorOf b prev := by
        rcases natural_cases hM hC.omega hbNat with he | hSucc
        · exact False.elim (hbZero (hM.1.eq_of_same_members b C.zero (fun t => iff_of_false (he t) (hC.zero_empty t))))
        · exact hSucc
      have hPrevCount := (hw.mem hCF.count_nat).transitive b hb prev hs.predecessor_mem
      have hRootZero := (hT.add.add_iff_sum hM hX.root hC.zero_nat).mpr (sum_zero_d hM X.root hC.zero_empty)
      have hEncode := (CopyCoordinates.parent_copy_bad_iff (SetTheory.KP.mem_irrefl_d (KP1Y.models_weakKP hM) X.root)).mp hRootMap
      have hPos := (CopyCoordinates.encode_at_base_iff_d hM hC hT hX.root hC.zero_nat hbNat hRootZero).mp hEncode
      obtain ⟨t,hParent,hBefore⟩ := ancestor_parent_cases_d hM hC hCF.forest hAncestor
      obtain ⟨p,hp,hOldParent,hMapP⟩ := (hCF.root_low_parent_iff_d hM hC hT hX hCF.count_nat hb hPrev hs hPreviousLow hPos t).mp hParent
      have hBound (q : M.Domain) (hq : M.mem q X.last) (hMap : CopyCoordinates.ParentCopy M C T X prev q x)
          (hAnc : Ancestor M C A.width F q X.last) : a=y ∨ M.mem a y :=
        copied_last_ancestor_value_ge_root_d hM hC hA hT hX hExp hLast hIndex hr hSel hRootLast hV hVB hRootValue
          hPrevCount hq hMap hAnc hAfter hValue
      rcases hBefore with he | hBefore
      · exact hBound p hp (he.symm ▸ hMapP) (ancestor_direct_d hM hC hSel.inherited hOldParent)
      · obtain ⟨J,hJ,hRows⟩ := hCF.copy_embedding_d hM hC hT hX hPrevCount
        obtain ⟨z,_,hJRoot⟩ := hJ.graph.total X.root hX.below
        have hPrevRoot := ((hRows X.root z).mp hJRoot).2
        rcases hCF.ancestor_origin_or_root_d hM hC hT hX hSel.inherited hLast hPrevCount hp hMapP hPrevRoot hBefore with
            ⟨q,hq,hMapQ,hAncQ⟩ | ⟨hToRoot,_⟩
        · exact hBound q hq hMapQ (ancestor_step_d hM hC hSel.inherited hAncQ hOldParent)
        · rcases hToRoot with he | hToRoot
          · have hrB : M.mem r B.height := hExp.height.symm ▸ hr
            have hLift := (hExp.parent_copy_entry_iff_d hM hC hA hT hX hLast hIndex hPrevCount hX.below hPrevRoot).mp
              ((matrix_row_view_entry_iff_d hM hExp.matrix hrB hVB z y).mp (he ▸ hValue))
            exact lifted_entry_base_le_d hM hC hA hT hRootValue hLift
          · have hPrevAncestor := (hCF.ancestor_previous_root_iff_d hM hC hT hX hSel.inherited hLast hb hPrev hs hPreviousLow
              (Or.inl rfl) hX.below hPrevRoot hPos).mpr hInheritedRootLast
            exact (rootBoundSchema_iff hM.1 C T X count B.width QF VB a z).mp (ih z hPrevAncestor.1)
              prev x y hPrevCount hPrevRoot hAfter hToRoot hValue)
  exact (rootBoundSchema_iff hM.1 C T X count B.width QF VB a child).mp (hAll child) copy x y hCopy hRootMap hAfter hAncestor hValue

/-- 低的上一行中，非root源列的好部父项也是新行的实际最右候选。 -/
theorem copied_nonroot_good_parent_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {A B : FiniteMatrix M.Domain} (hA : A.Valid M C.omega)
    {T : MatrixArithmetic M.Domain} (hT : T.Valid M C) {X : CopyCoordinates.Context M.Domain} (hX : X.Valid M C)
    {Forests Rows L maximal index count total r P F previous previousMax QF VB copy source p child target : M.Domain}
    (hRun : MatrixParentRun M C A.width A.height A.cells A.values Forests Rows L)
    (hExp : RawMatrixExpansion M C A T Forests Rows X.last maximal X.root index count X.length total B)
    (hLast : M.mem X.last A.width) (hIndex : M.mem index C.omega)
    (hPrev : PreviousMatrixForest M C A.height Forests Rows L r F) (hP : MemPair M Rows r P)
    (hCF : CopyForest M C T X F previous previousMax count B.width QF) (hPreviousLow : M.mem previous previousMax)
    (hRootLast : Ancestor M C A.width P X.root X.last)
    (hVB : MatrixRowValues M C.omega B.width B.cells B.values r VB)
    (hCopy : M.mem copy count) (hSource : M.mem source X.last) (hNonroot : source≠X.root)
    (hParent : MemPair M P source p) (hGoodParent : M.mem p X.root)
    (hChild : CopyCoordinates.ParentCopy M C T X copy source child)
    (hTarget : CopyCoordinates.ParentCopy M C T X copy p target) :
    RestrictedParent false M C B.width QF VB child target := by
  have hw := omega_isOrdinal_d hM hC.omega
  have hr := (hRun.graph.bounds hM.1 hP).1
  obtain ⟨V,hV⟩ := hRun.values_exist r hr
  have hSel := hRun.selects_previous_d hPrev hP hV
  have hInheritedRootLast := hSel.ancestor_inherited_d hM hC hRootLast
  have hRootLastF : M.mem previous previousMax → Ancestor M C A.width F X.root X.last := fun _ => hInheritedRootLast
  have hCandidate := copied_nonroot_parent_candidate_d hM hC hA hT hX hRun hExp hLast hIndex hPrev hP hCF hRootLastF
    hVB hCopy hSource hNonroot hParent hChild hTarget
  have hp := (hw.mem hX.last).transitive source hSource p (hSel.forest.left source p hParent)
  obtain ⟨J,hJ,hRows⟩ := hCF.copy_embedding_d hM hC hT hX hCopy
  have hJTarget := (hRows p target).mpr ⟨hp,hTarget⟩
  have hLocalBound (t q : M.Domain) (hq : M.mem q X.last) (hMap : CopyCoordinates.ParentCopy M C T X copy q t)
      (hNewCandidate : ParentCandidate false M C B.width QF VB child t) : t=target ∨ M.mem t target := by
    have hLe := copied_candidate_source_le_parent_d hM hC hA hT hX hRun hExp hLast hIndex hPrev hP hCF hRootLastF
      hVB hCopy hSource hNonroot hParent hq hChild hMap hNewCandidate
    have hJQ := (hRows q t).mpr ⟨hq,hMap⟩
    rcases hLe with he | hlt
    · subst q
      exact Or.inl (hJ.graph.unique p t target hJQ hJTarget)
    · exact Or.inr (hJ.strict q hq p hp hlt t target hJQ hJTarget)
  refine ⟨hCandidate,?_⟩
  intro t _ hNewCandidate
  obtain ⟨z,_,hJRoot⟩ := hJ.graph.total X.root hX.below
  have hRootMap := ((hRows X.root z).mp hJRoot).2
  rcases hCF.ancestor_origin_or_root_d hM hC hT hX hSel.inherited hLast hCopy hSource hChild hRootMap hNewCandidate.1 with
      ⟨q,hq,hMapQ,_⟩ | ⟨hToRoot,hFromRoot⟩
  · exact hLocalBound t q hq hMapQ hNewCandidate
  · have hRootSource : Ancestor M C A.width F X.root source := hFromRoot.elim (fun he => False.elim (hNonroot he)) id
    classical
    by_cases hGood : M.mem t X.root
    · have ht := (hw.mem hX.last).transitive X.root hX.below t hGood
      have hMap : CopyCoordinates.ParentCopy M C T X copy t t :=
        (CopyCoordinates.parent_copy_good_iff (hw.transitive count hCF.count_nat copy hCopy) (hw.transitive X.last hX.last t ht) hGood).mpr rfl
      exact hLocalBound t t ht hMap hNewCandidate
    · obtain ⟨x,hx,y,hy,hXValue,hYValue,hxy,_⟩ := hNewCandidate.2
      obtain ⟨a,_,hRootValue⟩ := hV.graph.total X.root (hRootLast.bounds hM.1).1
      have hRootEntry := (matrix_row_view_entry_iff_d hM hA hr hV X.root a).mp hRootValue
      have hrB : M.mem r B.height := hExp.height.symm ▸ hr
      have hSourceNot : ¬Ascending M C A.width Forests Rows maximal X.root source r :=
        fun h => not_ascending_good_d hM hC hX.root hGoodParent ((hRun.ascending_parent_iff_d hM hC hP hParent hNonroot).mpr h)
      have hSourceEntry := (lifted_entry_unascending_iff hM.1 hA hSourceNot).mp
        ((hExp.parent_copy_entry_iff_d hM hC hA hT hX hLast hIndex hCopy hSource hChild).mp
          ((matrix_row_view_entry_iff_d hM hExp.matrix hrB hVB child y).mp hYValue))
      have hSourceValue := (matrix_row_view_entry_iff_d hM hA hr hV source y).mpr hSourceEntry
      have hYA := hSel.value_ge_after_parent_d hM hC hParent hRootSource hGoodParent hSourceValue hRootValue
      have hAfter : X.root=t ∨ M.mem X.root t := by
        have htNat := hw.transitive B.width hExp.matrix.width t (hNewCandidate.1.bounds hM.1).1
        rcases hw.wellOrder.linear.compare X.root hX.root t htNat with he | hlt | hgt
        · exact Or.inl (hM.1.eq_of_same_members X.root t he)
        · exact Or.inr hlt
        · exact False.elim (hGood hgt)
      have hAX : a=x ∨ M.mem a x := by
        rcases hToRoot with he | hToRoot
        · have hLift := (hExp.parent_copy_entry_iff_d hM hC hA hT hX hLast hIndex hCopy hX.below hRootMap).mp
            ((matrix_row_view_entry_iff_d hM hExp.matrix hrB hVB z x).mp (he ▸ hXValue))
          exact lifted_entry_base_le_d hM hC hA hT hRootEntry hLift
        · exact copied_root_bad_ancestor_value_ge_d hM hC hA hT hX hExp hLast hIndex hr hSel hRootLast hCF hPreviousLow
            hV hVB hRootEntry hCopy hRootMap hAfter hToRoot hXValue
      exact False.elim (not_lt_of_le_d hM hC hy (le_trans_d hM hC hx hYA hAX) hxy)

theorem _root_.KP1Y.OneYFinite.Selects.no_parent_value_ge_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {m F V P source q a b : M.Domain}
    (hSel : Selects false M C m F V P) (hNone : NoParent M m P source)
    (hQ : Ancestor M C m F q source) (hA : MemPair M V source a) (hB : MemPair M V q b) : a=b ∨ M.mem a b := by
  have hw := omega_isOrdinal_d hM hC.omega
  have ha := (hSel.values.bounds hM.1 hA).2
  have hb := (hSel.values.bounds hM.1 hB).2
  rcases hw.wellOrder.linear.compare a ha b hb with he | hlt | hgt
  · exact Or.inl (hM.1.eq_of_same_members a b he)
  · exact Or.inr hlt
  · exact False.elim ((hSel.no_parent_iff_d hM hC).mp hNone q ⟨hQ,b,hb,a,ha,hB,hA,hgt,True.intro⟩)

/-- 无父的非root源列在低上一行的复制中确实没有任何新候选父项。 -/
theorem copied_nonroot_no_candidate_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {A B : FiniteMatrix M.Domain} (hA : A.Valid M C.omega)
    {T : MatrixArithmetic M.Domain} (hT : T.Valid M C) {X : CopyCoordinates.Context M.Domain} (hX : X.Valid M C)
    {Forests Rows L maximal index count total r P F previous previousMax QF VB copy source child : M.Domain}
    (hRun : MatrixParentRun M C A.width A.height A.cells A.values Forests Rows L)
    (hExp : RawMatrixExpansion M C A T Forests Rows X.last maximal X.root index count X.length total B)
    (hLast : M.mem X.last A.width) (hIndex : M.mem index C.omega)
    (hPrev : PreviousMatrixForest M C A.height Forests Rows L r F) (hP : MemPair M Rows r P)
    (hCF : CopyForest M C T X F previous previousMax count B.width QF) (hPreviousLow : M.mem previous previousMax)
    (hRootLast : Ancestor M C A.width P X.root X.last)
    (hVB : MatrixRowValues M C.omega B.width B.cells B.values r VB)
    (hCopy : M.mem copy count) (hSource : M.mem source X.last) (hNonroot : source≠X.root)
    (hNone : NoParent M A.width P source)
    (hChild : CopyCoordinates.ParentCopy M C T X copy source child) :
    ∀ target, ¬ParentCandidate false M C B.width QF VB child target := by
  have hw := omega_isOrdinal_d hM hC.omega
  have hr := (hRun.graph.bounds hM.1 hP).1
  obtain ⟨V,hV⟩ := hRun.values_exist r hr
  have hSel := hRun.selects_previous_d hPrev hP hV
  have hInheritedRootLast := hSel.ancestor_inherited_d hM hC hRootLast
  have hSourceNot : ¬Ascending M C A.width Forests Rows maximal X.root source r := by
    intro hAsc
    obtain ⟨_,he | hAnc⟩ := (hRun.ascending_at_d hM.1 hP).mp hAsc
    · exact hNonroot he
    · obtain ⟨p,hParent,_⟩ := ancestor_parent_cases_d hM hC hSel.forest hAnc
      exact hNone p (hSel.forest.bounds hM.1 hParent).2 hParent
  intro target hCandidate
  obtain ⟨x,hx,y,hy,hXValue,hYValue,hxy,_⟩ := hCandidate.2
  have hrB : M.mem r B.height := hExp.height.symm ▸ hr
  have hSourceEntry := (lifted_entry_unascending_iff hM.1 hA hSourceNot).mp
    ((hExp.parent_copy_entry_iff_d hM hC hA hT hX hLast hIndex hCopy hSource hChild).mp
      ((matrix_row_view_entry_iff_d hM hExp.matrix hrB hVB child y).mp hYValue))
  have hSourceValue := (matrix_row_view_entry_iff_d hM hA hr hV source y).mpr hSourceEntry
  have hLocalFalse (q : M.Domain) (hq : M.mem q X.last) (hMap : CopyCoordinates.ParentCopy M C T X copy q target)
      (hAnc : Ancestor M C A.width F q source) : False := by
    obtain ⟨b,hb,hBValue⟩ := hV.graph.total q (hAnc.bounds hM.1).1
    have hLift := (hExp.parent_copy_entry_iff_d hM hC hA hT hX hLast hIndex hCopy hq hMap).mp
      ((matrix_row_view_entry_iff_d hM hExp.matrix hrB hVB target x).mp hXValue)
    have hBX := lifted_entry_base_le_d hM hC hA hT ((matrix_row_view_entry_iff_d hM hA hr hV q b).mp hBValue) hLift
    have hBY : M.mem b y := by
      rcases hBX with he | hlt
      · exact he.symm ▸ hxy
      · exact (hw.mem hy).transitive x hxy b hlt
    exact (hSel.no_parent_iff_d hM hC).mp hNone q ⟨hAnc,b,hb,y,hy,hBValue,hSourceValue,hBY,True.intro⟩
  obtain ⟨J,hJ,hRows⟩ := hCF.copy_embedding_d hM hC hT hX hCopy
  obtain ⟨z,_,hJRoot⟩ := hJ.graph.total X.root hX.below
  have hRootMap := ((hRows X.root z).mp hJRoot).2
  rcases hCF.ancestor_origin_or_root_d hM hC hT hX hSel.inherited hLast hCopy hSource hChild hRootMap hCandidate.1 with
      ⟨q,hq,hMapQ,hAncQ⟩ | ⟨hToRoot,hFromRoot⟩
  · exact hLocalFalse q hq hMapQ hAncQ
  · have hRootSource : Ancestor M C A.width F X.root source := hFromRoot.elim (fun he => False.elim (hNonroot he)) id
    classical
    by_cases hGood : M.mem target X.root
    · have ht := (hw.mem hX.last).transitive X.root hX.below target hGood
      have hMap : CopyCoordinates.ParentCopy M C T X copy target target :=
        (CopyCoordinates.parent_copy_good_iff (hw.transitive count hCF.count_nat copy hCopy) (hw.transitive X.last hX.last target ht) hGood).mpr rfl
      have hOld := (hCF.ancestor_copy_iff_d hM hC hT hX hSel.inherited hLast hCopy (fun _ => hInheritedRootLast)
        ht hSource hMap hChild).mp hCandidate.1
      exact hLocalFalse target ht hMap hOld
    · obtain ⟨a,_,hRootValue⟩ := hV.graph.total X.root (hRootLast.bounds hM.1).1
      have hRootEntry := (matrix_row_view_entry_iff_d hM hA hr hV X.root a).mp hRootValue
      have hYA := hSel.no_parent_value_ge_d hM hC hNone hRootSource hSourceValue hRootValue
      have hAfter : X.root=target ∨ M.mem X.root target := by
        have htNat := hw.transitive B.width hExp.matrix.width target (hCandidate.1.bounds hM.1).1
        rcases hw.wellOrder.linear.compare X.root hX.root target htNat with he | hlt | hgt
        · exact Or.inl (hM.1.eq_of_same_members X.root target he)
        · exact Or.inr hlt
        · exact False.elim (hGood hgt)
      have hAX : a=x ∨ M.mem a x := by
        rcases hToRoot with he | hToRoot
        · have hLift := (hExp.parent_copy_entry_iff_d hM hC hA hT hX hLast hIndex hCopy hX.below hRootMap).mp
            ((matrix_row_view_entry_iff_d hM hExp.matrix hrB hVB z x).mp (he ▸ hXValue))
          exact lifted_entry_base_le_d hM hC hA hT hRootEntry hLift
        · exact copied_root_bad_ancestor_value_ge_d hM hC hA hT hX hExp hLast hIndex hr hSel hRootLast hCF hPreviousLow
            hV hVB hRootEntry hCopy hRootMap hAfter hToRoot hXValue
      exact not_lt_of_le_d hM hC hy (le_trans_d hM hC hx hYA hAX) hxy

/-- 低/临界行的完整非root父行识别，坏部父、好部父及无父三种情况全部闭合。 -/
theorem low_nonroot_selected_parent_iff_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {A B : FiniteMatrix M.Domain} (hA : A.Valid M C.omega)
    {T : MatrixArithmetic M.Domain} (hT : T.Valid M C) {X : CopyCoordinates.Context M.Domain} (hX : X.Valid M C)
    {Forests Rows L maximal index count total r P F previous previousMax QF VB Q copy source child : M.Domain}
    (hRun : MatrixParentRun M C A.width A.height A.cells A.values Forests Rows L)
    (hExp : RawMatrixExpansion M C A T Forests Rows X.last maximal X.root index count X.length total B)
    (hLast : M.mem X.last A.width) (hIndex : M.mem index C.omega)
    (hPrev : PreviousMatrixForest M C A.height Forests Rows L r F) (hP : MemPair M Rows r P)
    (hCF : CopyForest M C T X F previous previousMax count B.width QF) (hPreviousLow : M.mem previous previousMax)
    (hRootLast : Ancestor M C A.width P X.root X.last)
    (hVB : MatrixRowValues M C.omega B.width B.cells B.values r VB) (hNew : Selects false M C B.width QF VB Q)
    (hCopy : M.mem copy count) (hSource : M.mem source X.last) (hNonroot : source≠X.root)
    (hChild : CopyCoordinates.ParentCopy M C T X copy source child) :
    ∀ target, MemPair M Q child target ↔ ∃ p, M.mem p X.last ∧ MemPair M P source p ∧ CopyCoordinates.ParentCopy M C T X copy p target := by
  have hw := omega_isOrdinal_d hM hC.omega
  have hr := (hRun.graph.bounds hM.1 hP).1
  obtain ⟨V,hV⟩ := hRun.values_exist r hr
  have hSel := hRun.selects_previous_d hPrev hP hV
  have hInheritedRootLast := hSel.ancestor_inherited_d hM hC hRootLast
  have hSelected (p target : M.Domain) (hParent : MemPair M P source p) (hMap : CopyCoordinates.ParentCopy M C T X copy p target) :
      MemPair M Q child target := by
    classical
    by_cases hGood : M.mem p X.root
    · exact (hNew.parents child target).mpr (copied_nonroot_good_parent_d hM hC hA hT hX hRun hExp hLast hIndex hPrev hP
        hCF hPreviousLow hRootLast hVB hCopy hSource hNonroot hParent hGood hChild hMap)
    · have hpNat := hw.transitive A.width hA.width p (hSel.forest.bounds hM.1 hParent).2
      have hBad : X.root=p ∨ M.mem X.root p := by
        rcases hw.wellOrder.linear.compare X.root hX.root p hpNat with he | hlt | hgt
        · exact Or.inl (hM.1.eq_of_same_members X.root p he)
        · exact Or.inr hlt
        · exact False.elim (hGood hgt)
      exact copied_nonroot_bad_parent_selected_d hM hC hA hT hX hRun hExp hLast hIndex hPrev hP hCF (fun _ => hInheritedRootLast)
        hVB hNew hCopy hSource hNonroot hParent hBad hChild hMap
  intro target
  constructor
  · intro hParent
    have hExists : ∃ p, MemPair M P source p := by
      apply Classical.byContradiction
      intro hNone
      have hNo : NoParent M A.width P source := fun p _ hp => hNone ⟨p,hp⟩
      exact copied_nonroot_no_candidate_d hM hC hA hT hX hRun hExp hLast hIndex hPrev hP hCF hPreviousLow hRootLast
        hVB hCopy hSource hNonroot hNo hChild target ((hNew.parents child target).mp hParent).1
    obtain ⟨p,hOldParent⟩ := hExists
    have hp := (hw.mem hX.last).transitive source hSource p (hSel.forest.left source p hOldParent)
    obtain ⟨J,hJ,hRows⟩ := hCF.copy_embedding_d hM hC hT hX hCopy
    obtain ⟨t,_,hMap⟩ := hJ.graph.total p hp
    have hCopyP := ((hRows p t).mp hMap).2
    have hEq := hNew.forest.unique child t target (hSelected p t hOldParent hCopyP) hParent
    exact ⟨p,hp,hOldParent,hEq ▸ hCopyP⟩
  · rintro ⟨p,_,hParent,hMap⟩
    exact hSelected p target hParent hMap

/-- 不加量的同副本候选双向对应：包括copy=0或当前行≥maximal。 -/
theorem unlifted_candidate_iff_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {A B : FiniteMatrix M.Domain} (hA : A.Valid M C.omega)
    {T : MatrixArithmetic M.Domain} (hT : T.Valid M C) {X : CopyCoordinates.Context M.Domain} (hX : X.Valid M C)
    {Forests Rows maximal index count total r F previous previousMax QF V VB copy source p child target : M.Domain}
    (hExp : RawMatrixExpansion M C A T Forests Rows X.last maximal X.root index count X.length total B)
    (hLast : M.mem X.last A.width) (hIndex : M.mem index C.omega) (hr : M.mem r A.height)
    (hF : Forest M C.omega A.width F) (hCF : CopyForest M C T X F previous previousMax count B.width QF)
    (hRootLastF : M.mem previous previousMax → Ancestor M C A.width F X.root X.last)
    (hFixed : copy=C.zero ∨ ¬M.mem r maximal)
    (hV : MatrixRowValues M C.omega A.width A.cells A.values r V)
    (hVB : MatrixRowValues M C.omega B.width B.cells B.values r VB)
    (hCopy : M.mem copy count) (hSource : M.mem source X.last) (hp : M.mem p X.last)
    (hChild : CopyCoordinates.ParentCopy M C T X copy source child)
    (hTarget : CopyCoordinates.ParentCopy M C T X copy p target) :
    ParentCandidate false M C B.width QF VB child target ↔ ParentCandidate false M C A.width F V source p := by
  have hrB : M.mem r B.height := hExp.height.symm ▸ hr
  have hAnc := hCF.ancestor_copy_iff_d hM hC hT hX hF hLast hCopy hRootLastF hp hSource hTarget hChild
  have hUnlifted (s y : M.Domain) : LiftedEntry M C A T Forests Rows X.last maximal X.root copy s r y ↔ MatrixEntry M A r s y := by
    rcases hFixed with he | hHigh
    · subst copy
      exact lifted_entry_zero_iff_d hM hC hA hT hLast (((omega_isOrdinal_d hM hC.omega).mem hA.width).transitive X.last hLast X.root hX.below)
    · exact lifted_entry_unascending_iff hM.1 hA (fun h => hHigh h.1)
  have hEntry (s t : M.Domain) (hs : M.mem s X.last) (hMap : CopyCoordinates.ParentCopy M C T X copy s t) (y : M.Domain) :
      MemPair M VB t y ↔ MemPair M V s y :=
    (matrix_row_view_entry_iff_d hM hExp.matrix hrB hVB t y).trans
      ((hExp.parent_copy_entry_iff_d hM hC hA hT hX hLast hIndex hCopy hs hMap).trans
        ((hUnlifted s y).trans (matrix_row_view_entry_iff_d hM hA hr hV s y).symm))
  constructor
  · rintro ⟨hA,x,hx,y,hy,hX,hY,hxy,hPos⟩
    exact ⟨hAnc.mp hA,x,hx,y,hy,(hEntry p target hp hTarget x).mp hX,(hEntry source child hSource hChild y).mp hY,hxy,hPos⟩
  · rintro ⟨hA,x,hx,y,hy,hX,hY,hxy,hPos⟩
    exact ⟨hAnc.mpr hA,x,hx,y,hy,(hEntry p target hp hTarget x).mpr hX,(hEntry source child hSource hChild y).mpr hY,hxy,hPos⟩

/-- 不加量的复制根只能有好部候选，且候选条件与原root完全相同。 -/
theorem fixed_root_candidate_iff_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {A B : FiniteMatrix M.Domain} (hA : A.Valid M C.omega)
    {T : MatrixArithmetic M.Domain} (hT : T.Valid M C) {X : CopyCoordinates.Context M.Domain} (hX : X.Valid M C)
    {Forests Rows maximal index count total r F P previous previousMax QF V VB copy child target : M.Domain}
    (hExp : RawMatrixExpansion M C A T Forests Rows X.last maximal X.root index count X.length total B)
    (hLast : M.mem X.last A.width) (hIndex : M.mem index C.omega) (hr : M.mem r A.height)
    (hSel : Selects false M C A.width F V P) (hRootLast : Ancestor M C A.width P X.root X.last)
    (hCF : CopyForest M C T X F previous previousMax count B.width QF) (hPreviousLow : M.mem previous previousMax)
    (hFixed : copy=C.zero ∨ ¬M.mem r maximal)
    (hV : MatrixRowValues M C.omega A.width A.cells A.values r V)
    (hVB : MatrixRowValues M C.omega B.width B.cells B.values r VB) (hCopy : M.mem copy count)
    (hRootMap : CopyCoordinates.ParentCopy M C T X copy X.root child) :
    ParentCandidate false M C B.width QF VB child target ↔ ParentCandidate false M C A.width F V X.root target := by
  have hw := omega_isOrdinal_d hM hC.omega
  have hRootLastF : M.mem previous previousMax → Ancestor M C A.width F X.root X.last := fun _ => hSel.ancestor_inherited_d hM hC hRootLast
  have hGoodIff (hGood : M.mem target X.root) := by
    have ht := (hw.mem hX.last).transitive X.root hX.below target hGood
    have hMap : CopyCoordinates.ParentCopy M C T X copy target target :=
      (CopyCoordinates.parent_copy_good_iff (hw.transitive count hCF.count_nat copy hCopy) (hw.transitive X.last hX.last target ht) hGood).mpr rfl
    exact unlifted_candidate_iff_d hM hC hA hT hX hExp hLast hIndex hr hSel.inherited hCF hRootLastF hFixed hV hVB hCopy hX.below ht hRootMap hMap
  constructor
  · intro hCandidate
    have hGood : M.mem target X.root := by
      classical
      by_cases ht : M.mem target X.root
      · exact ht
      · have hAfter : X.root=target ∨ M.mem X.root target := by
          have htNat := hw.transitive B.width hExp.matrix.width target (hCandidate.1.bounds hM.1).1
          rcases hw.wellOrder.linear.compare X.root hX.root target htNat with he | hlt | hgt
          · exact Or.inl (hM.1.eq_of_same_members X.root target he)
          · exact Or.inr hlt
          · exact False.elim (ht hgt)
        rcases hFixed with he | hHigh
        · subst copy
          obtain ⟨J,hJ,hRows⟩ := hCF.copy_embedding_d hM hC hT hX hCopy
          have hEq := hJ.graph.unique X.root child X.root ((hRows X.root child).mpr ⟨hX.below,hRootMap⟩)
            ((hRows X.root X.root).mpr ⟨hX.below,CopyCoordinates.parent_copy_zero_d hM hC hT hX hX.root⟩)
          exact False.elim (not_lt_of_le_d hM hC hX.root hAfter (hEq ▸ hCandidate.1.1))
        · obtain ⟨x,_,y,hy,hTargetValue,hY,hxy,_⟩ := hCandidate.2
          have hrB : M.mem r B.height := hExp.height.symm ▸ hr
          have hRootEntry := (lifted_entry_unascending_iff hM.1 hA (fun h => hHigh h.1)).mp
            ((hExp.parent_copy_entry_iff_d hM hC hA hT hX hLast hIndex hCopy hX.below hRootMap).mp
              ((matrix_row_view_entry_iff_d hM hExp.matrix hrB hVB child y).mp hY))
          have hBound := copied_root_bad_ancestor_value_ge_d hM hC hA hT hX hExp hLast hIndex hr hSel hRootLast hCF hPreviousLow
            hV hVB hRootEntry hCopy hRootMap hAfter hCandidate.1 hTargetValue
          exact False.elim (not_lt_of_le_d hM hC hy hBound hxy)
    exact (hGoodIff hGood).mp hCandidate
  · intro hCandidate
    exact (hGoodIff hCandidate.1.1).mpr hCandidate

/-- 首副本root及临界行root的实际新父行等于原root父行，包含无父情况。 -/
theorem fixed_root_selected_parent_iff_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {A B : FiniteMatrix M.Domain} (hA : A.Valid M C.omega)
    {T : MatrixArithmetic M.Domain} (hT : T.Valid M C) {X : CopyCoordinates.Context M.Domain} (hX : X.Valid M C)
    {Forests Rows maximal index count total r F P previous previousMax QF V VB Q copy child : M.Domain}
    (hExp : RawMatrixExpansion M C A T Forests Rows X.last maximal X.root index count X.length total B)
    (hLast : M.mem X.last A.width) (hIndex : M.mem index C.omega) (hr : M.mem r A.height)
    (hSel : Selects false M C A.width F V P) (hRootLast : Ancestor M C A.width P X.root X.last)
    (hCF : CopyForest M C T X F previous previousMax count B.width QF) (hPreviousLow : M.mem previous previousMax)
    (hFixed : copy=C.zero ∨ ¬M.mem r maximal)
    (hV : MatrixRowValues M C.omega A.width A.cells A.values r V)
    (hVB : MatrixRowValues M C.omega B.width B.cells B.values r VB) (hNew : Selects false M C B.width QF VB Q)
    (hCopy : M.mem copy count) (hRootMap : CopyCoordinates.ParentCopy M C T X copy X.root child) :
    ∀ target, MemPair M Q child target ↔ MemPair M P X.root target := by
  have hCandidates (target : M.Domain) := fixed_root_candidate_iff_d hM hC hA hT hX hExp hLast hIndex hr hSel hRootLast
    hCF hPreviousLow hFixed hV hVB hCopy hRootMap (target := target)
  intro target
  rw [hNew.parents,hSel.parents]
  constructor
  · rintro ⟨hCandidate,hMax⟩
    refine ⟨(hCandidates target).mp hCandidate,?_⟩
    intro q _ hQ
    have hNewQ := (hCandidates q).mpr hQ
    exact hMax q hNewQ.1.1 hNewQ
  · rintro ⟨hCandidate,hMax⟩
    refine ⟨(hCandidates target).mpr hCandidate,?_⟩
    intro q _ hQ
    have hOldQ := (hCandidates q).mp hQ
    exact hMax q hOldQ.1.1 hOldQ

/-- 低行的新块根实际读值恰为前块virtual-last的提升值。 -/
theorem _root_.KP1Y.OneYFinite.RawMatrixExpansion.seam_entry_iff_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {A B : FiniteMatrix M.Domain} (hA : A.Valid M C.omega)
    {T : MatrixArithmetic M.Domain} (hT : T.Valid M C) {X : CopyCoordinates.Context M.Domain} (hX : X.Valid M C)
    {Forests Rows L maximal index count total r prev next child y : M.Domain}
    (hRun : MatrixParentRun M C A.width A.height A.cells A.values Forests Rows L)
    (hContext : MatrixExpansionContext M C A Forests Rows X.last maximal X.root)
    (hExp : RawMatrixExpansion M C A T Forests Rows X.last maximal X.root index count X.length total B)
    (hIndex : M.mem index C.omega) (hLow : M.mem r maximal) (hPrev : M.mem prev C.omega)
    (hs : M.SuccessorOf next prev) (hNext : M.mem next count)
    (hRootMap : CopyCoordinates.ParentCopy M C T X next X.root child) :
    MatrixEntry M B r child y ↔ LiftedEntry M C A T Forests Rows X.last maximal X.root prev X.last r y := by
  have hw := omega_isOrdinal_d hM hC.omega
  have hLast := hContext.width_successor.predecessor_mem
  have hRoot := (hw.mem hA.width).transitive X.last hLast X.root hX.below
  have hr := (hw.mem hA.height).transitive maximal hContext.row r hLow
  have hNextNat := natural_successor_mem_d hM hC hPrev hs
  have hEntry := hExp.parent_copy_entry_iff_d hM hC hA hT hX hLast hIndex hNext hX.below hRootMap (r := r) (y := y)
  constructor
  · intro hB
    have hNew := hEntry.mp hB
    obtain ⟨z,_,hOld⟩ := lifted_entry_exists_d hM hC hA hT hLast hRoot hPrev hLast hr
    have hEq := hContext.lifted_root_succ_eq_last_d hM hC hA hT hRun hLow hPrev hs hNew hOld
    exact hEq.symm ▸ hOld
  · intro hOld
    obtain ⟨z,_,hNew⟩ := lifted_entry_exists_d hM hC hA hT hLast hRoot hNextNat hRoot hr
    have hEq := hContext.lifted_root_succ_eq_last_d hM hC hA hT hRun hLow hPrev hs hNew hOld
    exact hEntry.mpr (hEq ▸ hNew)

/-- 下一块根的任意祖先来自前块的last候选链，或位于前块根及其祖先中。 -/
theorem CopyForest.ancestor_previous_root_origin_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {X : CopyCoordinates.Context M.Domain} (hX : X.Valid M C) {m F previous previousMax count width QF prev next child z x : M.Domain}
    (hF : Forest M C.omega m F) (hCF : CopyForest M C T X F previous previousMax count width QF)
    (hLast : M.mem X.last m) (hLow : M.mem previous previousMax) (hPrev : M.mem prev C.omega)
    (hs : M.SuccessorOf next prev) (hNext : M.mem next count)
    (hPos : CopyPosition M C.omega T.addPairs T.plus T.mulPairs T.times X.root X.length next C.zero child)
    (hRootMap : CopyCoordinates.ParentCopy M C T X prev X.root z) (hAncestor : Ancestor M C width QF x child) :
    (∃ q, M.mem q X.last ∧ CopyCoordinates.ParentCopy M C T X prev q x ∧ Ancestor M C m F q X.last) ∨
      (x=z ∨ Ancestor M C width QF x z) := by
  have hPrevCount := ((omega_isOrdinal_d hM hC.omega).mem hCF.count_nat).transitive next hNext prev hs.predecessor_mem
  obtain ⟨t,hParent,hBefore⟩ := ancestor_parent_cases_d hM hC hCF.forest hAncestor
  obtain ⟨p,hp,hOldParent,hMapP⟩ := (hCF.root_low_parent_iff_d hM hC hT hX hCF.count_nat hNext hPrev hs hLow hPos t).mp hParent
  rcases hBefore with he | hBefore
  · exact Or.inl ⟨p,hp,he.symm ▸ hMapP,ancestor_direct_d hM hC hF hOldParent⟩
  · rcases hCF.ancestor_origin_or_root_d hM hC hT hX hF hLast hPrevCount hp hMapP hRootMap hBefore with
      ⟨q,hq,hMapQ,hAncQ⟩ | ⟨hToRoot,_⟩
    · exact Or.inl ⟨q,hq,hMapQ,ancestor_step_d hM hC hF hAncQ hOldParent⟩
    · exact Or.inr hToRoot

/-- 低行seam的真实最右父项：前块virtual-last的坏部源父项。 -/
theorem seam_restricted_parent_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {A B : FiniteMatrix M.Domain} (hA : A.Valid M C.omega)
    {T : MatrixArithmetic M.Domain} (hT : T.Valid M C) {X : CopyCoordinates.Context M.Domain} (hX : X.Valid M C)
    {Forests Rows L maximal index count total r F P previous previousMax QF V VB prev next child p target : M.Domain}
    (hRun : MatrixParentRun M C A.width A.height A.cells A.values Forests Rows L)
    (hContext : MatrixExpansionContext M C A Forests Rows X.last maximal X.root)
    (hExp : RawMatrixExpansion M C A T Forests Rows X.last maximal X.root index count X.length total B)
    (hIndex : M.mem index C.omega) (hLow : M.mem r maximal)
    (hPrevious : PreviousMatrixForest M C A.height Forests Rows L r F) (hP : MemPair M Rows r P)
    (hV : MatrixRowValues M C.omega A.width A.cells A.values r V)
    (hVB : MatrixRowValues M C.omega B.width B.cells B.values r VB)
    (hCF : CopyForest M C T X F previous previousMax count B.width QF) (hPreviousLow : M.mem previous previousMax)
    (hPrev : M.mem prev C.omega) (hs : M.SuccessorOf next prev) (hNext : M.mem next count)
    (hRootMap : CopyCoordinates.ParentCopy M C T X next X.root child)
    (hParent : MemPair M P X.last p) (hBadParent : X.root=p ∨ M.mem X.root p)
    (hTarget : CopyCoordinates.ParentCopy M C T X prev p target) :
    RestrictedParent false M C B.width QF VB child target := by
  have hw := omega_isOrdinal_d hM hC.omega
  have hLast := hContext.width_successor.predecessor_mem
  have hr := (hRun.graph.bounds hM.1 hP).1
  have hrB : M.mem r B.height := hExp.height.symm ▸ hr
  have hSel := hRun.selects_previous_d hPrevious hP hV
  have hp := hSel.forest.left X.last p hParent
  have hPrevCount := (hw.mem hCF.count_nat).transitive next hNext prev hs.predecessor_mem
  have hNextNat := hw.transitive count hCF.count_nat next hNext
  have hRootZero := (hT.add.add_iff_sum hM hX.root hC.zero_nat).mpr (sum_zero_d hM X.root hC.zero_empty)
  have hEncode := (CopyCoordinates.parent_copy_bad_iff (SetTheory.KP.mem_irrefl_d (KP1Y.models_weakKP hM) X.root)).mp hRootMap
  have hPos := (CopyCoordinates.encode_at_base_iff_d hM hC hT hX.root hC.zero_nat hNextNat hRootZero).mp hEncode
  have hAncestor := (hCF.ancestor_previous_root_iff_d hM hC hT hX hSel.inherited hLast hNext hPrev hs hPreviousLow hBadParent hp hTarget hPos).mpr
    (hSel.parent_ancestor hParent)
  have hChildBound := hCF.copy_value_bound_d hM hC hT hX hNext hX.below hRootMap
  have hTargetBound := hCF.copy_value_bound_d hM hC hT hX hPrevCount hp hTarget
  obtain ⟨x,hx,hXValue⟩ := hVB.graph.total target hTargetBound
  obtain ⟨y,hy,hYValue⟩ := hVB.graph.total child hChildBound
  have hLiftY := (hExp.seam_entry_iff_d hM hC hA hT hX hRun hContext hIndex hLow hPrev hs hNext hRootMap).mp
    ((matrix_row_view_entry_iff_d hM hExp.matrix hrB hVB child y).mp hYValue)
  have hLiftX := (hExp.parent_copy_entry_iff_d hM hC hA hT hX hLast hIndex hPrevCount hp hTarget).mp
    ((matrix_row_view_entry_iff_d hM hExp.matrix hrB hVB target x).mp hXValue)
  obtain ⟨a,_,b,_,hAValue,hBValue,hab,_⟩ := hSel.parent_values hParent
  have hNonroot : X.last≠X.root := fun he => SetTheory.KP.mem_irrefl_d (KP1Y.models_weakKP hM) X.root (he ▸ hX.below)
  have hxy := lifted_values_lt_of_flags_mono_d hM hC hA hT (U := ⟨Forests,Rows,X.last,maximal,X.root,prev⟩)
    ((matrix_row_view_entry_iff_d hM hA hr hV p a).mp hAValue)
    ((matrix_row_view_entry_iff_d hM hA hr hV X.last b).mp hBValue) hab
    (hRun.ascending_parent_iff_d hM hC hP hParent hNonroot).mp hLiftX hLiftY
  refine ⟨⟨hAncestor,x,hx,y,hy,hXValue,hYValue,hxy,True.intro⟩,?_⟩
  intro t _ hCandidate
  obtain ⟨J,hJ,hRows⟩ := hCF.copy_embedding_d hM hC hT hX hPrevCount
  obtain ⟨z,_,hJRoot⟩ := hJ.graph.total X.root hX.below
  have hPrevRoot := ((hRows X.root z).mp hJRoot).2
  have hJTarget := (hRows p target).mpr ⟨hp,hTarget⟩
  have hZBefore : z=target ∨ M.mem z target := by
    rcases hBadParent with he | hlt
    · subst p
      exact Or.inl (hJ.graph.unique X.root z target hJRoot hJTarget)
    · exact Or.inr (hJ.strict X.root hX.below p hp hlt z target hJRoot hJTarget)
  rcases hCF.ancestor_previous_root_origin_d hM hC hT hX hSel.inherited hLast hPreviousLow hPrev hs hNext hPos hPrevRoot hCandidate.1 with
      ⟨q,hq,hMapQ,hOldQ⟩ | hToRoot
  · have hJQ := (hRows q t).mpr ⟨hq,hMapQ⟩
    rcases hw.wellOrder.linear.compare q (hw.transitive X.last hX.last q hq) p (hw.transitive X.last hX.last p hp) with he | hlt | hgt
    · have heq := hM.1.eq_of_same_members q p he
      subst q
      exact Or.inl (hJ.graph.unique p t target hJQ hJTarget)
    · exact Or.inr (hJ.strict q hq p hp hlt t target hJQ hJTarget)
    · obtain ⟨v,hv,w,hwNat,hVValue,hWValue,hvw,_⟩ := hCandidate.2
      have hW := (hExp.seam_entry_iff_d hM hC hA hT hX hRun hContext hIndex hLow hPrev hs hNext hRootMap).mp
        ((matrix_row_view_entry_iff_d hM hExp.matrix hrB hVB child w).mp hWValue)
      have hVq := (hExp.parent_copy_entry_iff_d hM hC hA hT hX hLast hIndex hPrevCount hq hMapQ).mp
        ((matrix_row_view_entry_iff_d hM hExp.matrix hrB hVB t v).mp hVValue)
      have hWV := lifted_entry_ge_after_parent_d hM hC hA hT (U := ⟨Forests,Rows,X.last,maximal,X.root,prev⟩)
        hRun hPrevious hP hParent hOldQ hgt hNonroot hW hVq
      exact False.elim (not_lt_of_le_d hM hC hwNat hWV hvw)
  · have hToRootLe := hToRoot.imp id (fun h => h.1)
    exact le_trans_d hM hC (hw.transitive B.width hExp.matrix.width target hTargetBound) hToRootLe hZBefore

/-- 低行后继副本root的实际父行精确等于前副本运输后的原last父行。 -/
theorem seam_selected_parent_iff_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {A B : FiniteMatrix M.Domain} (hA : A.Valid M C.omega)
    {T : MatrixArithmetic M.Domain} (hT : T.Valid M C) {X : CopyCoordinates.Context M.Domain} (hX : X.Valid M C)
    {Forests Rows L maximal index count total r F P previous previousMax QF V VB Q prev next child : M.Domain}
    (hRun : MatrixParentRun M C A.width A.height A.cells A.values Forests Rows L)
    (hContext : MatrixExpansionContext M C A Forests Rows X.last maximal X.root)
    (hExp : RawMatrixExpansion M C A T Forests Rows X.last maximal X.root index count X.length total B)
    (hIndex : M.mem index C.omega) (hLow : M.mem r maximal)
    (hPrevious : PreviousMatrixForest M C A.height Forests Rows L r F) (hP : MemPair M Rows r P)
    (hV : MatrixRowValues M C.omega A.width A.cells A.values r V)
    (hVB : MatrixRowValues M C.omega B.width B.cells B.values r VB) (hNew : Selects false M C B.width QF VB Q)
    (hCF : CopyForest M C T X F previous previousMax count B.width QF) (hPreviousLow : M.mem previous previousMax)
    (hPrev : M.mem prev C.omega) (hs : M.SuccessorOf next prev) (hNext : M.mem next count)
    (hRootMap : CopyCoordinates.ParentCopy M C T X next X.root child) :
    ∀ target, MemPair M Q child target ↔ ∃ p, M.mem p X.last ∧ MemPair M P X.last p ∧ CopyCoordinates.ParentCopy M C T X prev p target := by
  have hSel := hRun.selects_previous_d hPrevious hP hV
  have hRootLast : Ancestor M C A.width P X.root X.last := by
    obtain ⟨_,hEq | ⟨P',_,hP',hAnc⟩⟩ := hContext.last_ascending_below_d hM hC hRun hLow
    · exact False.elim (SetTheory.KP.mem_irrefl_d (KP1Y.models_weakKP hM) X.root (hEq ▸ hX.below))
    · exact hRun.graph.unique r P' P hP' hP ▸ hAnc
  have hChosen (p target : M.Domain) (hParent : MemPair M P X.last p) (hMap : CopyCoordinates.ParentCopy M C T X prev p target) : MemPair M Q child target := by
    have hBad := ancestor_le_parent_d hM hC hSel.forest hParent hRootLast
    exact (hNew.parents child target).mpr (seam_restricted_parent_d hM hC hA hT hX hRun hContext hExp hIndex hLow hPrevious hP
      hV hVB hCF hPreviousLow hPrev hs hNext hRootMap hParent hBad hMap)
  intro target
  constructor
  · intro hParent
    obtain ⟨p,hOldParent,_⟩ := ancestor_parent_cases_d hM hC hSel.forest hRootLast
    have hp := hSel.forest.left X.last p hOldParent
    have hPrevCount := ((omega_isOrdinal_d hM hC.omega).mem hCF.count_nat).transitive next hNext prev hs.predecessor_mem
    obtain ⟨J,hJ,hRows⟩ := hCF.copy_embedding_d hM hC hT hX hPrevCount
    obtain ⟨t,_,hMap⟩ := hJ.graph.total p hp
    have hCopyP := ((hRows p t).mp hMap).2
    have he := hNew.forest.unique child t target (hChosen p t hOldParent hCopyP) hParent
    exact ⟨p,hp,hOldParent,he ▸ hCopyP⟩
  · rintro ⟨p,_,hParent,hMap⟩
    exact hChosen p target hParent hMap

end KP1Y.OneYFinite.MatrixCopy
