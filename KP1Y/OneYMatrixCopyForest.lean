import KP1Y.OneYMatrixExpansionFacts
import KP1Y.OneYCopyCoordinates
import KP1Y.OneYForestEmbedding
import KP1Y.OneYSelectionOrder

/-! BM4 复制行的实际候选父图。所有分支均给字面代码关系，森林性质由这些关系证明。
尚需将该候选图与输出矩阵的真实最右选择运行识别，不能把识别当作输入。
-/
namespace KP1Y.OneYFinite.MatrixCopy
open YesMetaZFC YesMetaZFC.SetTheory YesMetaZFC.SetTheory.Definitional
open KP1Y.Kuratowski KP1Y.Functions KP1Y.Naturals KP1Y.Bounded
open KP1Y.OneYFinite
universe u

def CopyBranch (M : SetTheory.Structure.{u}) (C : ExpressionData M.Domain) (T : MatrixArithmetic M.Domain)
    (X : CopyCoordinates.Context M.Domain) (P row maximal copy slot source target : M.Domain) : Prop :=
  (slot≠C.zero ∧ ∃ p, M.mem p X.last ∧ MemPair M P source p ∧ CopyCoordinates.ParentCopy M C T X copy p target) ∨
    (slot=C.zero ∧ (((copy=C.zero ∨ ¬M.mem row maximal) ∧ MemPair M P X.root target) ∨
      (copy≠C.zero ∧ M.mem row maximal ∧ ∃ prev, M.mem prev C.omega ∧ M.SuccessorOf copy prev ∧
        ∃ p, M.mem p X.last ∧ MemPair M P X.last p ∧ CopyCoordinates.ParentCopy M C T X prev p target)))

def CopiedParent (M : SetTheory.Structure.{u}) (C : ExpressionData M.Domain) (T : MatrixArithmetic M.Domain)
    (X : CopyCoordinates.Context M.Domain) (P row maximal count child target : M.Domain) : Prop :=
  (M.mem child X.root ∧ MemPair M P child target) ∨
    ∃ copy, M.mem copy count ∧ ∃ slot, M.mem slot X.length ∧ ∃ source, M.mem source X.last ∧
      AddAt M T.addPairs T.plus X.root slot source ∧
      CopyPosition M C.omega T.addPairs T.plus T.mulPairs T.times X.root X.length copy slot child ∧
      CopyBranch M C T X P row maximal copy slot source target

def copyBranchFormula {d : Nat} (C : ExpressionData (Project.Term d)) (T : MatrixArithmetic (Project.Term d))
    (X : CopyCoordinates.Context (Project.Term d)) (P row maximal copy slot source target : Project.Term d) : Project.Formula 1 d :=
  .disj (.conj (.neg (Project.Formula.extensionalEq slot C.zero)) (Project.Formula.existsMem X.last
    (.conj (memPairFormula P.weaken source.weaken (.bound 0))
      (CopyCoordinates.parentCopyFormula C.weaken T.weaken X.weaken copy.weaken (.bound 0) target.weaken))))
    (.conj (Project.Formula.extensionalEq slot C.zero)
      (.disj (.conj (.disj (Project.Formula.extensionalEq copy C.zero) (.neg (.mem row maximal))) (memPairFormula P X.root target))
        (.conj (.neg (Project.Formula.extensionalEq copy C.zero)) (.conj (.mem row maximal)
          (Project.Formula.existsMem C.omega (.conj (successorFormula copy.weaken (.bound 0))
            (Project.Formula.existsMem X.last.weaken (.conj (memPairFormula P.weaken.weaken X.last.weaken.weaken (.bound 0))
              (CopyCoordinates.parentCopyFormula C.weaken.weaken T.weaken.weaken X.weaken.weaken (.bound 1) (.bound 0) target.weaken.weaken)))))))))

theorem copyBranchFormula_delta0 {d : Nat} (C : ExpressionData (Project.Term d)) (T : MatrixArithmetic (Project.Term d))
    (X : CopyCoordinates.Context (Project.Term d)) (P row maximal copy slot source target : Project.Term d) :
    (copyBranchFormula C T X P row maximal copy slot source target).IsDelta0 :=
  .disj (.conj (.neg (.atom _ _ _)) (.existsMem _ (.conj (memPairFormula_delta0 _ _ _) (CopyCoordinates.parentCopyFormula_delta0 _ _ _ _ _ _))))
    (.conj (.atom _ _ _) (.disj (.conj (.disj (.atom _ _ _) (.neg (.mem _ _))) (memPairFormula_delta0 _ _ _))
      (.conj (.neg (.atom _ _ _)) (.conj (.mem _ _) (.existsMem _ (.conj (successorFormula_delta0 _ _)
        (.existsMem _ (.conj (memPairFormula_delta0 _ _ _) (CopyCoordinates.parentCopyFormula_delta0 _ _ _ _ _ _)))))))))

theorem copyBranchFormula_iff {M : SetTheory.Structure.{u}} (he : Extensional M) {d : Nat} (env : Env M d)
    (C : ExpressionData (Project.Term d)) (T : MatrixArithmetic (Project.Term d)) (X : CopyCoordinates.Context (Project.Term d))
    (P row maximal copy slot source target : Project.Term d) :
    Project.Formula.satisfies env (copyBranchFormula C T X P row maximal copy slot source target) ↔
      CopyBranch M (C.eval env) (T.eval env) (X.eval env) (P.eval env) (row.eval env) (maximal.eval env)
        (copy.eval env) (slot.eval env) (source.eval env) (target.eval env) := by
  simp only [copyBranchFormula,CopyBranch,Project.Formula.satisfies_disj_iff,Project.Formula.satisfies_conj_iff,
    Project.Formula.satisfies_neg_iff,Project.Formula.satisfies_extensionalEq_iff_eq he,Project.Formula.satisfies_mem_iff,
    Project.Formula.satisfies_existsMem_iff,memPairFormula_iff he,CopyCoordinates.parentCopyFormula_iff he,
    successorFormula_iff he,ExpressionData.eval_weaken,MatrixArithmetic.eval_weaken,CopyCoordinates.Context.eval_weaken,Term.eval_weaken]
  rfl

def copiedParentFormula {d : Nat} (C : ExpressionData (Project.Term d)) (T : MatrixArithmetic (Project.Term d))
    (X : CopyCoordinates.Context (Project.Term d)) (P row maximal count child target : Project.Term d) : Project.Formula 1 d :=
  .disj (.conj (.mem child X.root) (memPairFormula P child target))
    (Project.Formula.existsMem count (Project.Formula.existsMem X.length.weaken (Project.Formula.existsMem X.last.weaken.weaken
      (.conj (addAtFormula T.addPairs.weaken.weaken.weaken T.plus.weaken.weaken.weaken X.root.weaken.weaken.weaken (.bound 1) (.bound 0))
        (.conj (copyPositionFormula C.omega.weaken.weaken.weaken T.addPairs.weaken.weaken.weaken T.plus.weaken.weaken.weaken
          T.mulPairs.weaken.weaken.weaken T.times.weaken.weaken.weaken X.root.weaken.weaken.weaken X.length.weaken.weaken.weaken
          (.bound 2) (.bound 1) child.weaken.weaken.weaken)
          (copyBranchFormula C.weaken.weaken.weaken T.weaken.weaken.weaken X.weaken.weaken.weaken P.weaken.weaken.weaken
            row.weaken.weaken.weaken maximal.weaken.weaken.weaken (.bound 2) (.bound 1) (.bound 0) target.weaken.weaken.weaken))))))

theorem copiedParentFormula_delta0 {d : Nat} (C : ExpressionData (Project.Term d)) (T : MatrixArithmetic (Project.Term d))
    (X : CopyCoordinates.Context (Project.Term d)) (P row maximal count child target : Project.Term d) :
    (copiedParentFormula C T X P row maximal count child target).IsDelta0 :=
  .disj (.conj (.mem _ _) (memPairFormula_delta0 _ _ _)) (.existsMem _ (.existsMem _ (.existsMem _
    (.conj (addAtFormula_delta0 _ _ _ _ _) (.conj (copyPositionFormula_delta0 _ _ _ _ _ _ _ _ _ _) (copyBranchFormula_delta0 _ _ _ _ _ _ _ _ _ _))))))

theorem copiedParentFormula_iff {M : SetTheory.Structure.{u}} (he : Extensional M) {d : Nat} (env : Env M d)
    (C : ExpressionData (Project.Term d)) (T : MatrixArithmetic (Project.Term d)) (X : CopyCoordinates.Context (Project.Term d))
    (P row maximal count child target : Project.Term d) :
    Project.Formula.satisfies env (copiedParentFormula C T X P row maximal count child target) ↔
      CopiedParent M (C.eval env) (T.eval env) (X.eval env) (P.eval env) (row.eval env) (maximal.eval env)
        (count.eval env) (child.eval env) (target.eval env) := by
  simp only [copiedParentFormula,CopiedParent,Project.Formula.satisfies_disj_iff,Project.Formula.satisfies_conj_iff,
    Project.Formula.satisfies_mem_iff,Project.Formula.satisfies_existsMem_iff,memPairFormula_iff he,addAtFormula_iff he,
    copyPositionFormula_iff he,copyBranchFormula_iff he,ExpressionData.eval_weaken,MatrixArithmetic.eval_weaken,
    CopyCoordinates.Context.eval_weaken,Term.eval_weaken]
  rfl

private theorem parent_copy_unique_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {X : CopyCoordinates.Context M.Domain} (hX : X.Valid M C) {copy p x y : M.Domain}
    (hx : CopyCoordinates.ParentCopy M C T X copy p x) (hy : CopyCoordinates.ParentCopy M C T X copy p y) : x=y := by
  obtain ⟨J,hJ,hRows⟩ := CopyCoordinates.parent_copy_graph_exists_d hM hC hT hX hx.2.1
  exact hJ.graph.unique p x y ((hRows p x).mpr hx) ((hRows p y).mpr hy)

theorem copied_parent_unique_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {X : CopyCoordinates.Context M.Domain} (hX : X.Valid M C) {m P row maximal count child x y : M.Domain}
    (hP : Forest M C.omega m P) (hCount : M.mem count C.omega)
    (hx : CopiedParent M C T X P row maximal count child x) (hy : CopiedParent M C T X P row maximal count child y) : x=y := by
  have hw := omega_isOrdinal_d hM hC.omega
  rcases hx with ⟨hGood,hParent⟩ | ⟨b,hb,j,hj,s,_,hSource,hPos,hBranch⟩ <;>
    rcases hy with ⟨hGood',hParent'⟩ | ⟨b',hb',j',hj',s',_,hSource',hPos',hBranch'⟩
  · exact hP.unique child x y hParent hParent'
  · exact False.elim (copy_position_not_good_d hM hC hT hX.root (hw.transitive X.length (hX.length_nat hM.1) j' hj') hPos' hGood)
  · exact False.elim (copy_position_not_good_d hM hC hT hX.root (hw.transitive X.length (hX.length_nat hM.1) j hj) hPos hGood')
  · obtain ⟨hCopies,hSlots⟩ := copy_position_injective_d hM hC hT.add hT.mul hX.root (hX.length_nat hM.1)
      (hw.transitive count hCount b hb) (hw.transitive count hCount b' hb') hj hj' hPos hPos'
    subst b'
    subst j'
    have hSources := hT.add.add_unique hM.1 hSource hSource'
    subst s'
    rcases hBranch with ⟨hj0,p,_,hSp,hCopyP⟩ | ⟨hj0,hRootCase⟩ <;>
      rcases hBranch' with ⟨hj0',q,_,hSq,hCopyQ⟩ | ⟨hj0',hRootCase'⟩
    · have hpq := hP.unique s p q hSp hSq
      subst q
      exact parent_copy_unique_d hM hC hT hX hCopyP hCopyQ
    · exact False.elim (hj0 hj0')
    · exact False.elim (hj0' hj0)
    · rcases hRootCase with ⟨hHigh,hRx⟩ | ⟨hb0,hr,prev,hPrev,hSucc,p,_,hLp,hCopyP⟩ <;>
        rcases hRootCase' with ⟨hHigh',hRy⟩ | ⟨hb0',hr',prev',hPrev',hSucc',q,_,hLq,hCopyQ⟩
      · exact hP.unique X.root x y hRx hRy
      · exact False.elim (hHigh.elim hb0' (fun h => h hr'))
      · exact False.elim (hHigh'.elim hb0 (fun h => h hr))
      · have hPrevEq := Structure.SuccessorOf.predecessor_eq hM.1 (hw.mem hPrev) hSucc hSucc'
        subst prev'
        have hpq := hP.unique X.last p q hLp hLq
        subst q
        exact parent_copy_unique_d hM hC hT hX hCopyP hCopyQ

theorem copied_parent_left_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {X : CopyCoordinates.Context M.Domain} (hX : X.Valid M C) {m P row maximal count child target : M.Domain}
    (hP : Forest M C.omega m P) (hCount : M.mem count C.omega)
    (h : CopiedParent M C T X P row maximal count child target) : M.mem target child := by
  rcases h with ⟨_,hParent⟩ | ⟨copy,hCopy,slot,hSlot,source,_,hSource,hPos,hBranch⟩
  · exact hP.left child target hParent
  · have hw := omega_isOrdinal_d hM hC.omega
    have hCopyNat := hw.transitive count hCount copy hCopy
    have hSlotNat := hw.transitive X.length (hX.length_nat hM.1) slot hSlot
    rcases hBranch with ⟨hSlot0,p,_,hParent,hParentCopy⟩ | ⟨hSlot0,hRootCase⟩
    · have hRootSource := KP1Y.Arithmetic.sum_base_mem_d hM (hw.mem hX.root)
        ((hT.add.add_iff_sum hM hX.root hSlotNat).mp hSource) ⟨C.zero,(hC.zero_mem_iff hM hSlotNat).mpr hSlot0⟩
      have hEncode := (CopyCoordinates.encode_at_base_iff_d hM hC hT hX.root hSlotNat hCopyNat hSource).mpr hPos
      exact CopyCoordinates.parent_copy_below_encode_d hM hC hT hX hRootSource (hP.left source p hParent) hParentCopy hEncode
    · subst slot
      rcases hRootCase with ⟨_,hParent⟩ | ⟨_,_,prev,hPrev,hSucc,p,_,hParent,hParentCopy⟩
      · obtain ⟨off,hOff,start,hStart,_,hRootStart,hStartChild⟩ := hPos
        have hChildStart := ((hT.add.add_iff_sum hM hStart hC.zero_nat).mp hStartChild).zero_value_d hM hC.zero_empty
        have hRootSub := KP1Y.Arithmetic.sum_base_subset_d hM (hw.mem hX.root) ((hT.add.add_iff_sum hM hX.root hOff).mp hRootStart)
        exact hChildStart.symm ▸ hRootSub target (hP.left X.root target hParent)
      · obtain ⟨off,hOff,hTimes⟩ := hT.mul.mul_exists_d hM hC hPrev (hX.length_nat hM.1)
        have hSeam := (CopyCoordinates.seam_bms_shift_iff_d hM hC hT hX hPrev hSucc hOff hTimes).mp hPos
        have hParentShift := (CopyCoordinates.parent_copy_shift_iff hM.1 hT hPrev hParentCopy.1 hOff hTimes).mp hParentCopy
        obtain ⟨J,hJ,hRows⟩ := CopyCoordinates.global_shift_map_exists_d hM hC hT hX.root hOff
        exact hJ.strict p hParentCopy.1 X.last hX.last (hP.left X.last p hParent) target child
          ((hRows p target).mpr ⟨hParentCopy.1,hParentShift⟩) ((hRows X.last child).mpr ⟨hX.last,hSeam⟩)

theorem copied_parent_bounds_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {X : CopyCoordinates.Context M.Domain} (hX : X.Valid M C) {m P row maximal count total width child target : M.Domain}
    (hP : Forest M C.omega m P) (hCount : M.mem count C.omega)
    (hTotal : KP1Y.Arithmetic.Product M count X.length total) (hWidth : KP1Y.Arithmetic.Sum M X.root total width)
    (h : CopiedParent M C T X P row maximal count child target) : M.mem child width ∧ M.mem target width := by
  have hLeft := copied_parent_left_d hM hC hT hX hP hCount h
  have hw := omega_isOrdinal_d hM hC.omega
  have hChild : M.mem child width := by
    rcases h with ⟨hGood,_⟩ | ⟨copy,hCopy,slot,hSlot,_,_,_,hPos,_⟩
    · exact KP1Y.Arithmetic.sum_base_subset_d hM (hw.mem hX.root) hWidth child hGood
    · exact copy_position_bounded_d hM hC hT.add hT.mul hX.root (hX.length_nat hM.1) hCount hTotal hWidth hCopy hSlot hPos
  exact ⟨hChild,(hWidth.isOrdinal_d hM (hw.mem hX.root)).transitive child hChild target hLeft⟩

private def copiedParentEnv {M : SetTheory.Structure.{u}} (C : ExpressionData M.Domain) (T : MatrixArithmetic M.Domain)
    (X : CopyCoordinates.Context M.Domain) (P row maximal count : M.Domain) : Env M 19 where
  bound i := match i.val with
    | 0 => C.omega | 1 => C.zero | 2 => C.one | 3 => C.sequences | 4 => C.expressions
    | 5 => T.addPairs | 6 => T.plus | 7 => T.mulPairs | 8 => T.times | 9 => T.diffPairs | 10 => T.difference
    | 11 => X.last | 12 => X.root | 13 => X.length | 14 => X.first
    | 15 => P | 16 => row | 17 => maximal | _ => count
  free _ := C.zero

private def copiedParentSchema : Project.Delta0BinarySchema 19 where
  body := copiedParentFormula ⟨.bound 2,.bound 3,.bound 4,.bound 5,.bound 6⟩
    ⟨.bound 7,.bound 8,.bound 9,.bound 10,.bound 11,.bound 12⟩ ⟨.bound 13,.bound 14,.bound 15,.bound 16⟩
    (.bound 17) (.bound 18) (.bound 19) (.bound 20) (.bound 1) (.bound 0)
  freeClosed := by
    simp [copiedParentFormula,copyBranchFormula,CopyCoordinates.parentCopyFormula,CopyCoordinates.encodeFormula,
      copyPositionFormula,ExpressionData.weaken,ExpressionData.map,MatrixArithmetic.weaken,MatrixArithmetic.map,
      CopyCoordinates.Context.weaken,CopyCoordinates.Context.map,mulAtFormula,addAtFormula,successorFormula,
      memPairFormula,codeFormula,pairFormula,Project.Formula.forallMem,Project.Formula.existsMem,Definitional.Formula.FreeClosed]
  delta0 := copiedParentFormula_delta0 _ _ _ _ _ _ _ _ _

private theorem copiedParentSchema_iff {M : SetTheory.Structure.{u}} (he : Extensional M)
    (C : ExpressionData M.Domain) (T : MatrixArithmetic M.Domain) (X : CopyCoordinates.Context M.Domain)
    (P row maximal count child target : M.Domain) :
    Project.Formula.satisfies (((copiedParentEnv C T X P row maximal count).push child).push target) copiedParentSchema.body ↔
      CopiedParent M C T X P row maximal count child target := by
  simp only [copiedParentSchema,copiedParentFormula_iff he]
  rfl

structure CopyForest (M : SetTheory.Structure.{u}) (C : ExpressionData M.Domain) (T : MatrixArithmetic M.Domain)
    (X : CopyCoordinates.Context M.Domain) (P row maximal count width Q : M.Domain) : Prop where
  forest : Forest M C.omega width Q
  parents : ∀ c p, MemPair M Q c p ↔ CopiedParent M C T X P row maximal count c p
  count_nat : M.mem count C.omega
  width_geometry : ∃ total, KP1Y.Arithmetic.Product M count X.length total ∧ KP1Y.Arithmetic.Sum M X.root total width

/-- 从分情况的字面父代码真正构造部分函数图，并证明森林性和精确父行。 -/
theorem copy_forest_exists_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {X : CopyCoordinates.Context M.Domain} (hX : X.Valid M C) {m P row maximal count total width : M.Domain}
    (hP : Forest M C.omega m P) (hCount : M.mem count C.omega)
    (hTotal : KP1Y.Arithmetic.Product M count X.length total) (hWidth : KP1Y.Arithmetic.Sum M X.root total width) :
    ∃ Q, CopyForest M C T X P row maximal count width Q := by
  let env := copiedParentEnv C T X P row maximal count
  obtain ⟨Q,hSupport,hRaw⟩ := relation_comprehension_d hM copiedParentSchema env width width
  have hRows (c p : M.Domain) : MemPair M Q c p ↔ CopiedParent M C T X P row maximal count c p := by
    rw [hRaw c p,copiedParentSchema_iff hM.1]
    refine ⟨fun h => h.2.2,fun h => ?_⟩
    have hBounds := copied_parent_bounds_d hM hC hT hX hP hCount hTotal hWidth h
    exact ⟨hBounds.1,hBounds.2,h⟩
  have hWidthNat := natural_sum_closed_d hM hC.omega hX.root
    (natural_product_closed_d hM hC hCount (hX.length_nat hM.1) hTotal) hWidth
  exact ⟨Q,⟨hWidthNat,hSupport,
    fun c p q hp hq => copied_parent_unique_d hM hC hT hX hP hCount ((hRows c p).mp hp) ((hRows c q).mp hq),
    fun c p hp => copied_parent_left_d hM hC hT hX hP hCount ((hRows c p).mp hp)⟩,hRows,hCount,total,hTotal,hWidth⟩

theorem CopyForest.at_copy_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {X : CopyCoordinates.Context M.Domain} (hX : X.Valid M C) {P row maximal count width Q copy slot source child : M.Domain}
    (hQ : CopyForest M C T X P row maximal count width Q) (hCount : M.mem count C.omega)
    (hCopy : M.mem copy count) (hSlot : M.mem slot X.length) (hSourceBound : M.mem source X.last)
    (hSource : AddAt M T.addPairs T.plus X.root slot source)
    (hPos : CopyPosition M C.omega T.addPairs T.plus T.mulPairs T.times X.root X.length copy slot child) :
    ∀ target, MemPair M Q child target ↔ CopyBranch M C T X P row maximal copy slot source target := by
  have hw := omega_isOrdinal_d hM hC.omega
  have hCopyNat := hw.transitive count hCount copy hCopy
  have hSlotNat := hw.transitive X.length (hX.length_nat hM.1) slot hSlot
  intro target
  constructor
  · intro hAt
    rcases (hQ.parents child target).mp hAt with ⟨hGood,_⟩ | ⟨b,hb,j,hj,s,_,hSource',hPos',hBranch⟩
    · exact False.elim (copy_position_not_good_d hM hC hT hX.root hSlotNat hPos hGood)
    · obtain ⟨hCopies,hSlots⟩ := copy_position_injective_d hM hC hT.add hT.mul hX.root (hX.length_nat hM.1)
        hCopyNat (hw.transitive count hCount b hb) hSlot hj hPos hPos'
      subst b
      subst j
      have hSources := hT.add.add_unique hM.1 hSource hSource'
      subst s
      exact hBranch
  · intro hBranch
    exact (hQ.parents child target).mpr (Or.inr ⟨copy,hCopy,slot,hSlot,source,hSourceBound,hSource,hPos,hBranch⟩)

theorem CopyForest.good_parent_iff_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {X : CopyCoordinates.Context M.Domain} (hX : X.Valid M C) {P row maximal count width Q child target : M.Domain}
    (hQ : CopyForest M C T X P row maximal count width Q) (hGood : M.mem child X.root) :
    MemPair M Q child target ↔ MemPair M P child target := by
  constructor
  · intro hAt
    rcases (hQ.parents child target).mp hAt with ⟨_,hParent⟩ | ⟨_,_,slot,hSlot,_,_,_,hPos,_⟩
    · exact hParent
    · exact False.elim (copy_position_not_good_d hM hC hT hX.root
        ((omega_isOrdinal_d hM hC.omega).transitive X.length (hX.length_nat hM.1) slot hSlot) hPos hGood)
  · intro hParent
    exact (hQ.parents child target).mpr (Or.inl ⟨hGood,hParent⟩)

theorem CopyForest.nonroot_parent_iff_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {X : CopyCoordinates.Context M.Domain} (hX : X.Valid M C) {P row maximal count width Q copy slot source child : M.Domain}
    (hQ : CopyForest M C T X P row maximal count width Q) (hCount : M.mem count C.omega)
    (hCopy : M.mem copy count) (hSlot : M.mem slot X.length) (hNot : slot≠C.zero) (hSourceBound : M.mem source X.last)
    (hSource : AddAt M T.addPairs T.plus X.root slot source)
    (hPos : CopyPosition M C.omega T.addPairs T.plus T.mulPairs T.times X.root X.length copy slot child) :
    ∀ target, MemPair M Q child target ↔ ∃ p, M.mem p X.last ∧ MemPair M P source p ∧ CopyCoordinates.ParentCopy M C T X copy p target := by
  intro target
  apply (hQ.at_copy_d hM hC hT hX hCount hCopy hSlot hSourceBound hSource hPos target).trans
  exact ⟨fun h => h.elim And.right (fun h => False.elim (hNot h.1)),fun h => Or.inl ⟨hNot,h⟩⟩

theorem CopyForest.root_high_parent_iff_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {X : CopyCoordinates.Context M.Domain} (hX : X.Valid M C) {P row maximal count width Q copy child : M.Domain}
    (hQ : CopyForest M C T X P row maximal count width Q) (hCount : M.mem count C.omega) (hCopy : M.mem copy count)
    (hHigh : copy=C.zero ∨ ¬M.mem row maximal)
    (hPos : CopyPosition M C.omega T.addPairs T.plus T.mulPairs T.times X.root X.length copy C.zero child) :
    ∀ target, MemPair M Q child target ↔ MemPair M P X.root target := by
  have hSource := (hT.add.add_iff_sum hM hX.root hC.zero_nat).mpr (KP1Y.Arithmetic.sum_zero_d hM X.root hC.zero_empty)
  intro target
  apply (hQ.at_copy_d hM hC hT hX hCount hCopy (hX.length_positive_d hM hC) hX.below hSource hPos target).trans
  constructor
  · rintro (⟨hNot,_⟩ | ⟨_,hCase⟩)
    · exact False.elim (hNot rfl)
    · rcases hCase with ⟨_,hParent⟩ | ⟨hCopy0,hLow,_⟩
      · exact hParent
      · exact False.elim (hHigh.elim hCopy0 (fun h => h hLow))
  · intro hParent
    exact Or.inr ⟨rfl,Or.inl ⟨hHigh,hParent⟩⟩

theorem CopyForest.root_low_parent_iff_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {X : CopyCoordinates.Context M.Domain} (hX : X.Valid M C) {P row maximal count width Q copy prev child : M.Domain}
    (hQ : CopyForest M C T X P row maximal count width Q) (hCount : M.mem count C.omega) (hCopy : M.mem copy count)
    (hPrev : M.mem prev C.omega) (hSucc : M.SuccessorOf copy prev) (hLow : M.mem row maximal)
    (hPos : CopyPosition M C.omega T.addPairs T.plus T.mulPairs T.times X.root X.length copy C.zero child) :
    ∀ target, MemPair M Q child target ↔ ∃ p, M.mem p X.last ∧ MemPair M P X.last p ∧ CopyCoordinates.ParentCopy M C T X prev p target := by
  have hCopy0 : copy≠C.zero := fun he => hC.zero_empty prev (he ▸ hSucc.predecessor_mem)
  have hSource := (hT.add.add_iff_sum hM hX.root hC.zero_nat).mpr (KP1Y.Arithmetic.sum_zero_d hM X.root hC.zero_empty)
  intro target
  apply (hQ.at_copy_d hM hC hT hX hCount hCopy (hX.length_positive_d hM hC) hX.below hSource hPos target).trans
  constructor
  · rintro (⟨hNot,_⟩ | ⟨_,hCase⟩)
    · exact False.elim (hNot rfl)
    · rcases hCase with ⟨hHigh,_⟩ | ⟨_,_,prev',_,hSucc',p,hp,hParent,hMap⟩
      · exact False.elim (hHigh.elim hCopy0 (fun h => h hLow))
      · have hPrevEq := Structure.SuccessorOf.predecessor_eq hM.1 ((omega_isOrdinal_d hM hC.omega).mem hPrev) hSucc hSucc'
        subst prev'
        exact ⟨p,hp,hParent,hMap⟩
  · rintro ⟨p,hp,hParent,hMap⟩
    exact Or.inr ⟨rfl,Or.inr ⟨hCopy0,hLow,prev,hPrev,hSucc,p,hp,hParent,hMap⟩⟩

theorem CopyForest.parent_prefix_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {X : CopyCoordinates.Context M.Domain} (hX : X.Valid M C) {m P row maximal count width Q : M.Domain}
    (hP : Forest M C.omega m P) (hQ : CopyForest M C T X P row maximal count width Q)
    (hCount : M.mem count C.omega) (hZeroCount : M.mem C.zero count) : RowsAgreeOn M P Q X.last := by
  intro c hc target
  classical
  by_cases hGood : M.mem c X.root
  · exact (hQ.good_parent_iff_d hM hC hT hX hGood).symm
  · have hw := omega_isOrdinal_d hM hC.omega
    have hcNat := hw.transitive X.last hX.last c hc
    have hAfter : X.root=c ∨ M.mem X.root c := by
      rcases hw.wellOrder.linear.compare X.root hX.root c hcNat with he | hlt | hgt
      · exact Or.inl (hM.1.eq_of_same_members X.root c he)
      · exact Or.inr hlt
      · exact False.elim (hGood hgt)
    obtain ⟨oneProduct,_,hOne⟩ := natural_product_exists_d hM hC hC.one_nat (hX.length_nat hM.1)
    have hOneEq := natural_product_one_left_d hM hC (hX.length_nat hM.1) hOne
    subst oneProduct
    obtain ⟨copy,hCopy,slot,hSlot,hPos⟩ := copy_interval_coverage_d hM hC hT.add hT.mul hX.root (hX.length_nat hM.1)
      hC.one_nat hOne (hX.root_add_length_d hM hC) hc hAfter
    have hCopyEq : copy=C.zero := by
      rcases (hC.one_succ copy).mp hCopy with he | he
      · exact False.elim (hC.zero_empty copy he)
      · exact hM.1.eq_of_same_members copy C.zero he
    subst copy
    have hSource := (copy_position_zero_iff_d hM hC hT hX.root (hX.length_nat hM.1)).mp hPos
    by_cases hSlot0 : slot=C.zero
    · subst slot
      have hcRoot := ((hT.add.add_iff_sum hM hX.root hC.zero_nat).mp hSource).zero_value_d hM hC.zero_empty
      subst c
      exact (hQ.root_high_parent_iff_d hM hC hT hX hCount hZeroCount (Or.inl rfl) hPos target).symm
    · have hAt := hQ.nonroot_parent_iff_d hM hC hT hX hCount hZeroCount hSlot hSlot0 hc hSource hPos target
      refine (hAt.trans ?_).symm
      constructor
      · rintro ⟨p,_,hParent,hMap⟩
        have hMap0 := CopyCoordinates.parent_copy_zero_d hM hC hT hX hMap.1
        have hTarget := parent_copy_unique_d hM hC hT hX hMap hMap0
        exact hTarget.symm ▸ hParent
      · intro hParent
        have hpLast := (hw.mem hX.last).transitive c hc target (hP.left c target hParent)
        exact ⟨target,hpLast,hParent,CopyCoordinates.parent_copy_zero_d hM hC hT hX (hw.transitive X.last hX.last target hpLast)⟩

/-- 任意非root源列的直接父行都按同一parentCopy运输，包含好部源列。 -/
theorem CopyForest.source_parent_nonroot_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {X : CopyCoordinates.Context M.Domain} (hX : X.Valid M C) {m P row maximal count width Q copy source child : M.Domain}
    (hP : Forest M C.omega m P) (hQ : CopyForest M C T X P row maximal count width Q)
    (hCount : M.mem count C.omega) (hCopy : M.mem copy count) (hSource : M.mem source X.last) (hNonroot : source≠X.root)
    (hImage : CopyCoordinates.ParentCopy M C T X copy source child) :
    ∀ target, MemPair M Q child target ↔ ∃ p, M.mem p X.last ∧ MemPair M P source p ∧ CopyCoordinates.ParentCopy M C T X copy p target := by
  have hw := omega_isOrdinal_d hM hC.omega
  have hCopyNat := hw.transitive count hCount copy hCopy
  have hSourceNat := hw.transitive X.last hX.last source hSource
  classical
  by_cases hGood : M.mem source X.root
  · have hChildSource := (CopyCoordinates.parent_copy_good_iff hCopyNat hSourceNat hGood).mp hImage
    subst child
    intro target
    apply (hQ.good_parent_iff_d hM hC hT hX hGood).trans
    constructor
    · intro hParent
      have hpSource := hP.left source target hParent
      have hpLast := (hw.mem hX.last).transitive source hSource target hpSource
      have hpRoot := (hw.mem hX.root).transitive source hGood target hpSource
      exact ⟨target,hpLast,hParent,(CopyCoordinates.parent_copy_good_iff hCopyNat (hw.transitive X.last hX.last target hpLast) hpRoot).mpr rfl⟩
    · rintro ⟨p,hp,hParent,hMap⟩
      have hpRoot := (hw.mem hX.root).transitive source hGood p (hP.left source p hParent)
      have hTarget := (CopyCoordinates.parent_copy_good_iff hCopyNat (hw.transitive X.last hX.last p hp) hpRoot).mp hMap
      exact hTarget.symm ▸ hParent
  · have hRootSource : M.mem X.root source := by
      rcases hw.wellOrder.linear.compare X.root hX.root source hSourceNat with he | hlt | hgt
      · exact False.elim (hNonroot (hM.1.eq_of_same_members X.root source he).symm)
      · exact hlt
      · exact False.elim (hGood hgt)
    have hEncode := (CopyCoordinates.parent_copy_bad_iff hGood).mp hImage
    obtain ⟨slot,hSlot,hSlotPos,hSlotSource,hPos⟩ := CopyCoordinates.encode_nonseam_bms_d hM hC hT hX hRootSource hSource hEncode
    have hSlot0 : slot≠C.zero := fun he => hC.zero_empty C.zero (he ▸ hSlotPos)
    exact hQ.nonroot_parent_iff_d hM hC hT hX hCount hCopy hSlot hSlot0 hSource hSlotSource hPos

/-- 高行对所有源列（含root）的同副本父运输。 -/
theorem CopyForest.source_parent_high_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {X : CopyCoordinates.Context M.Domain} (hX : X.Valid M C) {m P row maximal count width Q copy source child : M.Domain}
    (hP : Forest M C.omega m P) (hQ : CopyForest M C T X P row maximal count width Q)
    (hCount : M.mem count C.omega) (hCopy : M.mem copy count) (hSource : M.mem source X.last) (hHigh : ¬M.mem row maximal)
    (hImage : CopyCoordinates.ParentCopy M C T X copy source child) :
    ∀ target, MemPair M Q child target ↔ ∃ p, M.mem p X.last ∧ MemPair M P source p ∧ CopyCoordinates.ParentCopy M C T X copy p target := by
  classical
  by_cases hNonroot : source≠X.root
  · exact hQ.source_parent_nonroot_d hM hC hT hX hP hCount hCopy hSource hNonroot hImage
  · have hSourceRoot : source=X.root := Classical.byContradiction hNonroot
    subst source
    have hw := omega_isOrdinal_d hM hC.omega
    have hCopyNat := hw.transitive count hCount copy hCopy
    have hEncode := (CopyCoordinates.parent_copy_bad_iff (SetTheory.KP.mem_irrefl_d (KP1Y.models_weakKP hM) X.root)).mp hImage
    have hRootZero := (hT.add.add_iff_sum hM hX.root hC.zero_nat).mpr (KP1Y.Arithmetic.sum_zero_d hM X.root hC.zero_empty)
    have hPos := (CopyCoordinates.encode_at_base_iff_d hM hC hT hX.root hC.zero_nat hCopyNat hRootZero).mp hEncode
    intro target
    apply (hQ.root_high_parent_iff_d hM hC hT hX hCount hCopy (Or.inr hHigh) hPos target).trans
    constructor
    · intro hParent
      have hpRoot := hP.left X.root target hParent
      have hpLast := (hw.mem hX.last).transitive X.root hX.below target hpRoot
      exact ⟨target,hpLast,hParent,(CopyCoordinates.parent_copy_good_iff hCopyNat (hw.transitive X.last hX.last target hpLast) hpRoot).mpr rfl⟩
    · rintro ⟨p,hp,hParent,hMap⟩
      have hpRoot := hP.left X.root p hParent
      have hTarget := (CopyCoordinates.parent_copy_good_iff hCopyNat (hw.transitive X.last hX.last p hp) hpRoot).mp hMap
      exact hTarget.symm ▸ hParent

theorem CopyForest.copy_value_bound_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {X : CopyCoordinates.Context M.Domain} (hX : X.Valid M C) {P row maximal count width Q copy source target : M.Domain}
    (hQ : CopyForest M C T X P row maximal count width Q) (hCopy : M.mem copy count) (hSource : M.mem source X.last)
    (hMap : CopyCoordinates.ParentCopy M C T X copy source target) : M.mem target width := by
  obtain ⟨total,hTotal,hWidth⟩ := hQ.width_geometry
  have hw := omega_isOrdinal_d hM hC.omega
  have hCopyNat := hw.transitive count hQ.count_nat copy hCopy
  have hSourceNat := hw.transitive X.last hX.last source hSource
  have hL := hX.length_nat hM.1
  classical
  by_cases hGood : M.mem source X.root
  · have ht := (CopyCoordinates.parent_copy_good_iff hCopyNat hSourceNat hGood).mp hMap
    exact ht.symm ▸ KP1Y.Arithmetic.sum_base_subset_d hM (hw.mem hX.root) hWidth source hGood
  · have hEncode := (CopyCoordinates.parent_copy_bad_iff hGood).mp hMap
    by_cases hSourceRoot : source=X.root
    · subst source
      have hSourceAdd := (hT.add.add_iff_sum hM hX.root hC.zero_nat).mpr (KP1Y.Arithmetic.sum_zero_d hM X.root hC.zero_empty)
      have hPos := (CopyCoordinates.encode_at_base_iff_d hM hC hT hX.root hC.zero_nat hCopyNat hSourceAdd).mp hEncode
      exact copy_position_bounded_d hM hC hT.add hT.mul hX.root hL hQ.count_nat hTotal hWidth hCopy (hX.length_positive_d hM hC) hPos
    · have hRootSource : M.mem X.root source := by
        rcases hw.wellOrder.linear.compare X.root hX.root source hSourceNat with he | hlt | hgt
        · exact False.elim (hSourceRoot (hM.1.eq_of_same_members X.root source he).symm)
        · exact hlt
        · exact False.elim (hGood hgt)
      obtain ⟨slot,hSlot,_,_,hPos⟩ := CopyCoordinates.encode_nonseam_bms_d hM hC hT hX hRootSource hSource hEncode
      exact copy_position_bounded_d hM hC hT.add hT.mul hX.root hL hQ.count_nat hTotal hWidth hCopy hSlot hPos

theorem CopyForest.copy_embedding_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {X : CopyCoordinates.Context M.Domain} (hX : X.Valid M C) {P row maximal count width Q copy : M.Domain}
    (hQ : CopyForest M C T X P row maximal count width Q) (hCopy : M.mem copy count) :
    ∃ J, ColumnEmbedding M X.last width J ∧ ∀ p target, MemPair M J p target ↔
      M.mem p X.last ∧ CopyCoordinates.ParentCopy M C T X copy p target := by
  have hw := omega_isOrdinal_d hM hC.omega
  obtain ⟨Global,hGlobal,hGlobalRows⟩ := CopyCoordinates.parent_copy_graph_exists_d hM hC hT hX
    (hw.transitive count hQ.count_nat copy hCopy)
  obtain ⟨J,hJ,hRaw⟩ := restrict_graph_d hM hGlobal.graph (hw.transitive X.last hX.last)
  have hRows (p target : M.Domain) : MemPair M J p target ↔ M.mem p X.last ∧ CopyCoordinates.ParentCopy M C T X copy p target := by
    rw [hRaw p target,hGlobalRows p target]
  have hBounded := KP1Y.Assignments.graph_tighten_values hJ (by
    intro p target hAt
    obtain ⟨hp,hMap⟩ := (hRows p target).mp hAt
    exact hQ.copy_value_bound_d hM hC hT hX hCopy hp hMap)
  refine ⟨J,⟨hBounded,?_⟩,hRows⟩
  intro a ha c hc hac x y hax hcy
  exact hGlobal.strict a (hw.transitive X.last hX.last a ha) c (hw.transitive X.last hX.last c hc) hac x y
    ((hRaw a x).mp hax).2 ((hRaw c y).mp hcy).2

/-- 高行的同副本祖先对应使用局部父行双模拟，目标可以含其他所有副本。 -/
theorem CopyForest.ancestor_high_iff_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {X : CopyCoordinates.Context M.Domain} (hX : X.Valid M C) {m P row maximal count width Q copy a c x y : M.Domain}
    (hP : Forest M C.omega m P) (hQ : CopyForest M C T X P row maximal count width Q)
    (hLast : M.mem X.last m) (hCopy : M.mem copy count) (hHigh : ¬M.mem row maximal)
    (ha : M.mem a X.last) (hc : M.mem c X.last)
    (hax : CopyCoordinates.ParentCopy M C T X copy a x) (hcy : CopyCoordinates.ParentCopy M C T X copy c y) :
    Ancestor M C width Q x y ↔ Ancestor M C m P a c := by
  obtain ⟨J,hJ,hJRows⟩ := hQ.copy_embedding_d hM hC hT hX hCopy
  obtain ⟨P0,hP0,hPRows⟩ := hP.restrict_d hM hC.omega hX.last
  have hCorr : ParentCorrespondence M X.last P0 Q J := by
    intro source child hMap target
    obtain ⟨hSource,hImage⟩ := (hJRows source child).mp hMap
    apply (hQ.source_parent_high_d hM hC hT hX hP hQ.count_nat hCopy hSource hHigh hImage target).trans
    constructor
    · rintro ⟨p,hp,hParent,hParentCopy⟩
      exact ⟨p,hp,(hPRows source hSource p).mp hParent,(hJRows p target).mpr ⟨hp,hParentCopy⟩⟩
    · rintro ⟨p,hp,hParent,hParentCopy⟩
      exact ⟨p,hp,(hPRows source hSource p).mpr hParent,((hJRows p target).mp hParentCopy).2⟩
  have hToSmall := ancestor_correspondence_iff_d hM hC hP0 hQ.forest.width hJ hCorr
    ((hJRows a x).mpr ⟨ha,hax⟩) ((hJRows c y).mpr ⟨hc,hcy⟩)
  have hSub := ((omega_isOrdinal_d hM hC.omega).mem hP.width).transitive X.last hLast
  exact hToSmall.trans (ancestor_prefix_iff_d hM hC hP hX.last hSub hc hPRows).symm

private def eraseRowSchema : Project.Delta0BinarySchema 2 where
  body := .conj (memPairFormula (.bound 3) (.bound 1) (.bound 0)) (.neg (Project.Formula.extensionalEq (.bound 1) (.bound 2)))
  freeClosed := by
    simp [memPairFormula,codeFormula,pairFormula,Project.Formula.forallMem,Project.Formula.existsMem,Definitional.Formula.FreeClosed]
  delta0 := .conj (memPairFormula_delta0 _ _ _) (.neg (.atom _ _ _))

private theorem erase_parent_row_exists_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {w m P : M.Domain} (hP : Forest M w m P) (root : M.Domain) :
    ∃ E, Forest M w m E ∧ ∀ c p, MemPair M E c p ↔ MemPair M P c p ∧ c≠root := by
  have hφ (c p : M.Domain) : Project.Formula.satisfies ((((oneEnv P).push root).push c).push p) eraseRowSchema.body ↔
      MemPair M P c p ∧ c≠root := by
    simp only [eraseRowSchema,Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_neg_iff,
      Project.Formula.satisfies_extensionalEq_iff_eq hM.1,memPairFormula_iff hM.1]
    rfl
  obtain ⟨E,hSupport,hRaw⟩ := relation_comprehension_d hM eraseRowSchema ((oneEnv P).push root) m m
  have hRows (c p : M.Domain) : MemPair M E c p ↔ MemPair M P c p ∧ c≠root := by
    rw [hRaw c p,hφ]
    exact ⟨fun h => h.2.2,fun h => ⟨(hP.bounds hM.1 h.1).1,(hP.bounds hM.1 h.1).2,h⟩⟩
  exact ⟨E,⟨hP.width,hSupport,fun c p q hp hq => hP.unique c p q ((hRows c p).mp hp).1 ((hRows c q).mp hq).1,
    fun c p hp => hP.left c p ((hRows c p).mp hp).1⟩,hRows⟩

private theorem ancestor_erase_row_iff_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {m P E root a c : M.Domain}
    (hP : Forest M C.omega m P) (hRows : ∀ c p, MemPair M E c p ↔ MemPair M P c p ∧ c≠root)
    (hRootA : root=a ∨ M.mem root a) : Ancestor M C m E a c ↔ Ancestor M C m P a c := by
  constructor
  · rintro ⟨hac,len,hlen,f,hf,hPath⟩
    exact ⟨hac,len,hlen,f,hf,hPath.length,hPath.graph,hPath.endpoints,
      fun i j x y hi hj hIx hJy hs => ((hRows y x).mp (hPath.edges i j x y hi hj hIx hJy hs)).1⟩
  · rintro ⟨hac,len,hlen,f,hf,hPath⟩
    refine ⟨hac,len,hlen,f,hf,hPath.length,hPath.graph,hPath.endpoints,?_⟩
    intro i j p child hi hj hIp hJc hs
    have hParent := hPath.edges i j p child hi hj hIp hJc hs
    have hAP := hPath.values_above_start_d hM hC hP i p hIp
    have hw := omega_isOrdinal_d hM hC.omega
    have hOrdP := hw.mem (hw.transitive m hP.width p (hP.bounds hM.1 hParent).2)
    have hRootP : root=p ∨ M.mem root p := by
      rcases hAP with he | hap
      · exact he ▸ hRootA
      · rcases hRootA with he | hra
        · exact Or.inr (he.symm ▸ hap)
        · exact Or.inr (hOrdP.transitive a hap root hra)
    apply (hRows child p).mpr
    refine ⟨hParent,?_⟩
    intro he
    subst child
    rcases hRootP with he | hrp
    · exact SetTheory.KP.mem_irrefl_d (KP1Y.models_weakKP hM) p (he ▸ hP.left root p hParent)
    · exact SetTheory.KP.mem_irrefl_d (KP1Y.models_weakKP hM) p (hOrdP.transitive root hrp p (hP.left root p hParent))

/-- 同副本内的坏部祖先对应在低行也成立：删去根的出边不影响从根或其右侧开始的路径。 -/
theorem CopyForest.ancestor_bad_iff_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {X : CopyCoordinates.Context M.Domain} (hX : X.Valid M C) {m P row maximal count width Q copy a c x y : M.Domain}
    (hP : Forest M C.omega m P) (hQ : CopyForest M C T X P row maximal count width Q)
    (hLast : M.mem X.last m) (hCopy : M.mem copy count) (hRootA : X.root=a ∨ M.mem X.root a)
    (ha : M.mem a X.last) (hc : M.mem c X.last)
    (hax : CopyCoordinates.ParentCopy M C T X copy a x) (hcy : CopyCoordinates.ParentCopy M C T X copy c y) :
    Ancestor M C width Q x y ↔ Ancestor M C m P a c := by
  obtain ⟨J,hJ,hJRows⟩ := hQ.copy_embedding_d hM hC hT hX hCopy
  have hJA := (hJRows a x).mpr ⟨ha,hax⟩
  have hJC := (hJRows c y).mpr ⟨hc,hcy⟩
  obtain ⟨z,_,hRootZ⟩ := hJ.graph.total X.root hX.below
  have hZX : z=x ∨ M.mem z x := by
    rcases hRootA with he | hra
    · subst a
      exact Or.inl (hJ.graph.unique X.root z x hRootZ hJA)
    · exact Or.inr (hJ.strict X.root hX.below a ha hra z x hRootZ hJA)
  obtain ⟨P0,hP0,hPRows⟩ := hP.restrict_d hM hC.omega hX.last
  obtain ⟨PE,hPE,hPERows⟩ := erase_parent_row_exists_d hM hP0 X.root
  obtain ⟨QE,_,hQERows⟩ := erase_parent_row_exists_d hM hQ.forest z
  have hCorr : ParentCorrespondence M X.last PE QE J := by
    intro source child hMap target
    obtain ⟨hSource,hImage⟩ := (hJRows source child).mp hMap
    classical
    by_cases hSourceRoot : source=X.root
    · subst source
      have hChild := hJ.graph.unique X.root child z hMap hRootZ
      subst child
      apply iff_of_false
      · intro hAt
        exact ((hQERows z target).mp hAt).2 rfl
      · rintro ⟨p,_,hAt,_⟩
        exact ((hPERows X.root p).mp hAt).2 rfl
    · have hChildZ : child≠z := by
        intro he
        exact hSourceRoot (hJ.injective_d hM hC.omega hX.last hMap (he.symm ▸ hRootZ))
      have hAt := hQ.source_parent_nonroot_d hM hC hT hX hP hQ.count_nat hCopy hSource hSourceRoot hImage target
      constructor
      · intro hErase
        obtain ⟨p,hp,hParent,hParentCopy⟩ := hAt.mp ((hQERows child target).mp hErase).1
        exact ⟨p,hp,(hPERows source p).mpr ⟨(hPRows source hSource p).mp hParent,hSourceRoot⟩,
          (hJRows p target).mpr ⟨hp,hParentCopy⟩⟩
      · rintro ⟨p,hp,hParent,hParentCopy⟩
        exact (hQERows child target).mpr ⟨hAt.mpr ⟨p,hp,(hPRows source hSource p).mpr ((hPERows source p).mp hParent).1,
          ((hJRows p target).mp hParentCopy).2⟩,hChildZ⟩
  have hTarget := (ancestor_erase_row_iff_d hM hC (c := y) hQ.forest hQERows hZX).symm
  have hMapAnc := ancestor_correspondence_iff_d hM hC hPE hQ.forest.width hJ hCorr hJA hJC
  have hSource := ancestor_erase_row_iff_d hM hC (c := c) hP0 hPERows hRootA
  have hSub := ((omega_isOrdinal_d hM hC.omega).mem hP.width).transitive X.last hLast
  exact hTarget.trans (hMapAnc.trans (hSource.trans (ancestor_prefix_iff_d hM hC hP hX.last hSub hc hPRows).symm))

private theorem ancestor_at_mapped_row_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {X : CopyCoordinates.Context M.Domain} (hX : X.Valid M C) {m P row maximal count width Q copy a x source child : M.Domain}
    (hP : Forest M C.omega m P) (hQ : CopyForest M C T X P row maximal count width Q)
    (hCopy : M.mem copy count) (ha : M.mem a X.last)
    (hAnchor : CopyCoordinates.ParentCopy M C T X copy a x)
    (hParentBound : ∀ p, MemPair M P source p → M.mem p X.last)
    (hRows : ∀ t, MemPair M Q child t ↔ ∃ p, M.mem p X.last ∧ MemPair M P source p ∧
      CopyCoordinates.ParentCopy M C T X copy p t)
    (hIH : ∀ p t, M.mem p X.last → MemPair M Q child t → CopyCoordinates.ParentCopy M C T X copy p t →
      (Ancestor M C width Q x t ↔ Ancestor M C m P a p)) :
    Ancestor M C width Q x child ↔ Ancestor M C m P a source := by
  obtain ⟨J,hJ,hJRows⟩ := hQ.copy_embedding_d hM hC hT hX hCopy
  have hJA := (hJRows a x).mpr ⟨ha,hAnchor⟩
  have hEquality (p t : M.Domain) (hp : M.mem p X.last) (hMap : CopyCoordinates.ParentCopy M C T X copy p t) : x=t ↔ a=p := by
    have hJP := (hJRows p t).mpr ⟨hp,hMap⟩
    constructor
    · intro he
      exact hJ.injective_d hM hC.omega hX.last (he ▸ hJA) hJP
    · intro he
      subst p
      exact hJ.graph.unique a x t hJA hJP
  constructor
  · intro hAnc
    obtain ⟨t,hParent,hBefore⟩ := ancestor_parent_cases_d hM hC hQ.forest hAnc
    obtain ⟨p,hp,hSourceParent,hMap⟩ := (hRows t).mp hParent
    rcases hBefore with he | hAnc
    · have hEq := (hEquality p t hp hMap).mp he
      exact hEq.symm ▸ ancestor_direct_d hM hC hP hSourceParent
    · exact ancestor_step_d hM hC hP ((hIH p t hp hParent hMap).mp hAnc) hSourceParent
  · intro hAnc
    obtain ⟨p,hParent,hBefore⟩ := ancestor_parent_cases_d hM hC hP hAnc
    have hp := hParentBound p hParent
    obtain ⟨t,_,hMap⟩ := hJ.graph.total p hp
    have hCopyP := ((hJRows p t).mp hMap).2
    have hTargetParent := (hRows t).mpr ⟨p,hp,hParent,hCopyP⟩
    rcases hBefore with he | hAnc
    · have hEq := (hEquality p t hp hCopyP).mpr he
      exact hEq.symm ▸ ancestor_direct_d hM hC hQ.forest hTargetParent
    · exact ancestor_step_d hM hC hQ.forest ((hIH p t hp hTargetParent hCopyP).mpr hAnc) hTargetParent

private theorem ancestor_at_copied_row_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {X : CopyCoordinates.Context M.Domain} (hX : X.Valid M C) {m P row maximal count width Q copy a source child : M.Domain}
    (hP : Forest M C.omega m P) (hQ : CopyForest M C T X P row maximal count width Q)
    (hCopy : M.mem copy count) (hGood : M.mem a X.root)
    (hParentBound : ∀ p, MemPair M P source p → M.mem p X.last)
    (hRows : ∀ t, MemPair M Q child t ↔ ∃ p, M.mem p X.last ∧ MemPair M P source p ∧
      CopyCoordinates.ParentCopy M C T X copy p t)
    (hIH : ∀ p t, M.mem p X.last → MemPair M Q child t → CopyCoordinates.ParentCopy M C T X copy p t →
      (Ancestor M C width Q a t ↔ Ancestor M C m P a p)) :
    Ancestor M C width Q a child ↔ Ancestor M C m P a source := by
  have hw := omega_isOrdinal_d hM hC.omega
  have ha := (hw.mem hX.last).transitive X.root hX.below a hGood
  exact ancestor_at_mapped_row_d hM hC hT hX hP hQ hCopy ha
    ((CopyCoordinates.parent_copy_good_iff (hw.transitive count hQ.count_nat copy hCopy)
      (hw.transitive X.last hX.last a ha) hGood).mpr rfl) hParentBound hRows hIH

private def goodAncestorEnv {M : SetTheory.Structure.{u}} (C : ExpressionData M.Domain) (T : MatrixArithmetic M.Domain)
    (X : CopyCoordinates.Context M.Domain) (m P count width Q a : M.Domain) : Env M 21 :=
  ((((((((((((((((((((oneEnv C.omega).push C.zero).push C.one).push C.sequences).push C.expressions).push T.addPairs).push T.plus).push T.mulPairs).push T.times).push T.diffPairs).push T.difference).push X.last).push X.root).push X.length).push X.first).push m).push P).push count).push width).push Q).push a

private def goodAncestorSchema : Project.UnarySchema 21 where
  body := .forallE (.forallE (.imp
    (.conj (.mem (.bound 1) (.bound 6)) (.conj (.mem (.bound 0) (.bound 12))
      (CopyCoordinates.parentCopyFormula ⟨.bound 23,.bound 22,.bound 21,.bound 20,.bound 19⟩
        ⟨.bound 18,.bound 17,.bound 16,.bound 15,.bound 14,.bound 13⟩ ⟨.bound 12,.bound 11,.bound 10,.bound 9⟩
        (.bound 1) (.bound 0) (.bound 2))))
    (.iff (ancestorFormula ⟨.bound 23,.bound 22,.bound 21,.bound 20,.bound 19⟩ (.bound 5) (.bound 4) (.bound 3) (.bound 2))
      (ancestorFormula ⟨.bound 23,.bound 22,.bound 21,.bound 20,.bound 19⟩ (.bound 8) (.bound 7) (.bound 3) (.bound 0)))))
  freeClosed := by
    have hC : (⟨.bound 23,.bound 22,.bound 21,.bound 20,.bound 19⟩ : ExpressionData (Project.Term 24)).Closed := ⟨rfl,rfl,rfl,rfl,rfl⟩
    have hT : CopyCoordinates.ArithmeticClosed (⟨.bound 18,.bound 17,.bound 16,.bound 15,.bound 14,.bound 13⟩ : MatrixArithmetic (Project.Term 24)) := ⟨rfl,rfl,rfl,rfl,rfl,rfl⟩
    have hX : (⟨.bound 12,.bound 11,.bound 10,.bound 9⟩ : CopyCoordinates.Context (Project.Term 24)).Closed := ⟨rfl,rfl,rfl,rfl⟩
    have hMap := CopyCoordinates.parentCopyFormula_freeClosed hC hT hX (.bound 1) (.bound 0) (.bound 2) rfl rfl rfl
    have hA := ancestorFormula_freeClosed hC (.bound 5) (.bound 4) (.bound 3) (.bound 2) rfl rfl rfl rfl
    have hB := ancestorFormula_freeClosed hC (.bound 8) (.bound 7) (.bound 3) (.bound 0) rfl rfl rfl rfl
    simp [Definitional.Formula.FreeClosed,hMap,hA,hB]

private theorem goodAncestorSchema_iff {M : SetTheory.Structure.{u}} (he : Extensional M)
    (C : ExpressionData M.Domain) (T : MatrixArithmetic M.Domain) (X : CopyCoordinates.Context M.Domain)
    (m P count width Q a child : M.Domain) :
    Project.Formula.satisfies ((goodAncestorEnv C T X m P count width Q a).push child) goodAncestorSchema.body ↔
      ∀ copy source, M.mem copy count → M.mem source X.last → CopyCoordinates.ParentCopy M C T X copy source child →
        (Ancestor M C width Q a child ↔ Ancestor M C m P a source) := by
  simp only [goodAncestorSchema,Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_imp_iff,
    Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_mem_iff,CopyCoordinates.parentCopyFormula_iff he,
    Project.Formula.satisfies_iff_iff,ancestorFormula_iff he,and_imp]
  rfl

/-- 好部祖先可以越过低行接缝；由目标列的一次对象归纳和原root→last链证明。 -/
theorem CopyForest.ancestor_good_iff_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {X : CopyCoordinates.Context M.Domain} (hX : X.Valid M C) {m P row maximal count width Q copy a c y : M.Domain}
    (hP : Forest M C.omega m P) (hQ : CopyForest M C T X P row maximal count width Q)
    (hLast : M.mem X.last m) (hCopy : M.mem copy count) (hGood : M.mem a X.root)
    (hRootLast : M.mem row maximal → Ancestor M C m P X.root X.last)
    (hc : M.mem c X.last) (hcy : CopyCoordinates.ParentCopy M C T X copy c y) :
    Ancestor M C width Q a y ↔ Ancestor M C m P a c := by
  have hw := omega_isOrdinal_d hM hC.omega
  have hLastSub := (hw.mem hP.width).transitive X.last hLast
  have hAll := KP1Y.induction_d hM goodAncestorSchema (goodAncestorEnv C T X m P count width Q a) (by
    intro child ih
    apply (goodAncestorSchema_iff hM.1 C T X m P count width Q a child).mpr
    intro b source hb hSource hMap
    have hbNat := hw.transitive count hQ.count_nat b hb
    have hRecursive (b' p t : M.Domain) (hb' : M.mem b' count) (hp : M.mem p X.last)
        (hParent : MemPair M Q child t) (hMap' : CopyCoordinates.ParentCopy M C T X b' p t) :
        Ancestor M C width Q a t ↔ Ancestor M C m P a p :=
      (goodAncestorSchema_iff hM.1 C T X m P count width Q a t).mp (ih t (hQ.forest.left child t hParent)) b' p hb' hp hMap'
    classical
    by_cases hNonroot : source≠X.root
    · exact ancestor_at_copied_row_d hM hC hT hX hP hQ hb hGood
        (fun p hParent => (hw.mem hX.last).transitive source hSource p (hP.left source p hParent))
        (hQ.source_parent_nonroot_d hM hC hT hX hP hQ.count_nat hb hSource hNonroot hMap)
        (fun p t hp hParent hMap' => hRecursive b p t hb hp hParent hMap')
    · have hSourceRoot : source=X.root := Classical.byContradiction hNonroot
      subst source
      have hEncode := (CopyCoordinates.parent_copy_bad_iff (SetTheory.KP.mem_irrefl_d (KP1Y.models_weakKP hM) X.root)).mp hMap
      have hRootZero := (hT.add.add_iff_sum hM hX.root hC.zero_nat).mpr (KP1Y.Arithmetic.sum_zero_d hM X.root hC.zero_empty)
      have hPos := (CopyCoordinates.encode_at_base_iff_d hM hC hT hX.root hC.zero_nat hbNat hRootZero).mp hEncode
      by_cases hHigh : b=C.zero ∨ ¬M.mem row maximal
      · have hRows (t : M.Domain) : MemPair M Q child t ↔ ∃ p, M.mem p X.last ∧ MemPair M P X.root p ∧ CopyCoordinates.ParentCopy M C T X b p t := by
          apply (hQ.root_high_parent_iff_d hM hC hT hX hQ.count_nat hb hHigh hPos t).trans
          constructor
          · intro hParent
            have hpRoot := hP.left X.root t hParent
            have hp := (hw.mem hX.last).transitive X.root hX.below t hpRoot
            exact ⟨t,hp,hParent,(CopyCoordinates.parent_copy_good_iff hbNat (hw.transitive X.last hX.last t hp) hpRoot).mpr rfl⟩
          · rintro ⟨p,hp,hParent,hImage⟩
            have hpRoot := hP.left X.root p hParent
            have he := (CopyCoordinates.parent_copy_good_iff hbNat (hw.transitive X.last hX.last p hp) hpRoot).mp hImage
            exact he.symm ▸ hParent
        exact ancestor_at_copied_row_d hM hC hT hX hP hQ hb hGood
          (fun p hParent => (hw.mem hX.last).transitive X.root hX.below p (hP.left X.root p hParent)) hRows
          (fun p t hp hParent hMap' => hRecursive b p t hb hp hParent hMap')
      · have hLow : M.mem row maximal := Classical.byContradiction (fun h => hHigh (Or.inr h))
        have hb0 : b≠C.zero := fun h => hHigh (Or.inl h)
        obtain ⟨prev,hPrev,hs⟩ : ∃ prev, M.mem prev C.omega ∧ M.SuccessorOf b prev := by
          rcases natural_cases hM hC.omega hbNat with he | hs
          · exact False.elim (hb0 (hM.1.eq_of_same_members b C.zero (fun t => ⟨fun ht => False.elim (he t ht),fun ht => False.elim (hC.zero_empty t ht)⟩)))
          · exact hs
        have hPrevCount := (hw.mem hQ.count_nat).transitive b hb prev hs.predecessor_mem
        have hToLast := ancestor_at_copied_row_d hM hC hT hX hP hQ hPrevCount hGood
          (fun p hParent => hP.left X.last p hParent)
          (hQ.root_low_parent_iff_d hM hC hT hX hQ.count_nat hb hPrev hs hLow hPos)
          (fun p t hp hParent hMap' => hRecursive prev p t hPrevCount hp hParent hMap')
        apply hToLast.trans
        exact ⟨fun hAnc => ancestor_between_d hM hC hP hAnc (hRootLast hLow) hGood,
          fun hAnc => ancestor_trans_d hM hC hP hAnc (hRootLast hLow)⟩)
  exact (goodAncestorSchema_iff hM.1 C T X m P count width Q a y).mp (hAll y) copy c hCopy hc hcy

/-- 同副本祖先对应：好部和坏部均从实际候选父图导出。 -/
theorem CopyForest.ancestor_copy_iff_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {X : CopyCoordinates.Context M.Domain} (hX : X.Valid M C) {m P row maximal count width Q copy a c x y : M.Domain}
    (hP : Forest M C.omega m P) (hQ : CopyForest M C T X P row maximal count width Q)
    (hLast : M.mem X.last m) (hCopy : M.mem copy count)
    (hRootLast : M.mem row maximal → Ancestor M C m P X.root X.last)
    (ha : M.mem a X.last) (hc : M.mem c X.last)
    (hax : CopyCoordinates.ParentCopy M C T X copy a x) (hcy : CopyCoordinates.ParentCopy M C T X copy c y) :
    Ancestor M C width Q x y ↔ Ancestor M C m P a c := by
  have hw := omega_isOrdinal_d hM hC.omega
  classical
  by_cases hGood : M.mem a X.root
  · have hEq := (CopyCoordinates.parent_copy_good_iff (hw.transitive count hQ.count_nat copy hCopy)
      (hw.transitive X.last hX.last a ha) hGood).mp hax
    subst x
    exact hQ.ancestor_good_iff_d hM hC hT hX hP hLast hCopy hGood hRootLast hc hcy
  · have hAfter : X.root=a ∨ M.mem X.root a := by
      rcases hw.wellOrder.linear.compare X.root hX.root a (hw.transitive X.last hX.last a ha) with he | hlt | hgt
      · exact Or.inl (hM.1.eq_of_same_members X.root a he)
      · exact Or.inr hlt
      · exact False.elim (hGood hgt)
    exact hQ.ancestor_bad_iff_d hM hC hT hX hP hLast hCopy hAfter ha hc hax hcy

/-- 前副本坏部到下一根的祖先关系，精确等于源列到原last的祖先关系。 -/
theorem CopyForest.ancestor_previous_root_iff_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {X : CopyCoordinates.Context M.Domain} (hX : X.Valid M C) {m P row maximal count width Q prev next a x y : M.Domain}
    (hP : Forest M C.omega m P) (hQ : CopyForest M C T X P row maximal count width Q)
    (hLast : M.mem X.last m) (hNext : M.mem next count) (hPrev : M.mem prev C.omega)
    (hs : M.SuccessorOf next prev) (hLow : M.mem row maximal)
    (hAfter : X.root=a ∨ M.mem X.root a) (ha : M.mem a X.last)
    (hax : CopyCoordinates.ParentCopy M C T X prev a x)
    (hPos : CopyPosition M C.omega T.addPairs T.plus T.mulPairs T.times X.root X.length next C.zero y) :
    Ancestor M C width Q x y ↔ Ancestor M C m P a X.last := by
  have hPrevCount := ((omega_isOrdinal_d hM hC.omega).mem hQ.count_nat).transitive next hNext prev hs.predecessor_mem
  exact ancestor_at_mapped_row_d hM hC hT hX hP hQ hPrevCount ha hax
    (fun p hParent => hP.left X.last p hParent)
    (hQ.root_low_parent_iff_d hM hC hT hX hQ.count_nat hNext hPrev hs hLow hPos)
    (fun p t hp _ hMap => hQ.ancestor_bad_iff_d hM hC hT hX hP hLast hPrevCount hAfter ha hp hax hMap)

private def originEnv {M : SetTheory.Structure.{u}} (C : ExpressionData M.Domain)
    (m P n Q J root z : M.Domain) : Env M 12 :=
  (((((((((((oneEnv C.omega).push C.zero).push C.one).push C.sequences).push C.expressions).push m).push P).push n).push Q).push J).push root).push z

private def originSchema : Project.UnarySchema 12 where
  body := .forallE (.forallE (.imp
    (.conj (memPairFormula (.bound 5) (.bound 2) (.bound 1))
      (ancestorFormula ⟨.bound 14,.bound 13,.bound 12,.bound 11,.bound 10⟩ (.bound 7) (.bound 6) (.bound 0) (.bound 1)))
    (.disj (Project.Formula.existsMem (.bound 9)
      (.conj (memPairFormula (.bound 6) (.bound 0) (.bound 1))
        (ancestorFormula ⟨.bound 15,.bound 14,.bound 13,.bound 12,.bound 11⟩ (.bound 10) (.bound 9) (.bound 0) (.bound 3))))
      (.conj (.disj (Project.Formula.extensionalEq (.bound 0) (.bound 3))
        (ancestorFormula ⟨.bound 14,.bound 13,.bound 12,.bound 11,.bound 10⟩ (.bound 7) (.bound 6) (.bound 0) (.bound 3)))
        (.disj (Project.Formula.extensionalEq (.bound 2) (.bound 4))
          (ancestorFormula ⟨.bound 14,.bound 13,.bound 12,.bound 11,.bound 10⟩ (.bound 9) (.bound 8) (.bound 4) (.bound 2)))))))
  freeClosed := by
    have hC : (⟨.bound 14,.bound 13,.bound 12,.bound 11,.bound 10⟩ : ExpressionData (Project.Term 15)).Closed := ⟨rfl,rfl,rfl,rfl,rfl⟩
    have hC' : (⟨.bound 15,.bound 14,.bound 13,.bound 12,.bound 11⟩ : ExpressionData (Project.Term 16)).Closed := ⟨rfl,rfl,rfl,rfl,rfl⟩
    have hA := ancestorFormula_freeClosed hC (.bound 7) (.bound 6) (.bound 0) (.bound 1) rfl rfl rfl rfl
    have hB := ancestorFormula_freeClosed hC' (.bound 10) (.bound 9) (.bound 0) (.bound 3) rfl rfl rfl rfl
    have hD := ancestorFormula_freeClosed hC (.bound 7) (.bound 6) (.bound 0) (.bound 3) rfl rfl rfl rfl
    have hE := ancestorFormula_freeClosed hC (.bound 9) (.bound 8) (.bound 4) (.bound 2) rfl rfl rfl rfl
    simp [Definitional.Formula.FreeClosed,Project.Formula.existsMem,memPairFormula,codeFormula,pairFormula,
      Project.Formula.forallMem,hA,hB,hD,hE]

private theorem originSchema_iff {M : SetTheory.Structure.{u}} (he : Extensional M)
    (C : ExpressionData M.Domain) (m P n Q J root z source : M.Domain) :
    Project.Formula.satisfies ((originEnv C m P n Q J root z).push source) originSchema.body ↔
      ∀ child x, MemPair M J source child → Ancestor M C n Q x child →
        (∃ a, M.mem a m ∧ MemPair M J a x ∧ Ancestor M C m P a source) ∨
        ((x=z ∨ Ancestor M C n Q x z) ∧ (source=root ∨ Ancestor M C m P root source)) := by
  simp only [originSchema,Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_imp_iff,
    Project.Formula.satisfies_conj_iff,memPairFormula_iff he,ancestorFormula_iff he,
    Project.Formula.satisfies_existsMem_iff,Project.Formula.satisfies_disj_iff,
    Project.Formula.satisfies_extensionalEq_iff_eq he,and_imp]
  rfl

private theorem ancestor_origin_or_root_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {m P n Q J root z source child x : M.Domain}
    (hP : Forest M C.omega m P) (hQ : Forest M C.omega n Q) (hJ : ColumnEmbedding M m n J)
    (hRoot : MemPair M J root z)
    (hRows : ∀ source child, source≠root → MemPair M J source child → ∀ t,
      MemPair M Q child t ↔ ∃ p, M.mem p m ∧ MemPair M P source p ∧ MemPair M J p t)
    (hMap : MemPair M J source child) (hAnc : Ancestor M C n Q x child) :
    (∃ a, M.mem a m ∧ MemPair M J a x ∧ Ancestor M C m P a source) ∨
      ((x=z ∨ Ancestor M C n Q x z) ∧ (source=root ∨ Ancestor M C m P root source)) := by
  have hAll := KP1Y.induction_d hM originSchema (originEnv C m P n Q J root z) (by
    intro source ih
    apply (originSchema_iff hM.1 C m P n Q J root z source).mpr
    intro child x hMap hAnc
    classical
    by_cases he : source=root
    · subst source
      have hChild := hJ.graph.unique root child z hMap hRoot
      subst child
      exact Or.inr ⟨Or.inr hAnc,Or.inl rfl⟩
    · obtain ⟨t,hTarget,hBefore⟩ := ancestor_parent_cases_d hM hC hQ hAnc
      obtain ⟨p,hp,hSource,hMapP⟩ := (hRows source child he hMap t).mp hTarget
      rcases hBefore with hEq | hBefore
      · exact Or.inl ⟨p,hp,hEq.symm ▸ hMapP,ancestor_direct_d hM hC hP hSource⟩
      · rcases (originSchema_iff hM.1 C m P n Q J root z p).mp (ih p (hP.left source p hSource)) t x hMapP hBefore with
          ⟨a,ha,hMapA,hAS⟩ | ⟨hToRoot,hFromRoot⟩
        · exact Or.inl ⟨a,ha,hMapA,ancestor_step_d hM hC hP hAS hSource⟩
        · apply Or.inr
          refine ⟨hToRoot,Or.inr ?_⟩
          rcases hFromRoot with hEq | hFromRoot
          · subst p
            exact ancestor_direct_d hM hC hP hSource
          · exact ancestor_step_d hM hC hP hFromRoot hSource)
  exact (originSchema_iff hM.1 C m P n Q J root z source).mp (hAll source) child x hMap hAnc

/-- 任意祖先来自同副本，或经过该副本根；由真实非根父行逐边追溯。 -/
theorem CopyForest.ancestor_origin_or_root_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {X : CopyCoordinates.Context M.Domain} (hX : X.Valid M C) {m P row maximal count width Q copy source child x z : M.Domain}
    (hP : Forest M C.omega m P) (hQ : CopyForest M C T X P row maximal count width Q)
    (hLast : M.mem X.last m) (hCopy : M.mem copy count) (hSource : M.mem source X.last)
    (hMap : CopyCoordinates.ParentCopy M C T X copy source child)
    (hRootMap : CopyCoordinates.ParentCopy M C T X copy X.root z)
    (hAnc : Ancestor M C width Q x child) :
    (∃ a, M.mem a X.last ∧ CopyCoordinates.ParentCopy M C T X copy a x ∧ Ancestor M C m P a source) ∨
      ((x=z ∨ Ancestor M C width Q x z) ∧ (source=X.root ∨ Ancestor M C m P X.root source)) := by
  obtain ⟨J,hJ,hJRows⟩ := hQ.copy_embedding_d hM hC hT hX hCopy
  obtain ⟨P0,hP0,hPRows⟩ := hP.restrict_d hM hC.omega hX.last
  have hRows : ∀ s c, s≠X.root → MemPair M J s c → ∀ t,
      MemPair M Q c t ↔ ∃ p, M.mem p X.last ∧ MemPair M P0 s p ∧ MemPair M J p t := by
    intro s c hNot hMap t
    obtain ⟨hs,hImage⟩ := (hJRows s c).mp hMap
    apply (hQ.source_parent_nonroot_d hM hC hT hX hP hQ.count_nat hCopy hs hNot hImage t).trans
    constructor
    · rintro ⟨p,hp,hParent,hImageP⟩
      exact ⟨p,hp,(hPRows s hs p).mp hParent,(hJRows p t).mpr ⟨hp,hImageP⟩⟩
    · rintro ⟨p,hp,hParent,hImageP⟩
      exact ⟨p,hp,(hPRows s hs p).mpr hParent,((hJRows p t).mp hImageP).2⟩
  have hCases := MatrixCopy.ancestor_origin_or_root_d hM hC hP0 hQ.forest hJ
    ((hJRows X.root z).mpr ⟨hX.below,hRootMap⟩) hRows ((hJRows source child).mpr ⟨hSource,hMap⟩) hAnc
  have hSub := ((omega_isOrdinal_d hM hC.omega).mem hP.width).transitive X.last hLast
  have hBack (a : M.Domain) := (ancestor_prefix_iff_d hM hC hP hX.last hSub (a := a) hSource hPRows).symm
  rcases hCases with ⟨a,ha,hImageA,hAS⟩ | ⟨hToRoot,hFromRoot⟩
  · exact Or.inl ⟨a,ha,((hJRows a x).mp hImageA).2,(hBack a).mp hAS⟩
  · exact Or.inr ⟨hToRoot,hFromRoot.imp id (fun h => (hBack X.root).mp h)⟩

/-- 副本图像之外的祖先必须且只需经过该副本根。 -/
theorem CopyForest.ancestor_outside_copy_iff_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {X : CopyCoordinates.Context M.Domain} (hX : X.Valid M C) {m P row maximal count width Q copy source child x z : M.Domain}
    (hP : Forest M C.omega m P) (hQ : CopyForest M C T X P row maximal count width Q)
    (hLast : M.mem X.last m) (hCopy : M.mem copy count) (hSource : M.mem source X.last)
    (hMap : CopyCoordinates.ParentCopy M C T X copy source child)
    (hRootMap : CopyCoordinates.ParentCopy M C T X copy X.root z)
    (hOutside : ∀ a, M.mem a X.last → ¬CopyCoordinates.ParentCopy M C T X copy a x) :
    Ancestor M C width Q x child ↔
      Ancestor M C width Q x z ∧ (source=X.root ∨ Ancestor M C m P X.root source) := by
  constructor
  · intro hAnc
    rcases hQ.ancestor_origin_or_root_d hM hC hT hX hP hLast hCopy hSource hMap hRootMap hAnc with
        ⟨a,ha,hImage,_⟩ | ⟨hToRoot,hFromRoot⟩
    · exact False.elim (hOutside a ha hImage)
    · refine ⟨?_,hFromRoot⟩
      rcases hToRoot with he | hToRoot
      · exact False.elim (hOutside X.root hX.below (he.symm ▸ hRootMap))
      · exact hToRoot
  · rintro ⟨hToRoot,hFromRoot⟩
    rcases hFromRoot with he | hFromRoot
    · subst source
      have hEq := parent_copy_unique_d hM hC hT hX hMap hRootMap
      exact hEq.symm ▸ hToRoot
    · have hRootTarget := (hQ.ancestor_bad_iff_d hM hC hT hX hP hLast hCopy (Or.inl rfl)
        hX.below hSource hRootMap hMap).mpr hFromRoot
      exact ancestor_trans_d hM hC hQ.forest hToRoot hRootTarget

end KP1Y.OneYFinite.MatrixCopy
