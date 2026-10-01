import KP1Y.OneYTerminalCopy
import KP1Y.OneYLowerCopy
import KP1Y.OneYForestEmbedding
import KP1Y.OneYActiveFrameTransport

/-! 真实数值山形的低行根严格次序，以及活跃复制的父/根运输。 -/
namespace KP1Y.OneYFinite.CopiedMountain.Terminal
open YesMetaZFC YesMetaZFC.SetTheory YesMetaZFC.SetTheory.Definitional
open KP1Y.Kuratowski KP1Y.Functions KP1Y.Naturals KP1Y.Bounded
open KP1Y.Arithmetic
open KP1Y.OneYFinite.CopyCoordinates
open KP1Y.OneYFinite.CopiedMountain.Lower (RootAt)
universe u

/-- 在同一真实数值山形中，活跃高度以内的根随行号严格增加。 -/
theorem root_at_strict_rows_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {m : M.Domain} {R : RowStateSpace M.Domain}
    {V P H : M.Domain} {X : Data M.Domain} (hX : X.Valid M C)
    (hRun : RowRun M C m R V P H) (hFrom : FromRun M C m R V H X)
    (hPositive : ∀ c v, MemPair M V c v → M.mem C.zero v)
    {r d c height qLow qHigh : M.Domain} (hRD : M.mem r d)
    (hHeight : MemPair M X.heights c height) (hDHeight : d=height ∨ M.mem d height)
    (hLow : RootAt M C X r c qLow) (hHigh : RootAt M C X d c qHigh) : M.mem qLow qHigh := by
  obtain ⟨lowHeight,_,hLowHeight⟩ := hX.heights.total qLow (hLow.bounds hM.1 hX).2.1
  obtain ⟨highHeight,_,hHighHeight⟩ := hX.heights.total qHigh (hHigh.bounds hM.1 hX).2.1
  obtain ⟨F,_,hF,hRootF⟩ := hLow
  obtain ⟨G,_,hG,hRootG⟩ := hHigh
  obtain ⟨U,hRowF⟩ := (hFrom.parents r F).mp hF
  obtain ⟨W,hRowG⟩ := (hFrom.parents d G).mp hG
  have hRF : Root M C m F c qLow := hFrom.width ▸ hRootF
  have hRG : Root M C m G c qHigh := hFrom.width ▸ hRootG
  have hRHeight : r=height ∨ M.mem r height := by
    rcases hDHeight with he | hlt
    · exact .inr (he ▸ hRD)
    · exact .inr (((omega_isOrdinal_d hM hC.omega).mem (hX.heights.bounds hM.1 hHeight).2).transitive d hlt r hRD)
  have hLowEq := hFrom.heights.root_height_d hM hC hRun hPositive hRowF hRF hHeight hLowHeight hRHeight
  have hHighEq := hFrom.heights.root_height_d hM hC hRun hPositive hRowG hRG hHeight hHighHeight hDHeight
  have hThrough := (hRun.root_through_higher_d hM hC hRowF hRowG (.inr hRD) hRG).mp hRF
  rcases hThrough.2.2 with he | hAnc
  · have hHeightsEq := hX.heights.unique qHigh lowHeight highHeight (he ▸ hLowHeight) hHighHeight
    have hRD' := hLowEq.symm.trans (hHeightsEq.trans hHighEq)
    exact False.elim (SetTheory.KP.mem_irrefl_d (KP1Y.models_weakKP hM) d (hRD' ▸ hRD))
  · exact hAnc.1

theorem root_at_parent_iff_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {X : Data M.Domain} (hX : X.Valid M C)
    {r c p q : M.Domain} (hParent : ParentAt M X r c p) :
    RootAt M C X r c q ↔ RootAt M C X r p q := by
  obtain ⟨F,hF,hRow,hCP⟩ := hParent
  have hAt (a : M.Domain) : RootAt M C X r a q ↔ Root M C X.width F a q := by
    constructor
    · rintro ⟨G,_,hG,hRoot⟩
      have hGF := hX.parents.unique r G F hG hRow
      exact hGF ▸ hRoot
    · intro hRoot
      exact ⟨F,hF,hRow,hRoot⟩
  rw [hAt c,hAt p]
  exact root_parent_iff_d hM hC (hX.forest r F hRow) hCP

/-- 原控制根位于坏根左侧或等于坏根。 -/
theorem Active.control_le_root_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {A : Context M.Domain} {X : Data M.Domain} (hX : X.Valid M C)
    {level q : M.Domain} (hActive : Active M X A level) (hRoot : RootAt M C X level A.last q) :
    q=A.root ∨ M.mem q A.root :=
  ((root_at_parent_iff_d hM hC hX hActive.parent).mp hRoot).bounds hM.1 hX |>.2.2.2

/-- 低行末列根严格小于真实控制根，因此处于复制的固定前缀。 -/
theorem Active.low_root_lt_control_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {m : M.Domain} {R : RowStateSpace M.Domain}
    {V P H : M.Domain} {X : Data M.Domain} (hX : X.Valid M C)
    (hRun : RowRun M C m R V P H) (hFrom : FromRun M C m R V H X)
    (hPositive : ∀ c v, MemPair M V c v → M.mem C.zero v)
    {A : Context M.Domain} {level r qLow qControl : M.Domain}
    (hActive : Active M X A level) (hR : M.mem r level)
    (hLow : RootAt M C X r A.last qLow) (hControl : RootAt M C X level A.last qControl) :
    M.mem qLow qControl ∧ M.mem qLow A.root := by
  obtain ⟨height,hHeight,hSucc⟩ := hActive.lastHeight
  have hStrict := root_at_strict_rows_d hM hC hX hRun hFrom hPositive hR hHeight (.inr hSucc.predecessor_mem) hLow hControl
  refine ⟨hStrict,?_⟩
  rcases hActive.control_le_root_d hM hC hX hControl with he | hlt
  · exact he ▸ hStrict
  · have hRootNat := (omega_isOrdinal_d hM hC.omega).transitive X.width hX.width A.root
      (hActive.parent.bounds hM.1 hX).2.2.1
    exact ((omega_isOrdinal_d hM hC.omega).mem hRootNat).transitive qControl hlt qLow hStrict

theorem low_seam_parent_iff_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {A : Context M.Domain} (hA : A.Valid M C) {X Y : Data M.Domain}
    {level n r b boundary target : M.Domain} (hCopy : Copies M C T A X level n Y)
    (hWidth : Width M C T A b boundary) (hBoundary : M.mem boundary n)
    (hLevel : M.mem level C.omega) (hLow : M.mem r level) :
    ParentAt M Y r boundary target ↔ MappedParent M C T A X b r A.last target := by
  have hW := hWidth
  obtain ⟨_,_,off,hOff,_,hAdd⟩ := hW
  have hBoundaryNat := (hAdd.bounds hM.1 hT.add).2.2
  have hNot : ¬M.mem boundary A.last := by
    intro hlt
    exact SetTheory.KP.mem_irrefl_d (KP1Y.models_weakKP hM) boundary
      (sum_base_subset_d hM ((omega_isOrdinal_d hM hC.omega).mem hA.last)
        ((hT.add.add_iff_sum hM hA.last hOff).mp hAdd) boundary hlt)
  have hNoHigh : ¬HighSeam M A.last level r A.last := by
    rintro ⟨_,he | hgt⟩
    · exact SetTheory.KP.mem_irrefl_d (KP1Y.models_weakKP hM) level (he.symm ▸ hLow)
    · exact SetTheory.KP.mem_irrefl_d (KP1Y.models_weakKP hM) level
        (((omega_isOrdinal_d hM hC.omega).mem hLevel).transitive r hLow level hgt)
  rw [hCopy.parents]
  exact ⟨fun h => (parent_raw_low_iff_d hM hC hT hA hBoundaryNat hNot
      (seam_decodes_d hM hC hT hA hWidth) hNoHigh).mp h.2,
    fun h => ⟨hBoundary,(parent_raw_low_iff_d hM hC hT hA hBoundaryNat hNot
      (seam_decodes_d hM hC hT hA hWidth) hNoHigh).mpr h⟩⟩

theorem root_at_lt_of_parent_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {X : Data M.Domain} (hX : X.Valid M C)
    {r c p q : M.Domain} (hParent : ParentAt M X r c p) (hRoot : RootAt M C X r c q) : M.mem q c := by
  have hP := (hParent.bounds hM.1 hX).2.2.2
  rcases ((root_at_parent_iff_d hM hC hX hParent).mp hRoot).bounds hM.1 hX |>.2.2.2 with he | hlt
  · exact he.symm ▸ hP
  · have hc := (omega_isOrdinal_d hM hC.omega).transitive X.width hX.width c (hParent.bounds hM.1 hX).2.1
    exact ((omega_isOrdinal_d hM hC.omega).mem hc).transitive p hP q hlt

private def rootCopyCore {d : Nat} (C : ExpressionData (Project.Term d)) (T : MatrixArithmetic (Project.Term d))
    (A : Context (Project.Term d)) (X Y : Data (Project.Term d)) (r c : Project.Term d) : Project.Formula 1 d :=
  .imp (.mem c Y.width) (Project.Formula.forallMem A.last (Project.Formula.forallMem C.omega.weaken
    (Project.Formula.forallMem X.width.weaken.weaken (Project.Formula.forallMem Y.width.weaken.weaken.weaken
      (.imp (.conj (parentCopyFormula C.weaken.weaken.weaken.weaken T.weaken.weaken.weaken.weaken A.weaken.weaken.weaken.weaken
          (.bound 2) (.bound 3) c.weaken.weaken.weaken.weaken)
        (.conj (Lower.rootAtFormula C.weaken.weaken.weaken.weaken X.weaken.weaken.weaken.weaken r.weaken.weaken.weaken.weaken (.bound 3) (.bound 1))
          (parentCopyFormula C.weaken.weaken.weaken.weaken T.weaken.weaken.weaken.weaken A.weaken.weaken.weaken.weaken (.bound 2) (.bound 1) (.bound 0))))
        (Lower.rootAtFormula C.weaken.weaken.weaken.weaken Y.weaken.weaken.weaken.weaken r.weaken.weaken.weaken.weaken c.weaken.weaken.weaken.weaken (.bound 0)))))))

private theorem rootCopyCore_freeClosed {d : Nat} {C : ExpressionData (Project.Term d)} (hC : C.Closed)
    {T : MatrixArithmetic (Project.Term d)} (hT : ArithmeticClosed T) {A : Context (Project.Term d)} (hA : A.Closed)
    {X Y : Data (Project.Term d)} (hX : X.Closed) (hY : Y.Closed) (r c : Project.Term d)
    (hr : r.freeSupport=[]) (hc : c.freeSupport=[]) : (rootCopyCore C T A X Y r c).FreeClosed := by
  have hPC := parentCopyFormula_freeClosed hC.weaken.weaken.weaken.weaken hT.weaken.weaken.weaken.weaken hA.weaken.weaken.weaken.weaken
    (.bound 2) (.bound 3) c.weaken.weaken.weaken.weaken rfl rfl (by simpa using hc)
  have hPQ := parentCopyFormula_freeClosed hC.weaken.weaken.weaken.weaken hT.weaken.weaken.weaken.weaken hA.weaken.weaken.weaken.weaken
    (.bound 2) (.bound 1) (.bound 0) rfl rfl rfl
  have hRX := Lower.rootAtFormula_freeClosed hC.weaken.weaken.weaken.weaken hX.weaken.weaken.weaken.weaken
    r.weaken.weaken.weaken.weaken (.bound 3) (.bound 1) (by simpa using hr) rfl rfl
  have hRY := Lower.rootAtFormula_freeClosed hC.weaken.weaken.weaken.weaken hY.weaken.weaken.weaken.weaken
    r.weaken.weaken.weaken.weaken c.weaken.weaken.weaken.weaken (.bound 0) (by simpa using hr) (by simpa using hc) rfl
  simp [rootCopyCore,Project.Formula.forallMem,Definitional.Formula.FreeClosed,hC.omega,hA.last,hX.width,hY.width,hc,hPC,hPQ,hRX,hRY]

private def rootCopySchema : Project.UnarySchema 24 where
  body := rootCopyCore ⟨.bound 24,.bound 23,.bound 22,.bound 21,.bound 20⟩
    ⟨.bound 19,.bound 18,.bound 17,.bound 16,.bound 15,.bound 14⟩ ⟨.bound 13,.bound 12,.bound 11,.bound 10⟩
    ⟨.bound 9,.bound 8,.bound 7,.bound 6⟩ ⟨.bound 5,.bound 4,.bound 3,.bound 2⟩ (.bound 1) (.bound 0)
  freeClosed := rootCopyCore_freeClosed ⟨rfl,rfl,rfl,rfl,rfl⟩ ⟨rfl,rfl,rfl,rfl,rfl,rfl⟩
    ⟨rfl,rfl,rfl,rfl⟩ ⟨rfl,rfl,rfl,rfl⟩ ⟨rfl,rfl,rfl,rfl⟩ _ _ rfl rfl

private def rootCopyEnv {M : SetTheory.Structure.{u}} (C : ExpressionData M.Domain) (T : MatrixArithmetic M.Domain)
    (A : Context M.Domain) (X Y : Data M.Domain) (r : M.Domain) : Env M 24 :=
  (((((((((((((((((((((((oneEnv C.omega).push C.zero).push C.one).push C.sequences).push C.expressions).push T.addPairs).push T.plus).push T.mulPairs).push T.times).push T.diffPairs).push T.difference).push A.last).push A.root).push A.length).push A.first).push X.width).push X.heights).push X.forests).push X.parents).push Y.width).push Y.heights).push Y.forests).push Y.parents).push r

private theorem rootCopySchema_iff {M : SetTheory.Structure.{u}} (he : Extensional M)
    (C : ExpressionData M.Domain) (T : MatrixArithmetic M.Domain) (A : Context M.Domain) (X Y : Data M.Domain) (r c : M.Domain) :
    Project.Formula.satisfies ((rootCopyEnv C T A X Y r).push c) rootCopySchema.body ↔
      (M.mem c Y.width → ∀ s, M.mem s A.last → ∀ b, M.mem b C.omega → ∀ q, M.mem q X.width → ∀ z, M.mem z Y.width →
        ParentCopy M C T A b s c ∧ RootAt M C X r s q ∧ ParentCopy M C T A b q z → RootAt M C Y r c z) := by
  simp only [rootCopySchema,rootCopyCore,Project.Formula.satisfies_forallMem_iff,Project.Formula.satisfies_imp_iff,
    Project.Formula.satisfies_mem_iff,Project.Formula.satisfies_conj_iff,parentCopyFormula_iff he,Lower.rootAtFormula_iff he,
    ExpressionData.eval_weaken,MatrixArithmetic.eval_weaken,Context.eval_weaken,Data.eval_weaken,Term.eval_weaken]
  rfl

/-- 低行复制根精确沿ParentCopy运输；跨seam的额外路径由对象列归纳处理。 -/
theorem Copies.low_root_parent_copy_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {A : Context M.Domain} (hA : A.Valid M C) {X Y : Data M.Domain} (hX : X.Valid M C) (hY : Y.Valid M C)
    {m : M.Domain} {R : RowStateSpace M.Domain} {V P H : M.Domain}
    (hRun : RowRun M C m R V P H) (hFrom : FromRun M C m R V H X)
    {level n r b s c q z : M.Domain} (hActive : Active M X A level) (hCopy : Copies M C T A X level n Y)
    (hLow : M.mem r level) (hSource : M.mem s A.last) (hChild : M.mem c Y.width)
    (hMap : ParentCopy M C T A b s c) (hRoot : RootAt M C X r s q) (hMapRoot : ParentCopy M C T A b q z) :
    RootAt M C Y r c z := by
  have hw := omega_isOrdinal_d hM hC.omega
  have hLevel := (hActive.parent.bounds hM.1 hX).1
  have hr := hw.transitive level hLevel r hLow
  have hLast := (hActive.parent.bounds hM.1 hX).2.1
  have hCoherent := Lower.from_run_coherent_d hM hC hRun hFrom
  have hAll := KP1Y.ordinal_induction_d hM rootCopySchema (rootCopyEnv C T A X Y r) (by
    intro child _ ih
    apply (rootCopySchema_iff hM.1 C T A X Y r child).mpr
    intro hChild source hSource block hBlock oldRoot hOldRoot newRoot hNewRoot hAnte
    obtain ⟨hMap,hRoot,hMapRoot⟩ := hAnte
    have hChildN : M.mem child n := hCopy.width ▸ hChild
    have hSourceX := (hw.mem hX.width).transitive A.last hLast source hSource
    obtain ⟨J,hJ,hRows⟩ := parent_copy_graph_exists_d hM hC hT hA hBlock
    have hStep (p block' target : M.Domain) (hpLast : M.mem p A.last)
        (hParent : ParentAt M Y r child target) (hSourceRoot : RootAt M C X r p oldRoot)
        (hMapP : ParentCopy M C T A block' p target) (hMapQ : ParentCopy M C T A block' oldRoot newRoot) :
        RootAt M C Y r child newRoot := by
      have hBounds := hParent.bounds hM.1 hY
      apply (root_at_parent_iff_d hM hC hY hParent).mpr
      exact (rootCopySchema_iff hM.1 C T A X Y r target).mp (ih target hBounds.2.2.2)
        hBounds.2.2.1 p hpLast block' hMapP.2.1 oldRoot hOldRoot newRoot hNewRoot ⟨hMapP,hSourceRoot,hMapQ⟩
    classical
    by_cases hSome : ∃ p, ParentAt M X r source p
    · obtain ⟨p,hP⟩ := hSome
      have hpNat := hw.transitive X.width hX.width p (hP.bounds hM.1 hX).2.2.1
      have hpLast := (hw.mem hA.last).transitive source hSource p (hP.bounds hM.1 hX).2.2.2
      by_cases hIsRoot : source=A.root
      · subst source
        rcases natural_cases hM hC.omega hBlock with hEmpty | ⟨previous,hPrevious,hSucc⟩
        · have hZero := hM.1.eq_of_same_members block C.zero (fun a => ⟨fun h => False.elim (hEmpty a h),fun h => False.elim (hC.zero_empty a h)⟩)
          subst block
          have hChildEq := hJ.graph.unique A.root child A.root ((hRows A.root child).mpr hMap)
            ((hRows A.root A.root).mpr (parent_copy_zero_d hM hC hT hA hA.root))
          have hPMap := parent_copy_zero_d hM hC hT hA hpNat
          have hNewP : ParentAt M Y r child p := (hCopy.parents r child p).mpr
            ⟨hChildN,hChildEq.symm ▸ (parent_original_iff_d hM hC hA hA.below).mpr hP⟩
          exact hStep p C.zero p hpLast hNewP ((root_at_parent_iff_d hM hC hX hP).mp hRoot) hPMap hMapRoot
        · obtain ⟨boundary,_,hWidth⟩ := encode_exists_d hM hC hT hA hA.last hPrevious
          have hBad : ¬M.mem A.root A.root := SetTheory.KP.mem_irrefl_d (KP1Y.models_weakKP hM) A.root
          have hChildEq := encode_unique hM.1 hT ((parent_copy_bad_iff hBad).mp hMap)
            (width_is_next_cut_d hM hC hT hA hSucc hWidth)
          have hWidthChild : Width M C T A previous child := hChildEq.symm ▸ hWidth
          have hRootGood := root_at_lt_of_parent_d hM hC hX hP hRoot
          have hNewEq := (parent_copy_good_iff hBlock hMapRoot.1 hRootGood).mp hMapRoot
          have hPrevMapRoot : ParentCopy M C T A previous oldRoot newRoot :=
            (parent_copy_good_iff hPrevious hMapRoot.1 hRootGood).mpr hNewEq
          have hLastRoot : RootAt M C X r A.last oldRoot :=
            (hCoherent r level A.last A.root oldRoot hr (.inr hLow) hActive.parent).mpr hRoot
          obtain ⟨height,hHeight,hHeightSucc⟩ := hActive.lastHeight
          have hRH := ((hw.mem (hX.heights.bounds hM.1 hHeight).2).transitive level hHeightSucc.predecessor_mem r hLow)
          obtain ⟨pOld,hOldP⟩ := (hX.source r A.last height hHeight).mpr hRH
          have hpOld := hw.transitive X.width hX.width pOld (hOldP.bounds hM.1 hX).2.2.1
          obtain ⟨JPrev,hJPrev,hPrevRows⟩ := parent_copy_graph_exists_d hM hC hT hA hPrevious
          obtain ⟨target,_,hAtTarget⟩ := hJPrev.graph.total pOld hpOld
          have hMapTarget := (hPrevRows pOld target).mp hAtTarget
          have hNewP := (low_seam_parent_iff_d hM hC hT hA hCopy hWidthChild hChildN hLevel hLow).mpr
            ⟨pOld,hpOld,hOldP,hMapTarget⟩
          exact hStep pOld previous target (hOldP.bounds hM.1 hX).2.2.2 hNewP
            ((root_at_parent_iff_d hM hC hX hOldP).mp hLastRoot) hMapTarget hPrevMapRoot
      · obtain ⟨target,_,hAtTarget⟩ := hJ.graph.total p hpNat
        have hMapTarget := (hRows p target).mp hAtTarget
        have hNewP : ParentAt M Y r child target := (hCopy.parents r child target).mpr
          ⟨hChildN,(parent_parent_copy_nonroot_d hM hC hT hA hX hSource hIsRoot hMap).mpr ⟨p,hpNat,hP,hMapTarget⟩⟩
        exact hStep p block target hpLast hNewP ((root_at_parent_iff_d hM hC hX hP).mp hRoot) hMapTarget hMapRoot
    · obtain ⟨F,_,hRow,hRF⟩ := hRoot
      have hNo : NoParent M X.width F source := fun p _ hP => hSome ⟨p,F,(hX.parents.bounds hM.1 hRow).2,hRow,hP⟩
      have hRootEq := root_of_no_parent_d hM hC (hX.forest r F hRow) hNo hRF
      subst oldRoot
      have hTargetEq := hJ.graph.unique source newRoot child ((hRows source newRoot).mpr hMapRoot) ((hRows source child).mpr hMap)
      subst newRoot
      obtain ⟨height,_,hHeight⟩ := hX.heights.total source hSourceX
      have hTargetHeight : MemPair M Y.heights child height := (hCopy.heights child height).mpr
        ⟨hChildN,(height_parent_copy_iff_d hM hC hT hA hSource hMap).mpr hHeight⟩
      obtain ⟨G,hG,hRowG⟩ := hY.parents.total r hr
      refine ⟨G,hG,hRowG,hChild,?_,Or.inl rfl⟩
      intro p _ hP
      have hRH := (hY.source r child height hTargetHeight).mp ⟨p,G,hG,hRowG,hP⟩
      exact hSome ((hX.source r source height hHeight).mpr hRH))
  have hZ : M.mem z Y.width := by
    have hBounds := hRoot.bounds hM.1 hX
    obtain ⟨J,hJ,hRows⟩ := parent_copy_graph_exists_d hM hC hT hA hMap.2.1
    rcases hBounds.2.2.2 with he | hlt
    · have hzc := hJ.graph.unique s z c ((hRows s z).mpr (he ▸ hMapRoot)) ((hRows s c).mpr hMap)
      exact hzc.symm ▸ hChild
    · have hzc := hJ.strict q hMapRoot.1 s hMap.1 hlt z c ((hRows q z).mpr hMapRoot) ((hRows s c).mpr hMap)
      exact (hw.mem hY.width).transitive c hChild z hzc
  exact (rootCopySchema_iff hM.1 C T A X Y r c).mp (hAll c (hw.mem (hw.transitive Y.width hY.width c hChild))) hChild s hSource b hMap.2.1 q
    (hRoot.bounds hM.1 hX).2.1 z hZ ⟨hMap,hRoot,hMapRoot⟩

/-- 虚拟seam低行的根就是原末列低行根，并严格小于真实控制根。 -/
theorem Copies.low_seam_root_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {A : Context M.Domain} (hA : A.Valid M C) {X Y : Data M.Domain} (hX : X.Valid M C) (hY : Y.Valid M C)
    {m : M.Domain} {R : RowStateSpace M.Domain} {V P H : M.Domain}
    (hRun : RowRun M C m R V P H) (hFrom : FromRun M C m R V H X)
    (hPositive : ∀ c v, MemPair M V c v → M.mem C.zero v)
    {level n r b boundary qLow qControl : M.Domain} (hActive : Active M X A level)
    (hCopy : Copies M C T A X level n Y) (hLow : M.mem r level)
    (hWidth : Width M C T A b boundary) (hBoundary : M.mem boundary Y.width)
    (hRoot : RootAt M C X r A.last qLow) (hControl : RootAt M C X level A.last qControl) :
    RootAt M C Y r boundary qLow ∧ M.mem qLow qControl := by
  have hw := omega_isOrdinal_d hM hC.omega
  have hBounds := hActive.low_root_lt_control_d hM hC hX hRun hFrom hPositive hLow hRoot hControl
  have hr := hw.transitive level (hActive.parent.bounds hM.1 hX).1 r hLow
  have hRootRoot := (Lower.from_run_coherent_d hM hC hRun hFrom r level A.last A.root qLow hr (.inr hLow) hActive.parent).mp hRoot
  obtain ⟨next,hSucc,hNext⟩ := hC.omega.1.2 b hWidth.2.1
  have hNot : ¬M.mem A.root A.root := SetTheory.KP.mem_irrefl_d (KP1Y.models_weakKP hM) A.root
  have hMap : ParentCopy M C T A next A.root boundary :=
    (parent_copy_bad_iff hNot).mpr (width_is_next_cut_d hM hC hT hA hSucc hWidth)
  have hQNat := hw.transitive X.width hX.width qLow (hRoot.bounds hM.1 hX).2.1
  have hMapRoot := (parent_copy_good_iff (T := T) hNext hQNat hBounds.2).mpr rfl
  exact ⟨hCopy.low_root_parent_copy_d hM hC hT hA hX hY hRun hFrom hActive hLow hA.below hBoundary hMap hRootRoot hMapRoot,hBounds.1⟩

/-- 真实边界父/根记录的源见证；供CopyNeeds的Virtual/Adm证明消费。 -/
theorem Copies.low_seam_source_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {A : Context M.Domain} (hA : A.Valid M C) {X Y : Data M.Domain} (hX : X.Valid M C) (hY : Y.Valid M C)
    {m : M.Domain} {R : RowStateSpace M.Domain} {V P H : M.Domain}
    (hRun : RowRun M C m R V P H) (hFrom : FromRun M C m R V H X)
    (hPositive : ∀ c v, MemPair M V c v → M.mem C.zero v)
    {level n r b boundary pNew qNew qControl : M.Domain} (hActive : Active M X A level)
    (hCopy : Copies M C T A X level n Y) (hLow : M.mem r level)
    (hWidth : Width M C T A b boundary) (hParent : ParentAt M Y r boundary pNew)
    (hRoot : RootAt M C Y r boundary qNew) (hControl : RootAt M C X level A.last qControl) :
    ∃ pOld, ParentAt M X r A.last pOld ∧ RootAt M C X r A.last qNew ∧
      ParentCopy M C T A b pOld pNew ∧ ParentCopy M C T A b qNew qNew ∧ M.mem qNew qControl := by
  have hBoundary := (hParent.bounds hM.1 hY).2.1
  have hLevel := (hActive.parent.bounds hM.1 hX).1
  obtain ⟨pOld,_,hOldP,hMapP⟩ := (low_seam_parent_iff_d hM hC hT hA hCopy hWidth (hCopy.width ▸ hBoundary) hLevel hLow).mp hParent
  have hr := (omega_isOrdinal_d hM hC.omega).transitive level hLevel r hLow
  obtain ⟨qOld,hOldRoot⟩ := Lower.root_at_exists_d hM hC hX hr (hActive.parent.bounds hM.1 hX).2.1
  obtain ⟨hNewRoot,hStrict⟩ := hCopy.low_seam_root_d hM hC hT hA hX hY hRun hFrom hPositive hActive hLow hWidth hBoundary hOldRoot hControl
  have hEq := hNewRoot.unique_d hM hC hY hRoot
  subst qOld
  have hGood := (hActive.low_root_lt_control_d hM hC hX hRun hFrom hPositive hLow hOldRoot hControl).2
  have hQNat := (omega_isOrdinal_d hM hC.omega).transitive X.width hX.width qNew (hOldRoot.bounds hM.1 hX).2.1
  exact ⟨pOld,hOldP,hOldRoot,hMapP,(parent_copy_good_iff hWidth.2.1 hQNat hGood).mpr rfl,hStrict⟩

end KP1Y.OneYFinite.CopiedMountain.Terminal
