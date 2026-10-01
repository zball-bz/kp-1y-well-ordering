import KP1Y.OneYTerminalCanonical

/-! Terminal复制的伪父Top界：源正值记录界沿真实seam父前像传播。 -/
namespace KP1Y.OneYFinite.TerminalTopBound
open YesMetaZFC YesMetaZFC.SetTheory YesMetaZFC.SetTheory.Definitional
open KP1Y.Kuratowski KP1Y.Functions KP1Y.Naturals KP1Y.Bounded
open CopyCoordinates CopiedMountain
open ReconstructionSelection
universe u

def PositiveBound (M : SetTheory.Structure.{u}) (C : ExpressionData M.Domain) (m F V bound c : M.Domain) : Prop :=
  ∀ q, M.mem q m → (q=c ∨ Ancestor M C m F q c) → ∀ v, MemPair M V q v → M.mem C.zero v → bound=v ∨ M.mem bound v

def positiveBoundFormula {n : Nat} (C : ExpressionData (Project.Term n)) (m F V bound c : Project.Term n) : Project.Formula 1 n :=
  Project.Formula.forallMem m (.imp
    (.disj (Project.Formula.extensionalEq (.bound 0) c.weaken) (ancestorFormula C.weaken m.weaken F.weaken (.bound 0) c.weaken))
      (.forallE (.imp (memPairFormula V.weaken.weaken (.bound 1) (.bound 0))
        (.imp (.mem C.zero.weaken.weaken (.bound 0))
          (.disj (Project.Formula.extensionalEq bound.weaken.weaken (.bound 0)) (.mem bound.weaken.weaken (.bound 0)))))))

theorem positiveBoundFormula_freeClosed {n : Nat} {C : ExpressionData (Project.Term n)} (hC : C.Closed)
    (m F V bound c : Project.Term n) (hm : m.freeSupport=[]) (hF : F.freeSupport=[]) (hV : V.freeSupport=[])
    (hb : bound.freeSupport=[]) (hc : c.freeSupport=[]) : (positiveBoundFormula C m F V bound c).FreeClosed := by
  have hAnc := ancestorFormula_freeClosed hC.weaken m.weaken F.weaken (.bound 0) c.weaken
    (by simpa using hm) (by simpa using hF) rfl (by simpa using hc)
  simp [positiveBoundFormula,memPairFormula,codeFormula,pairFormula,Project.Formula.existsMem,Project.Formula.forallMem,
    Definitional.Formula.FreeClosed,hm,hV,hb,hc,hC.zero,hAnc]

theorem positiveBoundFormula_iff {M : SetTheory.Structure.{u}} (he : Extensional M) {n : Nat} (e : Env M n)
    (C : ExpressionData (Project.Term n)) (m F V bound c : Project.Term n) :
    Project.Formula.satisfies e (positiveBoundFormula C m F V bound c) ↔
      PositiveBound M (C.eval e) (m.eval e) (F.eval e) (V.eval e) (bound.eval e) (c.eval e) := by
  simp only [positiveBoundFormula,PositiveBound,Project.Formula.satisfies_forallMem_iff,Project.Formula.satisfies_imp_iff,
    Project.Formula.satisfies_disj_iff,Project.Formula.satisfies_extensionalEq_iff_eq he,ancestorFormula_iff he,
    Project.Formula.satisfies_forall_iff,memPairFormula_iff he,Project.Formula.satisfies_mem_iff,ExpressionData.eval_weaken,Term.eval_weaken]
  rfl

theorem PositiveBound.of_ancestor_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {m F V bound a c : M.Domain}
    (hF : Forest M C.omega m F) (h : PositiveBound M C m F V bound c) (hAnc : Ancestor M C m F a c) :
    PositiveBound M C m F V bound a := by
  intro q hq hReach v hV hPos
  apply h q hq (Or.inr ?_) v hV hPos
  rcases hReach with he | hQA
  · exact he.symm ▸ hAnc
  · exact ancestor_trans_d hM hC hF hQA hAnc

private theorem le_trans_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {a b c : M.Domain} (hc : M.mem c C.omega)
    (hAB : a=b ∨ M.mem a b) (hBC : b=c ∨ M.mem b c) : a=c ∨ M.mem a c := by
  rcases hAB with he | hlt
  · exact he.symm ▸ hBC
  · rcases hBC with he | hgt
    · exact Or.inr (he ▸ hlt)
    · exact Or.inr (((omega_isOrdinal_d hM hC.omega).mem hc).transitive b hgt a hlt)

theorem positive_bound_splice_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {m F V Q a c bound : M.Domain}
    (hS : Selects true M C m F V Q) (hZeros : NumericOrder.ZerosAtRoots M m F V C.zero)
    (hAnc : Ancestor M C m Q a c) (hSafe : PositiveBound M C m F V bound a) : PositiveBound M C m F V bound c := by
  have hw := omega_isOrdinal_d hM hC.omega
  have hAF := hS.ancestor_inherited_d hM hC hAnc
  obtain ⟨av,hav,hAV⟩ := hS.values.total a (hAnc.bounds hM.1).1
  obtain ⟨z,_,_,hZA⟩ := ancestor_child_above_d hM hC hS.forest hAnc
  obtain ⟨zv,_,hZV⟩ := hS.values.total z (hS.forest.bounds hM.1 hZA).1
  have hAPos := (hS.numeric_row.parentValues z a av zv hZA hAV hZV).1
  have hBA := hSafe a (hAnc.bounds hM.1).1 (Or.inl rfl) av hAV hAPos
  intro q hq hReach v hV hPos
  have hv := (hS.values.bounds hM.1 hV).2
  rcases hReach with he | hQC
  · subst q
    exact le_trans_d hM hC hv hBA (Or.inr (selected_ancestor_positive_lt_d hM hC hS hZeros hAnc hAV hV hAPos hPos))
  · have ha := hw.transitive m hS.forest.width a (hAnc.bounds hM.1).1
    have hqNat := hw.transitive m hS.forest.width q hq
    rcases hw.wellOrder.linear.compare a ha q hqNat with he | haq | hqa
    · have he := hM.1.eq_of_same_members a q he
      subst q
      exact hS.values.unique a av v hAV hV ▸ hBA
    · exact le_trans_d hM hC hv hBA (Or.inr (selected_ancestor_positive_lt_after_d hM hC hS hZeros hAnc hQC haq hAV hV hAPos hPos))
    · exact hSafe q hq (Or.inr (ancestor_between_d hM hC hS.inherited hQC hAF hqa)) v hV hPos

theorem positive_bound_of_no_parent_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {m F V Q c top : M.Domain}
    (hS : Selects true M C m F V Q) (hNo : NoParent M m Q c) (hTop : MemPair M V c top) : PositiveBound M C m F V top c := by
  intro q _ hReach v hV hPos
  rcases hReach with he | hAnc
  · subst q
    exact Or.inl (hS.values.unique c top v hTop hV)
  · have ht := (hS.values.bounds hM.1 hTop).2
    have hv := (hS.values.bounds hM.1 hV).2
    rcases (omega_isOrdinal_d hM hC.omega).wellOrder.linear.compare top ht v hv with he | hlt | hgt
    · exact Or.inl (hM.1.eq_of_same_members top v he)
    · exact Or.inr hlt
    · exact False.elim ((hS.no_parent_iff_d hM hC).mp hNo q ⟨hAnc,v,hv,top,ht,hV,hTop,hgt,hPos⟩)

/-- 每一真实低行父边都回到一个保持源正值界的列；root的后续副本回到前块last。 -/
theorem low_parent_preimage_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {A : Context M.Domain} (hA : A.Valid M C) {X Y : Data M.Domain} (hX : X.Valid M C) (hY : Y.Valid M C)
    {level n r F V bound source block child target : M.Domain}
    (hCopy : Terminal.Copies M C T A X level n Y) (hLevel : M.mem level C.omega) (hLow : M.mem r level)
    (hF : MemPair M X.parents r F)
    (hSplice : PositiveBound M C X.width F V bound A.root → PositiveBound M C X.width F V bound A.last)
    (hSource : M.mem source A.last) (hMap : ParentCopy M C T A block source child)
    (hSafe : PositiveBound M C X.width F V bound source) (hParent : ParentAt M Y r child target) :
    ∃ p b, M.mem p A.last ∧ PositiveBound M C X.width F V bound p ∧ ParentCopy M C T A b p target := by
  have hw := omega_isOrdinal_d hM hC.omega
  have hSourceF := hX.forest r F hF
  have hSafeParent (s p : M.Domain) (hSP : ParentAt M X r s p) (hS : PositiveBound M C X.width F V bound s) :
      PositiveBound M C X.width F V bound p := by
    obtain ⟨F',_,hF',hP⟩ := hSP
    have he := hX.parents.unique r F' F hF' hF
    exact hS.of_ancestor_d hM hC hSourceF (ancestor_direct_d hM hC hSourceF (he ▸ hP))
  classical
  by_cases hRoot : source=A.root
  · subst source
    rcases natural_cases hM hC.omega hMap.2.1 with hEmpty | ⟨previous,hPrevious,hSucc⟩
    · have he0 := hM.1.eq_of_same_members block C.zero (fun a => ⟨fun h => False.elim (hEmpty a h),fun h => False.elim (hC.zero_empty a h)⟩)
      subst block
      have hNot : ¬M.mem A.root A.root := SetTheory.KP.mem_irrefl_d (KP1Y.models_weakKP hM) A.root
      have hChildEq := encode_unique hM.1 hT ((parent_copy_bad_iff hNot).mp hMap) (encode_zero_d hM hC hT hA hA.root)
      subst child
      have hOld := (Terminal.parent_original_iff_d hM hC hA hA.below).mp ((hCopy.parents r A.root target).mp hParent).2
      have hpRoot := (hOld.bounds hM.1 hX).2.2.2
      have hpLast := (hw.mem hA.last).transitive A.root hA.below target hpRoot
      have hpNat := hw.transitive A.last hA.last target hpLast
      exact ⟨target,C.zero,hpLast,hSafeParent A.root target hOld hSafe,parent_copy_zero_d hM hC hT hA hpNat⟩
    · obtain ⟨boundary,_,hWidth⟩ := encode_exists_d hM hC hT hA hA.last hPrevious
      have hNot : ¬M.mem A.root A.root := SetTheory.KP.mem_irrefl_d (KP1Y.models_weakKP hM) A.root
      have hChildEq := encode_unique hM.1 hT ((parent_copy_bad_iff hNot).mp hMap) (width_is_next_cut_d hM hC hT hA hSucc hWidth)
      have hWidthChild : Width M C T A previous child := hChildEq.symm ▸ hWidth
      obtain ⟨p,_,hOld,hMapP⟩ := (Terminal.low_seam_parent_iff_d hM hC hT hA hCopy hWidthChild
        (hCopy.width ▸ (hParent.bounds hM.1 hY).2.1) hLevel hLow).mp hParent
      exact ⟨p,previous,(hOld.bounds hM.1 hX).2.2.2,hSafeParent A.last p hOld (hSplice hSafe),hMapP⟩
  · obtain ⟨p,_,hOld,hMapP⟩ := (Terminal.parent_parent_copy_nonroot_d hM hC hT hA hX hSource hRoot hMap).mp
      ((hCopy.parents r child target).mp hParent).2
    have hpLast := (hw.mem hA.last).transitive source hSource p (hOld.bounds hM.1 hX).2.2.2
    exact ⟨p,block,hpLast,hSafeParent source p hOld hSafe,hMapP⟩

private def copyBoundCore {d : Nat} (C : ExpressionData (Project.Term d)) (T : MatrixArithmetic (Project.Term d))
    (A : Context (Project.Term d)) (m n F Q V NewV bound source block child : Project.Term d) : Project.Formula 1 d :=
  .imp (.mem child n) (.imp (parentCopyFormula C T A block source child)
    (.imp (positiveBoundFormula C m F V bound source) (positiveBoundFormula C n Q NewV bound child)))

private def copyBoundSchema : Project.UnarySchema 22 where
  body := Project.Formula.forallMem (.bound 11) (Project.Formula.forallMem (.bound 23)
    (copyBoundCore ⟨.bound 24,.bound 23,.bound 22,.bound 21,.bound 20⟩
      ⟨.bound 19,.bound 18,.bound 17,.bound 16,.bound 15,.bound 14⟩ ⟨.bound 13,.bound 12,.bound 11,.bound 10⟩
      (.bound 9) (.bound 8) (.bound 7) (.bound 6) (.bound 5) (.bound 4) (.bound 3) (.bound 1) (.bound 0) (.bound 2)))
  freeClosed := by
    have hC : (⟨.bound 24,.bound 23,.bound 22,.bound 21,.bound 20⟩ : ExpressionData (Project.Term 25)).Closed := ⟨rfl,rfl,rfl,rfl,rfl⟩
    have hMap := parentCopyFormula_freeClosed hC (T := ⟨.bound 19,.bound 18,.bound 17,.bound 16,.bound 15,.bound 14⟩)
      ⟨rfl,rfl,rfl,rfl,rfl,rfl⟩ (A := ⟨.bound 13,.bound 12,.bound 11,.bound 10⟩) ⟨rfl,rfl,rfl,rfl⟩
      (.bound 0) (.bound 1) (.bound 2) rfl rfl rfl
    have hOld := positiveBoundFormula_freeClosed hC (.bound 9) (.bound 7) (.bound 5) (.bound 3) (.bound 1) rfl rfl rfl rfl rfl
    have hNew := positiveBoundFormula_freeClosed hC (.bound 8) (.bound 6) (.bound 4) (.bound 3) (.bound 2) rfl rfl rfl rfl rfl
    simp [copyBoundCore,Project.Formula.forallMem,Definitional.Formula.FreeClosed,hMap,hOld,hNew]

private def copyBoundEnv {M : SetTheory.Structure.{u}} (C : ExpressionData M.Domain) (T : MatrixArithmetic M.Domain)
    (A : Context M.Domain) (m n F Q V NewV bound : M.Domain) : Env M 22 :=
  (((((((((((((((((((((oneEnv C.omega).push C.zero).push C.one).push C.sequences).push C.expressions).push T.addPairs).push T.plus).push T.mulPairs).push T.times).push T.diffPairs).push T.difference).push A.last).push A.root).push A.length).push A.first).push m).push n).push F).push Q).push V).push NewV).push bound

private theorem copyBoundSchema_iff {M : SetTheory.Structure.{u}} (he : Extensional M)
    (C : ExpressionData M.Domain) (T : MatrixArithmetic M.Domain) (A : Context M.Domain) (m n F Q V NewV bound child : M.Domain) :
    Project.Formula.satisfies ((copyBoundEnv C T A m n F Q V NewV bound).push child) copyBoundSchema.body ↔
      ∀ source, M.mem source A.last → ∀ block, M.mem block C.omega → M.mem child n →
        ParentCopy M C T A block source child → PositiveBound M C m F V bound source → PositiveBound M C n Q NewV bound child := by
  simp only [copyBoundSchema,copyBoundCore,Project.Formula.satisfies_forallMem_iff,Project.Formula.satisfies_imp_iff,
    Project.Formula.satisfies_mem_iff,parentCopyFormula_iff he,positiveBoundFormula_iff he]
  rfl

/-- 真实父前像接口逐步实例化后，内部列归纳把整个路径的正值界运输到目标。 -/
theorem positive_bound_copy_from_preimages_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {A : Context M.Domain} (hA : A.Valid M C) {m n F Q V NewV bound source block child : M.Domain}
    (_hF : Forest M C.omega m F) (hQ : Forest M C.omega n Q) (hV : Graph M V m C.omega)
    (hTop : CopiedTop M C T A V n NewV)
    (hPreimage : ∀ source block child target, M.mem source A.last → ParentCopy M C T A block source child →
      PositiveBound M C m F V bound source → MemPair M Q child target →
        ∃ p b, M.mem p A.last ∧ PositiveBound M C m F V bound p ∧ ParentCopy M C T A b p target)
    (hSource : M.mem source A.last) (hChild : M.mem child n) (hMap : ParentCopy M C T A block source child)
    (hSafe : PositiveBound M C m F V bound source) : PositiveBound M C n Q NewV bound child := by
  have hAll := KP1Y.induction_d hM copyBoundSchema (copyBoundEnv C T A m n F Q V NewV bound) (by
    intro child ih
    apply (copyBoundSchema_iff hM.1 C T A m n F Q V NewV bound child).mpr
    intro source hSource block _ hChild hMap hSafe q hq hReach v hVNew hPos
    rcases hReach with he | hAnc
    · subst q
      have hOldValue := (hTop.parent_copy_iff_d hM hC hT hA hSource hChild hMap).mp hVNew
      exact hSafe source (hV.bounds hM.1 hOldValue).1 (Or.inl rfl) v hOldValue hPos
    · obtain ⟨target,hParent,hTail⟩ := ancestor_parent_cases_d hM hC hQ hAnc
      obtain ⟨p,b,hp,hSafeP,hMapP⟩ := hPreimage source block child target hSource hMap hSafe hParent
      have hBound := (copyBoundSchema_iff hM.1 C T A m n F Q V NewV bound target).mp (ih target (hQ.left child target hParent))
        p hp b hMapP.2.1 (hQ.bounds hM.1 hParent).2 hMapP hSafeP
      exact hBound q hq hTail v hVNew hPos)
  exact (copyBoundSchema_iff hM.1 C T A m n F Q V NewV bound child).mp (hAll child) source hSource block hMap.2.1 hChild hMap hSafe

theorem positive_bound_copy_low_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {A : Context M.Domain} (hA : A.Valid M C) {X Y : Data M.Domain} (hX : X.Valid M C) (hY : Y.Valid M C)
    {level n r F Q V NewV bound source block child : M.Domain}
    (hCopy : Terminal.Copies M C T A X level n Y) (hLevel : M.mem level C.omega) (hLow : M.mem r level)
    (hF : MemPair M X.parents r F) (hQ : MemPair M Y.parents r Q) (hV : Graph M V X.width C.omega)
    (hTop : CopiedTop M C T A V Y.width NewV)
    (hSplice : PositiveBound M C X.width F V bound A.root → PositiveBound M C X.width F V bound A.last)
    (hSource : M.mem source A.last) (hChild : M.mem child Y.width) (hMap : ParentCopy M C T A block source child)
    (hSafe : PositiveBound M C X.width F V bound source) : PositiveBound M C Y.width Q NewV bound child := by
  apply positive_bound_copy_from_preimages_d hM hC hT hA (hX.forest r F hF) (hY.forest r Q hQ) hV hTop ?_ hSource hChild hMap hSafe
  intro source block child target hSource hMap hSafe hParent
  exact low_parent_preimage_d hM hC hT hA hX hY hCopy hLevel hLow hF hSplice hSource hMap hSafe
    ⟨Q,(hY.parents.bounds hM.1 hQ).2,hQ,hParent⟩

theorem positive_bound_copy_high_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {A : Context M.Domain} (hA : A.Valid M C) {X Y : Data M.Domain} (hX : X.Valid M C) (hY : Y.Valid M C)
    {level n r F Q V NewV bound source block child : M.Domain}
    (hCopy : Terminal.Copies M C T A X level n Y) (hHigh : level=r ∨ M.mem level r)
    (hF : MemPair M X.parents r F) (hQ : MemPair M Y.parents r Q) (hV : Graph M V X.width C.omega)
    (hTop : CopiedTop M C T A V Y.width NewV)
    (hSource : M.mem source A.last) (hChild : M.mem child Y.width) (hMap : ParentCopy M C T A block source child)
    (hSafe : PositiveBound M C X.width F V bound source) : PositiveBound M C Y.width Q NewV bound child := by
  apply positive_bound_copy_from_preimages_d hM hC hT hA (hX.forest r F hF) (hY.forest r Q hQ) hV hTop ?_ hSource hChild hMap hSafe
  intro source block child target hSource hMap hSafe hParent
  have hP : ParentAt M Y r child target := ⟨Q,(hY.parents.bounds hM.1 hQ).2,hQ,hParent⟩
  have hP' := ((hCopy.parents r child target).mp hP).2
  have hcNat := (omega_isOrdinal_d hM hC.omega).transitive Y.width hY.width child ((hY.forest r Q hQ).bounds hM.1 hParent).1
  have hOrd := (Terminal.parent_high_eq_ordinary_d hM hC hT hA hX hcNat hHigh).mp hP'
  obtain ⟨p,_,hOld,hMapP⟩ := (Ordinary.parent_parent_copy_iff_d hM hC hT hA hX hSource hMap).mp hOrd
  obtain ⟨F',_,hF',hOldP⟩ := hOld
  have he := hX.parents.unique r F' F hF' hF
  have hOldF : MemPair M F source p := he ▸ hOldP
  have hpLast := ((omega_isOrdinal_d hM hC.omega).mem hA.last).transitive source hSource p ((hX.forest r F hF).left source p hOldF)
  exact ⟨p,block,hpLast,hSafe.of_ancestor_d hM hC (hX.forest r F hF) (ancestor_direct_d hM hC (hX.forest r F hF) hOldF),hMapP⟩

private theorem row_value_at_d {M : SetTheory.Structure.{u}} (he : Extensional M)
    {C : ExpressionData M.Domain} {m : M.Domain} {R : RowStateSpace M.Domain} {V P H r W Q c v : M.Domain}
    (hRun : RowRun M C m R V P H) (hAt : RowAt M R.states H r W Q)
    (hValue : RowValue M R.states R.values R.forests H r c v) : MemPair M W c v := by
  obtain ⟨W',_,Q',_,hAt',hV⟩ := hValue
  exact (hRun.at_unique he hAt' hAt).1 ▸ hV

private theorem successor_le_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {r s k : M.Domain} (hr : M.mem r C.omega)
    (hk : M.mem k C.omega) (hSucc : M.SuccessorOf s r) (hrk : M.mem r k) : s=k ∨ M.mem s k := by
  have hw := omega_isOrdinal_d hM hC.omega
  apply ordinal_subset_cases_d hM (hw.mem (natural_successor_mem_d hM hC hr hSucc)) (hw.mem hk)
  intro x hx
  rcases (hSucc x).mp hx with hxr | he
  · exact (hw.mem hk).transitive r hrk x hxr
  · exact (hM.1.eq_of_same_members x r he).symm ▸ hrk

/-- 实际源数值山形与实际普通Top复制给出Terminal伪父Top界，不保留splice或正值界假设。 -/
theorem terminal_pseudo_top_bound_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {A : Context M.Domain} (hA : A.Valid M C) {X Y : Data M.Domain} (hX : X.Valid M C) (hY : Y.Valid M C)
    {m : M.Domain} {R : RowStateSpace M.Domain} {V P H OldTop : M.Domain}
    (hRun : RowRun M C m R V P H) (hFrom : FromRun M C m R V H X)
    (hPositive : ∀ c v, MemPair M V c v → M.mem C.zero v)
    (hOldTop : TopValueGraph M C m R H X.heights OldTop) {level n NewTop : M.Domain}
    (hActive : Terminal.Active M X A level) (hCopy : Terminal.Copies M C T A X level n Y)
    (hTop : CopiedTop M C T A OldTop Y.width NewTop) : ReconstructionSelection.PseudoTopBound M C Y NewTop := by
  intro c p height tc tp hPseudo hHC hHP hTC hTP
  have hw := omega_isOrdinal_d hM hC.omega
  obtain ⟨height',_,hp,_,r,hr,hHC',hHP',hSucc,Q,_,hQ,hAnc,_⟩ := hPseudo.1
  have hHe := hY.heights.unique c height' height hHC' hHC
  subst height'
  have hs := (hY.heights.bounds hM.1 hHC).2
  obtain ⟨Vr,F,hAtR⟩ := hRun.at_exists_d hr
  obtain ⟨Vs,G,hAtS⟩ := hRun.at_exists_d hs
  have hNumericR := hRun.at_numeric_d hM hC hAtR
  have hNumericS := hRun.at_numeric_d hM hC hAtS
  have hNext := hRun.at_next hM.1 hSucc hAtR hAtS
  have hSourceF : MemPair M X.parents r F := (hFrom.parents r F).mpr ⟨Vr,hAtR⟩
  have hSourceG : MemPair M X.parents height G := (hFrom.parents height G).mpr ⟨Vs,hAtS⟩
  have hVsX : Graph M Vs X.width C.omega := hFrom.width.symm ▸ hNumericS.values
  have hLastX := (hActive.parent.bounds hM.1 hX).2.1
  obtain ⟨NewV,hNewV⟩ := copied_top_exists_d hM hC hT hA hX.width hY.width hVsX hLastX
  have hValueAtTop (source : M.Domain) (hHeight : MemPair M X.heights source height)
      (top : M.Domain) (hTopAt : MemPair M OldTop source top) : MemPair M Vs source top := by
    obtain ⟨h,_,hH,hValue⟩ := (hOldTop.rows source top).mp hTopAt
    have he := hX.heights.unique source h height hH hHeight
    subst h
    exact row_value_at_d hM.1 hRun hAtS hValue
  have hSameHeight (target top : M.Domain) (hHeight : MemPair M Y.heights target height)
      (hTopAt : MemPair M NewTop target top) : MemPair M NewV target top := by
    have ht := (hY.heights.bounds hM.1 hHeight).1
    have htNat := hw.transitive Y.width hY.width target ht
    obtain ⟨source,block,hDec⟩ := OrdinaryCoordinates.decoded_exists_d hM hC hT hA htNat
    have hSource := hDec.source_lt_last_d hM hC hT hA
    have hMap := hDec.parent_copy_reconstruct_d hM hC hT hA
    have hOldHeight := (Terminal.height_parent_copy_iff_d hM hC hT hA hSource hMap).mp ((hCopy.heights target height).mp hHeight).2
    have hOldTopAt := (hTop.parent_copy_iff_d hM hC hT hA hSource ht hMap).mp hTopAt
    exact (hNewV.parent_copy_iff_d hM hC hT hA hSource ht hMap).mpr (hValueAtTop source hOldHeight top hOldTopAt)
  have hc := (hY.heights.bounds hM.1 hHC).1
  obtain ⟨source,block,hDec⟩ := OrdinaryCoordinates.decoded_exists_d hM hC hT hA (hw.transitive Y.width hY.width c hc)
  have hSource := hDec.source_lt_last_d hM hC hT hA
  have hMap := hDec.parent_copy_reconstruct_d hM hC hT hA
  have hOldHeight := (Terminal.height_parent_copy_iff_d hM hC hT hA hSource hMap).mp ((hCopy.heights c height).mp hHC).2
  have hOldTC := (hTop.parent_copy_iff_d hM hC hT hA hSource hc hMap).mp hTC
  have hSourceNo : NoParent M m G source := by
    intro parent _ hP
    have hSelf := (hX.source height source height hOldHeight).mp
      ⟨parent,G,(hX.parents.bounds hM.1 hSourceG).2,hSourceG,hP⟩
    exact SetTheory.KP.mem_irrefl_d (KP1Y.models_weakKP hM) height hSelf
  have hSafe : PositiveBound M C X.width F Vs tc source := hFrom.width.symm ▸
    positive_bound_of_no_parent_d hM hC hNext.selection hSourceNo (hValueAtTop source hOldHeight tc hOldTC)
  have hSafeNew : PositiveBound M C Y.width Q NewV tc c := by
    classical
    by_cases hLow : M.mem r level
    · have hLevel := (hActive.parent.bounds hM.1 hX).1
      have hSLe := successor_le_d hM hC hr hLevel hSucc hLow
      obtain ⟨WLevel,FLevel,hAtLevel,hParentLevel⟩ := (hFrom.parent_iff hM.1 hX level A.last A.root).mp hActive.parent
      have hRootAnc := hRun.ancestor_lower_d hM hC hAtS hAtLevel hSLe
        (ancestor_direct_d hM hC (hRun.at_numeric_d hM hC hAtLevel).forest hParentLevel)
      have hZeros := NumericOrder.row_next_zeros_at_roots_d hM hC hNumericR hNext
      have hSplice : PositiveBound M C X.width F Vs tc A.root → PositiveBound M C X.width F Vs tc A.last := by
        intro hSafeRoot
        exact hFrom.width.symm ▸ positive_bound_splice_d hM hC hNext.selection hZeros hRootAnc (hFrom.width ▸ hSafeRoot)
      exact positive_bound_copy_low_d hM hC hT hA hX hY hCopy hLevel hLow hSourceF hQ hVsX hNewV hSplice hSource hc hMap hSafe
    · have hHigh : level=r ∨ M.mem level r := by
        rcases hw.wellOrder.linear.compare level (hActive.parent.bounds hM.1 hX).1 r hr with he | hlt | hgt
        · exact Or.inl (hM.1.eq_of_same_members level r he)
        · exact Or.inr hlt
        · exact False.elim (hLow hgt)
      exact positive_bound_copy_high_d hM hC hT hA hX hY hCopy hHigh hSourceF hQ hVsX hNewV hSource hc hMap hSafe
  have hTPPositive : M.mem C.zero tp := by
    obtain ⟨_,oldSource,_,_,_,_,hOldTP⟩ := (hTop.rows p tp).mp hTP
    obtain ⟨a,_,hOldA⟩ := hRun.base.values.total oldSource (hOldTop.graph.bounds hM.1 hOldTP).1
    exact hOldTop.positive_d hM hC hRun hFrom.heights hOldA (hPositive oldSource a hOldA) hOldTP
  exact hSafeNew p (hY.heights.bounds hM.1 hHP).1 (Or.inr hAnc) tp (hSameHeight p tp hHP hTP) hTPPositive

end KP1Y.OneYFinite.TerminalTopBound
