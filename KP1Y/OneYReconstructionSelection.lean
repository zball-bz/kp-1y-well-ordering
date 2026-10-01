import KP1Y.OneYReconstructionOrder
import KP1Y.OneYGraphPseudo
import KP1Y.OneYSelectionAncestorValues

/-! 指定数值森林的直接父与阻挡充分性。当前列的选择结论不是输入。 -/
namespace KP1Y.OneYFinite.ReconstructionSelection
open YesMetaZFC YesMetaZFC.SetTheory YesMetaZFC.SetTheory.Definitional
open KP1Y.Kuratowski KP1Y.Functions KP1Y.Naturals KP1Y.Bounded
open ReconstructionCanonical Reconstruction MountainReconstruction
universe u

private theorem not_reverse_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {a b : M.Domain} (hb : M.mem b C.omega)
    (hLe : a=b ∨ M.mem a b) : ¬M.mem b a := by
  intro hba
  rcases hLe with he | hab
  · exact SetTheory.KP.mem_irrefl_d (KP1Y.models_weakKP hM) b (he ▸ hba)
  · exact SetTheory.KP.mem_irrefl_d (KP1Y.models_weakKP hM) b
      (((omega_isOrdinal_d hM hC.omega).mem hb).transitive a hab b hba)

theorem restricted_parent_of_direct_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {m V F P c p : M.Domain}
    (hRow : NumericRow M C m V P) (hF : Forest M C.omega m F) (hP : MemPair M P c p) (hDirect : MemPair M F c p) :
    RestrictedParent true M C m F V c p := by
  obtain ⟨x,hx,hPX⟩ := hRow.values.total p (hRow.forest.bounds hM.1 hP).2
  obtain ⟨y,hy,hCY⟩ := hRow.values.total c (hRow.forest.bounds hM.1 hP).1
  have hValues := hRow.parentValues c p x y hP hPX hCY
  exact ⟨⟨ancestor_direct_d hM hC hF hDirect,x,hx,y,hy,hPX,hCY,hValues.2,hValues.1⟩,
    fun q _ hQ => ancestor_le_parent_d hM hC hF hDirect hQ.1⟩

theorem selected_value_ge_after_parent_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {m F V P c p q x y : M.Domain}
    (hS : Selects true M C m F V P) (hP : MemPair M P c p) (hQ : Ancestor M C m F q c) (hpq : M.mem p q)
    (hX : MemPair M V c x) (hY : MemPair M V q y) (hy : M.mem C.zero y) : x=y ∨ M.mem x y := by
  have hxNat := (hS.values.bounds hM.1 hX).2
  have hyNat := (hS.values.bounds hM.1 hY).2
  rcases (omega_isOrdinal_d hM hC.omega).wellOrder.linear.compare x hxNat y hyNat with he | hlt | hgt
  · exact Or.inl (hM.1.eq_of_same_members x y he)
  · exact Or.inr hlt
  · have hCand : ParentCandidate true M C m F V c q := ⟨hQ,y,hyNat,x,hxNat,hY,hX,hgt,hy⟩
    have hMax := ((hS.parents c p).mp hP).2 q hQ.1 hCand
    have hpNat := (omega_isOrdinal_d hM hC.omega).transitive m hS.forest.width p (hS.forest.bounds hM.1 hP).2
    exact False.elim (not_reverse_d hM hC hpNat hMax hpq)

theorem selected_ancestor_positive_lt_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {m F V P a c x y : M.Domain}
    (hS : Selects true M C m F V P) (hZeros : NumericOrder.ZerosAtRoots M m F V C.zero)
    (hAnc : Ancestor M C m P a c) (hX : MemPair M V a x) (hY : MemPair M V c y)
    (hx : M.mem C.zero x) (hy : M.mem C.zero y) : M.mem x y := by
  obtain ⟨_,Filled,_,_,hRows,hDense⟩ := hS.filled_selection_exists_d hM hC
    (fun q hQ => hZeros q (hS.values.bounds hM.1 hQ).1 hQ)
  have hFX := (hRows a x).mpr ⟨x,(hS.values.bounds hM.1 hX).2,hX,Or.inr ⟨fun he => hC.zero_empty C.zero (he ▸ hx),rfl⟩⟩
  have hFY := (hRows c y).mpr ⟨y,(hS.values.bounds hM.1 hY).2,hY,Or.inr ⟨fun he => hC.zero_empty C.zero (he ▸ hy),rfl⟩⟩
  exact hDense.ancestor_value_lt_d hM hC hAnc hFX hFY

theorem selected_ancestor_positive_lt_after_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {m F V P a c q x y : M.Domain}
    (hS : Selects true M C m F V P) (hZeros : NumericOrder.ZerosAtRoots M m F V C.zero)
    (hAnc : Ancestor M C m P a c) (hQ : Ancestor M C m F q c) (haq : M.mem a q)
    (hX : MemPair M V a x) (hY : MemPair M V q y) (hx : M.mem C.zero x) (hy : M.mem C.zero y) : M.mem x y := by
  obtain ⟨_,Filled,_,_,hRows,hDense⟩ := hS.filled_selection_exists_d hM hC
    (fun q hQ => hZeros q (hS.values.bounds hM.1 hQ).1 hQ)
  have hFX := (hRows a x).mpr ⟨x,(hS.values.bounds hM.1 hX).2,hX,Or.inr ⟨fun he => hC.zero_empty C.zero (he ▸ hx),rfl⟩⟩
  have hFY := (hRows q y).mpr ⟨y,(hS.values.bounds hM.1 hY).2,hY,Or.inr ⟨fun he => hC.zero_empty C.zero (he ▸ hy),rfl⟩⟩
  exact hDense.ancestor_value_lt_after_d hM hC hAnc hQ haq hFX hFY

/-- 只要求严格左前缀已恢复。零值条件会由真实重建DifferenceGraph自动提供。 -/
theorem restricted_parent_of_blocker_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {m V F P c q p z : M.Domain}
    (hRow : NumericRow M C m V P) (hF : Forest M C.omega m F)
    (hZeros : NumericOrder.ZerosAtRoots M m F V C.zero)
    (hQ : MemPair M F c q) (hP : MemPair M P c p) (hAnc : Ancestor M C m F p c)
    (hPrefix : ∀ i, M.mem i c → ∀ a, MemPair M P i a ↔ RestrictedParent true M C m F V i a)
    (hPath : z=q ∨ Ancestor M C m P z q) (hZP : MemPair M P z p)
    (hUpper : ∀ x y, MemPair M V c x → MemPair M V z y → x=y ∨ M.mem x y) :
    RestrictedParent true M C m F V c p := by
  have hw := omega_isOrdinal_d hM hC.omega
  have hcm := (hF.bounds hM.1 hQ).1
  have hc := hw.transitive m hF.width c hcm
  have hqC := hF.left c q hQ
  have hzC : M.mem z c := by
    rcases hPath with he | hAnc
    · exact he.symm ▸ hqC
    · exact (hw.mem hc).transitive q hqC z hAnc.1
  obtain ⟨S,hS⟩ := select_forest_exists_d hM true hC hF hRow.values
  have hRows : RowsAgreeOn M P S c := fun i hi a => (hPrefix i hi a).trans (hS.parents i a).symm
  have hSub : M.MemberSubset c m := fun i hi => (hw.mem hF.width).transitive c hcm i hi
  have hPathS : z=q ∨ Ancestor M C m S z q := hPath.imp id
    ((ancestor_common_prefix_iff_d hM hC hRow.forest hS.forest hc hSub hSub hqC hRows).mp)
  have hZPS := (hRows z hzC p).mp hZP
  have hZF : Ancestor M C m F z c := by
    rcases hPathS with he | hAncS
    · exact he.symm ▸ ancestor_direct_d hM hC hF hQ
    · exact ancestor_step_d hM hC hF (hS.ancestor_inherited_d hM hC hAncS) hQ
  obtain ⟨pv,hpv,hPV⟩ := hRow.values.total p (hRow.forest.bounds hM.1 hP).2
  obtain ⟨cv,hcv,hCV⟩ := hRow.values.total c hcm
  obtain ⟨zv,hzv,hZV⟩ := hRow.values.total z (hRow.forest.bounds hM.1 hZP).1
  have hValues := hRow.parentValues c p pv cv hP hPV hCV
  have hZValues := hRow.parentValues z p pv zv hZP hPV hZV
  have hZPos := (hw.mem hzv).transitive pv hZValues.2 C.zero hZValues.1
  refine ⟨⟨hAnc,pv,hpv,cv,hcv,hPV,hCV,hValues.2,hValues.1⟩,?_⟩
  intro a _ hCandidate
  have haNat := hw.transitive m hF.width a (hCandidate.1.bounds hM.1).1
  have hpNat := hw.transitive m hF.width p (hRow.forest.bounds hM.1 hP).2
  rcases hw.wellOrder.linear.compare a haNat p hpNat with he | hlt | hgt
  · exact Or.inl (hM.1.eq_of_same_members a p he)
  · exact Or.inr hlt
  · obtain ⟨av,hav,cv',_,hAV,hCV',hAC,hAPos⟩ := hCandidate.2
    have he := hRow.values.unique c cv' cv hCV' hCV
    subst cv'
    have hZBound : zv=av ∨ M.mem zv av := by
      rcases hw.wellOrder.linear.compare a haNat z (hw.transitive m hF.width z (hZF.bounds hM.1).1) with he | haz | hza
      · have he := hM.1.eq_of_same_members a z he
        subst a
        exact Or.inl (hRow.values.unique z zv av hZV hAV)
      · exact selected_value_ge_after_parent_d hM hC hS hZPS
          (ancestor_between_d hM hC hF hCandidate.1 hZF haz) hgt hZV hAV hAPos
      · obtain ⟨q',hCQ,hTail⟩ := ancestor_parent_cases_d hM hC hF hCandidate.1
        have hqq := hF.unique c q' q hCQ hQ
        subst q'
        rcases hPathS with heZ | hZAnc
        · rcases hTail with heA | hAAnc
          · have heZA := heZ.trans heA.symm
            exact False.elim (SetTheory.KP.mem_irrefl_d (KP1Y.models_weakKP hM) a (heZA ▸ hza))
          · exact False.elim (not_reverse_d hM hC (hw.transitive m hF.width z (hZF.bounds hM.1).1) (Or.inr (heZ.symm ▸ hAAnc.1)) hza)
        · rcases hTail with heA | hAAnc
          · subst a
            exact Or.inr (selected_ancestor_positive_lt_d hM hC hS hZeros hZAnc hZV hAV hZPos hAPos)
          · exact Or.inr (selected_ancestor_positive_lt_after_d hM hC hS hZeros hZAnc hAAnc hza hZV hAV hZPos hAPos)
    have hUpper' := hUpper cv zv hCV hZV
    have hCA : cv=av ∨ M.mem cv av := by
      rcases hUpper' with he | hlt
      · exact he.symm ▸ hZBound
      · rcases hZBound with he | hgt
        · exact Or.inr (he ▸ hlt)
        · exact Or.inr ((hw.mem hav).transitive zv hgt cv hlt)
    exact False.elim (not_reverse_d hM hC hav hCA hAC)

/-- 装饰图层阻挡转为实际数值阻挡，只消费高于待恢复行的选择结论。 -/
theorem reconstructed_parent_of_key_blocker_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {Pairs Plus : M.Domain} (hPlus : AdditionTable M C Pairs Plus)
    {X : CopiedMountain.Data M.Domain} (hX : X.Valid M C) {Top B Parents H r s t V W F Q c q p z tc tz : M.Domain}
    (hTop : Graph M Top X.width C.omega) (hPositive : ∀ c top, MemPair M Top c top → M.mem C.zero top)
    (hB : SequenceBound M C X.width X.heights B) (hParents : Prefix M Parents X.parents B X.forests)
    (hH : Reconstructs M (grid C X Top Pairs Plus B Parents) H)
    (hV : RowValues M (grid C X Top Pairs Plus B Parents) H r V)
    (hW : RowValues M (grid C X Top Pairs Plus B Parents) H s W)
    (hF : MemPair M X.parents r F) (hQ : MemPair M X.parents s Q)
    (hSucc : M.SuccessorOf s r) (hNext : M.SuccessorOf t s)
    (hHigher : ∀ a b V0 W0 F' Q', M.mem a C.omega → (s=a ∨ M.mem s a) → M.SuccessorOf b a →
      RowValues M (grid C X Top Pairs Plus B Parents) H a V0 → RowValues M (grid C X Top Pairs Plus B Parents) H b W0 →
      MemPair M X.parents a F' → MemPair M X.parents b Q' → Selects true M C X.width F' W0 Q')
    (hOld : MemPair M F c q) (hNew : MemPair M Q c p) (hRefines : Ancestor M C X.width F p c)
    (hPrefix : ∀ i, M.mem i c → ∀ a, MemPair M Q i a ↔ RestrictedParent true M C X.width F W i a)
    (hPath : z=q ∨ Ancestor M C X.width Q z q) (hZP : MemPair M Q z p)
    (hTC : MemPair M Top c tc) (hTZ : MemPair M Top z tz)
    (hKey : ForestOrder.KeyLE M C X c z t tc tz) : RestrictedParent true M C X.width F W c p := by
  have hD := grid_valid_d hM hC hX hTop hPlus hB hParents
  have hNumeric := hW.numeric_d hM hC hPlus hX hTop hPositive hB hParents hH hQ
  have hNumericV := hV.numeric_d hM hC hPlus hX hTop hPositive hB hParents hH hF
  have hDiff := hV.difference_d hM hC hPlus hX hTop hB hParents hH hW hF hSucc
  have hZeros : NumericOrder.ZerosAtRoots M X.width F W C.zero := by
    intro a _ hZero b _ hAB
    exact hC.zero_empty C.zero ((hNumericV.difference_positive_iff_d hM hC hDiff hZero).mpr ⟨b,hAB⟩)
  apply restricted_parent_of_blocker_d hM hC hNumeric (hX.forest r F hF) hZeros hOld hNew hRefines hPrefix hPath hZP
  intro x y hWX hWY
  have hs := (hX.parents.bounds hM.1 hQ).1
  have ht := natural_successor_mem_d hM hC hs hNext
  obtain ⟨Z,hZ⟩ := row_values_exists_d hM hD hH ht
  obtain ⟨x',hx',hZX⟩ := hZ.graph.total c (hNumeric.forest.bounds hM.1 hNew).1
  obtain ⟨y',hy',hZY⟩ := hZ.graph.total z (hNumeric.forest.bounds hM.1 hZP).1
  have hDiffNext := hW.difference_d hM hC hPlus hX hTop hB hParents hH hZ hQ hNext
  have hXPos := (hNumeric.difference_positive_iff_d hM hC hDiffNext hZX).mpr ⟨p,hNew⟩
  have hYPos := (hNumeric.difference_positive_iff_d hM hC hDiffNext hZY).mpr ⟨p,hZP⟩
  have hSame : ParentRowsEqual M Q c z := by
    intro a
    constructor
    · intro h
      exact (hNumeric.forest.unique c a p h hNew).symm ▸ hZP
    · intro h
      exact (hNumeric.forest.unique z a p h hZP).symm ▸ hNew
  have hCompare := (ReconstructionOrder.key_iff_value_le_d hM hC hPlus hX hTop hPositive hB hParents hH hHigher
    hs (Or.inl rfl) hNext ⟨Q,(hX.parents.bounds hM.1 hQ).2,hQ,hSame⟩
    ((hZ.rows c x').mp hZX) ((hZ.rows z y').mp hZY) hXPos hYPos hTC hTZ).mp hKey
  obtain ⟨parentValue,hPV,hParentValue⟩ := hW.graph.total p (hNumeric.forest.bounds hM.1 hNew).2
  have hParentC : CopiedMountain.ParentAt M X s c p := ⟨Q,(hX.parents.bounds hM.1 hQ).2,hQ,hNew⟩
  have hParentZ : CopiedMountain.ParentAt M X s z p := ⟨Q,(hX.parents.bounds hM.1 hQ).2,hQ,hZP⟩
  have hSumC := ((hW.rows c x).mp hWX).parent_sum_d hM hD hH ((grid_parent_iff_d hM hC hX hB hParents).mpr hParentC) hNext
    ((hZ.rows c x').mp hZX) ((hW.rows p parentValue).mp hParentValue)
  have hSumZ := ((hW.rows z y).mp hWY).parent_sum_d hM hD hH ((grid_parent_iff_d hM hC hX hB hParents).mpr hParentZ) hNext
    ((hZ.rows z y').mp hZY) ((hW.rows p parentValue).mp hParentValue)
  rcases hCompare with he | hlt
  · subst y'
    exact Or.inl (hPlus.add_unique hM.1 hSumC hSumZ)
  · exact Or.inr (natural_sum_strict_left_d hM hC hx' hy' hPV
      ((hPlus.add_iff_sum hM hx' hPV).mp hSumC) ((hPlus.add_iff_sum hM hy' hPV).mp hSumZ) hlt)

private def ancestorValueEnv {M : SetTheory.Structure.{u}} (C : ExpressionData M.Domain) (m F V : M.Domain) : Env M 8 :=
  (((((((oneEnv C.omega).push C.zero).push C.one).push C.sequences).push C.expressions).push m).push F).push V

private def ancestorValueSchema : Project.UnarySchema 8 where
  body := .forallE (.forallE (.forallE (.imp
    (ancestorFormula ⟨.bound 11,.bound 10,.bound 9,.bound 8,.bound 7⟩ (.bound 6) (.bound 5) (.bound 2) (.bound 3))
      (.imp (memPairFormula (.bound 4) (.bound 2) (.bound 1))
        (.imp (memPairFormula (.bound 4) (.bound 3) (.bound 0)) (.mem (.bound 1) (.bound 0)))))))
  freeClosed := by
    have hA := ancestorFormula_freeClosed
      (show (⟨.bound 11,.bound 10,.bound 9,.bound 8,.bound 7⟩ : ExpressionData (Project.Term 12)).Closed from ⟨rfl,rfl,rfl,rfl,rfl⟩)
      (.bound 6) (.bound 5) (.bound 2) (.bound 3) rfl rfl rfl rfl
    simp [Definitional.Formula.FreeClosed,hA,memPairFormula,codeFormula,pairFormula,Project.Formula.existsMem,Project.Formula.forallMem]

private theorem ancestorValueSchema_iff {M : SetTheory.Structure.{u}} (he : Extensional M)
    (C : ExpressionData M.Domain) (m F V c : M.Domain) :
    Project.Formula.satisfies ((ancestorValueEnv C m F V).push c) ancestorValueSchema.body ↔
      ∀ a x y, Ancestor M C m F a c → MemPair M V a x → MemPair M V c y → M.mem x y := by
  simp only [ancestorValueSchema,Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_imp_iff,
    ancestorFormula_iff he,memPairFormula_iff he,Project.Formula.satisfies_mem_iff]
  rfl

/-- 任何真实NumericRow的父链值严格增加；无需先证明该行来自Selects。 -/
theorem numeric_ancestor_values_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {m V F a c x y : M.Domain}
    (hRow : NumericRow M C m V F) (hAnc : Ancestor M C m F a c) (hX : MemPair M V a x) (hY : MemPair M V c y) : M.mem x y := by
  have hAll := KP1Y.induction_d hM ancestorValueSchema (ancestorValueEnv C m F V) (by
    intro c ih
    apply (ancestorValueSchema_iff hM.1 C m F V c).mpr
    intro a x y hAnc hX hY
    obtain ⟨p,hCP,hTail⟩ := ancestor_parent_cases_d hM hC hRow.forest hAnc
    obtain ⟨pv,_,hPV⟩ := hRow.values.total p (hRow.forest.bounds hM.1 hCP).2
    have hPY := (hRow.parentValues c p pv y hCP hPV hY).2
    rcases hTail with he | hAP
    · subst a
      exact (hRow.values.unique p pv x hPV hX) ▸ hPY
    · have hXP := (ancestorValueSchema_iff hM.1 C m F V p).mp (ih p (hRow.forest.left c p hCP)) a x pv hAP hX hPV
      exact ((omega_isOrdinal_d hM hC.omega).mem (hRow.values.bounds hM.1 hY).2).transitive pv hPY x hXP)
  exact (ancestorValueSchema_iff hM.1 C m F V c).mp (hAll c) a x y hAnc hX hY

def PseudoTopBound (M : SetTheory.Structure.{u}) (C : ExpressionData M.Domain) (X : CopiedMountain.Data M.Domain) (Top : M.Domain) : Prop :=
  ∀ c p height tc tp, CopiedMountain.GraphPseudoParent M C X c p →
    MemPair M X.heights c height → MemPair M X.heights p height →
    MemPair M Top c tc → MemPair M Top p tp → tc=tp ∨ M.mem tc tp

private theorem le_trans_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {a b c : M.Domain} (hc : M.mem c C.omega)
    (hab : a=b ∨ M.mem a b) (hbc : b=c ∨ M.mem b c) : a=c ∨ M.mem a c := by
  rcases hab with he | hab
  · exact he.symm ▸ hbc
  · rcases hbc with he | hbc
    · exact Or.inr (he ▸ hab)
    · exact Or.inr (((omega_isOrdinal_d hM hC.omega).mem hc).transitive b hbc a hab)

/-- 顶格无额外最近更小父项；只使用真实相邻行精化、伪父Top界与严格左前缀。 -/
theorem reconstructed_top_no_candidate_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {Pairs Plus : M.Domain} (hPlus : AdditionTable M C Pairs Plus)
    {X : CopiedMountain.Data M.Domain} (hX : X.Valid M C) {Top B Parents H r s W F Q c : M.Domain}
    (hTop : Graph M Top X.width C.omega) (hPositive : ∀ c top, MemPair M Top c top → M.mem C.zero top)
    (hB : SequenceBound M C X.width X.heights B) (hParents : Prefix M Parents X.parents B X.forests)
    (hH : Reconstructs M (grid C X Top Pairs Plus B Parents) H)
    (hW : RowValues M (grid C X Top Pairs Plus B Parents) H s W)
    (hF : MemPair M X.parents r F) (hQ : MemPair M X.parents s Q) (hSucc : M.SuccessorOf s r)
    (hRefines : ForestRefines M C X.width Q F) (hBound : PseudoTopBound M C X Top)
    (hHeight : MemPair M X.heights c s)
    (hPrefix : ∀ i, M.mem i c → ∀ a, MemPair M Q i a ↔ RestrictedParent true M C X.width F W i a) :
    ¬∃ q, ParentCandidate true M C X.width F W c q := by
  rintro ⟨q,hCandidate⟩
  have hD := grid_valid_d hM hC hX hTop hPlus hB hParents
  have hNumeric := hW.numeric_d hM hC hPlus hX hTop hPositive hB hParents hH hQ
  have hForestF := hX.forest r F hF
  have hForestQ := hX.forest s Q hQ
  have hr := (hX.parents.bounds hM.1 hF).1
  have hs := (hX.parents.bounds hM.1 hQ).1
  have hw := omega_isOrdinal_d hM hC.omega
  obtain ⟨qv,hqv,cv,_,hQV,hCV,hQC,hQPositive⟩ := hCandidate.2
  obtain ⟨hq,_,hHQ⟩ := hX.heights.total q (hCandidate.1.bounds hM.1).1
  obtain ⟨tq,_,hTQ⟩ := hTop.total q (hCandidate.1.bounds hM.1).1
  have hQLive := (((hW.rows q qv).mp hQV).positive_iff_d hM hD hH hHQ hTQ (hPositive q tq hTQ)).mp hQPositive
  obtain ⟨a,hRoot⟩ := root_exists_d hM hC hForestQ (hCandidate.1.bounds hM.1).1
  obtain ⟨ha,_,hHA⟩ := hX.heights.total a hRoot.1
  have hHa := CopiedMountain.graph_root_height_d hM hC hX hQ hRoot hHQ hHA hQLive
  subst ha
  have hAC : Ancestor M C X.width F a c := by
    rcases hRoot.2.2 with he | hAQ
    · exact he.symm ▸ hCandidate.1
    · exact ancestor_trans_d hM hC hForestF (ancestor_refines_d hM hC hForestF hRefines hAQ) hCandidate.1
  have hCandidateA : CopiedMountain.GraphPseudoCandidate M C X c a :=
    ⟨s,hs,s,hs,r,hr,hHeight,hHA,hSucc,F,(hX.parents.bounds hM.1 hF).2,hF,hAC,Or.inl rfl⟩
  have hSPos : M.mem C.zero s := (hC.zero_mem_iff hM hs).mpr (by
    intro he
    exact hC.zero_empty r (he ▸ hSucc.predecessor_mem))
  obtain ⟨p,hPseudo⟩ := CopiedMountain.graph_pseudo_parent_exists_d hM hC hX hHeight hSPos
  have hAP := hPseudo.2 a hAC.1 hCandidateA
  have hPLt := (hPseudo.1.bounds hM.1).2.2
  have hPseudoC := hPseudo.1
  obtain ⟨height,_,hp,hpNat,u,hu,hHeight',hHP,hSucc',G,_,hG,hPC,hPHeight⟩ := hPseudoC
  have hHeightEq := hX.heights.unique c height s hHeight' hHeight
  subst height
  have hUR := Structure.SuccessorOf.predecessor_eq hM.1 (hw.mem hr) hSucc hSucc'
  subst u
  have hGF := hX.parents.unique r G F hG hF
  subst G
  have hAPath : a=p ∨ Ancestor M C X.width F a p :=
    hAP.imp id (fun hap => ancestor_between_d hM hC hForestF hAC hPC hap)
  have hPHeightEq : hp=s := by
    rcases hPHeight with he | he
    · exact he
    · rcases hAPath with hEq | hPath
      · have hAt : MemPair M X.heights p s := hEq ▸ hHA
        exact hX.heights.unique p hp s hHP hAt
      · obtain ⟨b,hPB,_⟩ := ancestor_parent_cases_d hM hC hForestF hPath
        have hRH := (hX.source r p hp hHP).mp ⟨b,F,(hX.parents.bounds hM.1 hF).2,hF,hPB⟩
        exact False.elim (SetTheory.KP.mem_irrefl_d (KP1Y.models_weakKP hM) r (he ▸ hRH))
  subst hp
  obtain ⟨av,hav,hAV⟩ := hW.graph.total a hRoot.1
  obtain ⟨pv,hpv,hPV⟩ := hW.graph.total p (hPseudo.1.bounds hM.1).1
  obtain ⟨ta,_,hTA⟩ := hTop.total a hRoot.1
  have hAPos := ((hW.rows a av).mp hAV).live_positive_d hM hD hH hHA hTA (hPositive a ta hTA) (Or.inl rfl)
  have hAQValue : av=qv ∨ M.mem av qv := by
    rcases hRoot.2.2 with he | hAQ
    · subst a
      exact Or.inl (hW.graph.unique q av qv hAV hQV)
    · exact Or.inr (numeric_ancestor_values_d hM hC hNumeric hAQ hAV hQV)
  have hPAValue : pv=av ∨ M.mem pv av := by
    rcases hAPath with he | hAP
    · subst a
      exact Or.inl (hW.graph.unique p pv av hPV hAV)
    · rcases hw.wellOrder.linear.compare pv hpv av hav with he | hlt | hgt
      · exact Or.inl (hM.1.eq_of_same_members pv av he)
      · exact Or.inr hlt
      · have hCan : ParentCandidate true M C X.width F W p a := ⟨hAP,av,hav,pv,hpv,hAV,hPV,hgt,hAPos⟩
        obtain ⟨b,hRestricted⟩ := restricted_parent_exists_d hM true hC hForestF ⟨a,hCan⟩
        have hPB := (hPrefix p hPLt b).mpr hRestricted
        have hSS := (hX.source s p s hHP).mp ⟨b,Q,(hX.parents.bounds hM.1 hQ).2,hQ,hPB⟩
        exact False.elim (SetTheory.KP.mem_irrefl_d (KP1Y.models_weakKP hM) s hSS)
  obtain ⟨tc,_,hTC⟩ := hTop.total c (hX.heights.bounds hM.1 hHeight).1
  obtain ⟨tp,_,hTP⟩ := hTop.total p (hX.heights.bounds hM.1 hHP).1
  have hCVTop := ReconstructionOrder.padded_top_value_d hM hD hH ((hW.rows c cv).mp hCV) hHeight hTC
  have hPVTop := ReconstructionOrder.padded_top_value_d hM hD hH ((hW.rows p pv).mp hPV) hHP hTP
  have hCPValue : cv=pv ∨ M.mem cv pv := hCVTop.symm ▸ hPVTop.symm ▸ hBound c p s tc tp hPseudo hHeight hHP hTC hTP
  have hCAValue := le_trans_d hM hC hav hCPValue hPAValue
  exact not_reverse_d hM hC hqv (le_trans_d hM hC hqv hCAValue hAQValue) hQC

end KP1Y.OneYFinite.ReconstructionSelection
