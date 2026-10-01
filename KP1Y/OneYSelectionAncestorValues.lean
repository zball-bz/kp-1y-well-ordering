import KP1Y.OneYSelectionOrder

/-! 最右较小值选择的所有祖先都恰好是原候选链上的记录最小值。 -/
namespace KP1Y.OneYFinite
open YesMetaZFC YesMetaZFC.SetTheory YesMetaZFC.SetTheory.Definitional
open KP1Y.Kuratowski KP1Y.Functions KP1Y.Naturals
universe u

private def ancestorRecordEnv {M : SetTheory.Structure.{u}} (C : ExpressionData M.Domain)
    (m F V P : M.Domain) : Env M 9 :=
  ((((((((oneEnv C.omega).push C.zero).push C.one).push C.sequences).push C.expressions).push m).push F).push V).push P

private def ancestorRecordSchema : Project.UnarySchema 9 where
  body := .forallE (.imp
    (ancestorFormula ⟨.bound 10,.bound 9,.bound 8,.bound 7,.bound 6⟩ (.bound 5) (.bound 2) (.bound 0) (.bound 1))
    (recordMinimumFormula ⟨.bound 10,.bound 9,.bound 8,.bound 7,.bound 6⟩ (.bound 5) (.bound 4) (.bound 3) (.bound 0) (.bound 1)))
  freeClosed := by
    have hC : (⟨.bound 10,.bound 9,.bound 8,.bound 7,.bound 6⟩ : ExpressionData (Project.Term 11)).Closed := ⟨rfl,rfl,rfl,rfl,rfl⟩
    have hA := ancestorFormula_freeClosed hC (.bound 5) (.bound 2) (.bound 0) (.bound 1) rfl rfl rfl rfl
    have hR := recordMinimumFormula_freeClosed hC (.bound 5) (.bound 4) (.bound 3) (.bound 0) (.bound 1) rfl rfl rfl rfl rfl
    simp [Definitional.Formula.FreeClosed,hA,hR]

private theorem ancestorRecordSchema_iff {M : SetTheory.Structure.{u}} (he : Extensional M)
    (C : ExpressionData M.Domain) (m F V P c : M.Domain) :
    Project.Formula.satisfies ((ancestorRecordEnv C m F V P).push c) ancestorRecordSchema.body ↔
      ∀ a, Ancestor M C m P a c → RecordMinimum M C m F V a c := by
  simp only [ancestorRecordSchema,Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_imp_iff,
    ancestorFormula_iff he,recordMinimumFormula_iff he]
  rfl

theorem Selects.parent_record_minimum_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {m F V P c p : M.Domain}
    (hS : Selects false M C m F V P) (hP : MemPair M P c p) : RecordMinimum M C m F V p c := by
  have hParent := (hS.parents c p).mp hP
  obtain ⟨x,hx,y,hy,hX,hY,hxy,_⟩ := hParent.1.2
  refine ⟨hParent.1.1,x,hx,y,hy,hX,hY,hxy,?_⟩
  intro q _ hQ hpq v hv hV
  rcases hS.value_ge_after_parent_d hM hC hP hQ hpq hY hV with he | hyv
  · exact he ▸ hxy
  · exact (omega_isOrdinal_d hM hC.omega).wellOrder.linear.trans x hx y hy v hv hxy hyv

/-- 必要方向的对象父链归纳，与已有充分方向共同识别真实记录最小值。 -/
theorem Selects.ancestor_record_minimum_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {m F V P a c : M.Domain}
    (hS : Selects false M C m F V P) (hAnc : Ancestor M C m P a c) : RecordMinimum M C m F V a c := by
  have hw := omega_isOrdinal_d hM hC.omega
  have hAll := KP1Y.induction_d hM ancestorRecordSchema (ancestorRecordEnv C m F V P) (by
    intro c ih
    apply (ancestorRecordSchema_iff hM.1 C m F V P c).mpr
    intro a hAnc
    obtain ⟨p,hP,hTail⟩ := ancestor_parent_cases_d hM hC hS.forest hAnc
    rcases hTail with he | hAp
    · exact he.symm ▸ hS.parent_record_minimum_d hM hC hP
    · have hParent := (hS.parents c p).mp hP
      obtain ⟨v,hv,w,hwv,hV,hW,hvw,_⟩ := hParent.1.2
      obtain ⟨hAF,x,hx,v',_,hX,hV',hxv,hMin⟩ :=
        (ancestorRecordSchema_iff hM.1 C m F V P p).mp (ih p (hS.forest.left c p hP)) a hAp
      have hvv := hS.values.unique p v' v hV' hV
      subst v'
      have hxw := hw.wellOrder.linear.trans x hx v hv w hwv hxv hvw
      refine ⟨ancestor_trans_d hM hC hS.inherited hAF hParent.1.1,x,hx,w,hwv,hX,hW,hxw,?_⟩
      intro q hq hQ haq y hy hY
      rcases hw.wellOrder.linear.compare q (hw.transitive m hS.forest.width q hq)
          p (hw.transitive m hS.forest.width p (hS.forest.bounds hM.1 hP).2) with he | hqp | hpq
      · have hqp := hM.1.eq_of_same_members q p he
        subst q
        exact hS.values.unique p v y hV hY ▸ hxv
      · exact hMin q hq (ancestor_between_d hM hC hS.inherited hQ hParent.1.1 hqp) haq y hy hY
      · rcases hS.value_ge_after_parent_d hM hC hP hQ hpq hW hY with he | hwy
        · exact he ▸ hxw
        · exact hw.wellOrder.linear.trans x hx w hwv y hy hxw hwy)
  exact (ancestorRecordSchema_iff hM.1 C m F V P c).mp (hAll c) a hAnc

theorem Selects.ancestor_iff_record_minimum_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {m F V P a c : M.Domain}
    (hS : Selects false M C m F V P) : Ancestor M C m P a c ↔ RecordMinimum M C m F V a c :=
  ⟨hS.ancestor_record_minimum_d hM hC,hS.record_minimum_ancestor_d hM hC⟩

theorem Selects.ancestor_value_lt_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {m F V P a c x y : M.Domain}
    (hS : Selects false M C m F V P) (hAnc : Ancestor M C m P a c)
    (hX : MemPair M V a x) (hY : MemPair M V c y) : M.mem x y := by
  obtain ⟨_,x',_,y',_,hX',hY',hxy,_⟩ := hS.ancestor_record_minimum_d hM hC hAnc
  have hxx := hS.values.unique a x' x hX' hX
  have hyy := hS.values.unique c y' y hY' hY
  subst x'
  subst y'
  exact hxy

theorem Selects.ancestor_value_lt_after_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {m F V P a c q x y : M.Domain}
    (hS : Selects false M C m F V P) (hAnc : Ancestor M C m P a c)
    (hQ : Ancestor M C m F q c) (haq : M.mem a q)
    (hX : MemPair M V a x) (hY : MemPair M V q y) : M.mem x y := by
  obtain ⟨_,x',_,_,_,hX',_,_,hMin⟩ := hS.ancestor_record_minimum_d hM hC hAnc
  have hxx := hS.values.unique a x' x hX' hX
  subst x'
  exact hMin q (hQ.bounds hM.1).1 hQ haq y (hS.values.bounds hM.1 hY).2 hY

end KP1Y.OneYFinite
