import KP1Y.OneYSelectionOrder

/-! 最右较小值选择的真实阻挡点；从内部父路径构造，不把阻挡点作为输入。 -/
namespace KP1Y.OneYFinite
open YesMetaZFC YesMetaZFC.SetTheory YesMetaZFC.SetTheory.Definitional
open KP1Y.Kuratowski KP1Y.Functions KP1Y.Naturals
universe u

private def childAboveEnv {M : SetTheory.Structure.{u}} (C : ExpressionData M.Domain) (m P : M.Domain) : Env M 7 :=
  ((((((oneEnv C.omega).push C.zero).push C.one).push C.sequences).push C.expressions).push m).push P

private def childAboveSchema : Project.UnarySchema 7 where
  body := .forallE (.imp (ancestorFormula ⟨.bound 8,.bound 7,.bound 6,.bound 5,.bound 4⟩ (.bound 3) (.bound 2) (.bound 0) (.bound 1))
    (Project.Formula.existsMem (.bound 3) (.conj
      (.disj (Project.Formula.extensionalEq (.bound 0) (.bound 2))
        (ancestorFormula ⟨.bound 9,.bound 8,.bound 7,.bound 6,.bound 5⟩ (.bound 4) (.bound 3) (.bound 0) (.bound 2)))
      (memPairFormula (.bound 3) (.bound 0) (.bound 1)))))
  freeClosed := by
    have hC : (⟨.bound 8,.bound 7,.bound 6,.bound 5,.bound 4⟩ : ExpressionData (Project.Term 9)).Closed := ⟨rfl,rfl,rfl,rfl,rfl⟩
    have hA := ancestorFormula_freeClosed hC (.bound 3) (.bound 2) (.bound 0) (.bound 1) rfl rfl rfl rfl
    have hC' : (⟨.bound 9,.bound 8,.bound 7,.bound 6,.bound 5⟩ : ExpressionData (Project.Term 10)).Closed := ⟨rfl,rfl,rfl,rfl,rfl⟩
    have hA' := ancestorFormula_freeClosed hC' (.bound 4) (.bound 3) (.bound 0) (.bound 2) rfl rfl rfl rfl
    simp [Project.Formula.existsMem,Definitional.Formula.FreeClosed,memPairFormula,codeFormula,pairFormula,
      Project.Formula.forallMem,hA,hA']

private theorem childAboveSchema_iff {M : SetTheory.Structure.{u}} (he : Extensional M)
    (C : ExpressionData M.Domain) (m P c : M.Domain) :
    Project.Formula.satisfies ((childAboveEnv C m P).push c) childAboveSchema.body ↔
      ∀ a, Ancestor M C m P a c → ∃ z, M.mem z m ∧ (z=c ∨ Ancestor M C m P z c) ∧ MemPair M P z a := by
  simp only [childAboveSchema,Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_imp_iff,
    Project.Formula.satisfies_existsMem_iff,Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_disj_iff,
    Project.Formula.satisfies_extensionalEq_iff_eq he,ancestorFormula_iff he,memPairFormula_iff he]
  rfl

theorem ancestor_child_above_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {m P a c : M.Domain}
    (hP : Forest M C.omega m P) (hAnc : Ancestor M C m P a c) :
    ∃ z, M.mem z m ∧ (z=c ∨ Ancestor M C m P z c) ∧ MemPair M P z a := by
  have hAll := KP1Y.induction_d hM childAboveSchema (childAboveEnv C m P) (by
    intro c ih
    apply (childAboveSchema_iff hM.1 C m P c).mpr
    intro a hAnc
    obtain ⟨p,hParent,hTail⟩ := ancestor_parent_cases_d hM hC hP hAnc
    rcases hTail with he | hAp
    · subst a
      exact ⟨c,(hP.bounds hM.1 hParent).1,Or.inl rfl,hParent⟩
    · obtain ⟨z,hz,hZ,hZA⟩ := (childAboveSchema_iff hM.1 C m P p).mp (ih p (hP.left c p hParent)) a hAp
      refine ⟨z,hz,Or.inr ?_,hZA⟩
      rcases hZ with he | hZP
      · exact he.symm ▸ ancestor_direct_d hM hC hP hParent
      · exact ancestor_step_d hM hC hP hZP hParent)
  exact (childAboveSchema_iff hM.1 C m P c).mp (hAll c) a hAnc

theorem Selects.parent_lt_inherited_parent_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {positive : Bool} {m F V P c p q : M.Domain}
    (hS : Selects positive M C m F V P) (hOld : MemPair M F c q) (hNew : MemPair M P c p) (hNe : p≠q) : M.mem p q := by
  obtain ⟨q',hQ,hTail⟩ := ancestor_parent_cases_d hM hC hS.inherited (hS.parent_ancestor hNew)
  have hqq := hS.inherited.unique c q q' hOld hQ
  subst q'
  rcases hTail with he | hAnc
  · exact False.elim (hNe he)
  · exact hAnc.1

/-- 返回真正的阻挡列，值界对该列的所有实际读取成立。 -/
theorem Selects.blocker_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {m F V P c p q : M.Domain}
    (hS : Selects false M C m F V P) (hOld : MemPair M F c q) (hNew : MemPair M P c p) (hNe : p≠q) :
    ∃ z, M.mem z m ∧ (z=q ∨ Ancestor M C m P z q) ∧ MemPair M P z p ∧
      ∀ x y, MemPair M V c x → MemPair M V z y → x=y ∨ M.mem x y := by
  have hpq := hS.parent_lt_inherited_parent_d hM hC hOld hNew hNe
  have hQ := ancestor_direct_d hM hC hS.inherited hOld
  have hPQ := hS.ancestor_of_between_d hM hC hNew hQ hpq
  obtain ⟨z,hz,hZ,hZP⟩ := ancestor_child_above_d hM hC hS.forest hPQ
  have hZF : Ancestor M C m F z c := by
    rcases hZ with he | hAnc
    · exact he.symm ▸ hQ
    · exact ancestor_trans_d hM hC hS.inherited (hS.ancestor_inherited_d hM hC hAnc) hQ
  exact ⟨z,hz,hZ,hZP,fun _ _ hX hY =>
    hS.value_ge_after_parent_d hM hC hNew hZF (hS.forest.left z p hZP) hX hY⟩

theorem Selects.blocker_with_values_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {m F V P c p q x : M.Domain}
    (hS : Selects false M C m F V P) (hOld : MemPair M F c q) (hNew : MemPair M P c p) (hNe : p≠q)
    (hX : MemPair M V c x) :
    ∃ z, M.mem z m ∧ (z=q ∨ Ancestor M C m P z q) ∧ MemPair M P z p ∧
      ∃ y, M.mem y C.omega ∧ MemPair M V z y ∧ (x=y ∨ M.mem x y) := by
  obtain ⟨z,hz,hZ,hZP,hValues⟩ := hS.blocker_d hM hC hOld hNew hNe
  obtain ⟨y,hy,hY⟩ := hS.values.total z hz
  exact ⟨z,hz,hZ,hZP,y,hy,hY,hValues x y hX hY⟩

end KP1Y.OneYFinite
