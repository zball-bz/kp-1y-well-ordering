import KP1Y.OneYForestSelection

/-! 实际内部父路径的传递闭包及祖先精化，供山形和矩阵复制共同复用。 -/
namespace KP1Y.OneYFinite
open YesMetaZFC YesMetaZFC.SetTheory YesMetaZFC.SetTheory.Definitional
open KP1Y.Kuratowski KP1Y.Functions KP1Y.Naturals
universe u

private def closureEnv {M : SetTheory.Structure.{u}} (C : ExpressionData M.Domain) (m P : M.Domain) : Env M 7 :=
  ((((((oneEnv C.omega).push C.zero).push C.one).push C.sequences).push C.expressions).push m).push P

private def ancestorTransSchema : Project.UnarySchema 7 where
  body := .forallE (.forallE (.forallE (.forallE (.imp
    (.conj (ancestorFormula ⟨.bound 11,.bound 10,.bound 9,.bound 8,.bound 7⟩ (.bound 6) (.bound 5) (.bound 2) (.bound 1))
      (parentPathFormula ⟨.bound 11,.bound 10,.bound 9,.bound 8,.bound 7⟩ (.bound 6) (.bound 5)
        (.bound 3) (.bound 4) (.bound 1) (.bound 0)))
    (ancestorFormula ⟨.bound 11,.bound 10,.bound 9,.bound 8,.bound 7⟩ (.bound 6) (.bound 5) (.bound 2) (.bound 0))))))
  freeClosed := by
    have hC : (⟨.bound 11,.bound 10,.bound 9,.bound 8,.bound 7⟩ : ExpressionData (Project.Term 12)).Closed := ⟨rfl,rfl,rfl,rfl,rfl⟩
    have hA := ancestorFormula_freeClosed hC (.bound 6) (.bound 5) (.bound 2) (.bound 1) rfl rfl rfl rfl
    have hP := parentPathFormula_freeClosed hC (.bound 6) (.bound 5) (.bound 3) (.bound 4) (.bound 1) (.bound 0) rfl rfl rfl rfl rfl rfl
    have hOut := ancestorFormula_freeClosed hC (.bound 6) (.bound 5) (.bound 2) (.bound 0) rfl rfl rfl rfl
    simp [Definitional.Formula.FreeClosed,hA,hP,hOut]

private theorem ancestorTransSchema_iff {M : SetTheory.Structure.{u}} (he : Extensional M)
    (C : ExpressionData M.Domain) (m P len : M.Domain) :
    Project.Formula.satisfies ((closureEnv C m P).push len) ancestorTransSchema.body ↔
      ∀ f a b c, Ancestor M C m P a b → ParentPath M C m P f len b c → Ancestor M C m P a c := by
  simp only [ancestorTransSchema,Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_imp_iff,
    Project.Formula.satisfies_conj_iff,ancestorFormula_iff he,parentPathFormula_iff he,and_imp]
  rfl

theorem ancestor_trans_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {m P a b c : M.Domain}
    (hP : Forest M C.omega m P) (hab : Ancestor M C m P a b) (hbc : Ancestor M C m P b c) : Ancestor M C m P a c := by
  have hAll := natural_induction_d hM ancestorTransSchema (closureEnv C m P) hC.omega
    (fun zero hEmpty => (ancestorTransSchema_iff hM.1 C m P zero).mpr (by
      intro f a b c _ hPath
      exact False.elim (hEmpty C.zero (hPath.zero_in_length hM.1))))
    (fun len hLen ih next hs => (ancestorTransSchema_iff hM.1 C m P next).mpr (by
      intro f a b c hab hPath
      rcases hPath.peel_d hM hC with ⟨_,hEq,_⟩ | ⟨prev,g,d,hPrev,_,_,hOld,hParent⟩
      · exact hEq ▸ hab
      · have hLenPrev := Structure.SuccessorOf.predecessor_eq hM.1 ((omega_isOrdinal_d hM hC.omega).mem hLen) hs hPrev
        subst prev
        have hAd := (ancestorTransSchema_iff hM.1 C m P len).mp ih g a b d hab hOld
        exact ancestor_step_d hM hC hP hAd hParent))
  obtain ⟨_,len,_,f,_,hPath⟩ := hbc
  exact (ancestorTransSchema_iff hM.1 C m P len).mp (hAll len hPath.length) f a b c hab hPath

def ForestRefines (M : SetTheory.Structure.{u}) (C : ExpressionData M.Domain) (m fine coarse : M.Domain) : Prop :=
  ∀ c p, MemPair M fine c p → Ancestor M C m coarse p c

private def refinementSchema : Project.UnarySchema 8 where
  body := .forallE (.forallE (.forallE (.imp
    (parentPathFormula ⟨.bound 11,.bound 10,.bound 9,.bound 8,.bound 7⟩ (.bound 6) (.bound 4)
      (.bound 2) (.bound 3) (.bound 1) (.bound 0))
    (.disj (Project.Formula.extensionalEq (.bound 1) (.bound 0))
      (ancestorFormula ⟨.bound 11,.bound 10,.bound 9,.bound 8,.bound 7⟩ (.bound 6) (.bound 5) (.bound 1) (.bound 0))))))
  freeClosed := by
    have hC : (⟨.bound 11,.bound 10,.bound 9,.bound 8,.bound 7⟩ : ExpressionData (Project.Term 12)).Closed := ⟨rfl,rfl,rfl,rfl,rfl⟩
    have hP := parentPathFormula_freeClosed hC (.bound 6) (.bound 4) (.bound 2) (.bound 3) (.bound 1) (.bound 0) rfl rfl rfl rfl rfl rfl
    have hA := ancestorFormula_freeClosed hC (.bound 6) (.bound 5) (.bound 1) (.bound 0) rfl rfl rfl rfl
    simp [Definitional.Formula.FreeClosed,hP,hA]

private theorem refinementSchema_iff {M : SetTheory.Structure.{u}} (he : Extensional M)
    (C : ExpressionData M.Domain) (m coarse fine len : M.Domain) :
    Project.Formula.satisfies (((closureEnv C m coarse).push fine).push len) refinementSchema.body ↔
      ∀ f a c, ParentPath M C m fine f len a c → a=c ∨ Ancestor M C m coarse a c := by
  simp only [refinementSchema,Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_imp_iff,
    Project.Formula.satisfies_disj_iff,Project.Formula.satisfies_extensionalEq_iff_eq he,
    parentPathFormula_iff he,ancestorFormula_iff he]
  rfl

/-- 每条细父边为粗祖先时，任意内部有限细祖先链也为粗祖先。 -/
theorem ancestor_refines_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {m fine coarse a c : M.Domain}
    (hCoarse : Forest M C.omega m coarse) (hRef : ForestRefines M C m fine coarse)
    (hAnc : Ancestor M C m fine a c) : Ancestor M C m coarse a c := by
  have hAll := natural_induction_d hM refinementSchema ((closureEnv C m coarse).push fine) hC.omega
    (fun zero hEmpty => (refinementSchema_iff hM.1 C m coarse fine zero).mpr (by
      intro f a c hPath
      exact False.elim (hEmpty C.zero (hPath.zero_in_length hM.1))))
    (fun len hLen ih next hs => (refinementSchema_iff hM.1 C m coarse fine next).mpr (by
      intro f a c hPath
      rcases hPath.peel_d hM hC with ⟨_,he,_⟩ | ⟨prev,g,b,hPrev,_,_,hOld,hParent⟩
      · exact Or.inl he
      · have hLenPrev := Structure.SuccessorOf.predecessor_eq hM.1 ((omega_isOrdinal_d hM hC.omega).mem hLen) hs hPrev
        subst prev
        have hbc := hRef c b hParent
        rcases (refinementSchema_iff hM.1 C m coarse fine len).mp ih g a b hOld with he | hab
        · exact Or.inr (he ▸ hbc)
        · exact Or.inr (ancestor_trans_d hM hC hCoarse hab hbc)))
  obtain ⟨hac,len,_,f,_,hPath⟩ := hAnc
  rcases (refinementSchema_iff hM.1 C m coarse fine len).mp (hAll len hPath.length) f a c hPath with he | hAnc
  · exact False.elim (SetTheory.KP.mem_irrefl_d (KP1Y.models_weakKP hM) c (he ▸ hac))
  · exact hAnc

theorem Selects.ancestor_inherited_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {positive : Bool} {m inherited V selected a c : M.Domain}
    (h : Selects positive M C m inherited V selected) (hAnc : Ancestor M C m selected a c) :
    Ancestor M C m inherited a c :=
  ancestor_refines_d hM hC h.inherited (fun _ _ hP => h.parent_ancestor hP) hAnc

end KP1Y.OneYFinite
