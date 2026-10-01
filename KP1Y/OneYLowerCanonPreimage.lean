import KP1Y.OneYLowerCanonOrder
import KP1Y.OneYCopyPathTransport

/-! 目标森林祖先沿映射的前像：沿源链逐边反射，直到遇到指定停止列。对象∈归纳。 -/
namespace KP1Y.OneYFinite.LowerCanon
open YesMetaZFC YesMetaZFC.SetTheory YesMetaZFC.SetTheory.Definitional
open KP1Y.Kuratowski KP1Y.Functions KP1Y.Naturals KP1Y.Bounded KP1Y.Arithmetic
open KP1Y.OneYFinite
universe u

private def preimageEnv {M : SetTheory.Structure.{u}} (C : ExpressionData M.Domain) (m P n Q J s₀ y₀ : M.Domain) : Env M 12 :=
  (((((((((((oneEnv C.omega).push C.zero).push C.one).push C.sequences).push C.expressions).push m).push P).push n).push Q).push J).push s₀).push y₀

/- 体内绑定（自内向外）：外层 c(0) y₀(1) s₀(2) J(3) Q(4) n(5) P(6) m(7) expr(8) seq(9) one(10) zero(11) omega(12)。 -/
private def preimageSchema : Project.UnarySchema 12 where
  body := .forallE (.imp
    (.disj (Project.Formula.extensionalEq (.bound 0) (.bound 3))
      (ancestorFormula ⟨.bound 13,.bound 12,.bound 11,.bound 10,.bound 9⟩ (.bound 8) (.bound 7) (.bound 0) (.bound 3)))
    (.imp (memPairFormula (.bound 4) (.bound 0) (.bound 1))
      (.forallE (.imp
        (ancestorFormula ⟨.bound 14,.bound 13,.bound 12,.bound 11,.bound 10⟩ (.bound 7) (.bound 6) (.bound 0) (.bound 2))
        (.disj
          (.existsE (.conj
            (ancestorFormula ⟨.bound 15,.bound 14,.bound 13,.bound 12,.bound 11⟩ (.bound 10) (.bound 9) (.bound 0) (.bound 2))
            (memPairFormula (.bound 6) (.bound 0) (.bound 1))))
          (.conj
            (.disj (Project.Formula.extensionalEq (.bound 3) (.bound 1))
              (ancestorFormula ⟨.bound 14,.bound 13,.bound 12,.bound 11,.bound 10⟩ (.bound 9) (.bound 8) (.bound 3) (.bound 1)))
            (.existsE (.conj (memPairFormula (.bound 6) (.bound 4) (.bound 0))
              (.disj (Project.Formula.extensionalEq (.bound 1) (.bound 0))
                (ancestorFormula ⟨.bound 15,.bound 14,.bound 13,.bound 12,.bound 11⟩ (.bound 8) (.bound 7) (.bound 1) (.bound 0)))))))))))
  freeClosed := by
    have h13 : (⟨.bound 13,.bound 12,.bound 11,.bound 10,.bound 9⟩ : ExpressionData (Project.Term 14)).Closed := ⟨rfl,rfl,rfl,rfl,rfl⟩
    have h14 : (⟨.bound 14,.bound 13,.bound 12,.bound 11,.bound 10⟩ : ExpressionData (Project.Term 15)).Closed := ⟨rfl,rfl,rfl,rfl,rfl⟩
    have h15 : (⟨.bound 15,.bound 14,.bound 13,.bound 12,.bound 11⟩ : ExpressionData (Project.Term 16)).Closed := ⟨rfl,rfl,rfl,rfl,rfl⟩
    have hA1 := ancestorFormula_freeClosed h13 (.bound 8) (.bound 7) (.bound 0) (.bound 3) rfl rfl rfl rfl
    have hA2 := ancestorFormula_freeClosed h14 (.bound 7) (.bound 6) (.bound 0) (.bound 2) rfl rfl rfl rfl
    have hA3 := ancestorFormula_freeClosed h15 (.bound 10) (.bound 9) (.bound 0) (.bound 2) rfl rfl rfl rfl
    have hA4 := ancestorFormula_freeClosed h14 (.bound 9) (.bound 8) (.bound 3) (.bound 1) rfl rfl rfl rfl
    have hA5 := ancestorFormula_freeClosed h15 (.bound 8) (.bound 7) (.bound 1) (.bound 0) rfl rfl rfl rfl
    simp [Definitional.Formula.FreeClosed,Project.Formula.extensionalEq,memPairFormula,codeFormula,pairFormula,
      Project.Formula.forallMem,Project.Formula.existsMem,hA1,hA2,hA3,hA4,hA5]

private theorem preimageSchema_iff {M : SetTheory.Structure.{u}} (he : Extensional M)
    (C : ExpressionData M.Domain) (m P n Q J s₀ y₀ c : M.Domain) :
    Project.Formula.satisfies ((preimageEnv C m P n Q J s₀ y₀).push c) preimageSchema.body ↔
      ∀ d, (d=s₀ ∨ Ancestor M C m P d s₀) → MemPair M J d c → ∀ a, Ancestor M C n Q a c →
        (∃ q, Ancestor M C m P q d ∧ MemPair M J q a) ∨
          ((y₀=d ∨ Ancestor M C m P y₀ d) ∧ ∃ w, MemPair M J y₀ w ∧ (a=w ∨ Ancestor M C n Q a w)) := by
  simp only [preimageSchema,Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_imp_iff,
    Project.Formula.satisfies_disj_iff,Project.Formula.satisfies_extensionalEq_iff_eq he,ancestorFormula_iff he,
    memPairFormula_iff he,Project.Formula.satisfies_exists_iff,Project.Formula.satisfies_conj_iff]
  rfl

/-- 目标祖先的前像：沿源链（停止列y₀之前）逐边反射，或落到y₀的像之上。 -/
theorem ancestor_preimage_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {m n P Q J s₀ y₀ c a : M.Domain}
    (hP : Forest M C.omega m P) (hQ : Forest M C.omega n Q)
    (hEdge : ∀ d u v, (d=s₀ ∨ Ancestor M C m P d s₀) → d≠y₀ → MemPair M J d u → MemPair M Q u v →
      ∃ p, MemPair M P d p ∧ MemPair M J p v)
    (hJS : MemPair M J s₀ c) (hAnc : Ancestor M C n Q a c) :
    (∃ q, Ancestor M C m P q s₀ ∧ MemPair M J q a) ∨
      ((y₀=s₀ ∨ Ancestor M C m P y₀ s₀) ∧ ∃ w, MemPair M J y₀ w ∧ (a=w ∨ Ancestor M C n Q a w)) := by
  have hAll := KP1Y.induction_d hM preimageSchema (preimageEnv C m P n Q J s₀ y₀) (by
    intro c ih
    apply (preimageSchema_iff hM.1 C m P n Q J s₀ y₀ c).mpr
    intro d hChain hDC a hAnc
    classical
    by_cases hdy : d=y₀
    · subst hdy
      exact Or.inr ⟨Or.inl rfl,c,hDC,Or.inr hAnc⟩
    · obtain ⟨p',hCP,hTail⟩ := ancestor_parent_cases_d hM hC hQ hAnc
      obtain ⟨p'',hDP,hJP⟩ := hEdge d c p' hChain hdy hDC hCP
      have hPD := ancestor_direct_d hM hC hP hDP
      have hChain' : p''=s₀ ∨ Ancestor M C m P p'' s₀ := by
        rcases hChain with he | hDS
        · exact Or.inr (he ▸ hPD)
        · exact Or.inr (ancestor_trans_d hM hC hP hPD hDS)
      rcases hTail with he | hAP
      · subst he
        exact Or.inl ⟨p'',hPD,hJP⟩
      · rcases (preimageSchema_iff hM.1 C m P n Q J s₀ y₀ p').mp (ih p' (hQ.left c p' hCP)) p'' hChain' hJP a hAP with
          ⟨q,hQP,hJQ⟩ | ⟨hY,w,hJW,hAW⟩
        · exact Or.inl ⟨q,ancestor_trans_d hM hC hP hQP hPD,hJQ⟩
        · refine Or.inr ⟨Or.inr ?_,w,hJW,hAW⟩
          rcases hY with he | hYP
          · exact he ▸ hPD
          · exact ancestor_trans_d hM hC hP hYP hPD)
  rcases (preimageSchema_iff hM.1 C m P n Q J s₀ y₀ c).mp (hAll c) s₀ (Or.inl rfl) hJS a hAnc with h | h
  · exact Or.inl h
  · exact Or.inr h

end KP1Y.OneYFinite.LowerCanon
