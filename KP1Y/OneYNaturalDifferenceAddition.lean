import KP1Y.OneYNaturalAdditionFacts

/-! 有界截断差确实反解自然数加法，供复制区间与列地址覆盖使用。 -/
namespace KP1Y.OneYFinite
open YesMetaZFC YesMetaZFC.SetTheory YesMetaZFC.SetTheory.Definitional
open KP1Y.Kuratowski KP1Y.Naturals KP1Y.Arithmetic
universe u

private def differenceAdditionSchema : Project.UnarySchema 2 where
  body := Project.Formula.forallMem (.bound 2) (Project.Formula.forallMem (.bound 3)
    (.imp (.conj (differenceFormula (.bound 4) (.bound 3) (.bound 2) (.bound 1) (.bound 0))
      (.disj (Project.Formula.extensionalEq (.bound 1) (.bound 2)) (.mem (.bound 1) (.bound 2))))
      (sumFormula (.bound 1) (.bound 0) (.bound 2))))
  freeClosed := by
    have hd := differenceFormula_freeClosed (n := 5) (.bound 4) (.bound 3) (.bound 2) (.bound 1) (.bound 0) rfl rfl rfl rfl rfl
    have hs := sumFormula_freeClosed (n := 5) (.bound 1) (.bound 0) (.bound 2) rfl rfl rfl
    simp [Project.Formula.forallMem,Definitional.Formula.FreeClosed,hd,hs]

private theorem differenceAdditionSchema_iff {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory) (w z a : M.Domain) :
    Project.Formula.satisfies (((oneEnv w).push z).push a) differenceAdditionSchema.body ↔
      ∀ b, M.mem b w → ∀ d, M.mem d w → TruncatedDifference M w z a b d →
        (b=a ∨ M.mem b a) → Sum M b d a := by
  simp only [differenceAdditionSchema,Project.Formula.satisfies_forallMem_iff,Project.Formula.satisfies_imp_iff,
    Project.Formula.satisfies_conj_iff,differenceFormula_iff hM.1,Project.Formula.satisfies_disj_iff,
    Project.Formula.satisfies_extensionalEq_iff_eq hM.1,Project.Formula.satisfies_mem_iff,sumFormula_iff hM,and_imp]
  rfl

theorem truncated_difference_add_inverse_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {a b d : M.Domain}
    (hDiff : TruncatedDifference M C.omega C.zero a b d) (hba : b=a ∨ M.mem b a) : Sum M b d a := by
  have hAll := natural_induction_d hM differenceAdditionSchema ((oneEnv C.omega).push C.zero) hC.omega
    (by
      intro z hz
      have hzz := hM.1.eq_of_same_members z C.zero (fun x => iff_of_false (hz x) (hC.zero_empty x))
      subst z
      apply (differenceAdditionSchema_iff hM C.omega C.zero C.zero).mpr
      intro b _ d _ hD hLe
      have hb0 : b=C.zero := hLe.resolve_right (hC.zero_empty b)
      have hd0 := truncated_difference_left_zero_d hM hC hD
      subst b
      subst d
      exact sum_zero_d hM C.zero hC.zero_empty)
    (by
      intro a ha ih a' hA
      apply (differenceAdditionSchema_iff hM C.omega C.zero a').mpr
      intro b hb d hd hD hLe
      rcases natural_cases hM hC.omega hb with hEmpty | ⟨p,hp,hB⟩
      · have hb0 := hM.1.eq_of_same_members b C.zero (fun x => iff_of_false (hEmpty x) (hC.zero_empty x))
        subst b
        have hda := truncated_difference_unique_d hM hC hD
          (truncated_difference_zero_d hM hC (natural_successor_mem_d hM hC ha hA))
        subst d
        exact natural_sum_comm_d hM hC (natural_successor_mem_d hM hC ha hA) hC.zero_nat
          (sum_zero_d hM a' hC.zero_empty)
      · have hpa : p=a ∨ M.mem p a := by
          rcases hLe with hEq | hLess
          · subst b
            exact Or.inl (Structure.SuccessorOf.predecessor_eq hM.1 ((omega_isOrdinal_d hM hC.omega).mem hp) hB hA)
          · exact Or.inr ((natural_successor_lt_iff hM hC ha hp hA hB).mp hLess)
        obtain ⟨e,_,hE⟩ := truncated_difference_exists_d hM hC ha hp
        have hde := truncated_difference_cancel_successors_d hM hC hA hB hD hE
        subst e
        have hSum := (differenceAdditionSchema_iff hM C.omega C.zero a).mp ih p hp d hd hE hpa
        obtain ⟨x,_,hx⟩ := natural_sum_exists_d hM hC.omega hb hd
        have hSucc := natural_sum_left_successor_d hM hC hd hB hSum hx
        exact (Structure.SuccessorOf.eq hM.1 hSucc hA) ▸ hx)
  exact (differenceAdditionSchema_iff hM C.omega C.zero a).mp (hAll a hDiff.1) b hDiff.2.1 d
    (truncated_difference_natural hM.1 hDiff) hDiff hba

theorem natural_sum_cancel_left_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {a b c d : M.Domain}
    (ha : M.mem a C.omega) (hb : M.mem b C.omega) (hc : M.mem c C.omega)
    (hB : Sum M a b d) (hC' : Sum M a c d) : b=c := by
  have hOrd := omega_isOrdinal_d hM hC.omega
  rcases hOrd.wellOrder.linear.compare b hb c hc with he | hbc | hcb
  · exact hM.1.eq_of_same_members b c he
  · exact False.elim (SetTheory.KP.mem_irrefl_d (KP1Y.models_weakKP hM) d
      (sum_strict_right_d hM (hOrd.mem ha) hB hC' hbc))
  · exact False.elim (SetTheory.KP.mem_irrefl_d (KP1Y.models_weakKP hM) d
      (sum_strict_right_d hM (hOrd.mem ha) hC' hB hcb))

theorem truncated_difference_of_sum_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {a b d : M.Domain}
    (hb : M.mem b C.omega) (hd : M.mem d C.omega) (hSum : Sum M b d a) :
    TruncatedDifference M C.omega C.zero a b d := by
  have ha := natural_sum_closed_d hM hC.omega hb hd hSum
  have hOrd := omega_isOrdinal_d hM hC.omega
  have hba := ordinal_subset_cases_d hM (hOrd.mem hb) (hOrd.mem ha) (sum_base_subset_d hM (hOrd.mem hb) hSum)
  obtain ⟨e,he,hE⟩ := truncated_difference_exists_d hM hC ha hb
  have hInv := truncated_difference_add_inverse_d hM hC hE hba
  exact natural_sum_cancel_left_d hM hC hb he hd hInv hSum ▸ hE

end KP1Y.OneYFinite
