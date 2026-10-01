import KP1Y.OneYNaturalMultiplicationLaws

/-! 内部自然数乘法的分配与结合律。 -/
namespace KP1Y.OneYFinite
open YesMetaZFC YesMetaZFC.SetTheory YesMetaZFC.SetTheory.Definitional
open KP1Y.Kuratowski KP1Y.Naturals KP1Y.Arithmetic
universe u

private def distributivitySchema : Project.UnarySchema 3 where
  body := .forallE (.forallE (.forallE (.imp
    (.conj (sumFormula (.bound 5) (.bound 3) (.bound 2))
      (.conj (mulFormula (.bound 6) (.bound 3) (.bound 1)) (mulFormula (.bound 6) (.bound 2) (.bound 0))))
    (sumFormula (.bound 4) (.bound 1) (.bound 0)))))
  freeClosed := by
    have h1 := sumFormula_freeClosed (n := 7) (.bound 5) (.bound 3) (.bound 2) rfl rfl rfl
    have h2 := mulFormula_freeClosed (n := 7) (.bound 6) (.bound 3) (.bound 1) rfl rfl rfl
    have h3 := mulFormula_freeClosed (n := 7) (.bound 6) (.bound 2) (.bound 0) rfl rfl rfl
    have h4 := sumFormula_freeClosed (n := 7) (.bound 4) (.bound 1) (.bound 0) rfl rfl rfl
    simp [Definitional.Formula.FreeClosed,h1,h2,h3,h4]

private theorem distributivitySchema_iff {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory) (a b ab c : M.Domain) :
    Project.Formula.satisfies ((((oneEnv a).push b).push ab).push c) distributivitySchema.body ↔
      ∀ bc ac x, Sum M b c bc → Product M a c ac → Product M a bc x → Sum M ab ac x := by
  simp only [distributivitySchema,Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_imp_iff,
    Project.Formula.satisfies_conj_iff,sumFormula_iff hM,mulFormula_iff hM,and_imp]
  rfl

theorem natural_product_distrib_left_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {a b c ab ac bc x : M.Domain}
    (ha : M.mem a C.omega) (hb : M.mem b C.omega) (hc : M.mem c C.omega)
    (hAB : Product M a b ab) (hBC : Sum M b c bc) (hAC : Product M a c ac) (hX : Product M a bc x) : Sum M ab ac x := by
  have hab := natural_product_closed_d hM hC ha hb hAB
  have hAll := natural_induction_d hM distributivitySchema (((oneEnv a).push b).push ab) hC.omega
    (by
      intro z hz
      apply (distributivitySchema_iff hM a b ab z).mpr
      intro bc ac x hbc hac hx
      have hbcb := hbc.zero_value_d hM hz
      subst bc
      have hxab := product_unique_d hM hx hAB
      have hac0 := hM.1.eq_of_same_members ac C.zero (fun u => iff_of_false (hac.zero_value_d hM hz u) (hC.zero_empty u))
      subst x
      subst ac
      exact sum_zero_d hM ab hC.zero_empty)
    (by
      intro p hp ih c hSucc
      apply (distributivitySchema_iff hM a b ab c).mpr
      intro bc ac x hbc hac hx
      obtain ⟨bp,hbp,hBP⟩ := natural_sum_exists_d hM hC.omega hb hp
      obtain ⟨ap,hap,hAP⟩ := natural_product_exists_d hM hC ha hp
      obtain ⟨u,_,hU⟩ := natural_product_exists_d hM hC ha hbp
      have hOld := (distributivitySchema_iff hM a b ab p).mp ih bp ap u hBP hAP hU
      have hBPSucc := sum_successor_d hM hSucc hBP hbc
      have hAddA := product_successor_d hM hSucc hAP hac
      have hAddX := product_successor_d hM hBPSucc hU hx
      have hcNat := natural_successor_mem_d hM hC hp hSucc
      have hacNat := natural_product_closed_d hM hC ha hcNat hac
      obtain ⟨y,_,hY⟩ := natural_sum_exists_d hM hC.omega hab hacNat
      exact (natural_sum_assoc_d hM hC hap ha hOld hAddX hAddA hY).symm ▸ hY)
  exact (distributivitySchema_iff hM a b ab c).mp (hAll c hc) bc ac x hBC hAC hX

theorem natural_product_distrib_right_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {a b c ab ac bc x : M.Domain}
    (ha : M.mem a C.omega) (hb : M.mem b C.omega) (hc : M.mem c C.omega)
    (hAB : Sum M a b ab) (hAC : Product M a c ac) (hBC : Product M b c bc) (hX : Product M ab c x) : Sum M ac bc x := by
  have hab := natural_sum_closed_d hM hC.omega ha hb hAB
  exact natural_product_distrib_left_d hM hC hc ha hb (natural_product_comm_d hM hC ha hc hAC) hAB
    (natural_product_comm_d hM hC hb hc hBC) (natural_product_comm_d hM hC hab hc hX)

private def productAssociativeSchema : Project.UnarySchema 3 where
  body := .forallE (.forallE (.forallE (.imp
    (.conj (mulFormula (.bound 5) (.bound 3) (.bound 2))
      (.conj (mulFormula (.bound 4) (.bound 3) (.bound 1)) (mulFormula (.bound 6) (.bound 2) (.bound 0))))
    (Project.Formula.extensionalEq (.bound 1) (.bound 0)))))
  freeClosed := by
    have h1 := mulFormula_freeClosed (n := 7) (.bound 5) (.bound 3) (.bound 2) rfl rfl rfl
    have h2 := mulFormula_freeClosed (n := 7) (.bound 4) (.bound 3) (.bound 1) rfl rfl rfl
    have h3 := mulFormula_freeClosed (n := 7) (.bound 6) (.bound 2) (.bound 0) rfl rfl rfl
    simp [Definitional.Formula.FreeClosed,h1,h2,h3]

private theorem productAssociativeSchema_iff {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory) (a b ab c : M.Domain) :
    Project.Formula.satisfies ((((oneEnv a).push b).push ab).push c) productAssociativeSchema.body ↔
      ∀ bc x y, Product M b c bc → Product M ab c x → Product M a bc y → x=y := by
  simp only [productAssociativeSchema,Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_imp_iff,
    Project.Formula.satisfies_conj_iff,mulFormula_iff hM,Project.Formula.satisfies_extensionalEq_iff_eq hM.1,and_imp]
  rfl

theorem natural_product_assoc_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {a b c ab bc x y : M.Domain}
    (ha : M.mem a C.omega) (hb : M.mem b C.omega) (hc : M.mem c C.omega)
    (hAB : Product M a b ab) (hBC : Product M b c bc) (hX : Product M ab c x) (hY : Product M a bc y) : x=y := by
  have hab := natural_product_closed_d hM hC ha hb hAB
  have hAll := natural_induction_d hM productAssociativeSchema (((oneEnv a).push b).push ab) hC.omega
    (by
      intro z hz
      apply (productAssociativeSchema_iff hM a b ab z).mpr
      intro bc x y hbc hx hy
      have hbc0 := hM.1.eq_of_same_members bc C.zero (fun u => iff_of_false (hbc.zero_value_d hM hz u) (hC.zero_empty u))
      subst bc
      have hy0 := natural_product_zero_right_d hM hC hy
      have hx0 := hM.1.eq_of_same_members x C.zero (fun u => iff_of_false (hx.zero_value_d hM hz u) (hC.zero_empty u))
      exact hx0.trans hy0.symm)
    (by
      intro p hp ih c hSucc
      apply (productAssociativeSchema_iff hM a b ab c).mpr
      intro bc x y hbc hx hy
      obtain ⟨u,_,hU⟩ := natural_product_exists_d hM hC hab hp
      obtain ⟨v,hv,hV⟩ := natural_product_exists_d hM hC hb hp
      obtain ⟨w,_,hW⟩ := natural_product_exists_d hM hC ha hv
      have huw := (productAssociativeSchema_iff hM a b ab p).mp ih v u w hV hU hW
      subst w
      have hXSum := product_successor_d hM hSucc hU hx
      have hBCSum := product_successor_d hM hSucc hV hbc
      have hYSum := natural_product_distrib_left_d hM hC ha hv hb hW hBCSum hAB hy
      exact sum_unique_d hM hXSum hYSum)
  exact (productAssociativeSchema_iff hM a b ab c).mp (hAll c hc) bc x y hBC hX hY

end KP1Y.OneYFinite
