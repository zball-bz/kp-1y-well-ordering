import KP1Y.OneYNaturalMultiplication

/-! 内部自然数乘法的代数与顺序律，不使用宿主自然数归纳。 -/
namespace KP1Y.OneYFinite
open YesMetaZFC YesMetaZFC.SetTheory YesMetaZFC.SetTheory.Definitional
open KP1Y.Kuratowski KP1Y.Naturals KP1Y.Arithmetic
universe u

theorem natural_product_zero_right_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {a c : M.Domain} (hP : Product M a C.zero c) : c=C.zero :=
  hM.1.eq_of_same_members c C.zero (fun x => iff_of_false (hP.zero_value_d hM hC.zero_empty x) (hC.zero_empty x))

private def productZeroLeftSchema : Project.UnarySchema 1 where
  body := .forallE (.imp (mulFormula (.bound 2) (.bound 1) (.bound 0)) (Project.Formula.extensionalEq (.bound 0) (.bound 2)))
  freeClosed := by
    have h := mulFormula_freeClosed (n := 3) (.bound 2) (.bound 1) (.bound 0) rfl rfl rfl
    simp [Definitional.Formula.FreeClosed,h]

private theorem productZeroLeftSchema_iff {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory) (z b : M.Domain) :
    Project.Formula.satisfies ((oneEnv z).push b) productZeroLeftSchema.body ↔ ∀ c, Product M z b c → c=z := by
  simp only [productZeroLeftSchema,Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_imp_iff,
    mulFormula_iff hM,Project.Formula.satisfies_extensionalEq_iff_eq hM.1]
  rfl

theorem natural_product_zero_left_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {b c : M.Domain} (hb : M.mem b C.omega) (hP : Product M C.zero b c) : c=C.zero := by
  have hAll := natural_induction_d hM productZeroLeftSchema (oneEnv C.zero) hC.omega
    (by
      intro z hz
      apply (productZeroLeftSchema_iff hM C.zero z).mpr
      intro c hc
      exact hM.1.eq_of_same_members c C.zero (fun x => iff_of_false (hc.zero_value_d hM hz x) (hC.zero_empty x)))
    (by
      intro p hp ih b hs
      apply (productZeroLeftSchema_iff hM C.zero b).mpr
      intro c hc
      obtain ⟨d,_,hd⟩ := natural_product_exists_d hM hC hC.zero_nat hp
      have hd0 := (productZeroLeftSchema_iff hM C.zero p).mp ih d hd
      exact ((product_successor_d hM hs hd hc).zero_value_d hM hC.zero_empty).trans hd0)
  exact (productZeroLeftSchema_iff hM C.zero b).mp (hAll b hb) c hP

private def productLeftSuccessorSchema : Project.UnarySchema 2 where
  body := .forallE (.forallE (.imp
    (.conj (mulFormula (.bound 4) (.bound 2) (.bound 1)) (mulFormula (.bound 3) (.bound 2) (.bound 0)))
    (sumFormula (.bound 1) (.bound 2) (.bound 0))))
  freeClosed := by
    have h := mulFormula_freeClosed (n := 5) (.bound 4) (.bound 2) (.bound 1) rfl rfl rfl
    have h' := mulFormula_freeClosed (n := 5) (.bound 3) (.bound 2) (.bound 0) rfl rfl rfl
    have hs := sumFormula_freeClosed (n := 5) (.bound 1) (.bound 2) (.bound 0) rfl rfl rfl
    simp [Definitional.Formula.FreeClosed,h,h',hs]

private theorem productLeftSuccessorSchema_iff {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory) (a a' b : M.Domain) :
    Project.Formula.satisfies (((oneEnv a).push a').push b) productLeftSuccessorSchema.body ↔
      ∀ x y, Product M a b x → Product M a' b y → Sum M x b y := by
  simp only [productLeftSuccessorSchema,Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_imp_iff,
    Project.Formula.satisfies_conj_iff,mulFormula_iff hM,sumFormula_iff hM,and_imp]
  rfl

theorem natural_product_left_successor_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {a a' b x y : M.Domain}
    (ha : M.mem a C.omega) (hb : M.mem b C.omega) (hA : M.SuccessorOf a' a)
    (hX : Product M a b x) (hY : Product M a' b y) : Sum M x b y := by
  have ha' := natural_successor_mem_d hM hC ha hA
  have hAll := natural_induction_d hM productLeftSuccessorSchema ((oneEnv a).push a') hC.omega
    (by
      intro z hz
      apply (productLeftSuccessorSchema_iff hM a a' z).mpr
      intro x y hx hy
      have hxy := hM.1.eq_of_same_members x y (fun u => iff_of_false (hx.zero_value_d hM hz u) (hy.zero_value_d hM hz u))
      exact hxy ▸ sum_zero_d hM x hz)
    (by
      intro p hp ih b hB
      apply (productLeftSuccessorSchema_iff hM a a' b).mpr
      intro x y hx hy
      obtain ⟨u,hu,huP⟩ := natural_product_exists_d hM hC ha hp
      obtain ⟨v,hv,hvP⟩ := natural_product_exists_d hM hC ha' hp
      have hUV := (productLeftSuccessorSchema_iff hM a a' p).mp ih u v huP hvP
      have hUX := product_successor_d hM hB huP hx
      have hVY := product_successor_d hM hB hvP hy
      have hb' := natural_successor_mem_d hM hC hp hB
      have hxNat := natural_product_closed_d hM hC ha hb' hx
      obtain ⟨z,_,hXZ⟩ := natural_sum_exists_d hM hC.omega hxNat hp
      obtain ⟨t,_,hVT⟩ := natural_sum_exists_d hM hC.omega hv ha
      have hzt := natural_sum_shuffle_d hM hC ha hp hUX hXZ hUV hVT
      subst t
      obtain ⟨w,_,hXW⟩ := natural_sum_exists_d hM hC.omega hxNat hb'
      have hwz := sum_successor_d hM hB hXZ hXW
      have hyz := sum_successor_d hM hA hVT hVY
      exact (Structure.SuccessorOf.eq hM.1 hwz hyz) ▸ hXW)
  exact (productLeftSuccessorSchema_iff hM a a' b).mp (hAll b hb) x y hX hY

private def productCommutativeSchema : Project.UnarySchema 1 where
  body := .forallE (.imp (mulFormula (.bound 2) (.bound 1) (.bound 0)) (mulFormula (.bound 1) (.bound 2) (.bound 0)))
  freeClosed := by
    have h := mulFormula_freeClosed (n := 3) (.bound 2) (.bound 1) (.bound 0) rfl rfl rfl
    have h' := mulFormula_freeClosed (n := 3) (.bound 1) (.bound 2) (.bound 0) rfl rfl rfl
    simp [Definitional.Formula.FreeClosed,h,h']

private theorem productCommutativeSchema_iff {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory) (a b : M.Domain) :
    Project.Formula.satisfies ((oneEnv a).push b) productCommutativeSchema.body ↔
      ∀ c, Product M a b c → Product M b a c := by
  simp only [productCommutativeSchema,Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_imp_iff,mulFormula_iff hM]
  rfl

theorem natural_product_comm_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {a b c : M.Domain}
    (ha : M.mem a C.omega) (hb : M.mem b C.omega) (hP : Product M a b c) : Product M b a c := by
  have hAll := natural_induction_d hM productCommutativeSchema (oneEnv a) hC.omega
    (by
      intro z hz
      have hzz := hM.1.eq_of_same_members z C.zero (fun x => iff_of_false (hz x) (hC.zero_empty x))
      subst z
      apply (productCommutativeSchema_iff hM a C.zero).mpr
      intro c hc
      have hc0 := natural_product_zero_right_d hM hC hc
      subst c
      obtain ⟨d,_,hd⟩ := natural_product_exists_d hM hC hC.zero_nat ha
      exact natural_product_zero_left_d hM hC ha hd ▸ hd)
    (by
      intro p hp ih b hB
      apply (productCommutativeSchema_iff hM a b).mpr
      intro c hc
      obtain ⟨d,_,hd⟩ := natural_product_exists_d hM hC ha hp
      have hReverse := (productCommutativeSchema_iff hM a p).mp ih d hd
      obtain ⟨e,_,he⟩ := natural_product_exists_d hM hC (natural_successor_mem_d hM hC hp hB) ha
      have hDE := natural_product_left_successor_d hM hC hp ha hB hReverse he
      exact sum_unique_d hM hDE (product_successor_d hM hB hd hc) ▸ he)
  exact (productCommutativeSchema_iff hM a b).mp (hAll b hb) c hP

theorem natural_product_one_right_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {a c : M.Domain}
    (ha : M.mem a C.omega) (hP : Product M a C.one c) : c=a := by
  have hZero := product_zero_d hM ((omega_isOrdinal_d hM hC.omega).mem ha) hC.zero_empty
  exact natural_sum_left_zero_d hM hC ha (product_successor_d hM hC.one_succ hZero hP)

theorem natural_product_one_left_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {a c : M.Domain}
    (ha : M.mem a C.omega) (hP : Product M C.one a c) : c=a :=
  natural_product_one_right_d hM hC ha (natural_product_comm_d hM hC hC.one_nat ha hP)

theorem natural_product_strict_left_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {a a' b c c' : M.Domain}
    (ha : M.mem a C.omega) (ha' : M.mem a' C.omega) (hb : M.mem b C.omega) (hbPos : M.mem C.zero b)
    (hP : Product M a b c) (hP' : Product M a' b c') (haa' : M.mem a a') : M.mem c c' :=
  product_strict_right_d hM ⟨C.zero,hbPos⟩ (natural_product_comm_d hM hC ha hb hP)
    (natural_product_comm_d hM hC ha' hb hP') haa'

theorem natural_product_mono_left_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {a a' b c c' : M.Domain}
    (ha : M.mem a C.omega) (ha' : M.mem a' C.omega) (hb : M.mem b C.omega)
    (hP : Product M a b c) (hP' : Product M a' b c') (haa' : M.MemberSubset a a') : M.MemberSubset c c' := by
  classical
  by_cases hb0 : b=C.zero
  · subst b
    have hc0 := natural_product_zero_right_d hM hC hP
    have hc0' := natural_product_zero_right_d hM hC hP'
    subst c
    subst c'
    exact fun _ h => h
  · exact product_mono_right_d hM ⟨C.zero,(hC.zero_mem_iff hM hb).mpr hb0⟩
      (natural_product_comm_d hM hC ha hb hP) (natural_product_comm_d hM hC ha' hb hP') haa'

end KP1Y.OneYFinite
