import KP1Y.OneYNaturalAdditionTable
import KP1Y.OneYNaturalDifferenceOrder

/-! 内部自然数加法的代数与序性质；每项归纳均使用实际对象公式。 -/
namespace KP1Y.OneYFinite
open YesMetaZFC YesMetaZFC.SetTheory YesMetaZFC.SetTheory.Definitional
open KP1Y.Kuratowski KP1Y.Naturals KP1Y.Arithmetic KP1Y.Bounded
universe u

private def zeroLeftSchema : Project.UnarySchema 1 where
  body := .forallE (.imp (sumFormula (.bound 2) (.bound 1) (.bound 0)) (Project.Formula.extensionalEq (.bound 0) (.bound 1)))
  freeClosed := by
    have h := sumFormula_freeClosed (n := 3) (.bound 2) (.bound 1) (.bound 0) rfl rfl rfl
    simp [Definitional.Formula.FreeClosed,h]

private theorem zeroLeftSchema_iff {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory) (z b : M.Domain) :
    Project.Formula.satisfies ((oneEnv z).push b) zeroLeftSchema.body ↔ ∀ c, Sum M z b c → c=b := by
  simp only [zeroLeftSchema,Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_imp_iff,
    sumFormula_iff hM,Project.Formula.satisfies_extensionalEq_iff_eq hM.1]
  rfl

theorem natural_sum_left_zero_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {b c : M.Domain} (hb : M.mem b C.omega) (hS : Sum M C.zero b c) : c=b := by
  have hAll := natural_induction_d hM zeroLeftSchema (oneEnv C.zero) hC.omega
    (by
      intro z hz
      apply (zeroLeftSchema_iff hM C.zero z).mpr
      intro c hc
      exact (hc.zero_value_d hM hz).trans (hM.1.eq_of_same_members C.zero z
        (fun x => iff_of_false (hC.zero_empty x) (hz x))))
    (by
      intro p hp ih b hbSucc
      apply (zeroLeftSchema_iff hM C.zero b).mpr
      intro c hc
      obtain ⟨d,hd⟩ := sum_exists_d hM C.zero ((omega_isOrdinal_d hM hC.omega).mem hp)
      have hdp := (zeroLeftSchema_iff hM C.zero p).mp ih d hd
      subst d
      exact Structure.SuccessorOf.eq hM.1 (sum_successor_d hM hbSucc hd hc) hbSucc)
  exact (zeroLeftSchema_iff hM C.zero b).mp (hAll b hb) c hS

private def leftSuccessorSchema : Project.UnarySchema 2 where
  body := .forallE (.forallE (.imp
    (.conj (sumFormula (.bound 4) (.bound 2) (.bound 1)) (sumFormula (.bound 3) (.bound 2) (.bound 0)))
    (successorFormula (.bound 0) (.bound 1))))
  freeClosed := by
    have h := sumFormula_freeClosed (n := 5) (.bound 4) (.bound 2) (.bound 1) rfl rfl rfl
    have h' := sumFormula_freeClosed (n := 5) (.bound 3) (.bound 2) (.bound 0) rfl rfl rfl
    simp [successorFormula,Project.Formula.forallMem,Definitional.Formula.FreeClosed,h,h']

private theorem leftSuccessorSchema_iff {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory) (a a' b : M.Domain) :
    Project.Formula.satisfies (((oneEnv a).push a').push b) leftSuccessorSchema.body ↔
      ∀ c c', Sum M a b c → Sum M a' b c' → M.SuccessorOf c' c := by
  simp only [leftSuccessorSchema,Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_imp_iff,
    Project.Formula.satisfies_conj_iff,sumFormula_iff hM,successorFormula_iff hM.1,and_imp]
  rfl

theorem natural_sum_left_successor_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {a a' b c c' : M.Domain}
    (hb : M.mem b C.omega) (hA : M.SuccessorOf a' a) (hS : Sum M a b c) (hS' : Sum M a' b c') : M.SuccessorOf c' c := by
  have hAll := natural_induction_d hM leftSuccessorSchema ((oneEnv a).push a') hC.omega
    (by
      intro z hz
      apply (leftSuccessorSchema_iff hM a a' z).mpr
      intro c c' hc hc'
      have hca := hc.zero_value_d hM hz
      have hca' := hc'.zero_value_d hM hz
      subst c
      subst c'
      exact hA)
    (by
      intro p hp ih b hB
      apply (leftSuccessorSchema_iff hM a a' b).mpr
      intro c c' hc hc'
      obtain ⟨d,hd⟩ := sum_exists_d hM a ((omega_isOrdinal_d hM hC.omega).mem hp)
      obtain ⟨d',hd'⟩ := sum_exists_d hM a' ((omega_isOrdinal_d hM hC.omega).mem hp)
      have hDD := (leftSuccessorSchema_iff hM a a' p).mp ih d d' hd hd'
      have hCD := sum_successor_d hM hB hd hc
      have hCD' := sum_successor_d hM hB hd' hc'
      have hEq := Structure.SuccessorOf.eq hM.1 hCD hDD
      subst c
      exact hCD')
  exact (leftSuccessorSchema_iff hM a a' b).mp (hAll b hb) c c' hS hS'

private def commutativeSchema : Project.UnarySchema 1 where
  body := .forallE (.imp (sumFormula (.bound 2) (.bound 1) (.bound 0)) (sumFormula (.bound 1) (.bound 2) (.bound 0)))
  freeClosed := by
    have h := sumFormula_freeClosed (n := 3) (.bound 2) (.bound 1) (.bound 0) rfl rfl rfl
    have h' := sumFormula_freeClosed (n := 3) (.bound 1) (.bound 2) (.bound 0) rfl rfl rfl
    simp [Definitional.Formula.FreeClosed,h,h']

private theorem commutativeSchema_iff {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory) (a b : M.Domain) :
    Project.Formula.satisfies ((oneEnv a).push b) commutativeSchema.body ↔ ∀ c, Sum M a b c → Sum M b a c := by
  simp only [commutativeSchema,Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_imp_iff,sumFormula_iff hM]
  rfl

theorem natural_sum_comm_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {a b c : M.Domain}
    (ha : M.mem a C.omega) (hb : M.mem b C.omega) (hS : Sum M a b c) : Sum M b a c := by
  have hAll := natural_induction_d hM commutativeSchema (oneEnv a) hC.omega
    (by
      intro z hz
      have hzz := hM.1.eq_of_same_members z C.zero (fun x => iff_of_false (hz x) (hC.zero_empty x))
      subst z
      apply (commutativeSchema_iff hM a C.zero).mpr
      intro c hc
      have hca := hc.zero_value_d hM hC.zero_empty
      subst c
      obtain ⟨d,hd⟩ := sum_exists_d hM C.zero ((omega_isOrdinal_d hM hC.omega).mem ha)
      exact natural_sum_left_zero_d hM hC ha hd ▸ hd)
    (by
      intro p hp ih b hB
      apply (commutativeSchema_iff hM a b).mpr
      intro c hc
      obtain ⟨d,hd⟩ := sum_exists_d hM a ((omega_isOrdinal_d hM hC.omega).mem hp)
      have hReverse := (commutativeSchema_iff hM a p).mp ih d hd
      obtain ⟨e,he⟩ := sum_exists_d hM b ((omega_isOrdinal_d hM hC.omega).mem ha)
      have hEd := natural_sum_left_successor_d hM hC ha hB hReverse he
      have hCd := sum_successor_d hM hB hd hc
      exact (Structure.SuccessorOf.eq hM.1 hEd hCd) ▸ he)
  exact (commutativeSchema_iff hM a b).mp (hAll b hb) c hS

private def associativeSchema : Project.UnarySchema 3 where
  body := .forallE (.forallE (.forallE (.imp
    (.conj (sumFormula (.bound 4) (.bound 3) (.bound 2))
      (.conj (sumFormula (.bound 5) (.bound 3) (.bound 1)) (sumFormula (.bound 6) (.bound 1) (.bound 0))))
    (Project.Formula.extensionalEq (.bound 2) (.bound 0)))))
  freeClosed := by
    have h := sumFormula_freeClosed (n := 7) (.bound 4) (.bound 3) (.bound 2) rfl rfl rfl
    have h' := sumFormula_freeClosed (n := 7) (.bound 5) (.bound 3) (.bound 1) rfl rfl rfl
    have h'' := sumFormula_freeClosed (n := 7) (.bound 6) (.bound 1) (.bound 0) rfl rfl rfl
    simp [Definitional.Formula.FreeClosed,h,h',h'']

private theorem associativeSchema_iff {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory) (a b ab c : M.Domain) :
    Project.Formula.satisfies ((((oneEnv a).push b).push ab).push c) associativeSchema.body ↔
      ∀ x y z, Sum M ab c x → Sum M b c y → Sum M a y z → x=z := by
  simp only [associativeSchema,Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_imp_iff,
    Project.Formula.satisfies_conj_iff,sumFormula_iff hM,Project.Formula.satisfies_extensionalEq_iff_eq hM.1,and_imp]
  rfl

theorem natural_sum_assoc_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {a b c ab x bc y : M.Domain}
    (hb : M.mem b C.omega) (hc : M.mem c C.omega)
    (hAB : Sum M a b ab) (hX : Sum M ab c x) (hBC : Sum M b c bc) (hY : Sum M a bc y) : x=y := by
  have hAll := natural_induction_d hM associativeSchema (((oneEnv a).push b).push ab) hC.omega
    (by
      intro zero hz
      apply (associativeSchema_iff hM a b ab zero).mpr
      intro x bc y hx hbc hy
      have hxab := hx.zero_value_d hM hz
      have hbcb := hbc.zero_value_d hM hz
      subst x
      subst bc
      exact sum_unique_d hM hAB hy)
    (by
      intro p hp ih c hSucc
      apply (associativeSchema_iff hM a b ab c).mpr
      intro x bc y hx hbc hy
      obtain ⟨u,hu⟩ := sum_exists_d hM ab ((omega_isOrdinal_d hM hC.omega).mem hp)
      obtain ⟨v,hv⟩ := sum_exists_d hM b ((omega_isOrdinal_d hM hC.omega).mem hp)
      obtain ⟨w,hw⟩ := sum_exists_d hM a (hv.isOrdinal_d hM ((omega_isOrdinal_d hM hC.omega).mem hb))
      have huw := (associativeSchema_iff hM a b ab p).mp ih u v w hu hv hw
      subst w
      have hXu := sum_successor_d hM hSucc hu hx
      have hBCv := sum_successor_d hM hSucc hv hbc
      exact Structure.SuccessorOf.eq hM.1 hXu (sum_successor_d hM hBCv hw hy))
  exact (associativeSchema_iff hM a b ab c).mp (hAll c hc) x bc y hX hBC hY

theorem natural_sum_shuffle_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {a b c ab ac x y : M.Domain}
    (hb : M.mem b C.omega) (hc : M.mem c C.omega)
    (hAB : Sum M a b ab) (hX : Sum M ab c x) (hAC : Sum M a c ac) (hY : Sum M ac b y) : x=y := by
  obtain ⟨bc,hbcω,hBC⟩ := natural_sum_exists_d hM hC.omega hb hc
  obtain ⟨z,hZ⟩ := sum_exists_d hM a ((omega_isOrdinal_d hM hC.omega).mem hbcω)
  have hXZ := natural_sum_assoc_d hM hC hb hc hAB hX hBC hZ
  have hYZ := natural_sum_assoc_d hM hC hc hb hAC hY (natural_sum_comm_d hM hC hb hc hBC) hZ
  exact hXZ.trans hYZ.symm

theorem natural_sum_strict_left_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {a a' b c c' : M.Domain}
    (ha : M.mem a C.omega) (ha' : M.mem a' C.omega) (hb : M.mem b C.omega)
    (hS : Sum M a b c) (hS' : Sum M a' b c') (haa' : M.mem a a') : M.mem c c' :=
  sum_strict_right_d hM ((omega_isOrdinal_d hM hC.omega).mem hb)
    (natural_sum_comm_d hM hC ha hb hS) (natural_sum_comm_d hM hC ha' hb hS') haa'

theorem natural_sum_mono_left_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {a a' b c c' : M.Domain}
    (ha : M.mem a C.omega) (ha' : M.mem a' C.omega) (hb : M.mem b C.omega)
    (hS : Sum M a b c) (hS' : Sum M a' b c') (haa' : M.MemberSubset a a') : M.MemberSubset c c' :=
  sum_mono_right_d hM ((omega_isOrdinal_d hM hC.omega).mem hb)
    (natural_sum_comm_d hM hC ha hb hS) (natural_sum_comm_d hM hC ha' hb hS') haa'

end KP1Y.OneYFinite
