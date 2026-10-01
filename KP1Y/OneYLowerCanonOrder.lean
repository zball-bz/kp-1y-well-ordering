import KP1Y.OneYLowerCanonPaths

/-! 内部ω上的小序工具（只用于Lower规范性证明；全部对象为内部自然数）。 -/
namespace KP1Y.OneYFinite.LowerCanon
open YesMetaZFC YesMetaZFC.SetTheory YesMetaZFC.SetTheory.Definitional
open KP1Y.Kuratowski KP1Y.Functions KP1Y.Naturals KP1Y.Bounded KP1Y.Arithmetic
open KP1Y.OneYFinite
universe u

theorem nat_irrefl {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory) (a : M.Domain) : ¬M.mem a a :=
  SetTheory.KP.mem_irrefl_d (KP1Y.models_weakKP hM) a

theorem nat_not_lt_of_le {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {a b : M.Domain} (hb : M.mem b C.omega)
    (hab : a=b ∨ M.mem a b) : ¬M.mem b a := by
  intro hba
  rcases hab with he | hab
  · exact nat_irrefl hM b (he ▸ hba)
  · exact nat_irrefl hM b (((omega_isOrdinal_d hM hC.omega).mem hb).transitive a hab b hba)

theorem nat_le_of_not_lt {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {a b : M.Domain} (ha : M.mem a C.omega) (hb : M.mem b C.omega)
    (hNot : ¬M.mem a b) : b=a ∨ M.mem b a := by
  rcases (omega_isOrdinal_d hM hC.omega).wellOrder.linear.compare a ha b hb with he | hlt | hgt
  · exact Or.inl (hM.1.eq_of_same_members a b he).symm
  · exact False.elim (hNot hlt)
  · exact Or.inr hgt

theorem nat_le_trans {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {a b c : M.Domain} (hc : M.mem c C.omega)
    (hab : a=b ∨ M.mem a b) (hbc : b=c ∨ M.mem b c) : a=c ∨ M.mem a c := by
  rcases hab with he | hab
  · exact he ▸ hbc
  · rcases hbc with he | hbc
    · exact Or.inr (he ▸ hab)
    · exact Or.inr (((omega_isOrdinal_d hM hC.omega).mem hc).transitive b hbc a hab)

theorem nat_lt_of_le_of_lt {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {a b c : M.Domain} (hc : M.mem c C.omega)
    (hab : a=b ∨ M.mem a b) (hbc : M.mem b c) : M.mem a c := by
  rcases hab with he | hab
  · exact he ▸ hbc
  · exact ((omega_isOrdinal_d hM hC.omega).mem hc).transitive b hbc a hab

theorem nat_lt_of_lt_of_le {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {a b c : M.Domain} (hc : M.mem c C.omega)
    (hab : M.mem a b) (hbc : b=c ∨ M.mem b c) : M.mem a c := by
  rcases hbc with he | hbc
  · exact he ▸ hab
  · exact ((omega_isOrdinal_d hM hC.omega).mem hc).transitive b hbc a hab

theorem nat_lt_trans {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {a b c : M.Domain} (hc : M.mem c C.omega)
    (hab : M.mem a b) (hbc : M.mem b c) : M.mem a c :=
  ((omega_isOrdinal_d hM hC.omega).mem hc).transitive b hbc a hab

theorem nat_mem_omega {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {a b : M.Domain} (hb : M.mem b C.omega) (hab : M.mem a b) :
    M.mem a C.omega :=
  (omega_isOrdinal_d hM hC.omega).transitive b hb a hab

/-- succ r ≤ q 当且仅当 r<q。 -/
theorem nat_succ_le_of_lt {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {r s q : M.Domain}
    (hr : M.mem r C.omega) (hq : M.mem q C.omega) (hs : M.SuccessorOf s r) (hrq : M.mem r q) : s=q ∨ M.mem s q := by
  have hw := omega_isOrdinal_d hM hC.omega
  apply ordinal_subset_cases_d hM (hw.mem (natural_successor_mem_d hM hC hr hs)) (hw.mem hq)
  intro x hx
  rcases (hs x).mp hx with hxr | he
  · exact (hw.mem hq).transitive r hrq x hxr
  · exact (hM.1.eq_of_same_members x r he).symm ▸ hrq

theorem nat_lt_of_succ_le {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {r s q : M.Domain} (hq : M.mem q C.omega)
    (hs : M.SuccessorOf s r) (hsq : s=q ∨ M.mem s q) : M.mem r q :=
  nat_lt_of_lt_of_le hM hC hq hs.predecessor_mem hsq

/-- x<succ r 当且仅当 x≤r。 -/
theorem nat_lt_succ_iff {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory) {r s x : M.Domain}
    (hs : M.SuccessorOf s r) : M.mem x s ↔ (x=r ∨ M.mem x r) := by
  constructor
  · intro hx
    rcases (hs x).mp hx with hlt | he
    · exact Or.inr hlt
    · exact Or.inl (hM.1.eq_of_same_members x r he)
  · rintro (he | hlt)
    · exact he ▸ hs.predecessor_mem
    · exact (hs x).mpr (Or.inl hlt)

/-- 内部自然数三歧，以 ≤ 与 > 两类返回。 -/
theorem nat_le_or_lt {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {a b : M.Domain} (ha : M.mem a C.omega) (hb : M.mem b C.omega) :
    (a=b ∨ M.mem a b) ∨ M.mem b a := by
  rcases (omega_isOrdinal_d hM hC.omega).wellOrder.linear.compare a ha b hb with he | hlt | hgt
  · exact Or.inl (Or.inl (hM.1.eq_of_same_members a b he))
  · exact Or.inl (Or.inr hlt)
  · exact Or.inr hgt

/-- 加法右侧固定基的单调：b≤b' 则 a+b≤a+b'。 -/
theorem nat_sum_le_right {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {a b b' s s' : M.Domain}
    (ha : M.mem a C.omega) (hS : Sum M a b s) (hS' : Sum M a b' s') (hbb : b=b' ∨ M.mem b b') : s=s' ∨ M.mem s s' := by
  rcases hbb with he | hlt
  · subst b'
    exact Or.inl (sum_unique_d hM hS hS')
  · exact Or.inr (sum_strict_right_d hM ((omega_isOrdinal_d hM hC.omega).mem ha) hS hS' hlt)

/-- 加法左侧单调（交换律）。 -/
theorem nat_sum_le_left {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {a a' b s s' : M.Domain}
    (ha : M.mem a C.omega) (ha' : M.mem a' C.omega) (hb : M.mem b C.omega)
    (hS : Sum M a b s) (hS' : Sum M a' b s') (haa : a=a' ∨ M.mem a a') : s=s' ∨ M.mem s s' :=
  nat_sum_le_right hM hC hb (natural_sum_comm_d hM hC ha hb hS) (natural_sum_comm_d hM hC ha' hb hS') haa

/-- 加数不超过和。 -/
theorem nat_le_sum_right {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {a b s : M.Domain}
    (ha : M.mem a C.omega) (hb : M.mem b C.omega) (hS : Sum M a b s) : b=s ∨ M.mem b s := by
  have hw := omega_isOrdinal_d hM hC.omega
  have hs := natural_sum_closed_d hM hC.omega ha hb hS
  exact ordinal_subset_cases_d hM (hw.mem hb) (hw.mem hs)
    (sum_base_subset_d hM (hw.mem hb) (natural_sum_comm_d hM hC ha hb hS))

end KP1Y.OneYFinite.LowerCanon
