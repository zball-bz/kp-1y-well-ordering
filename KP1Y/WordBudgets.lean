import KP1Y.WordBoundGrowth
import KP1Y.SigmaFunctionGraph
import KP1Y.NaturalNumbers

/-! 为所有内部自然数长度构造实际统一序数界和预算函数ω→C。 -/
namespace KP1Y.WordRank
open YesMetaZFC YesMetaZFC.SetTheory YesMetaZFC.SetTheory.Definitional
open KP1Y.Kuratowski KP1Y.Functions KP1Y.Naturals
universe u

def BudgetValue (M : SetTheory.Structure.{u}) (κ one n B : M.Domain) : Prop :=
  KP1Y.OrdinalIteration.Value growthMatrix ((oneEnv κ).push one) n B

structure Budget (M : SetTheory.Structure.{u}) (κ ω zero one C F : M.Domain) : Prop where
  omega : M.IsOmega ω
  stride : M.IsOrdinal κ
  zero_empty : ∀ x, ¬M.mem x zero
  zero_nat : M.mem zero ω
  one_successor : M.SuccessorOf one zero
  one_nat : M.mem one ω
  ceiling : M.IsOrdinal C
  graph : Graph M F ω C
  limit_value : BudgetValue M κ one ω C
  rows : ∀ n B, MemPair M F n B ↔ M.mem n ω ∧ BudgetValue M κ one n B

theorem budget_exists_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory) {κ ω : M.Domain}
    (hω : M.IsOmega ω) (hκ : M.IsOrdinal κ) : ∃ zero one C F, Budget M κ ω zero one C F := by
  obtain ⟨zero,hZero,hZeroNat⟩ := hω.1.1
  obtain ⟨one,hOne,hOneNat⟩ := hω.1.2 zero hZeroNat
  have hOneOrd := SetTheory.KP.successor_isOrdinal (KP1Y.models_weakKP hM) (Structure.IsOrdinal.of_no_members hZero) hOne
  let e : Env M 2 := (oneEnv κ).push one
  have hTotal := growth_total_d hM (KP1Y.OrdinalIteration.tailEnv e) hκ
  have hFun := growth_functional_d hM (KP1Y.OrdinalIteration.tailEnv e)
  obtain ⟨C,hC⟩ := KP1Y.OrdinalIteration.value_exists_d hM growthMatrix e hTotal hFun (omega_isOrdinal_d hM hω)
  have hCOrd := hC.isOrdinal_d hM growthMatrix e hOneOrd (growth_preserves_d hM _)
  have hBound (n B : M.Domain) (hn : M.mem n ω) (hB : BudgetValue M κ one n B) : M.mem B C :=
    KP1Y.OrdinalIteration.value_strict_d hM growthMatrix e hOneOrd hFun (growth_preserves_d hM _) (growth_strict_d hM _) hB hC hn
  obtain ⟨F,hF,hRows⟩ := sigma_function_graph_d hM (KP1Y.OrdinalIteration.valueMatrix growthMatrix) e ω C (by
    intro n hn
    obtain ⟨B,hB⟩ := KP1Y.OrdinalIteration.value_exists_d hM growthMatrix e hTotal hFun ((omega_isOrdinal_d hM hω).mem hn)
    obtain ⟨W,hW⟩ := hB
    exact ⟨B,W,(KP1Y.OrdinalIteration.valueMatrix_iff hM growthMatrix e n B W).mpr hW⟩) (by
    intro n hn B W hW
    exact hBound n B hn ⟨W,(KP1Y.OrdinalIteration.valueMatrix_iff hM growthMatrix e n B W).mp hW⟩) (by
    intro n _ B B' W W' hW hW'
    exact KP1Y.OrdinalIteration.value_unique_d hM growthMatrix e hFun
      ⟨W,(KP1Y.OrdinalIteration.valueMatrix_iff hM growthMatrix e n B W).mp hW⟩
      ⟨W',(KP1Y.OrdinalIteration.valueMatrix_iff hM growthMatrix e n B' W').mp hW'⟩)
  refine ⟨zero,one,C,F,hω,hκ,hZero,hZeroNat,hOne,hOneNat,hCOrd,hF,hC,?_⟩
  intro n B
  constructor
  · intro hAt
    obtain ⟨hn,_,W,hW⟩ := (hRows n B).mp hAt
    exact ⟨hn,W,(KP1Y.OrdinalIteration.valueMatrix_iff hM growthMatrix e n B W).mp hW⟩
  · rintro ⟨hn,W,hW⟩
    exact (hRows n B).mpr ⟨hn,hBound n B hn ⟨W,hW⟩,W,(KP1Y.OrdinalIteration.valueMatrix_iff hM growthMatrix e n B W).mpr hW⟩

theorem Budget.value_ordinal_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {κ ω zero one C F n B : M.Domain} (h : Budget M κ ω zero one C F) (hAt : MemPair M F n B) : M.IsOrdinal B :=
  (h.ceiling.mem (h.graph.bounds hM.1 hAt).2)

theorem Budget.initial_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {κ ω zero one C F : M.Domain} (h : Budget M κ ω zero one C F) : MemPair M F zero one := by
  obtain ⟨B,_,hAt⟩ := h.graph.total zero h.zero_nat
  have hB := ((h.rows zero B).mp hAt).2
  have hEq : B=one := hB.initial_d hM h.zero_empty
  exact hEq ▸ hAt

theorem Budget.next_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {κ ω zero one C F n m B D : M.Domain} (h : Budget M κ ω zero one C F) (hs : M.SuccessorOf m n)
    (hB : MemPair M F n B) (hD : MemPair M F m D) :
    ∃ W, KP1Y.OrdinalIteration.Next growthMatrix (oneEnv κ) B D W := by
  have hNext := KP1Y.OrdinalIteration.Value.next_d hM growthMatrix ((oneEnv κ).push one) (growth_functional_d hM _)
    hs ((h.rows n B).mp hB).2 ((h.rows m D).mp hD).2
  exact hNext

theorem Budget.product_bounded_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {κ ω zero one C F n m B D P : M.Domain} (h : Budget M κ ω zero one C F) (hs : M.SuccessorOf m n)
    (hB : MemPair M F n B) (hD : MemPair M F m D) (hP : KP1Y.Arithmetic.Product M κ B P) : M.MemberSubset P D := by
  obtain ⟨W,hNext⟩ := h.next_d hM hs hB hD
  exact growth_contains_product_d hM (oneEnv κ) hP hNext

end KP1Y.WordRank
