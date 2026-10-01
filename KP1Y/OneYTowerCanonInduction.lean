import KP1Y.OneYNaturalDifferenceAddition

/-! 任意(非Δ₀)对象公式的有界反向归纳：对内部间隔 j 作对象自然数归纳，
谓词为 ∀x∈ω (x+j=top → φ(x))，加法用实际加法表的Δ₀读取。不使用宿主归纳。 -/
namespace KP1Y.OneYFinite.TowerCanon
open YesMetaZFC YesMetaZFC.SetTheory YesMetaZFC.SetTheory.Definitional
open KP1Y.Kuratowski KP1Y.Functions KP1Y.Naturals KP1Y.Bounded
universe u

/-- φ 的元素位与参数位嵌入 ∀x 之下：x在0，j,top,Plus,Pairs,ω占1..5，参数整体后移。 -/
def gapSlots {n : Nat} : Fin (n+1) → Fin (n+6) :=
  Fin.cases 0 (fun i => ⟨i.val+6, by omega⟩)

def gapSchema {n : Nat} (φ : Project.UnarySchema n) : Project.UnarySchema (n+4) where
  body := .forallE (.imp (.mem (.bound 0) (.bound 5))
    (.imp (addAtFormula (.bound 4) (.bound 3) (.bound 0) (.bound 1) (.bound 2)) (φ.body.rename gapSlots)))
  freeClosed := by
    simp [Definitional.Formula.FreeClosed,addAtFormula,codeFormula,pairFormula,memPairFormula,
      Project.Formula.forallMem,Project.Formula.existsMem,φ.freeClosed]

private theorem gapSlots_env {M : SetTheory.Structure.{u}} {n : Nat} (env : Env M n) (w Pairs Plus top j x : M.Domain) :
    ((((((env.push w).push Pairs).push Plus).push top).push j).push x).reindex gapSlots = env.push x := by
  rw [Env.mk.injEq]
  constructor
  · funext i
    refine Fin.cases ?_ (fun i => ?_) i <;> rfl
  · rfl

theorem gapSchema_iff {M : SetTheory.Structure.{u}} (he : Extensional M) {n : Nat} (φ : Project.UnarySchema n)
    (env : Env M n) (w Pairs Plus top j : M.Domain) :
    Project.Formula.satisfies (((((env.push w).push Pairs).push Plus).push top).push j) (gapSchema φ).body ↔
      ∀ x, M.mem x w → AddAt M Pairs Plus x j top → Project.Formula.satisfies (env.push x) φ.body := by
  simp only [gapSchema,Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_imp_iff,
    Project.Formula.satisfies_mem_iff,addAtFormula_iff he,Project.Formula.satisfies_rename,gapSlots_env]
  rfl

/-- 有界反向归纳（任意项目公式）。顶点成立，且每步由后继推回前驱，则 ≤top 全部成立。 -/
theorem backward_induction_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {Pairs Plus : M.Domain} (hPlus : AdditionTable M C Pairs Plus)
    {n : Nat} (φ : Project.UnarySchema n) (env : Env M n) {top : M.Domain} (hTopNat : M.mem top C.omega)
    (hTop : Project.Formula.satisfies (env.push top) φ.body)
    (hStep : ∀ p, M.mem p top → ∀ q, M.SuccessorOf q p →
      Project.Formula.satisfies (env.push q) φ.body → Project.Formula.satisfies (env.push p) φ.body) :
    ∀ x, (x=top ∨ M.mem x top) → Project.Formula.satisfies (env.push x) φ.body := by
  have hw := omega_isOrdinal_d hM hC.omega
  have hAll := natural_induction_d hM (gapSchema φ) ((((env.push C.omega).push Pairs).push Plus).push top) hC.omega
    (fun z hz => (gapSchema_iff hM.1 φ env C.omega Pairs Plus top z).mpr (by
      intro x hx hAdd
      have hzz := hM.1.eq_of_same_members z C.zero (fun a => iff_of_false (hz a) (hC.zero_empty a))
      subst z
      have hSum := (hPlus.add_iff_sum hM hx hC.zero_nat).mp hAdd
      have hxt := hSum.zero_value_d hM hC.zero_empty
      exact hxt ▸ hTop))
    (fun j hj ih j' hs => (gapSchema_iff hM.1 φ env C.omega Pairs Plus top j').mpr (by
      intro x hx hAdd
      have hj' := natural_successor_mem_d hM hC hj hs
      obtain ⟨x',hx',hx'ω⟩ := hC.omega.1.2 x hx
      have hSum := (hPlus.add_iff_sum hM hx hj').mp hAdd
      obtain ⟨c,hc,hSumC⟩ := natural_sum_exists_d hM hC.omega hx hj
      have hTopSucc := KP1Y.Arithmetic.sum_successor_d hM hs hSumC hSum
      obtain ⟨c',_,hSumC'⟩ := natural_sum_exists_d hM hC.omega hx'ω hj
      have hTopSucc' := natural_sum_left_successor_d hM hC hj hx' hSumC hSumC'
      have hcc := Structure.SuccessorOf.eq hM.1 hTopSucc' hTopSucc
      subst c'
      have hNext := (gapSchema_iff hM.1 φ env C.omega Pairs Plus top j).mp ih x' hx'ω
        ((hPlus.add_iff_sum hM hx'ω hj).mpr hSumC')
      have hxTop : M.mem x top := KP1Y.Arithmetic.sum_base_mem_d hM (hw.mem hx) hSum ⟨j,hs.predecessor_mem⟩
      exact hStep x hxTop x' hx' hNext))
  intro x hx
  have hxNat : M.mem x C.omega := hx.elim (fun he => he ▸ hTopNat) (fun h => hw.transitive top hTopNat x h)
  obtain ⟨j,hj,hDiff⟩ := truncated_difference_exists_d hM hC hTopNat hxNat
  have hSum := truncated_difference_add_inverse_d hM hC hDiff (hx.imp id id)
  exact (gapSchema_iff hM.1 φ env C.omega Pairs Plus top j).mp (hAll j hj) x hxNat ((hPlus.add_iff_sum hM hxNat hj).mpr hSum)

end KP1Y.OneYFinite.TowerCanon
