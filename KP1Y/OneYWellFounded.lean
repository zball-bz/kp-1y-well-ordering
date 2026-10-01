import KP1Y.OneYTheoremData
import KP1Y.OneYRankStatement

/-! M04：把共享实际秩见证 `RankWitness` 接到通用 `RankedDynamics`。
关系 t≺s 为 t≠s 且 t=E_N(s) 对某个内部 N∈ω，读取实际 EN 图；它被分离为实际集合 R⊆E×E。
得到：每个非空内部 X⊆E 有 ≺-极小元；每条集合编码的 ω 展开轨迹在某内部时刻到达 ∅。
最小元只取内部集合的序数像最小值，不使用宿主良基、标准 ω 或依赖选择。 -/
namespace KP1Y.OneYTheorem
open YesMetaZFC YesMetaZFC.SetTheory YesMetaZFC.SetTheory.Definitional
open KP1Y.Kuratowski KP1Y.Functions KP1Y.Naturals KP1Y.Bounded
open KP1Y.OneYFinite KP1Y.OneYRank
universe u

/-- t≺s 的参数化形式：ω、Keys、EN 为实际集合。 -/
def PrecedesIn (M : SetTheory.Structure.{u}) (w Keys EN t s : M.Domain) : Prop :=
  t≠s ∧ ∃ N, M.mem N w ∧ KP1Y.Dynamics.Expansion M Keys EN s N t

/-- 文稿的 t≺s：t≠s 且 t=E_N(s)，N<ω。 -/
abbrev Precedes (M : SetTheory.Structure.{u}) (D : TheoremData M.Domain) (t s : M.Domain) : Prop :=
  PrecedesIn M D.expr.omega D.keys D.expansion t s

def precedesFormula {n : Nat} (w Keys EN t s : Project.Term n) : Project.Formula 1 n :=
  .conj (.neg (Project.Formula.extensionalEq t s))
    (Project.Formula.existsMem w (KP1Y.Dynamics.expansionFormula Keys.weaken EN.weaken s.weaken (.bound 0) t.weaken))

theorem precedesFormula_delta0 {n : Nat} (w Keys EN t s : Project.Term n) :
    (precedesFormula w Keys EN t s).IsDelta0 :=
  .conj (.neg (.atom _ _ _)) (.existsMem _ (KP1Y.Dynamics.expansionFormula_delta0 _ _ _ _ _))

theorem precedesFormula_freeClosed {n : Nat} (w Keys EN t s : Project.Term n) (hw : w.freeSupport=[])
    (hK : Keys.freeSupport=[]) (hEN : EN.freeSupport=[]) (ht : t.freeSupport=[]) (hs : s.freeSupport=[]) :
    (precedesFormula w Keys EN t s).FreeClosed := by
  simp [precedesFormula,KP1Y.Dynamics.expansionFormula,memPairFormula,codeFormula,pairFormula,
    Project.Formula.forallMem,Project.Formula.existsMem,Definitional.Formula.FreeClosed,hw,hK,hEN,ht,hs]

theorem precedesFormula_iff {M : SetTheory.Structure.{u}} (he : Extensional M) {n : Nat} (e : Env M n)
    (w Keys EN t s : Project.Term n) :
    Project.Formula.satisfies e (precedesFormula w Keys EN t s) ↔
      PrecedesIn M (w.eval e) (Keys.eval e) (EN.eval e) (t.eval e) (s.eval e) := by
  simp only [precedesFormula,Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_neg_iff,
    Project.Formula.satisfies_extensionalEq_iff_eq he,Project.Formula.satisfies_existsMem_iff,
    KP1Y.Dynamics.expansionFormula_iff he,Term.eval_weaken]
  rfl

/-- 实际集合 R：MemPair R t s 恰当 t,s∈E 且 t≺s。 -/
structure PrecedenceRelation (M : SetTheory.Structure.{u}) (D : TheoremData M.Domain) (R : M.Domain) : Prop where
  support : RelationSupport M R D.expr.expressions D.expr.expressions
  rows : ∀ t s, MemPair M R t s ↔ M.mem t D.expr.expressions ∧ M.mem s D.expr.expressions ∧ Precedes M D t s

private def precedesSchema : Project.Delta0BinarySchema 3 where
  body := precedesFormula (.bound 4) (.bound 3) (.bound 2) (.bound 1) (.bound 0)
  freeClosed := precedesFormula_freeClosed _ _ _ _ _ rfl rfl rfl rfl rfl
  delta0 := precedesFormula_delta0 _ _ _ _ _

theorem precedence_relation_exists_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    (D : TheoremData M.Domain) : ∃ R, PrecedenceRelation M D R := by
  obtain ⟨R,hSupport,hRaw⟩ := relation_comprehension_d hM precedesSchema
    (((oneEnv D.expr.omega).push D.keys).push D.expansion) D.expr.expressions D.expr.expressions
  refine ⟨R,hSupport,fun t s => ?_⟩
  rw [hRaw t s]
  exact and_congr Iff.rfl (and_congr Iff.rfl (precedesFormula_iff hM.1 _ _ _ _ _ _))

theorem PrecedenceRelation.unique {M : SetTheory.Structure.{u}} (he : Extensional M) {D : TheoremData M.Domain}
    {R R' : M.Domain} (h : PrecedenceRelation M D R) (h' : PrecedenceRelation M D R') : R=R' :=
  relation_ext he h.support h'.support (fun t s => (h.rows t s).trans (h'.rows t s).symm)

/-- 空表达式只展开到自身。 -/
theorem TheoremData.Valid.empty_step_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {D : TheoremData M.Domain} (hD : D.Valid M) {N t : M.Domain} (hN : M.mem N D.expr.omega)
    (h : Step M D D.expr.zero N t) : t=D.expr.zero :=
  (Expansion.Expands.empty_iff_d hM hD.expr hD.arith hN).mp ((hD.step_iff_d hM).mp h)

/-- 秩下降读入 EN 集合：s≠∅、t=E_N(s) 时 μ(t)∈μ(s)。 -/
theorem witness_step_descends_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {D : TheoremData M.Domain} (hD : D.Valid M) {χ μ : M.Domain} (hW : RankWitness M D.expr D.arith χ μ)
    {s N t a b : M.Domain} (hs : M.mem s D.expr.expressions) (hs0 : s≠D.expr.zero) (hN : M.mem N D.expr.omega)
    (hStep : Step M D s N t) (hsa : MemPair M μ s a) (htb : MemPair M μ t b) : M.mem b a :=
  hW.descends s hs hs0 N hN t ((hD.step_iff_d hM).mp hStep) a b hsa htb

/-- 非空表达式的展开结果不等于自身。 -/
theorem witness_step_ne_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {D : TheoremData M.Domain} (hD : D.Valid M) {χ μ : M.Domain} (hW : RankWitness M D.expr D.arith χ μ)
    {s N t : M.Domain} (hs : M.mem s D.expr.expressions) (hs0 : s≠D.expr.zero) (hN : M.mem N D.expr.omega)
    (hStep : Step M D s N t) : t≠s := by
  intro he
  subst t
  obtain ⟨a,ha,hsa⟩ := hW.graph.total s hs
  exact hW.ordinal.wellOrder.linear.irrefl a ha (witness_step_descends_d hM hD hW hs hs0 hN hStep hsa hsa)

/-- 实际 μ 与 χ 使实际 ≺ 集合成为通用 `RankedRelation`。 -/
theorem witness_ranked_relation_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {D : TheoremData M.Domain} (hD : D.Valid M) {χ μ R : M.Domain} (hW : RankWitness M D.expr D.arith χ μ)
    (hR : PrecedenceRelation M D R) : KP1Y.Dynamics.RankedRelation M R μ D.expr.expressions χ := by
  refine ⟨hW.ordinal,hW.graph,?_⟩
  intro x hx y _ a _ b _ hAnte
  obtain ⟨hyx,hxa,hyb⟩ := hAnte
  obtain ⟨_,_,hNe,N,hN,hStep⟩ := (hR.rows y x).mp hyx
  have hx0 : x≠D.expr.zero := by
    intro he
    subst x
    exact hNe (hD.empty_step_d hM hN hStep)
  exact witness_step_descends_d hM hD hW hx hx0 hN hStep hxa hyb

/-- M04 的集合形式：实际 ≺ 集合在 E 上内部良基。 -/
theorem witness_internal_wellFounded_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {D : TheoremData M.Domain} (hD : D.Valid M) {χ μ R : M.Domain} (hW : RankWitness M D.expr D.arith χ μ)
    (hR : PrecedenceRelation M D R) : KP1Y.Dynamics.InternalWellFounded M R D.expr.expressions :=
  fun _ hSE hNe => (witness_ranked_relation_d hM hD hW hR).minimal_d hM hSE hNe

/-- 文稿“≺ 良基”：每个非空内部集合 X⊆E 都有 ≺-极小元。 -/
def WellFoundedClause (M : SetTheory.Structure.{u}) (D : TheoremData M.Domain) : Prop :=
  ∀ X, M.MemberSubset X D.expr.expressions → (∃ x, M.mem x X) →
    ∃ x, M.mem x X ∧ ∀ y, M.mem y X → ¬Precedes M D y x

/-- 文稿“每条展开轨迹到达 ∅”：集合编码轨迹 H:ω→E，每步 H(i+1)=E_N(H(i)) 对某个 N∈ω。 -/
def TerminationClause (M : SetTheory.Structure.{u}) (D : TheoremData M.Domain) : Prop :=
  ∀ H, Graph M H D.expr.omega D.expr.expressions →
    (∀ i j x y, M.SuccessorOf j i → MemPair M H i x → MemPair M H j y →
      ∃ N, M.mem N D.expr.omega ∧ Step M D x N y) →
    ∃ i, M.mem i D.expr.omega ∧ MemPair M H i D.expr.zero

theorem witness_wellFounded_clause_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {D : TheoremData M.Domain} (hD : D.Valid M) {χ μ : M.Domain} (hW : RankWitness M D.expr D.arith χ μ) :
    WellFoundedClause M D := by
  intro X hXE hNe
  obtain ⟨R,hR⟩ := precedence_relation_exists_d hM D
  obtain ⟨x,hx,hMin⟩ := witness_internal_wellFounded_d hM hD hW hR X hXE hNe
  exact ⟨x,hx,fun y hy hyx => hMin y hy ((hR.rows y x).mpr ⟨hXE y hy,hXE x hx,hyx⟩)⟩

theorem witness_termination_clause_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {D : TheoremData M.Domain} (hD : D.Valid M) {χ μ : M.Domain} (hW : RankWitness M D.expr D.arith χ μ) :
    TerminationClause M D := by
  intro H hH hTraj
  obtain ⟨R,hR⟩ := precedence_relation_exists_d hM D
  apply (witness_ranked_relation_d hM hD hW hR).trajectory_hits_terminal_d hM hD.expr.omega hH
  intro i j x y hSucc hix hjy hx0
  obtain ⟨N,hN,hStep⟩ := hTraj i j x y hSucc hix hjy
  have hx := (hH.bounds hM.1 hix).2
  have hy := (hH.bounds hM.1 hjy).2
  exact (hR.rows y x).mpr ⟨hy,hx,witness_step_ne_d hM hD hW hx hx0 hN hStep,N,hN,hStep⟩

end KP1Y.OneYTheorem
