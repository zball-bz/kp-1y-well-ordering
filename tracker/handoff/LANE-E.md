# LANE-E 交接（M04 / M04b / M05 / Q01 草稿）

状态：进行中。全部定理在任意 `M : SetTheory.Structure`、`hM : M.Models KP1Y.theory` 内；长度、N、指标均为内部 ω 元素；
无 sorry/admit/axiom/额外对象公理，不假设 ω 标准或宿主 membership 良基，无依赖选择。命名空间 `KP1Y.OneYTheorem`。

## 1. `KP1Y/OneYTheoremData.lean`（单模块 `--emit` exit 0，日志空）

导入 `KP1Y.OneYReachability`、`KP1Y.OneYLexOrder`。闭句的辅助集合族及其**显式定义公式**：

```lean
structure TheoremData (α) where
  expr : ExpressionData α        -- ω, 0, 1, 有限序列空间, E
  arith : MatrixArithmetic α     -- 加/乘/截断减法表
  forests forestLists grids : α  -- 全部森林、森林列表、网格空间
  keys expansion : α             -- Keys=E×ω, EN : Keys→E
structure TheoremData.Valid (M) (D : TheoremData M.Domain) : Prop where
  expr : D.expr.Valid M
  arith : D.arith.Valid M D.expr
  forests : ExpressionDiagram.AllForests M D.expr.omega D.forests
  spaces : MountainReconstruction.Spaces.Valid M D.expr D.forests ⟨D.forestLists,D.grids⟩
  graph : Expansion.Graph M D.expr D.arith D.keys D.expansion
abbrev Step M D s N t := KP1Y.Dynamics.Expansion M D.keys D.expansion s N t   -- t=E_N(s)

def theoremDataFormula (D : TheoremData (Project.Term k)) : Project.Formula 1 k
theorem theoremDataFormula_iff (hM) (e) (D) : satisfies e (theoremDataFormula D) ↔ (D.eval e).Valid M
theorem theoremDataFormula_freeClosed (hD : D.Closed) : (theoremDataFormula D).FreeClosed
theorem theorem_data_exists_d (hM) : ∃ D : TheoremData M.Domain, D.Valid M
theorem TheoremData.Valid.unique (he) : D.Valid M → D'.Valid M → D=D'
theorem ExpressionData.Valid.unique (he) : C.Valid M → C'.Valid M → C=C'
theorem MatrixArithmetic.Valid.unique (he) : T.Valid M C → T'.Valid M C → T=T'
theorem TheoremData.Valid.step_iff_d (hM) (hD) : Step M D s N t ↔ Expansion.Expands M D.expr D.arith s N t
```

EN 的行公式是 `∃Box expansionMatrix.body`（`witnessInstanceFormula` 绑定 14 个参数槽）；
在其余数据有效时由 `expansion_sigmaOne_iff_d` 精确读成 `CodedExpands`。算术表行分别用
`sumFormula`、`∃B productCertificateFormula`、`differenceFormula`。

## 2. `KP1Y/OneYWellFounded.lean`（M04；`--emit` exit 0，日志空）

导入 `KP1Y.OneYTheoremData`、`KP1Y.OneYRankStatement`（LANE-D 共享 `RankWitness`，未另立版本）。

```lean
def PrecedesIn M w Keys EN t s := t≠s ∧ ∃ N, M.mem N w ∧ KP1Y.Dynamics.Expansion M Keys EN s N t
abbrev Precedes M D t s := PrecedesIn M D.expr.omega D.keys D.expansion t s      -- t ≺ s
structure PrecedenceRelation M D R : Prop  -- R⊆E×E 实际集合，MemPair R t s ↔ t,s∈E ∧ t≺s
theorem precedence_relation_exists_d (hM) (D) : ∃ R, PrecedenceRelation M D R
theorem witness_ranked_relation_d (hM) (hD : D.Valid M) (hW : RankWitness M D.expr D.arith χ μ)
    (hR : PrecedenceRelation M D R) : KP1Y.Dynamics.RankedRelation M R μ D.expr.expressions χ
theorem witness_internal_wellFounded_d … : KP1Y.Dynamics.InternalWellFounded M R D.expr.expressions
def WellFoundedClause M D := ∀ X, M.MemberSubset X E → (∃ x, M.mem x X) → ∃ x, M.mem x X ∧ ∀ y, M.mem y X → ¬Precedes M D y x
def TerminationClause M D := ∀ H, Graph M H ω E → (∀ i j x y, M.SuccessorOf j i → MemPair M H i x → MemPair M H j y →
    ∃ N, M.mem N ω ∧ Step M D x N y) → ∃ i, M.mem i ω ∧ MemPair M H i D.expr.zero
theorem witness_wellFounded_clause_d (hM) (hD) (hW) : WellFoundedClause M D
theorem witness_termination_clause_d (hM) (hD) (hW) : TerminationClause M D
```
通用定理 `RankedRelation.minimal_d`、`trajectory_hits_terminal_d` 以实际 ≺ 集合与实际 μ 实例化。

## 3. `KP1Y/OneYWellOrdering.lean`（M04b；`--emit` exit 0，日志空）

```lean
def PairExpressionIn M w z o s b := ∃ two, two∈w ∧ SuccessorOf two o ∧ Graph s two w ∧ s(z)=o ∧ s(o)=b   -- s=(1,b)
def Seed M C r := ∃ m, m∈ω ∧ 1∈m ∧ PairExpression M C r m                                          -- (1,m), m≥2
structure OrderFacts (M) (C : ExpressionData M.Domain) (T : MatrixArithmetic M.Domain) : Prop where
  index_mono : ∀ Keys EN Reach, Expansion.Graph M C T Keys EN → Reachability.Relation M C Keys EN Reach →
    ∀ s i j t u, (i=j ∨ M.mem i j) → KP1Y.Dynamics.Expansion M Keys EN s i t →
      KP1Y.Dynamics.Expansion M Keys EN s j u → MemPair M Reach t u
  lex_descent : ∀ s, M.mem s C.expressions → s≠C.zero → ∀ N, M.mem N C.omega → ∀ t,
    Expansion.Expands M C T s N t → Lex M C t s
  seed_step : ∀ n, M.mem n C.omega → ∀ a b, M.SuccessorOf a n → M.SuccessorOf b a → ∀ s t,
    PairExpression M C s b → PairExpression M C t a → Expansion.Expands M C T s C.one t
theorem descendant_system_d (hM) (hD) (hW : RankWitness …) (hF : OrderFacts …) (hR : Reachability.Relation …) (hL : LexRelation …) :
    KP1Y.Dynamics.DescendantSystem M D.expr.omega D.expr.expressions χ μ D.keys D.expansion Reach L
def LexWellOrder M C X  -- Lex 严格线性 + 每个非空内部子集有最小元
def DescClause M D := ∀ s∈E, ∃ X, (∀ x, x∈X ↔ x∈E ∧ Reachability.Reaches M C Keys EN x s) ∧ LexWellOrder M C X
def GenClause M D := ∃ X, (∀ x, x∈X ↔ x∈E ∧ ∃ r, Seed M C r ∧ Reaches … x r) ∧ LexWellOrder M C X
theorem seed_chain_d / seeds_join_d   -- 共同种子祖先由 seed_step 经内部自然数归纳推出（不是前提）
theorem desc_clause_d (hM) (hD) (hW) (hF) : DescClause M D
theorem gen_clause_d (hM) (hD) (hW) (hF) : GenClause M D
```

`OrderFacts` 解除方式：`index_mono` 由 LANE-F `ExpansionOrder.index_mono_d hM hC hT hEN hR hij ht hu` 直接给出；
`lex_descent`、`seed_step` 待 LANE-F (c)(d)。

## 4. `KP1Y/OneYTheoremClauses.lean`（`--emit` exit 0，日志空；281 行）

各结论子句的公式与 `_iff`（参数仅 `C : ExpressionData (Term n)`、Keys、EN）：
`rankClauseFormula`（内部用 LANE-D `rankWitnessFormula`）、`wellFoundedFormula`、`terminationFormula`、
`reachFormula`（∃steps count nodes controls `pathFormula`）、`lexWellOrderFormula`、`descFormula`、`genFormula`、
`conclusionFormula`。

```lean
def RankClause M D ν := ∃ χ μ, RankWitness M D.expr D.arith χ μ ∧ (χ=ν ∨ M.mem χ ν)
def ConclusionClause M D := ∀ ν, UncountableOrdinal M D.expr.omega ν →
  RankClause M D ν ∧ WellFoundedClause M D ∧ TerminationClause M D ∧ DescClause M D ∧ GenClause M D
theorem conclusionFormula_iff (hM) (e) (D : TheoremData (Project.Term n)) (hD : (D.eval e).Valid M) :
  satisfies e (conclusionFormula D.expr D.keys D.expansion) ↔ ConclusionClause M (D.eval e)
```

## 5. `KP1Y/OneYTheoremSentence.lean`（M05 闭句；`--emit` exit 0，日志空）

```lean
def boundData : TheoremData (Project.Term 16)        -- bound 15 = ω, …, bound 0 = EN
def mainCore : Project.Formula 1 16 :=
  .imp (theoremDataFormula boundData) (conclusionFormula boundData.expr boundData.keys boundData.expansion)
def mainFormula : Project.Formula 1 0 := .conj (existsData (theoremDataFormula boundData)) (forallData mainCore)
theorem mainFormula_freeClosed : mainFormula.FreeClosed
def mainSentence : Project.Sentence := Project.Sentence.ofFormula mainFormula mainFormula_freeClosed
def MainSemantic (M) : Prop := (∃ D : TheoremData M.Domain, D.Valid M) ∧ ∀ D, D.Valid M → ConclusionClause M D
theorem mainSentence_iff {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory) (free : FreeVarId → M.Domain) :
  Project.Formula.satisfies ({bound := Fin.elim0,free := free} : Env M 0) mainSentence.formula ↔ MainSemantic M
```
`existsData`/`forallData` 为 16 个显式嵌套量词；`satisfies_existsData_iff`/`satisfies_forallData_iff` 读成 `∃/∀ D : TheoremData`。

## 6. `KP1Y/OneYTheorem.lean`（M05 封装；`--emit` exit 0，日志空）

```lean
def RankTransferAt (M) : Prop := ∀ (C : ExpressionData M.Domain) (T : MatrixArithmetic M.Domain) (ν : M.Domain),
  C.Valid M → T.Valid M C → UncountableOrdinal M C.omega ν → ∃ χ μ, RankWitness M C T χ μ ∧ (χ=ν ∨ M.mem χ ν)
def OrderFactsAt (M) : Prop := ∀ C T, C.Valid M → T.Valid M C → OrderFacts M C T
theorem rank_transfer_of_some_d (hM) (h : ∀ w ν, M.IsOmega w → UncountableOrdinal M w ν →
  ∃ C T χ μ, C.Valid M ∧ T.Valid M C ∧ RankWitness M C T χ μ ∧ (χ=ν ∨ M.mem χ ν)) : RankTransferAt M
theorem conclusion_clause_d (hM) (hD : D.Valid M) (hRank : RankTransferAt M) (hOrder : OrderFactsAt M) : ConclusionClause M D
theorem main_semantic_d (hM) (hRank : RankTransferAt M) (hOrder : OrderFactsAt M) : MainSemantic M
theorem main_derivable (h : ∀ M : SetTheory.Structure.{0}, M.Models KP1Y.theory → MainSemantic M) : KP1Y.Derives mainSentence
def RankTransferStatement : Prop := ∀ M : SetTheory.Structure.{0}, M.Models KP1Y.theory → RankTransferAt M
def OrderFactsStatement : Prop := ∀ M : SetTheory.Structure.{0}, M.Models KP1Y.theory → OrderFactsAt M
theorem main_derivable_of (hRank : RankTransferStatement) (hOrder : OrderFactsStatement) : KP1Y.Derives mainSentence
```

## 7. `KP1Y/OneYTheoremInputs.lean`（`--emit` exit 0，日志空）

导入 LANE-F 的 `KP1Y.OneYExpansionOrder`（其文件仍在演进，集成前需确认 `index_mono_d` 签名不变）。

```lean
structure OrderInputs (M) (C) (T) : Prop where      -- 仅剩两项
  lex_descent : ∀ s, M.mem s C.expressions → s≠C.zero → ∀ N, M.mem N C.omega → ∀ t,
    Expansion.Expands M C T s N t → Lex M C t s
  seed_step : ∀ n, M.mem n C.omega → ∀ a b, M.SuccessorOf a n → M.SuccessorOf b a → ∀ s t,
    PairExpression M C s b → PairExpression M C t a → Expansion.Expands M C T s C.one t
theorem OrderInputs.order_facts_d (hM) (hC) (hT) (h : OrderInputs M C T) : OrderFacts M C T
def OrderInputsStatement : Prop := ∀ M : Structure.{0}, M.Models KP1Y.theory → ∀ C T, C.Valid M → T.Valid M C → OrderInputs M C T
theorem main_derivable_of_inputs (hRank : RankTransferStatement) (hInputs : OrderInputsStatement) : KP1Y.Derives mainSentence
```

`#print axioms`：main_derivable / main_derivable_of / main_derivable_of_inputs / main_semantic_d / mainSentence_iff
仅 `propext, Classical.choice, Quot.sound`。

## 8. 未解除前提与下一步
- `RankTransferStatement`：M02+Y08+M03（LANE-D）。存在形结果可经 `rank_transfer_of_some_d` 接入。
- `OrderInputs.lex_descent`：Y07a(c)；`OrderInputs.seed_step`：Y07b（LANE-F）。共同种子祖先已由本车道证明。
- Q01 草稿：`tracker/FINAL-STATEMENT-REVIEW.md`（算法层 §5 对照仍待最终复核）。
- 待审计声明：上述各模块全部公开定理；新模块均未加入 `KP1Y.lean`/`Audit.lean`（由协调者集成）。

## 9. Q01 终稿（2026-10-01）
`tracker/FINAL-STATEMENT-REVIEW.md` 已完成 §5 算法层逐定义对照（五路只读审读 + 回查引用）：
**0 个 FINDING**；5 条约定性观察（O-1…O-5）均已由对象引理调和、无需修改。
命题层复核同时覆盖协调者新增的 `OneYMainAssembly.main_derivable_of_canonical_bound`，其唯一剩余前提为 Y05b `CanonicalCopyBound.{0}`（证明内部，不出现在闭句中）。
