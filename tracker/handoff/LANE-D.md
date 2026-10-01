# LANE-D 交接（Y08 / M03）

## 1. 共享秩语句 `KP1Y/OneYRankStatement.lean`（已单模块检查：exit 0，日志空）

导入：`KP1Y.OneYExpansion`、`KP1Y.OneYMinimumRank`。命名空间 `KP1Y.OneYRank`。

```lean
def RankDescends (M : SetTheory.Structure.{u}) (E : ExpressionData M.Domain) (T : MatrixArithmetic M.Domain)
    (μ : M.Domain) : Prop :=
  ∀ s, M.mem s E.expressions → s≠E.zero → ∀ N, M.mem N E.omega → ∀ t, Expansion.Expands M E T s N t →
    ∀ a b, MemPair M μ s a → MemPair M μ t b → M.mem b a

structure RankWitness (M : SetTheory.Structure.{u}) (E : ExpressionData M.Domain) (T : MatrixArithmetic M.Domain)
    (χ μ : M.Domain) : Prop where
  ordinal : M.IsOrdinal χ
  graph : Graph M μ E.expressions χ          -- KP1Y.Functions.Graph
  empty : MemPair M μ E.zero E.zero          -- μ(∅)=0（E.zero 同为空序列和序数0）
  descends : RankDescends M E T μ
```

`Expansion.Expands` 即 `KP1Y.OneYFinite.Expansion.Expands`（实际 EN 关系，N∈内部ω，N=0 删除末项，空输入固定）。

### Δ₀ 公式（以实际 EN 图 Keys/EN 为参数）

```lean
def rankDescentFormula {n} (E : ExpressionData (Project.Term n)) (Keys EN χ μ : Project.Term n) : Project.Formula 1 n
--  ∀s∈E.expr (¬ s≐E.zero → ∀N∈ω ∀key∈Keys (Code(key,s,N) → ∀t∈E.expr (⟨key,t⟩∈EN →
--     ∀a∈χ ∀b∈χ (⟨s,a⟩∈μ → ⟨t,b⟩∈μ → b∈a)))))
def rankWitnessFormula {n} (E) (Keys EN χ μ) : Project.Formula 1 n :=
  .conj (ordinalFormula χ) (.conj (graphFormula μ E.expressions χ)
    (.conj (memPairFormula μ E.zero E.zero) (rankDescentFormula E Keys EN χ μ)))

theorem rankWitnessFormula_delta0 : (rankWitnessFormula E Keys EN χ μ).IsDelta0
theorem rankWitnessFormula_freeClosed (hE : E.Closed) (Keys EN χ μ) (hKeys : Keys.freeSupport=[]) (hEN : …) (hχ : …) (hμ : …) :
    (rankWitnessFormula E Keys EN χ μ).FreeClosed
theorem rankWitnessFormula_iff (hM : M.Models KP1Y.theory) (e : Env M n) (E) (Keys EN χ μ) (hE : (E.eval e).Valid M)
    {T : MatrixArithmetic M.Domain} (hG : Expansion.Graph M (E.eval e) T (Keys.eval e) (EN.eval e)) :
    Project.Formula.satisfies e (rankWitnessFormula E Keys EN χ μ) ↔ RankWitness M (E.eval e) T (χ.eval e) (μ.eval e)
```

（`rankDescentFormula_iff` 另需 μ 图前提；`rankDescent_graph_iff` 为纯语义版本。）
诚实复杂度：去掉 EN 参数后，下降子句是 Π₁（展开关系为 Σ₁ 证书 `expansionMatrix`，出现在蕴含前件）。
最终句可写 `∃Keys ∃EN (Expansion.Graph 的定义 ∧ rankWitnessFormula …)`；Expansion.Graph 的公式化由最终句车道负责。

### M02 / M03 接口命题

```lean
def MinimumRankDescentStatement : Prop :=   -- M02 应交付的精确形状
  ∀ (M : SetTheory.Structure.{u}), M.Models KP1Y.theory → ∀ (C : ArticleData M.Domain) (E : ExpressionData M.Domain)
    (T : MatrixArithmetic M.Domain) (μ : M.Domain), C.Valid M → UncountableOrdinal M C.reflection.omega C.top →
      E.Valid M → E.omega=C.reflection.omega → T.Valid M E → MinimumRank M E T C μ → RankDescends M E T μ

def ArticleRankWitnessStatement : Prop :=   -- M03 唯一消费的存在形
  ∀ (M : SetTheory.Structure.{u}), M.Models KP1Y.theory → ∀ (C : ArticleData M.Domain), C.Valid M →
    UncountableOrdinal M C.reflection.omega C.top →
      ∃ (E : ExpressionData M.Domain) (T : MatrixArithmetic M.Domain) (μ : M.Domain),
        E.Valid M ∧ E.omega=C.reflection.omega ∧ T.Valid M E ∧ RankWitness M E T C.top μ

theorem article_rank_witness_of_descent (hDesc : MinimumRankDescentStatement.{u}) : ArticleRankWitnessStatement.{u}
```

## 2. Y08 `KP1Y/OneYInnerAbsoluteness.lean`（232 行）+ `KP1Y/OneYInnerAbsolutenessExpansion.lean`（170 行）

两个模块单独 `--emit`：exit 0，日志空。命名空间 `KP1Y.OneYFinite.InnerAbsoluteness`。
记号：下文 `L := innerModel hM env hS`，`hS : FixedSyntax M (defContext.eval env) (defData.eval env) (env.bound 0) (env.bound 1) (env.bound 2)`
（任意固定语法即可；M03 用 canonical 环境的 `h.toFixedSyntax`）。全部定理对任意 `M`、`hM : M.Models KP1Y.theory`。

参数（E、ω、表、森林/空间）：
```lean
theorem expression_data_unique (he : Extensional M) (hC : C.Valid M) (hD : D.Valid M) : C=D
theorem inner_expression_data_eq_d (hC : C.Valid M) {D : ExpressionData L.Domain} (hD : D.Valid L) : D=innerExpressionData hM env hS C hC
theorem inner_expression_data_values_d (hC : C.Valid M) (hD : D.Valid L) : D.map Subtype.val=C        -- E^L = E^M（同一集合）
theorem inner_expression_data_outer_valid_d (hD : D.Valid L) : (D.map Subtype.val).Valid M
theorem inner_omega_outer_d {w : L.Domain} (hw : L.IsOmega w) : M.IsOmega w.val
theorem inner_sum_up_d / inner_product_up_d (a b c : L.Domain) : Sum/Product L a b c → Sum/Product M a.val b.val c.val
theorem inner_difference_up_d (w z a b d : L.Domain) : TruncatedDifference L w z a b d → TruncatedDifference M …vals
theorem inner_matrix_arithmetic_up_d (hD : D.Valid L) (hT : T.Valid L D) : (T.map Subtype.val).Valid M (D.map Subtype.val)
theorem matrix_arithmetic_unique (he : Extensional M) (hT : T.Valid M C) (hT' : T'.Valid M C) : T=T'
theorem inner_all_forests_up_d (hD) (h : ExpressionDiagram.AllForests L D.omega AF) : ExpressionDiagram.AllForests M D.omega.val AF.val
theorem inner_spaces_up_d (hD) (h : S.Valid L D AF) :
    MountainReconstruction.Spaces.Valid M (D.map Subtype.val) AF.val ⟨S.forestLists.val,S.grids.val⟩
```
（Legal 的绝对性沿用 `legal_class_absolute`；外部每个合法表达式/有限森林/有限序列属于 L 沿用 Y08a 的构造闭合，含非标准长度。）

实际 EN 关系与图（L 内存在 + Σ₁ 证书 `expansionMatrix` 的 Δ₀ 向上 + M 内唯一）：
```lean
theorem inner_expands_up_d (hD : D.Valid L) (hT : T.Valid L D) {s N t : L.Domain} (h : Expansion.Expands L D T s N t) :
    Expansion.Expands M (D.map Subtype.val) (T.map Subtype.val) s.val N.val t.val
theorem inner_expands_iff_d (hD) (hT) (s N t : L.Domain) :
    Expansion.Expands L D T s N t ↔ Expansion.Expands M (D.map Subtype.val) (T.map Subtype.val) s.val N.val t.val
theorem outer_expands_inner_d (hD) (hT) {s N t : M.Domain} (h : Expansion.Expands M (D.map Subtype.val) (T.map Subtype.val) s N t) :
    ∃ s0 N0 t0 : L.Domain, s0.val=s ∧ N0.val=N ∧ t0.val=t ∧ Expansion.Expands L D T s0 N0 t0
theorem inner_expands_outer_iff_d (hD) (hT0 : T0.Valid L D) (hC : C.Valid M) (hT : T.Valid M C) (s N t : L.Domain) :
    Expansion.Expands L D T0 s N t ↔ Expansion.Expands M C T s.val N.val t.val
theorem inner_expansion_graph_up_d (hD) (hT) (h : Expansion.Graph L D T Keys EN) :
    Expansion.Graph M (D.map Subtype.val) (T.map Subtype.val) Keys.val EN.val
theorem outer_expansion_graph_inner_d (hD) (hT) {Keys EN : M.Domain} (h : Expansion.Graph M (D.map Subtype.val) (T.map Subtype.val) Keys EN) :
    ∃ Keys0 EN0 : L.Domain, Keys0.val=Keys ∧ EN0.val=EN ∧ Expansion.Graph L D T Keys0 EN0
```

秩见证（回传的是 μ 集合本身）：
```lean
theorem inner_rank_witness_up_d (hD) (hT) {χ μ : L.Domain} (h : RankWitness L D T χ μ) :
    RankWitness M (D.map Subtype.val) (T.map Subtype.val) χ.val μ.val
theorem inner_rank_witness_iff_d (hD) (hT) (χ μ : L.Domain) :
    RankWitness L D T χ μ ↔ RankWitness M (D.map Subtype.val) (T.map Subtype.val) χ.val μ.val
theorem inner_rank_witness_outer_d (hD) (hT0 : T0.Valid L D) (hC : C.Valid M) (hT : T.Valid M C)
    (h : RankWitness L D T0 χ μ) : RankWitness M C T χ.val μ.val
```

## 3. M03 `KP1Y/OneYRankTransfer.lean`（53 行，`--emit` exit 0，日志空）

命名空间 `KP1Y.OneYRank`。
```lean
theorem rank_transfer_d (hRank : ArticleRankWitnessStatement.{u}) {M : SetTheory.Structure.{u}}
    (hM : M.Models KP1Y.theory) {ω ν : M.Domain} (hω : M.IsOmega ω) (hν : UncountableOrdinal M ω ν) :
    ∃ (E : ExpressionData M.Domain) (T : MatrixArithmetic M.Domain) (χ μ : M.Domain),
      E.Valid M ∧ E.omega=ω ∧ T.Valid M E ∧ (χ=ν ∨ M.mem χ ν) ∧ RankWitness M E T χ μ
theorem rank_transfer_of_descent_d (hDesc : MinimumRankDescentStatement.{u}) … : （同上结论）
theorem rank_transfer_graph_d (hRank : ArticleRankWitnessStatement.{u}) … :
    ∃ E T Keys EN χ μ, E.Valid M ∧ E.omega=ω ∧ T.Valid M E ∧ Expansion.Graph M E T Keys EN ∧ (χ=ν ∨ M.mem χ ν) ∧ RankWitness M E T χ μ
```
证明链：canonical 环境 → `inner_least_uncountable_enumeration_d`（ν 在 L 中不可数、L 的最小不可数 κ≤ν、统一枚举）→
L 内 `article_data_exists_d`（top=κ）→ 前提 `hRank` 作用于 L → Y08 把 E^L、T^L、μ 原样回传。

**唯一剩余前提**：`ArticleRankWitnessStatement`（或更强、由 M02 直接交付的 `MinimumRankDescentStatement`）。
其余全部无条件；`#print axioms` 只含 propext / Classical.choice / Quot.sound。

## 4. 下一步依赖
- M02 交付 `MinimumRankDescentStatement`（即对 `MinimumRank` 的 `RankDescends`），则 `rank_transfer_of_descent_d` 无条件化。
- 最终句车道：用 `rank_transfer_graph_d` + `rankWitnessFormula_iff` 写闭句；`Expansion.Graph` 自身的公式化（rows 用 `expansionMatrix`）由该车道负责。
- 待审计声明：上列全部公开定理与 `RankDescends`/`RankWitness`/`rankDescentFormula`/`rankWitnessFormula`/两个 Statement 定义。

## 5. M02（第十三批后续任务）

### CopyDescentStatement (target for LANE-A)

文件 `KP1Y/OneYRankDescentStatement.lean`（`--emit` exit 0，日志空），命名空间 `KP1Y.OneYRank`，导入 `KP1Y.OneYRankStatement`，
open `KP1Y.ReflectionModel KP1Y.OneYFinite KP1Y.OneYFinite.ExpressionDiagram`。逐字定义：

```lean
def CopyDescentStatement : Prop :=
  ∀ (M : SetTheory.Structure.{u}), M.Models KP1Y.theory → ∀ (C : ArticleData M.Domain) (E : ExpressionData M.Domain)
    (T : MatrixArithmetic M.Domain), C.Valid M → UncountableOrdinal M C.reflection.omega C.top →
      E.Valid M → E.omega=C.reflection.omega → T.Valid M E →
      ∀ s m A β, M.mem s E.expressions → s≠E.zero → ExpressionGraph M E T C.reflection s m A →
        M.mem β C.top → RealizesLast M C m A β →
        ∀ N, M.mem N E.omega → ∀ t, Expansion.Expands M E T s N t → t≠E.zero →
          ∀ m' A', ExpressionGraph M E T C.reflection t m' A' → ∃ b, M.mem b β ∧ RealizesLast M C m' A' b
```

- `ExpressionGraph` = `KP1Y.OneYFinite.ExpressionDiagram.ExpressionGraph`（规范根图 A(s)，宽度 m）。
- `RealizesLast M C m A a := ∃ f, f∈C.reflection.labels ∧ Representation M C.reflection C.table m A f ∧ LastValue M (C.numbers 0) m f a`
  （`KP1Y.OneYRank`，OneYDiagramMinimumRank）。
- 相对协调者草案的唯一改动：多给证明方一个前提 `M.mem β C.top`（μ 值均在 top 内，M02 能提供；LANE-A 不需要可忽略）。

### M02 证明 `KP1Y/OneYRankDescent.lean`（57 行，`--emit` exit 0，日志空）

命名空间 `KP1Y.OneYRank`；导入 `KP1Y.OneYRankDescentStatement`、`KP1Y.OneYRankTransfer`。

```lean
theorem MinimumRank.descends_of_copy_d (hM : M.Models KP1Y.theory) {C : ArticleData M.Domain} (hC : C.Valid M)
    {E : ExpressionData M.Domain} (hE : E.Valid M) (hOmega : E.omega=C.reflection.omega) {T : MatrixArithmetic M.Domain} {μ : M.Domain}
    (hμ : MinimumRank M E T C μ)
    (hCopy : ∀ s m A β, M.mem s E.expressions → s≠E.zero → ExpressionGraph M E T C.reflection s m A →
        M.mem β C.top → RealizesLast M C m A β →
        ∀ N, M.mem N E.omega → ∀ t, Expansion.Expands M E T s N t → t≠E.zero →
          ∀ m' A', ExpressionGraph M E T C.reflection t m' A' → ∃ b, M.mem b β ∧ RealizesLast M C m' A' b) :
    RankDescends M E T μ
theorem minimum_rank_descent_of_copy_descent (h : CopyDescentStatement.{u}) : MinimumRankDescentStatement.{u}
theorem rank_transfer_of_copy_descent_d (h : CopyDescentStatement.{u}) {M : SetTheory.Structure.{u}}
    (hM : M.Models KP1Y.theory) {ω ν : M.Domain} (hω : M.IsOmega ω) (hν : UncountableOrdinal M ω ν) :
    ∃ (E : ExpressionData M.Domain) (T : MatrixArithmetic M.Domain) (χ μ : M.Domain),
      E.Valid M ∧ E.omega=ω ∧ T.Valid M E ∧ (χ=ν ∨ M.mem χ ν) ∧ RankWitness M E T χ μ
theorem rank_transfer_graph_of_copy_descent_d (h : CopyDescentStatement.{u}) … :
    ∃ E T Keys EN χ μ, E.Valid M ∧ E.omega=ω ∧ T.Valid M E ∧ Expansion.Graph M E T Keys EN ∧ (χ=ν ∨ M.mem χ ν) ∧ RankWitness M E T χ μ
```

空输出：`MinimumRank.empty_d` 给 μ(∅)=∅，`MinimumRank.nonempty_positive_d` 给 ∅∈μ(s)。非空输出：μ(s)=a 的 `DiagramMinimum`
给 `RealizesLast m A a` 与 a∈top，Lemma 3 给 b'∈a 的 `RealizesLast m' A' b'`，μ(t) 的最小性给 μ(t)≤b'，序数传递得 μ(t)∈a。
`#print axioms`：propext / Classical.choice / Quot.sound。**唯一剩余前提：`CopyDescentStatement`（Y06，LANE-A）。**

## 6. Helper for LANE-C: Task H（Terminal 底行 k=K 的四个出口）

状态：进行中（LANE-D 接手，2026-10-01）。文件 `KP1Y/OneYCanonHelper*.lean`，命名空间 `KP1Y.OneYFinite.TerminalBase`。
四个导出定理的前提块与 `ExpansionCanonical.terminal_rebuild_rows_d` 完全相同，结论逐字取自 LANE-C.md「Available for helper」。
每个定理落地后在此处补逐字类型与检查状态。

### H2 已落地 —— `KP1Y/OneYCanonHelperSetting.lean`（`--emit` exit 0，日志空）

```lean
theorem KP1Y.OneYFinite.TerminalBase.terminal_base_nonroot_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {m V P H level index n OldTop NewTop Bottom : M.Domain} {R : RowStateSpace M.Domain}
    (hRun : RowRun M C m R V P H) (hBase : RootedRow M C m V P)
    {X Y : CopiedMountain.Data M.Domain} (hX : X.Valid M C) (hFrom : CopiedMountain.FromRun M C m R V H X)
    (hOldTop : TopValueGraph M C m R H X.heights OldTop)
    {A : CopyCoordinates.Context M.Domain} (hA : A.Valid M C) (hWidth : M.SuccessorOf m A.last)
    (hBad : RowBadAt M C R H level A.last A.root) (hIndex : M.mem index C.omega)
    (hN : CopyCoordinates.Width M C T A index n) (hY : Y.Valid M C)
    (hCopy : CopiedMountain.Terminal.Copies M C T A X level n Y)
    (hTop : CopiedTop M C T A OldTop Y.width NewTop)
    (hRebuild : Rebuilds M C T.addPairs T.plus Y NewTop Bottom)   -- MountainReconstruction.Rebuilds
    {P0 s b c p : M.Domain} (hP0 : MemPair M Y.parents C.zero P0)
    (hs : M.mem A.root s) (hsx : M.mem s A.last) (hMap : CopyCoordinates.ParentCopy M C T A b s c) (hc : M.mem c n) :
    MemPair M P0 c p ↔ ∃ q, MemPair M P s q ∧ CopyCoordinates.ParentCopy M C T A b q p
```
同文件还有打包结构 `TerminalBase.Base`（14个字段即上列前提）与若干 `Base.*` 读数（源/目标第0行、前缀值、目标网格规范选择）。

### H3 已落地 —— `KP1Y/OneYCanonHelperFixed.lean`（`--emit` exit 0，日志空；导入 `OneYCanonHelperKey` ← `OneYCanonHelperSetting`）

```lean
theorem KP1Y.OneYFinite.TerminalBase.terminal_base_upper_fixed_d （前提块同 H2，至 hRebuild 为止）
    {D : CopiedMountain.Lower.Context M.Domain} (hD : D.coordinates=A) :
    CopiedMountain.Lower.UpperFixed M C T D V P n Bottom
```
无额外前提。证明：副本列与原列在目标山形逐行父项相同（好部父不平移）、新Top相同 ⇒ 目标网格孪生列底值相等
（`Base.twin_value_d`，用 `key_iff_value_le_d` 双向），再用前缀值 `Base.prefix_values_d`。

### H1 已落地 —— `KP1Y/OneYCanonHelperSelect.lean`（`--emit` exit 0，日志空）

依赖链：`OneYCanonHelperSetting` → `Key` → `Fixed`/`Order` → `Frame` → `SelectCases` → `Select`（均 `--emit` exit 0、日志空）。
```lean
theorem KP1Y.OneYFinite.TerminalBase.terminal_base_select_d （前提块同 H2，至 hRebuild 为止）
    {F F' P0 : M.Domain} (hF : Selects true M C m F V P) (hF' : FrameCopy.Copies M C T A F index n F')
    (hP0 : MemPair M Y.parents C.zero P0) : Selects true M C n F' Bottom P0
```
无额外前提。对目标列作对象集合归纳（谓词 `∀p, P0(c)=p ↔ RestrictedParent true n F' Bottom c p` 的显式公式）；
前缀列用前缀同余；非root副本列分直接父/好部阻挡（root 特例：活动层0 用 root 副本孪生值，低层用 root 复制链）/
坏部阻挡（`copied_key_le_d` 运输图层 Key，`key_iff_value_le_d` 回到底值）；seam 列分活动层0（root 副本阻挡，底值相同）
与低层（`seam_key_le_d`）；无父列底值为1。`#print axioms`：propext / Classical.choice / Quot.sound。

### H4 已落地 —— `KP1Y/OneYCanonHelperUpperOrder.lean`（`--emit` exit 0，日志空）

```lean
theorem KP1Y.OneYFinite.TerminalBase.terminal_base_upper_order_d （前提块同 H2，至 hRebuild 为止）
    {D : CopiedMountain.Lower.Context M.Domain} (hD : D.coordinates=A)
    {F : M.Domain} (hF : Selects true M C m F V P) : CopiedMountain.Lower.UpperOrder M C T D F V Bottom
```
无额外前提。活动层0：目标山形即普通复制，底值由 `Ordinary.Copies.row_values_copy_d` 读源 source0（末列副本读 root，严格小）。
低活动层：目标第0行恰是 P 的低行 BM4 复制（`Base.zero_copy_forest_d`，经 `copied_forest_terminal_parent_iff_d`），
祖先关系由 `CopyForest.ancestor_{copy,good,previous_root}_iff_d` 双向运输；若目标逆序，H1 目标选择与源选择的祖先单调性
给出源两列祖先集相等 ⇒ 第0行父项相同，再由 (O1)/(O2) 共同父项数值运输或"无父底值为1"得矛盾。不需要深度公式。

### `TowerCanon.TerminalExits` 打包 —— `KP1Y/OneYCanonHelperExits.lean`（`--emit` exit 0，日志空）

```lean
theorem KP1Y.OneYFinite.TerminalBase.terminal_exits_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory) :
    KP1Y.OneYFinite.TowerCanon.TerminalExits M
```
导入 `KP1Y.OneYTowerCanonExits`（已集成）与 `KP1Y.OneYCanonHelperUpperOrder`；四个字段与 LANE-C 的陈述逐字一致，无适配包装。
`#print axioms terminal_exits_d`：propext / Classical.choice / Quot.sound。

Task H 模块清单（集成顺序）：OneYCanonHelperSetting → OneYCanonHelperKey → OneYCanonHelperFixed → OneYCanonHelperOrder →
OneYCanonHelperFrame → OneYCanonHelperSelectCases → OneYCanonHelperSelect → OneYCanonHelperUpperOrder → OneYCanonHelperExits
（行数 204/223/90/180/314/268/112/286/20，全部单模块 `--emit` exit 0、日志空）。
