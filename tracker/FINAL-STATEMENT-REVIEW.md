# Q01：定理 1 与 Lean 纯 ∈ 闭句的忠实性审读

日期：2026-10-01。审读人：LANE-E。本次审读只读源码，不修改任何 Lean 文件。

**结论：没有发现忠实性偏差（0 个 FINDING）。** §7 列出 5 条约定差异，都已在 Lean 中调和，不需要修改。

**完成状态：** 闭句 `mainSentence` 已构造，语义等价已证明。最终 `KP1Y.Derives mainSentence` 目前只剩一个前提，即 Y05b 的 `CanonicalCopyBound`：

```lean
theorem main_derivable_of_canonical_bound (hCanon : CopyDescent.CanonicalCopyBound.{0}) :
    KP1Y.Derives mainSentence
```

该定理位于 `KP1Y/OneYMainAssembly.lean:38`。`#print axioms` 只给出 `propext`、`Classical.choice`、`Quot.sound`，三者都是 Lean 元公理，不是对象理论的公理。在 Y05b 解除这一前提之前，**定理 1 尚未完成**。

审读分三层：
- §1–§4 核对**命题层**：对象理论、闭句形状、辅助定义、结论子句。
- §5 核对**算法层**：对象层实现与宿主算法 `/home/dev/ggg/1Y-Well-Ordering-Lean/formalization/OneY`、文稿 §1 逐个定义对照。
- §6 核对剩余前提，§7 汇总发现与约定。

区分两类定义：
- **命题关键**：E 与 E_N 直接出现在闭句中，偏差会改变定理本身。
- **证明内部**：A(s)、μ 的具体构造、反射与复制下降只影响证明能否成立。闭句只断言“存在”χ 与 μ，并不指定 μ 的构造。

## 1. 对象理论与纯 ∈ 语言

| 文稿 §1 | Lean：`KP1Y/Axioms.lean`，`KP1Y.theory` |
|---|---|
| Extensionality, Empty Set, Pairing, Union, Infinity | 构造子 `extensionality`、`emptySet`、`pairing`、`union`、`infinity` |
| ∆0-Separation、∆0-Collection | `separation φ`、`collection φ`，其中 φ 只能是 `Delta0UnarySchema` 或 `Delta0BinarySchema` |
| full set induction | `setInduction φ`，φ 为任意 `UnarySchema`，带参数 |
| 存在不可数序数 | 不是公理，而是闭句内部的前件 `∀ν (UncountableOrdinal(ω,ν) → …)` |

**推导层。** `KP1Y.Derives s := Project.Derives KP1Y.theory s` 是真正的 Hilbert 推导。`derives_of_all_models`（`KP1Y/Completeness.lean`）经强完备性得到它：需要对每个 `M : Structure.{0}` 证明 `M.Models KP1Y.theory → M.SatisfiesSentence s`。

**语言。** `Project.fo_formula`（`third_party/.../Project/Derivation.lean:56-114`）负责翻译到一阶语言：
- 定义原子 `extensionalEq` 译为一阶等号 `=`。
- 定义原子 `subset` 译为 `∀z (z∈a → z∈b)`。
- 其余只有 `∈`。

所以闭句属于只有 ∈ 关系、带逻辑等号的一阶语言。语义桥 `pure_extensional` 由对象理论自身的外延公理保证 `=` 与“成员相同”一致。

**没有越权。** 理论中没有 Choice、Power Set、完整 Separation 或 Replacement。证明不假设 ω 标准，也不假设宿主 membership 良基。所有最小元都取内部集合序数像的最小值（`rank_minimum_d`、`ordinal_induction_d`），不用依赖选择。

**宇宙层级。**
- `main_derivable` 与 `main_derivable_of_canonical_bound` 只对 `Structure.{0}` 量化。完备性定理只需要这一层。
- 结论 `Derives` 是语法对象，与宇宙无关。
- 模型层定理（`main_semantic_d`、`conclusion_clause_d` 等）对宇宙多态。
- 前提 `CanonicalCopyBound.{0}` 只用于 0 层模型。

无问题。

## 2. 闭句的整体形状

```text
mainSentence := ofFormula mainFormula mainFormula_freeClosed          -- KP1Y/OneYTheoremSentence.lean
mainFormula  := (∃𝔇. Def(𝔇)) ∧ (∀𝔇. Def(𝔇) → Concl(𝔇))
Concl(𝔇)     := ∀ν ( UncountableOrdinal(ω,ν) → Rank(ν) ∧ WF ∧ Term ∧ DescWO ∧ GenWO )
```

𝔇 是 16 个约束变量：

- ω、0、1；
- 全部有限序列组成的空间；
- E；
- 加、乘、截断减法三张表，每张表各有 Pairs 与 Op 两个集合；
- 全部森林、森林列表、网格空间；
- Keys 与 EN。

`Def(𝔇)` 即 `theoremDataFormula boundData`。

- **无自由变量。** 由 `mainFormula_freeClosed` 保证；ν 被约束在 ∀𝔇 之内。
- **不是空真。** 每个 KPω 模型中都有满足 `Def` 的 𝔇（`theorem_data_exists_d`），所以第一合取项为真，∀𝔇 也不会因前件不可满足而空真。
- **𝔇 唯一。** `TheoremData.Valid.unique` 证明满足 `Def` 的 𝔇 唯一，因此全称读法与存在读法表达同一个命题。
- **语义等价。** `mainSentence_iff hM free : satisfies ⟨Fin.elim0,free⟩ mainSentence.formula ↔ MainSemantic M`，其中

  ```text
  MainSemantic M := (∃ D, D.Valid M) ∧ ∀ D, D.Valid M → ConclusionClause M D
  ```

## 3. 辅助定义逐项对照

每一项都给出显式公式，以及证明公式语义等于对应 Lean 谓词的 `_iff` 定理。

| 文稿对象 | Lean 语义 | 公式 / 等价定理 | 核对 |
|---|---|---|---|
| ω | `M.IsOmega ω`：最小归纳集 | `isOmega`，`satisfies_isOmega_iff` | 模型内部 ω，不要求标准 |
| 0、1 | `∀x, x∉0`；`SuccessorOf 1 0` | `emptyFormula`、`successorFormula` | 0 同时是空序列与序数 0 |
| 有限序列空间 | s∈Seq ⟺ ∃m∈ω，`Graph s m ω` | `expressionValidFormula` | 长度取内部 ω |
| **E** | `Legal ω 0 1 s`（`OneYExpression.lean:13-19`） | `legalFormula_iff` | 见 §5.1 |
| 算术表（辅助） | `AdditionTable`、`MultiplicationTable`、`DifferenceTable` | `tableFormula`，配合 `sumFormula`、`naturalProductFormula`、`differenceFormula` | 只用于 E_N 的 Σ₁ 定义 |
| 森林、列表、网格空间（辅助） | `AllForests`、`Spaces.Valid` | `spacesFormula` | 同上 |
| Keys = E×ω，EN : Keys→E | `Expansion.Graph`：`IsProduct` ∧ `Graph` ∧（⟨key,t⟩∈EN ⟺ `CodedExpands key t`） | `expansionGraphFormula`。行为 `∃Box expansionMatrix.body`，由 `expansion_sigmaOne_iff_d` 精确读取 | EN 的行由 Σ₁ 证书定义，不是附加假设 |
| t = E_N(s) | `Step M D s N t` ⟺ `Expansion.Expands M C T s N t`（`TheoremData.Valid.step_iff_d`） | `Dynamics.expansionFormula` | N 取内部 ω；算法核对见 §5 |
| UncountableOrdinal(ν) | ν 是序数，ω∈ν，且不存在满射 f : ω ↠ ν（`Countability.lean:53`） | `uncountableFormula` | 即文稿的“ν>ω 且没有集合函数把 ω 映满 ν” |

## 4. 结论逐项对照（`KP1Y/OneYTheoremClauses.lean`）

| 文稿定理 1 | Lean 语义 | 核对 |
|---|---|---|
| ∃ 序数 χ≤ν ∃ 集合函数 μ:E→χ | `RankClause`：∃χ μ，`RankWitness M C T χ μ` ∧ (χ=ν ∨ χ∈ν)。`RankWitness`（`OneYRankStatement.lean`）要求 `IsOrdinal χ`、`Graph μ E χ`、`μ(∅)=∅`、`RankDescends` | ν 是约束变量；χ≤ν 写成 = 或 ∈；μ 在**全部** E 上有定义 |
| μ(∅)=0 | `MemPair μ C.zero C.zero` | 空表达式与序数 0 都是 ∅ |
| s≠∅ ⇒ μ(E_N(s))<μ(s)（N<ω） | 对所有 s∈E、s≠∅、N∈ω，以及所有满足 `Expands s N t` 的 t，有 μ(t)∈μ(s)。公式通过 Keys/EN 读取（`rankDescent_graph_iff`） | 覆盖全部内部 N；EN 是全函数，所以两种读法等价 |
| t≺s ⟺ t≠s 且 t=E_N(s)，N<ω | `PrecedesIn ω Keys EN t s` | 与文稿逐字一致 |
| ≺ 良基 | `WellFoundedClause`：每个非空内部 X⊆E 都有 ≺-极小元 | 只对内部集合；不是宿主良基 |
| 每条展开轨迹到达 ∅ | `TerminationClause`：若图 H:ω→E 满足每步 H(i+1)=E_N(H(i))（N∈ω），则存在 i∈ω 使 H(i)=∅ | 每步的 N 可以不同，比固定控制序列的版本更强 |
| Desc(s)：s 的有限步后代，含 s | 对每个 s∈E 有集合 X：x∈X ⟺ x∈E ∧ `Reaches x s` | 路径长度为内部 ω，steps=0 时即为 s 本身 |
| G：种子 (1,m)（m≥2）的后代 | 存在集合 X：x∈X ⟺ x∈E ∧ ∃r（`Seed r` ∧ `Reaches x r`） | `Seed r`：∃m∈ω，1∈m，r=(1,m)；合法性已证（`Seed.legal_d`），不是额外条件 |
| 字典序，真前缀较小 | `Lex`：存在 i<\|t\|，在 i 之前一致，且 i=\|s\| 或 s(i)<t(i) | 与文稿一致 |
| 字典序良序 Desc(s) 与 G | `LexWellOrder`：非自反、传递、三分，且每个非空内部子集有最小元 | **只**断言 Desc(s) 与 G，不断言全部 E |

文稿把 ≺ 良基、轨迹终止、良序写成由 (1) 推出的“Hence”。闭句把它们放在同一个前件 UncountableOrdinal(ν) 之下，与秩子句并列。这些子句都不提到 ν，所以与文稿等强。

## 5. 算法层逐定义对照

本节由五路只读审读完成，所有引用位置都经过回查。下文“宿主”指 `formalization/OneY/…`，“对象”指 `KP1Y/…`。判定词：“一致”表示逐式相同；“约定下一致”表示存在表示约定差异，并已由所列对象引理调和。

### 5.1 表达式与合法性（命题关键）

- **宿主：** `ZeroY/Syntax.lean:15`，`Legal s := (∀v∈s, 0<v) ∧ (s=[] ∨ head? = some 1)`。
- **对象：** `LegalAt`（`OneYExpression.lean:13-19`）要求 m∈ω、`Graph s m ω`、所有值 >0，并且 m=0 或 s(0)=1。`ExpressionData.Valid.expressions` 定义 E 为全部合法序列。
- 空序列恰为 ∅：`legal_zero_length_iff_d`（`OneYMinimumRank.lean:134`）给出 m=0 ⟺ s=∅；长度唯一由 `legal_length_unique` 给出。
- 没有种子条件，也没有标准性条件。

**判定：一致**（同时与文稿的 E 一致）。

### 5.2 展开的三个分支（命题关键）

对象 `Expands`（`OneYExpansionCore.lean:80-83`）与宿主 `expandValues`（`Expansion.lean:119-126`）对照：

1. **空输入。** 宿主中 `x = 0−1 = 0`，`findBadRoot [] 0 = none`（第 0 列为填充列，值为 1，没有父项），结果为 `[].take 0 = []`。对象分支为 m=0 时 t=s，`Expands.empty_iff_d` 进一步给出 t=∅。即 E_N(∅)=∅。**一致。**
2. **无坏根，删除末项。** 宿主条件为 `findBadRoot = none`。由 `findBadRoot_none_iff` 与 `Row.parent_none_iff_one`，它等价于末项为 1，输出 `s.take x`。对象直接写“末项=1 ∧ t 为长度 last 的前缀”。等价性由以下引理给出：
   - `no_bad_iff_one_d`（`OneYExpansionCore.lean:219`）；
   - `bad_at_exists_iff_d`（`OneYBadRoot.lean:320`）；
   - 分支互斥由 `Successful.not_last_one_d`（`:150`）给出。

   **约定下一致**：宿主写成“无坏根”，对象写成“末项=1”，两者已证等价。
3. **有坏根，复制并重建。** 对象 `Successful`（`:62-75`）依次包含：
   - 线性森林与初始选择；
   - `LayerRun`；
   - `BadAt … K level last root`；
   - `Horizon`；
   - 复制坐标与 `Width`；
   - `Tower`（B=horizon）；
   - `AllOne` 顶层；
   - `Assembles`。

   这与宿主 `reconstructedValues (expandedGraphs … (sequenceBound s)) (x + N*(x − z.column))` 逐项对应，细节见 §5.3–§5.8。**一致。**

**总性与唯一性。** `expands_exists_d` 与 `Expands.unique_d`（`:191`）成立。唯一性经 `Successful.unique_d`（`:157`）依赖坏根唯一（`BadAt.unique_d`），这对应宿主 `badAt_unique`、`rootAddress_unique`，也正是宿主取 `head?` 结果唯一的原因。

### 5.3 N 的含义与宽度（命题关键）

- **宿主：** `CopyCoordinates.lean:19-24`，`width N = x + N*(x−y)`，`expandValues` 传入 `x + N*(x − z.column)`。
- **对象：** `Width A N w := Encode A A.last N w`（`OneYCopyCoordinates.lean:443`），即 w = last + N·(last−root)，其中 length = last ∸ root（`Valid`，`:51`）。
- `width_as_bms_d`（`:447`）把它改写为 root + (N+1)·length，即“N+1 份完整坏块”，也就是 **N 份额外复制**。
- N=0 时宽度为 last，即删去末列：`width_zero_d`（`:595`）、`expands_zero_iff_drop_d`（`OneYExpansionPrefix.lean:197`）、`Graph.zero_iff_drop_d`（`OneYExpansion.lean:847`）。对应宿主 `expandValues_zero`（`ExpansionProperties.lean:88`）。即文稿的 E_0 删除末项。
- 宿主的已核查算例（`ExpansionExamples.lean`）与文稿描述一致：
  - E_3(1,2) = (1,1,1,1)；
  - E_3(1,3) = (1,2,4,8)，因而 E_1(1,3) = (1,2)；
  - E_3(1,3,1) = (1,3)。

**判定：一致。**

### 5.4 山形行与继承祖先选择（命题关键：它们定义 E_N）

| 宿主 | 对象 | 判定 |
|---|---|---|
| `ofSequence s = select linearForest (s[c]?.getD 1)`（`NumericGeometry.lean:75`） | `LinearForest`（`OneYLinearForest.lean:9`）配合 `Selects true … W.linear s W.initial`（`OneYExpansion.lean:254`）；`linear_forest_ancestor_iff_d`（`:103`） | 约定下一致：宿主用值 1 填充到无穷宽，对象用有限宽 m。选择只向左看、只依赖前缀，由 `restricted_parent_prefix_iff_d`（`OneYForestSelection.lean:387`）调和 |
| `restrictedParent`：继承森林中 c 的严格祖先 p（`ancestorChain` ≅ TransGen）里取最大者，要求 0<v(p)<v(c)（`Numeric.lean:16`） | `ParentCandidate` / `RestrictedParent`（`OneYForestSelection.lean:26,63`）；`Ancestor` 为严格祖先（`OneYAncestry.lean:153`） | 一致。宿主的“最大者”写成“q∈c → q=p ∨ q∈p”；宿主的 0<v 写成 `C.zero∈v` |
| `Row.difference`：无父项为 0，否则 v(c)∸v(p)；`Row.next = select a.forest difference`（`:62-67`） | `DifferenceAt`（`OneYMountain.lean:18`，用 `TruncatedDifference`，参数顺序正确）；`RowNext`（`:167`）继承的框架是旧森林 P | 一致。宿主“缺格=0”，对象是全值图中显式的 0 |
| `rows` 无行数上限；`topSearch` / `height` / `topValue`（`:104-201`） | `RowRun`（`:395`，在内部 ω 上无上限）；`HeightAt`（`OneYMountainHeight.lean:301`）、`TopValueGraph`（`:493`） | 一致。预算、存活、父项与高度、顶层无父项等各条引理一一对应 |
| 抽取：`Pseudo.Candidate`（`Pseudo.lean:16`）要求在第 `height c − 1` 行是祖先，且 h(p)=h(c) 或 h(p)+1=h(c)；`rawExtract = select (Pseudo.forest) topValue` | `PseudoCandidate` / `PseudoParent` / `Extraction`（`OneYMountainExtraction.lean:10,62,143`） | 一致。h−1 是截断的 `PreviousLength`，并要求 0∈h(c) 才有父项 |
| `layers base k` 对一切 k（`Extraction.lean:169`） | `LayerRun`（`OneYMountainLayers.lean:67`），在内部 ω 上全定义且唯一（`LayerRun.unique_d`，`:151`） | 一致 |

### 5.5 坏根（命题关键）

- **定义。** 宿主 `BadAt a k r c p`（`BadRoot.lean:18`）：第 k 层第 r 行中，c 的父项为 p 且 v(c)=v(p)+1。对象 `BadAt` / `RowBadAt`（`OneYBadRoot.lean:58,25`）为 `MemPair F c p` 且 `SuccessorOf y x`，即 y=x+1。c 均取最后一列。**一致。**
- **搜索范围。** 宿主只搜索 k < `sequenceBound s` 且 r < height。对象 `BadAt` 不设范围。两边的范围限制实际都不起作用：
  - 宿主的 `badAt_layer_bound` 与对象的 `BadAt.successor_layer_lt_initial_d`（`:331`）、`bad_in_horizon_d`（`OneYExpansion.lean:376`）都证明坏根必然落在 horizon 之内；
  - 再加上唯一性（宿主 `badAt_unique`，对象 `BadAt.unique_d`，`OneYBadRoot.lean:287`）。

  所以对象既不会多收、也不会漏掉宿主找到的坏根，也不涉及选择。Δ₀ 证书 `CompleteCalculation.bad` 中多出的合取项 “K ∈ horizon” 是冗余的，由 `complete_calculation_exists_d` 补上。**一致。**
- **存在性。** 宿主 `sequence_badRoot_exists` 对应对象 `bad_at_exists_iff_d`：存在坏根 ⟺ 1∈s(last)。**一致。**

### 5.6 界：horizon 与 max(1, maxValue)（命题关键）

- **宿主：** `sequenceBound s = max 1 (maxValue s)`（`Extraction.lean:76`），复制塔共 `sequenceBound` 层。
- **对象：** `SequenceBound`（`OneYExtractionBounds.lean:231`）是**严格**界，即最小的 B 使 0∈B 且所有值 ∈B，对非空序列为 max+1。`Horizon`（`OneYExpansionCore.lean:11`）取其前驱。
- `Horizon.original_sequence_bound_d`（`OneYExpansion.lean:871`）证明：对非空合法输入，horizon 被某个值取到、≥1、且是所有值的上界。因此 horizon = max(1, maxValue) = 宿主的 sequenceBound。
- 空输入不经过 `Horizon`（m=0 分支）。复制塔层数 B = horizon（`Tower`，`OneYCopyTower.lean:307`），与宿主 `List.range (sequenceBound s)` 同长，**没有差一**。

### 5.7 复制坐标与三类单层复制（命题关键）

| 内容 | 宿主 | 对象 | 判定 |
|---|---|---|---|
| raw 坐标 | `source c = y+1+(c−y−1)%L`，`block`，`encode`，`parentCopy`（`CopyCoordinates.lean:19-26`）；raw 源区间 (y,x] | `Source`（`:93`，root<s≤last）、`RawDecoded`（`:255`）、`Encode`（`:141`）、`ParentCopy`（`:858`）；`raw_decoded_iff_remainder_spec_d`（`:694`）把它与宿主取模公式逐字对应 | 一致 |
| ordinary 坐标 | `source0` / `block0`，区间 [y,x)（`OrdinaryCopy.lean:20-25`） | `Decoded`（`OneYOrdinaryCoordinates.lean:12`） | 一致 |
| raw 接缝 (x,b) ↔ ordinary (y,b+1) | 宿主隐含 | `raw_seam_decoded_d`（`:74`）、`encode_seam_bms_d`（`OneYCopyCoordinates.lean:464`）；非接缝不变：`raw_nonseam_decoded_d`（`:63`） | 已调和 |
| Lower（k<K） | `floor`、`rise`、`InCone`（`LowerCopy.lean:23-26`）；`height`：c≤x 时取原值，否则锥内取 height s + b·rise（`:62-67`）；`parent`：r≥floor 时行号平移，否则用 `parentCopy`（`:137-148`） | `Context.Valid`（`OneYLowerCopy.lean:99`）；`InCone`（`:152`）；`Height`（`:250`）；`Parent`（`:603`），配合 `MovedParent`（`:596`）与 `ShiftedRow`（`OneYLowerRowShift.lean:53`） | 一致（已逐式复读）。“Lower 保留 c≤last”，与 Terminal 的约定差一由 `Height.uniform_d`（`:445`）统一 |
| Terminal（k=K） | `height`：c<x 时取原值，raw 源=x 时取 height y，否则取 height(source)；`parent`：raw 源=x 且 level≤r 时读 y 的父项，**不平移**（`TerminalCopy.lean:29-39`） | `Height = Ordinary.Height`（`OneYTerminalCopy.lean:11`）；`Parent`（`:20`），配合 `HighSeam`（`:14`）；`height_raw_seam_iff_d`（`:142`）、`parent_raw_high_iff_d`（`:437`）；`active_from_bad_d`（`:381`）给出 level=d、height(last)=level+1 | 一致（已逐式复读）。“Terminal 保留 c<last；高接缝读原 root 且不平移” |
| Ordinary（k>K） | `copyValue`、`height = height(source0)`、`parent = map parentCopy`（`OrdinaryCopy.lean:106-111`） | `Ordinary.Height` / `Ordinary.Parent`（`OneYCopiedMountain.lean:176-183`） | 一致 |
| 分层 | `expandedMountain`：k<K 用 Lower，k=K 用 Terminal，否则用 Ordinary（`Expansion.lean:20-29`） | `Branch`（`OneYCopyTower.lean:170-173`）：k∈K 用 Lower，k=K 用 Terminal，K∈k 用 Ordinary；`Branch.unique_d`；三支共用同一组 A.last=x、A.root=y（`tower_from_bad_exists_d`，`:774`） | 一致 |

### 5.8 数值重建（命题关键）

| 内容 | 宿主 | 对象 | 判定 |
|---|---|---|---|
| 单座山的列递推 | `value r c = value (r+1) c + parentValue r c`，顶部取 top，高于顶部的格为 0（`Reconstruction.lean:17-68`） | `ColumnSum` / `FilledColumn`（`OneYReconstruction.lean`）、`Reconstructs`（`OneYReconstructionGrid.lean:518`）；唯一性 `reconstruction_unique_d`（`:598`） | 约定下一致：对象只有有限行与列；以零填充，并用前缀不变性 `reconstruction_prefix_values_d` 调和 |
| 层的折叠顺序 | `assemble [] top = top`；`assemble (M::rest) top = value M (assemble rest top) 0`，第 0 层在最外（`TowerReconstruction.lean:10-12`） | `Run`（`OneYTowerReconstruction.lean:425`）：H(B)=Top，H(i)=CodeStep(G(i), H(i+1))，输出 H(0)；`Assembles`（`:448`） | 一致，下标相同 |
| 全 1 顶层 | `fun _ => 1` | `AllOne`（`:548`），只取宽度之内 | 约定下一致：父项只指向左侧 |
| 输出合法 | `reconstructedValues_legal` | `Assembles.legal_d`；`assemble_ones_exists_d` / `assemble_ones_unique_d`（`:672`） | 一致 |
| 原塔复原 | `assemble_sequence` | `original_tower_assembles_d`、`horizon_layer_all_one_d`（`OneYExpansionPrefix.lean:79,98`） | 一致 |

### 5.9 规范根图 A(s) 与 μ（证明内部，不影响命题）

- **原子。** 宿主 `rowAtom k M r c = ⟨k, rootAt r c, parent c, c⟩`（`RootIndexed/Diagram.lean:17`）。对象 `ActualAtom`（`OneYExpressionDiagram.lean:508`）的四元组为（层，第 r 行森林中 c 的根，父项，子项），行号 r 只作见证。**一致。**
- **枚举。** 宿主按层、列、行做 flatMap。对象 `Position = ((k·m)+c)·B + r`，`Filter.Filtered` 保留全部定义位置，因而保留重复。两侧只用到“e ∈ atoms”或 `EdgeAt`，顺序与重复都不影响语义（`Enumerated.edges_iff_d`，`:805`：EdgeAt ⟺ ActualAtom）。
- **层数上限。** 宿主 `exprDiagram = sequenceDiagram … (sequenceBound s)`（`ExpansionWellFounded.lean:51`），上限 K=max(1, maxValue)。对象的语义原子**不设上限**。`actualAtom_iff_bounded_d`（`:561`）配合 `LayerRun.parent_indices_below_d`（`OneYExtractionBounds.lean:420`）证明有界枚举是完备的。宿主中 k ≥ sequenceBound−1 的层没有父项（`sequence_layers_no_parents`），所以两侧原子集合相同。**集合相等，已调和。**
- **μ。** μ 取 A(s) 的最小可实现末标签（`DiagramMinimum`，`OneYDiagramMinimumRank.lean:97`），这正是文稿式 (9)。μ(∅)=0 由 `LastValue` 在宽度 0 时的约定给出。闭句只要求“存在”μ，所以这里任何偏差都只可能影响证明能否成立，不改变命题。

### 5.10 差一与约定总表

| 约定 | 宿主 | 对象 | 调和位置 |
|---|---|---|---|
| raw 源区间与 ordinary 块区间 | (y,x] / [y,x) | 两者都实现 | `OneYOrdinaryCoordinates.lean:63,74`；`OneYCopyCoordinates.lean:464,694` |
| raw 接缝与 ordinary 块编号 | (x,b) ↔ (y,b+1) | 同左 | `raw_seam_decoded_d` |
| Lower 与 Terminal 的保留列 | c≤x / c<x | 同左 | `Height.uniform_d`、`height_raw_seam_iff_d` |
| 高接缝父项 | 读 y 的父项，不平移 | `HighSeam`，读 root | `parent_raw_high_iff_d` |
| 界 | max(1, maxValue) | 严格界 max+1 的前驱 | `Horizon.original_sequence_bound_d` |
| 无坏根分支 | `findBadRoot = none` | 末项=1 | `no_bad_iff_one_d` |
| E_0 | 宽度 x | `Width A 0 w → w=last` | `width_zero_d`、`Graph.zero_iff_drop_d` |
| 宽度与缺格 | 用 1 填充到无穷宽、缺格=0 | 有限宽 m、显式 0 | `restricted_parent_prefix_iff_d`、`Selects.prefix_rows_d` |

## 6. 剩余前提

```lean
-- KP1Y/OneYCopyDescent.lean:15-24（Y05b，LANE-B/B2/C 进行中）
def CanonicalCopyBoundIn (M) : Prop :=
  ∀ E T D, E.Valid M → T.Valid M E → D.Valid M → D.omega=E.omega →
    ∀ s m last N t W, Expansion.Successful M E T s m last N t W →
    ∀ Old, CopyDiagram.Enumerated M E T D ⟨W.horizon,W.width,W.forests,W.codes,W.tower⟩ Old →
    ∀ n B, ExpressionGraph M E T D t n B → ∀ k q p c, EdgeAt M D B k q p c → EdgeAt M D Old k q p c
def CanonicalCopyBound : Prop := ∀ M, M.Models KP1Y.theory → CanonicalCopyBoundIn M
```

- **内容：** 实际输出 t 的规范图 A(t) 的每条边，都是同一座复制塔所枚举的复制图中的边，对应宿主的 `expandValues_diagram_of_badRoot` / `ExpansionRebuildPrefix`。它属于**证明内部**，不出现在闭句中。
- **已解除：** `OrderFacts`（`OneYSeeds.lean`，经 `order_facts_statement`），以及秩回传。秩回传由 M02/M03 完成，前提已归约到 `CanonicalCopyBound`（`rank_transfer_at_of_canonical`）。
- **完成判据：** 该前提解除后得到无条件的 `KP1Y.Derives mainSentence`，并须对其依赖闭包重新进行阶段核验与公理审计。

## 7. 发现与约定

**FINDING：无。** 本次核对的每一项（§1–§5）都与宿主算法及文稿一致，或在 §5.10 所列约定下由对象引理调和。下列 5 条是约定差异，记录在案，不需要修改：

- **O-1：坏根搜索证书的上界放宽了一位。** `bad_root_search_exists_d` / `badRootMatrix`（`OneYBadRoot.lean:354-471`）用严格界 max+1 限制 k 与 r，比宿主宽一位。坏根唯一且必在范围内，所以无害。该证书不在 `Expands` / `Successful` 链上。
- **O-2：一条界引理弱于宿主对应引理。** `LayerRun.value_one_of_bound_d`（`OneYExtractionBounds.lean:154`）需要 a≤k，宿主 `layers_one_of_bound` 只需 a≤k+1。它仍足以推出 `bad_in_horizon_d`。
- **O-3：A(s) 枚举上限宽一位。** 对象的有界枚举用 B=maxValue+1 层，宿主为 max(1, maxValue)。多出的层全为 1，没有原子；集合相等由 `actualAtom_iff_bounded_d` 证明。
- **O-4：Δ₀ 证书带冗余合取项。** `CompleteCalculation.bad` 多出 “K∈horizon”，由 `bad_in_horizon_d` 提供，与 `Successful` 等价（`certificate_sound_d` / `certificate_exists_d`）。
- **O-5：空输入的 horizon 约定不同。** 对空输入，对象 horizon 可为 0，宿主 sequenceBound=1。空输入走 m=0 分支，从不使用 horizon；`original_sequence_bound_d` 只对非空输入陈述。

## 8. 复核清单（Q01 验收项）

- [x] KP 公理表与文稿第 1 页逐项一致；对象层没有 AC、幂集、完整 Replacement 或完整 Separation。
- [x] 一阶语言为带等号的纯 ∈ 语言。
- [x] N 与所有长度取内部 ω；ω 由 `isOmega` 定义，不要求标准。
- [x] χ≤ν 写成 χ=ν ∨ χ∈ν，χ 为序数；ν 是约束变量；闭句无自由参数（`mainFormula_freeClosed`）。
- [x] μ 是定义在全部 E 上的函数图；μ(∅)=0；对全部非空 s 与全部 N∈ω 严格下降。
- [x] ∅∈E，且 E_N(∅)=∅；E_0 删除末项；E_N 恰做 N 份额外复制。
- [x] 继承祖先选择（`RestrictedParent`）、山形行、抽取、坏根、horizon、三类复制、数值重建均与宿主一一对应（§5）。
- [x] ≺ 与文稿逐字一致；良基与终止子句只涉及内部集合，不用依赖选择。
- [x] Desc(s) 含 s 自身；G 为种子 (1,m)（m≥2）的后代；Lex 以真前缀为小；良序只断言在 Desc(s) 与 G 上。
- [x] 辅助集合存在且唯一，`mainSentence_iff` 给出精确语义。
- [x] 宇宙：推导对 0 层模型完备；结论与宇宙无关。
- [ ] Y05b `CanonicalCopyBound` 被实际证明解除，随后重做阶段核验与公理审计。

## 9. 未能核验的部分

- **证明本身。** 只核对了定义与陈述，没有逐行重验所引对象引理的证明体，例如：
  - `greatest_below_exists_d`、`above_one_layer_lt_initial_d`、`parent_indices_below_d` 的证明；
  - `reconstruction_prefix_values_d`、`reconstruction_unique_d` 的证明。

  它们的正确性依赖阶段编译与公理审计，协调者报告第 15、17 批 PASS。
- **证书公式的 de Bruijn 编号。** `rowBadAtFormula`、`badFormula`、`expansionMatrix` 等的编号只通过其已证的 `_iff` 定理间接确认。
- **对象层 `FromRun` 的定义细节。** 只读到其使用处。
- **文稿引用 [1] 的中文手稿。** 未读。算法层以宿主 Lean 仓库为准，并用宿主算例（`ExpansionExamples.lean`）对照文稿的文字描述。
- **Y05b 尚未解除。** 因此“A(E_N(s)) 恰由同塔复制图给出”这一证明内部事实目前只是命名前提。
