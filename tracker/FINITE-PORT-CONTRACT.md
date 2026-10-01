# Y00：1-Y 有限算法迁移契约

日期：2026-09-13。状态：**源码审查及接口契约已完成；下列对象算法接口尚待实现**。

审查范围是原仓库 `formalization/OneY/RootIndexed/ExpansionWellFounded.lean` 中的 `OneY.RootIndexed.expand_lastRepresentation_lower`，以及它实际调用的复制、反射拼接、规范重建分支。原仓库未修改，未重新编译。机器可读清单见 [finite-port-map.json](finite-port-map.json)。

## 1. 结论与实现边界

1. **有限复制下降不需要先引入 WF(0-Y) 或 WF(BM4)。** `expand_lastRepresentation_lower` 的参数是标签关系的传递性、R 严格性、根指标弱化、`FiniteReflection`、旧表示、非空输出。证明通过有限次复制及规范重建得到新表示。`RelativeBlocker.framedStep_wellFounded` 的 BM4 良基性参数属于旁支；主链用到同文件的有限结构保持定理，不调用这条良基性定理。
2. 可复用的是 **ZeroY/Structural 的有限矩阵证明思路及原 1-Y 复制证明**。不能把宿主 `Nat` 的实例直接套到任意 KP 模型的内部 ω。每一归纳、列表遍历、最大元搜索和递归都要有实际对象公式及对象归纳/递归证书。
3. **山形状态必须保留父森林和继承候选。** 仅保留当前数值行会改变算法。尤其帧矩阵只在活动边界以上满足 S；不能把全矩阵 `Structural` 当作已知。
4. **重建必须连回实际数值输出重新提取的山形。** 证明“某个复制图有较小表示”不够。原 `expandValues_diagram_of_badRoot` 正是连接 `A(E_N(s))` 和复制图的关键证据。
5. 最终有限支线只交付引理 3 的下降，不使用初等高度、初始表示或全局 μ。这些仍由 C/M/O 支线提供。原导入闭包的 154 个 OneY/ZeroY 模块、23,397 行只是源码范围，**不是还需逐字迁移的工作量或完成比例**。

## 2. 原定理的真实调用主干

以下箭头是已逐段读取的证明调用，不是只根据 `import` 推断。路径均相对于原仓库 `formalization/`；机器清单记录声明所在行。

```text
RootIndexed.expand_lastRepresentation_lower
├─ 无坏根：Numeric.expandValues_of_no_parent
│  ├─ Numeric.findBadRoot_none_iff
│  ├─ RootIndexed.sequenceDiagram_take_isPrefix
│  └─ RootIndexed.proper_prefix_lowers_last_label
└─ 有坏根：Numeric.findBadRoot_sound
   ├─ RootIndexed.copied_diagrams_bounded
   │  ├─ RootIndexed.actualBlockScheme
   │  │  ├─ actual_splice_geometry
   │  │  ├─ copyNeeds_virtual / copyNeeds_levels
   │  │  └─ copyFacts_succ / copyTemplates_succ / copyControlRoot_succ
   │  ├─ initial_facts_hold / initial_templates_hold / initial_control_holds
   │  └─ blockScheme_bounded_representations      [对复制次数 N 的 Nat 归纳]
   │     └─ exists_bounded_representation_splice
   │        ├─ virtual_demands_from_templates / admissible_of_root_position
   │        ├─ FiniteReflection                 [唯一语义反射输入]
   │        ├─ representation_splice
   │        └─ reservoir_splice
   ├─ RootIndexed.expandValues_diagram_of_badRoot
   │  ├─ Numeric.expandValues_of_badRoot
   │  └─ RootIndexed.reconstructedValues_diagram
   │     ├─ reconstructedValues_diagram_isPrefix_of_height_bound
   │     ├─ Numeric.assemble_expanded_sequence_lower
   │     ├─ Numeric.lowerTowerRooted_select_linear
   │     ├─ Numeric.lowerTowerRooted_layers_mountain
   │     └─ Numeric.expandedMountain_height_zero_above_bound
   └─ representation_prefix / last_label_of_bounded_representation
```

主要源码：

| 文件 | 实际职责 |
|---|---|
| `OneY/RootIndexed/ExpansionWellFounded.lean:54` | 上述有限下降定理；同文件稍后的 `actual_expansion_wellFounded` 才消费宿主 `WellFounded lt`。 |
| `OneY/RootIndexed/Representation.lean` | 单块拼接、源事实保留、模板弱化、精确 Adm、内部 N 次复制所需的归纳不变量。 |
| `OneY/RootIndexed/ActualScheme.lean` | 用实际山形填写 BlockScheme 的每个几何字段。 |
| `OneY/RootIndexed/SpliceGeometry.lean` | 每条新边分为旧边、复制边或接缝边；按 k<K、k=K、k>K 分支。 |
| `OneY/ExpansionCanonical.lean` | 真实输出重新提取的所有层/父图正确，得到其图是复制图前缀。 |
| `OneY/LowerTowerRebuild.lean` | 从活动层向下重建整个塔，并证明外部线性候选选择、再次提取都恢复复制图。 |
| `OneY/LowerTowerInputs.lean` | `prefixTop/fixed/order/bound` 四项重建输入由旧层、活动层与下层复制引理全部证明。 |
| `OneY/TerminalCopyComplete.lean` | `badAtTerminal_restrictedParent`：活动复制图的父关系确为数值与继承候选重新选择出的父关系。 |

### 有限矩阵证明确实在重建主链中使用

一个可逐段追踪的实际调用链为：

```text
lowerTowerRooted_select_linear
→ lowerTowerBase_select_external
→ badAtTerminalBase_select_external             [活动层分支]
→ badAtTerminal_restrictedParent_external
→ badAtTerminal_external_seam_low
→ badAtTerminalBase_seam_order
→ NumericFrame.seam_keyLE
→ NumericFrame.expanded_entry
→ NumericFrame.expanded_relative_structure
→ RelativeBlocker.relative_structural_expand
→ depthRegular_expand / aboveS_expand_of_context
```

`seam_keyLE` 还实际调用 `DecoratedColumn.lifted_le`、`newroot_suffix_lt_ghost`、`suffix_copyColumn_eq_lifted`；`TerminalFrameParents.expanded_parent_parentCopy` 调用 `BMS.parent_copyColumn_nonroot`、`BMS.parent_expand_prefix` 等有限父图运输引理。迁移时可裁剪未用的 WF/后代比较出口，不能裁剪这些帧、深度、阻挡和数值次序证明。

### 良基性与有限归纳的分类

| 源码位置 | 实际内容 | 对象迁移处理 |
|---|---|---|
| `OneY/Forest.lean` 的 `root/depth`，`FirstMatch.lean`，`PseudoCollapse.lean` | `termination_by c`，每次移到严格较小的列。 | 以内部列界给燃料，或对实际公式作内部强归纳；不需要外部 membership 良基。 |
| `OneY/Reconstruction.lean:14` 的 `value` | 对列 c 的良基递归；每次父列 p<c。 | 采用 `ReconstructionCompute.valueFuel`，燃料 c+1；`value_eq_compute` 已给宿主算法对照。对象版须独立证明总性及重建方程。 |
| `Numeric.rows_value_budget / rows_zero_of_bound` | 每个活值消耗行号预算。 | 对内部 r∈ω 归纳，得行高的实际内部有限界。 |
| `Numeric.layers_value_budget / layers_one_of_bound` | 每次提取使大于 1 的值下降。 | 对内部 k∈ω 归纳；这是一次山形构造的有限性，不是展开终止性。 |
| `RootIndexed.blockScheme_bounded_representations` | 对 N 的归纳，逐块反射并保留源事实、模板、控制边。 | 对存在表示的**可定义公式**作对象自然数归纳；无需选择整条外部无限标签序列。 |
| `RootIndexed.expansion_accessible_of_lastRepresentation / actual_expansion_wellFounded` | `Acc lt beta` / `WellFounded lt`。 | 不复制到 Y 支线；最终由实际序数值集合函数 μ 接到对象秩论证。 |
| `RelativeBlocker.framedStep_wellFounded` | 从 `WellFounded YesMetaZFC.BMS.Step` 传输到任意固定 base 的 FramedState。 | 非本路线前置。不能从导入该文件推断主复制定理需要这条前提。 |
| `ZeroY/BMS/AnyArray.lean` 的 `step_wellFounded_any` | `RepresentationDescentSystem` 与 `frame.lt_wellFounded` 给任意 ValidArray 的一步良基性。 | 同样是旁支。可作为未来 0-Y 独立项目的入口，不能当作本文已证明的对象定理。 |

旁支检查范围：对原 `formalization/OneY`、`formalization/ZeroY` 全部 Lean 源文件检索 `framedStep_wellFounded`，只出现该声明和同文件 `#print axioms`；未见调用。`step_wellFounded_any` 的外部调用位于 `ZeroY/BMS/PaddedDescent.lean`、`ZeroY/Dynamics/Equivalence.lean` 等 WF/后代支线；本次有限复制调用链不使用其结果。本文给的是源码调用审查，不冒充已重新导出的 Lean 内核常量依赖图；JSON 的完整 import 闭包单独标为 `import_graph`。

## 3. 冻结的对象编码：Y01 可以立即实现

命名空间建议 `KP1Y.OneYFinite`。**下文新名字均为待实现规范**。任意模型 `M : SetTheory.Structure` 满足 `M.Models KP1Y.theory`，内部 ω 为 `w`。所有算法索引和数值是 `M.Domain` 中的 w 元素；固定记录字段数可以用宿主 `Fin n`，可变长度不得用宿主 `Nat`。

### 3.1 表达式就是实际函数图

`NatSequence M w s m := M.mem m w ∧ Functions.Graph M s m w`。

`LegalAt M w z o s m` 精确为：

- `NatSequence M w s m`；z 是空集、o 是 z 的后继；
- 对每个 i∈m 和 v∈w，`MemPair M s i v → M.mem z v`；
- `m=z ∨ MemPair M s z o`。

`Legal M w z o s := ∃m∈w, LegalAt M w z o s m`。

长度不另加进表达式编码，直接从函数图唯一确定。空表达式是空函数图 z，长度 0；`[1]`、`[1,1]` 等保留不同定义域。**不要求由种子生成**。

交付 `ExpressionData α` 的字段固定为 `omega, zero, one, sequences, expressions`。其 `Valid M` 包含实际 IsOmega/Empty/Successor 证据、

```text
s∈sequences ↔ ∃m∈omega, Graph M s m omega
s∈expressions ↔ Legal M omega zero one s
```

存在性必须调用 `KP1Y.Sequences.finite_sequences_exist_d` 后作 Δ₀ 分离；同时提供 `legalAtFormula`、`legalFormula` 的 Δ₀/FreeClosed/满足等价。不能仅给元理论集合 `{s | Legal s}`。

Y01 最小可验收 API：

```text
expression_data_exists_d : KP(M) → IsOmega(M,w) → ∃ C, C.omega=w ∧ C.Valid M
legal_length_unique_d  : LegalAt(...,s,m) → LegalAt(...,s,n) → m=n
empty_legal_d          : C.Valid M → LegalAt(M,...,C.zero,C.zero)
legal_values_positive : LegalAt(...,s,m) → i∈m → s(i)=v → 0<v
legal_prefix_d        : LegalAt(...,s,m) → n≤m → ∃! t, Graph(t,n,w) ∧ t=s↾n ∧ LegalAt(...,t,n)
legal_drop_last_d     : LegalAt(...,s,m) → ∃! t, t=s↾pred(m) ∧ Legal(t)
seed_exists_d         : h∈w → ∃! s, s=[1,h+1] ∧ Legal(s)
```

以上 `∃!`、`0<v`、`s(i)=v`、`n≤m` 为易读缩写；实际 theorem 用 `M.mem`、`MemPair`、`Graph`、Empty/Successor 证据展开。不存在依靠对象选择公理确定长度、函数值或前缀的步骤。

### 3.2 Y01 的有限计算基础

现有序数加法/乘法不等于已经有可直接引用的内部自然数全部算术 API。Y01 明确负责：

- 内部后继、前驱/截断减法、加法、乘法、除法余数的图及唯一性；暂时不用的除法可以留给复制坐标任务，但不能另由两个 worker 各造一套。
- 有界最大值/最右满足者：在 b∈w 以下对一个**给定 Δ₀ 矩阵**搜索；输出 `none` 或唯一最大 p，不对任意宿主谓词声称可搜索。
- 有限自然数图的共同上界：复用 `FiniteNaturalRange.finite_natural_range_bounded_d`，为 max 值、矩阵行高等取得内部界。
- 对内部有限函数图的 map、fold/累计和、固定记录编码及有界循环证书；复用 `Functions.Graph`、`bounded_recursion_d`、`sigma_recursion_d`，逐项给 Total/Functional，不把待求算法自身的总性藏在前提里。

计算状态固定采用**自然数坐标的有限记录表**。元数固定的记录用已存在的 Kuratowski 对/积；记录表是 `Graph trace length recordSpace`，长度∈w。父项是部分函数图 `P⊆m×m`；不存在父项表示该列没有 P 行，避免把自然数 0 和 `none` 混同。输入数值行 V 是总图 m→w，0 表示缺失数值格。

循环/算法证书 `Run(program,input,output,trace)` 的每一步检查必须有 Δ₀ 公式；trace 存在性来自对象归纳/递归。若给定固定元数记录空间及其全部有限序列集合，量词 `∃trace∈TraceSpace` 有界；若消去这些辅助集参数，则只承诺已有构造能证明的 Σ₁ 复杂度，**不把任意未界定历史存在式叫作 Δ₀**。所需的实际运行图可通过 Σ₁ 收集和唯一性构造。

不要建立通用宿主 `Nat → State` 编译器后把其输入定义为所有内部自然数：这会遗漏非标准输入。可用固定程序作为元数据，但每个循环计数器、迹长度与记录值均须在 M 内量化。

## 4. 山形、父关系和提取契约（Y02）

### 4.1 父森林与一层数值山形

`Forest(M,w,m,P)` 是实际部分函数图，所有边 `(c,p)` 满足 `p<c<m`。祖先 `Ancestor(P,p,c)` 使用长度≤c+1 的内部父链证书；搜索和链成员关系在共同有限序列空间中可定义。`Root(P,c,q)` 为反复取父直到无父的 q，证明 q≤c、根唯一、根与父共享。

输入行含 **值图 V 与实际父图 P**，并满足每条父边 `0<V(p)<V(c)`。一般构造的 `Select(F,V)` 在继承森林 F 的 c 祖先中，选择最大的 p 满足 `0<V(p)<V(c)`。线性 F 仅用于最初序列及最终规范重建，不得在提取层中无条件重置。

`Difference(V,P)(c)`：P(c) 无定义则 0；P(c)=p 则 V(c)−V(p)。下一行取 `Select(P,Difference)`。保持同一内部列宽 m；不必把对象行扩成任意域上的外部总函数。

原算法把序列界外值默认设为 1。迁移可只存有限前缀，但必须证明 prefix-local：所有 c<m 的父链、值、根、提取结果仅依赖 <m 的输入，因此有限图版本等于原有默认扩展在前缀上的限制。

### 4.2 完整提取塔

塔证书保存 `(k,r,c)` 对应的数值/父项、每层每列高度、根，及提取所用候选森林；全部是实际有限记录表。原输入 `B=max(1,max values(s))` 是统一层数与原行值上界。

- 对 r 证明 `value(k,r,c)>0 → value(k,r,c)+r≤value(k,0,c)`。
- 高度 h(k,c) 为最后活行，`r≤h ↔ value>0`；父存在当且仅当 r<h。
- 提取值是顶部值；伪父取最右候选 p：p 是 `row(h(c)−1)` 中 c 的祖先，且 `h(p)=h(c)` 或 `h(p)+1=h(c)`。h(c)=0 时无伪父。
- 随后确实执行 `Select(pseudoForest,topValues)`，不能直接把伪父当最终数值父项；已有 `rawExtract_parent_eq_topForest` 等等价可在迁移后优化。
- 根值 1 保持；`value(k,0,c)>1 → value(k,0,c)+k≤value(0,0,c)`；k≥B−1 时全为 1、无父边。

`BuildMountain(s,T)` 应给对每个合法内部 s 唯一的规范塔 T，以及实际 graph 的总性。该构造只需内部有限归纳；**与每次展开的终止性无循环依赖**。

### 4.3 精确接到现有 Reflection.Diagram

规范表达式图 A(s) 的宽度 m 等于 s 长度。按 k、c、r 的自然顺序枚举所有 `k<B, c<m, r<h(k,c)`；令 `p=parent(k,r,c)`，`q=root(k,r,c)`，输出边码 `((k,q),(p,c))`。允许重复原子，枚举不做去重。图长度必须是内部自然数；删除伪边不能靠把长度换成任意无限集合。

交付：

```text
expression_diagram_exists_unique_d : C.Valid M → Legal(s) → ∃ m A, ExprDiagram(M,C,s,m,A)
exprDiagram_diagram_d : ExprDiagram(...) → Reflection.Diagram M C m A
exprDiagram_edge_iff  : EdgeAt M C A k q p j ↔ ∃r<h(k,j), parent(k,r,j)=p ∧ root(k,r,j)=q ∧ k<B ∧ j<m
exprDiagram_prefix_d : t=s↾n → ExprDiagram(t,n,A_t) → ExprDiagram(s,m,A_s) → n≤m ∧ edges(A_t)⊆edges(A_s)
```

`Reflection.Diagram` / `Template` 已有 Δ₀ 公式。边满足 q≤p<j<m；**不要加入 k<K 之类当前反射层上界**。A(s) 的实际有限界 B 是算法提取界，不能与反射控制层 K 混淆。模板码沿现有 `Packet(k,(q,p))`，不另发明另一种三元组。

## 5. 复制坐标、帧及实际展开（Y03–Y05）

### 5.1 坏根与额外复制次数

非空 s 令 x=m−1。`BadAt(T,K,d,x,y)` 是 `parent(K,d,x)=y` 且 `value(K,d,x)=value(K,d,y)+1`。证明坏根全局唯一及 K<B；原 `findBadRoot` 在 k<B、r<h(k,x) 内查找第一项，因唯一性与遍历顺序无关。

无坏根时 `Expand(s,N,t)` 为 `t=s↾x`，与 N 无关。有坏根时 y<x，令 L=x−y：

```text
width(N)=x+N*L
encode(source,b)=source+b*L          [实际源坐标的适用范围由坐标定理给出]
source(c)=y+1+((c−y−1) mod L)
block(c)=(c−y−1) div L
parentCopy(b,p)=if p<y then p else p+b*L
blockCut(b)=y+b*L
moveColumn(n,cut,i)=if i<cut then i else n+(i−cut)
```

以原 `CopyCoordinates.Context` 精确的 `source/block/parentCopy` 方程为规范。**反解源列区间是 (y,x]，不是 [y,x)**；source=x 表示接缝，第一处保留接缝列 x 的 block=0。不能将上面适用范围内的 `encode` 等式误当所有反向解码的总公式。N=0 输出删除末项；N=1 是一份额外坏块。

### 5.2 帧状态覆盖范围

`FramedState(base)` 的矩阵状态为 **任意** `ValidArray`，满足 `DepthRegular ∧ AboveS base`；前 base 行不要求 S，不要求矩阵从标准种子生成或是普通 ZeroY 编码像。

数值活动层的具体矩阵由 `OneY.NumericFrame.matrix` 产生。列宽为 width，森林帧占前 width+1 行，数值行 r 出现在 width+1+r；活动坏根位于宽 x+1 的矩阵行 `(x+1)+1+d`。`NumericFrame.maximalParentRow_eq` 证明 BM4 自己的搜索恰好选中此行；不能将该行作为额外假设指定。

Y03 应覆盖所有内部 width、cap、base、index 及满足这些有限条件的矩阵。所需有限结论包括实际 BM4 父图恢复、深度正规保持、`AboveS` 保持、父图复制、解码重建、装饰列/接缝比较。即使以后得到外部 0-Y 的 WF 证明，也必须核对其覆盖 **任意行数统一、任意相应带帧状态**，不是仅各固定标准高度或由标准种子生成状态。当前主路线不用该 WF 结论。

### 5.3 重建与再次提取

复制塔分 k<K 的下层参考填充、k=K 的活动复制、k>K 的普通复制。Y05 负责它的数值 `Reconstruct`：

```text
r>height(c) 时 v(r,c)=0
v(height(c),c)=top(c)
parent(r,c)=p 时 v(r,c)=v(r+1,c)+v(r,p)
```

取燃料 c+1 的 `valueFuel` 或等价有限动态规划，从左到右/每列从顶向下给实际函数图；所有值在内部 ω。输出值可能大于输入最大值，不能继续把输出值空间限制为 B。使用 ω 作值载域并由递归证明自然数闭合；需要有限数值上界时再从已得到的内部有限图取界。

由最高层全 1 向下 assemble。证明值图唯一，然后证明 `Select`、各层再次提取、所有父关系恰为指定复制图（不是只证明旧父边仍成立）；尤其需要最右合法候选的“无更近候选”方向。

最终交付：

```text
expand_exists_unique_d : C.Valid M → s∈C.expressions → N∈C.omega → ∃! t, Expand(M,C,s,N,t)
expand_legal_d         : Expand(...,s,N,t) → t∈C.expressions
expand_zero_d          : Expand(...,s,0,t) ↔ t=s↾pred(length(s))
expand_empty_d         : Expand(...,empty,N,t) ↔ t=empty
expand_diagram_prefix_d: BadAt(...) → Expand(...,s,N,t) → ExprDiagram(t,m_t,A_t)
                         → m_t=width(N) ∧ edges(A_t)⊆edges(CopyDiagram(T,B,N))
```

附加标准输入对照：对每个宿主合法 `s : ZeroY.Expr` 和宿主 N，证明其逐项内部 numeral 编码运行结果等于 `Numeric.expand s N` 的编码。此对照用于字面算法核验；任意内部输入总性/下降须来自前面的对象证明，不能由这个只覆盖标准输入的对照代替。

## 6. 单块语义拼接与 N 次归纳（Y04/Y06）

冻结共享纯几何产物：`CopyDiagram(T,B,b)`、`Cut(T,b)`、`ControlRoot(T,b)`、`Facts(T,B,b)`、`Templates(T,B,b)`、`Needs(T,B,b)` 均是实际内部函数图/有限列表，定义由 Y04 唯一负责。Y05 导入这些定义用于规范重建，不得另定义另一套复制塔。反过来 Y04 不证明数值重建、BM4 全局性质或重写 Y03 的帧算法。

必证字段逐项对应原 `BlockScheme`：

- 新宽度 n+(n−cut)、cut<n、controlRoot≤cut；下步 cut=n。
- 每条新边旧/CopyCase/SeamCase 三分；复制边的根或为移动后的源根，或位于旧段且源根≥cut。
- facts/templates/needs 的合法性；facts 与 templates 随 move 映射保留。
- needs 是 templates 的原根或更小前段根；层条件是 `k<K ∨ (k=K ∧ q<controlRoot)`。
- 据有序旧标签得到精确 Adm：`k<K ∨ (k=K ∧ q<cut ∧ f(q)<f(controlRoot))`。
- 反射生成 g 后 splice：前 n 列用 g，后块复用 f 的 cut 以后列；新图有序、所有标签<旧末标签 β，源事实、模板、控制边全部保留。

对内部 N 证明的是 `∃当前标签图` 的可定义归纳谓词，保持上述四项不变量即可；**不需先选一个在整个 ω 上给出每步标签的函数**。Y06 最终形状：

```text
KP(M), Reflection.Data.Valid M C, Table M C H,
ExprDiagram(s,m,A), Expand(s,N,t), ExprDiagram(t,n,B),
N∈C.omega, n≠0,
Reflection.Representation M C H m A f, f(m−1)=beta
→ ∃g b, Reflection.Representation M C H n B g ∧ g(n−1)=b ∧ M.mem b beta.
```

此处 `Table/Representation` 参数以现有真实声明为准；上式是语义形状，不能直接粘贴作已通过的 Lean 类型。严格性、根弱化、FR 必须从真实 Table 接口导出，不能留下新的“复制下降”公理。

## 7. 非标准输入与内模型回传验收

所有算法的关键可定义性、总性、唯一性必须对 `M.Models KP1Y.theory` 成立，不增加 ω 标准性、外部 `WellFounded M.mem`、对象选择/幂集/全分离。

为后续 L 回传预留以下具体义务：

1. L 与外部同 ω；内部自然数元及固定对/函数图的编码相同。
2. 由共同元素组成的内部有限序列、每次有界循环证书在 L 中存在，且原始公式对这些对象绝对；“在宿主看来有限”不够，因为 M 的长度可能非标准。
3. 算术图、有限表运行图的总性与唯一性在两个模型中都证明，然后由证书检查的绝对性识别同一输出。
4. `Legal/ExprDiagram/Expand` 的桥给双向一致；由实际 μ 图的标签和值定义域得到外部见证，而非只传输一句内部 WF。

Y01/Y02/Y05 交付 formula/Δ₀ 或 Σ₁/FreeClosed/满足等价，供 M 支线做绝对性。绝对性证明由 M 支线唯一负责；Y worker 不同时改写内模型基础。

## 8. 可立即派发的顺序与无重叠所有权

**当前最先实现 Y01a**。ExpressionData/Legal/长度/空/前缀可只依赖现有对象函数图与序列空间，得到稳定接口后才启动依赖它的算法模块。Y01b 的算术与有限运行图应继续由同一个 Y01 所有者负责，或先由协调者将该任务明确拆分到新文件；不要同时派两个 agent 改 `OneYFiniteComputation.lean`。

| 子任务 | 前置 | 独占文件/接口 | 可验收出口 |
|---|---|---|---|
| Y01a | Y00、现有 Functions/Sequences | `KP1Y/OneYExpression.lean` | 实际 E、精确 Legal、长度唯一、空、前缀、drop。 |
| Y01b | Y01a 的参数约定冻结 | `KP1Y/OneYFiniteComputation.lean` | 所需内部算术图、有界搜索/fold、有限运行证书。 |
| Y02a | Y01b | `KP1Y/OneYAncestry.lean` | 有限父图、链/根、restricted-parent 搜索、前缀局部性。 |
| Y02b | Y02a | `KP1Y/OneYMountain.lean` | 数值行迭代、height、pseudo 候选与提取。 |
| Y02c | Y02b | `KP1Y/OneYExtractionBounds.lean` | 内部提取界、坏根唯一、A(s)→Reflection.Diagram。 |
| Y03a | Y01b + Y02a 的 Forest 接口 | `KP1Y/OneYFrameTransport.lean` | BM4 有限父图/帧/实际活动行匹配。 |
| Y03b | Y03a | `KP1Y/OneYFiniteBlocker.lean` | relative S、copy order、装饰接缝/数值比较接口。 |
| Y04a | Y02c + Y03 约定冻结 | `KP1Y/OneYCopyInvariant.lean` | 唯一复制塔与坐标定义、source facts/templates、纯几何 BlockScheme。 |
| Y04b | Y04a + F06 | `KP1Y/OneYCopySeams.lean` | 模板 Adm、真实 FR 拼接、对象 N 次存在表示归纳。 |
| Y05a | Y01b + Y02b | `KP1Y/OneYReconstruction.lean` | 通用有限 Reconstruct/valueFuel、唯一性和前缀局部性。 |
| Y05b | Y05a + Y03b + Y04a | `KP1Y/OneYExpansion.lean` | 实际 Expand、规范重提取、A(E_N(s)) 前缀。 |
| Y06 | Y04b + Y05b + F06 | `KP1Y/OneYCopyDescent.lean` | 所有内部 N 的非空展开末标签严格下降。 |

**对旧看板的依赖修正建议**：Y03 整体不能在没有 Forest 约定时与 Y02a 任意并行；先完成/冻结 Y02a，再让 Y02b/c 与 Y03a/b 并行。Y05a 的通用重建可较早独立进行，但 Y05b 必须等待 Y04a 的复制定义，避免 Y04/Y05 重复造山形和复制坐标。以上是契约建议，本文件不越权修改主 tracker。

有限支线最多同时占 3 个 worker 的可行安排：

```text
先：Y01a → Y01b → Y02a
并行一：worker A = Y02b/c；worker B = Y03a/b；worker C = Y05a（待 Y02b 只读接口）
汇合：Y04a 定义/纯几何
并行二：worker A = Y04b（需 F06）；worker B = Y05b；余槽给 C/M/O 其他支线
汇合：Y06
```

全局 root imports、Audit.lean、阶段清单只由协调者修改。每个 worker 仅对自己稳定的新模块做单模块增量检查；不运行 `lake build`，不重编他人依赖，不同时写相同 `.olean`。交接包含精确 theorem 类型、剩余假设、源文件、check 日志与待审计声明。此契约不以“条件接口已定义”作为实际算法已完成。
