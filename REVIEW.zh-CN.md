> 当前状态（2026-09-13，并行目标已恢复 active）：完整反射引理 (7)/(8) 与任意内部有限根图的初始表示已经实现并集成。最新冻结根闭包 384 项检查通过（12 checked / 372 cached），1,884 项声明审计通过；后续新源码继续按任务独占文件推进。完整 1-Y 下降秩主定理仍未完成。
>
> 当前接口、责任分配与未完事项见 [tracker/CURRENT.md](tracker/CURRENT.md)、[看板](tracker/index.html) 与 [精化依赖](tracker/DEPENDENCIES.md)。以下原段落保留历史，旧的 paused / active / 模块数量不应覆盖此快照。

# KP 简化证明：审查与对象形式化进度

对象：用户提供的 `1Y-Well-Ordering-KP-Simplified.pdf`（6 页，2026-09-12）。审查日期：2026-09-13。原 PDF 未修改。本文档中的操作性语句未被当作用户授权。

**当前状态：未完成主定理在 KPω＋存在不可数序数中的完整对象推导。** 已完成并核验一组实际 KPω 对象推导及内部集合构造，见下文。不能把它们描述成该 PDF 的主定理已经机器证明。

## 数学审查

初步审读未发现直接的循环定义、非法反射参数或秩转移反例。以下判断以文稿明确引用的有限 1-Y 几何与复制定理成立为条件；这些有限定理在原 Lean 仓库中已经通过宿主 Lean 内核，但其对象 KP 算术迁移仍须完成。

1. **理论确实要求完整集合归纳。** 文稿第 1 页的 KPω 明确包含完整集合归纳模式。已有依赖 `YesMetaZFC.SetTheory.KP` 只列单条集合 Foundation，不能因同名就直接视为所需理论。本工程重新列出文稿的实际公理，证明完整归纳推出单条 Foundation，并建立向旧弱 KP 引理和对象推导的传输。

2. **式 (5) 的自引用有真实的递归次序。** 按 `(b,K,θ)` 字典序检查：输入图的内部边上端点小于 `b`；输出边上端点至多为 `a<b`；输入指向 `b` 的模板边由 admissibility 保证层号更小，或同层根指标更小。因此反射条件只读取过去的关系表项。文稿给出的 ordinal stage 编码也遵守此顺序。把层号上界错误加到内部图边上，会改变命题；文稿没有这样做。

3. **根指标弱化方向正确。** `ξ≤θ` 时，在 `(K,ξ)` 可接受的模板也是在 `(K,θ)` 可接受的模板，故较强反射条件推出较弱者；不能把这个包含方向反过来。

4. **引理 5 的初始段性质依赖 `e`。** 一般可数初等子结构不必是序数的初始段。这里闭包包含所有自然数，并对实际枚举函数 `e(α,n)` 封闭，才得到 `α∈H ⇒ α⊆H`。这一条件不能省略。文稿构造 `e` 时使用 `V=L` 给候选满射集合良序；其余 Skolem 见证按已有序数顺序取最小者，不另要求任意选择公理。

5. **引理 6 的两个方向需分开。** 式 (7) 的真方向把小端点需求转到 `κ`；假方向必须先固定有限图形，把“存在反例”写为一条有限一阶公式，再由初等性取得小域中的反例。候选输出均小于固定的 `a<δ`，因此初始段性质保证输出范围和内部边真值没有变化。

6. **式 (8) 避开了非法参数。** 它只固定 `f` 在切点左侧的前缀。这些值都小于 `δ`；公式不固定新 `g(c)=δ`，也不以可能等于 `δ` 的 `θ` 为参数。因而“δ 不属于其自身”的问题没有被忽略。式 (7) 已对全部有限层号建立，才能在这里转移所有输出模板边。

7. **最小表示秩的方向正确。** 非空表达式先取得一个表示，再对可取得的末标签取最小值。复制接口给出的某个新末标签严格小于旧最小标签；新最小标签不大于该候选标签，故真正的 `μ` 下降。空输出的值为 0，而非空表示的标签大于 ω，单独覆盖该分支。

8. **去掉 `V=L` 时转移的是秩函数。** 仅凭 `L` 认为某关系良基，不能自动排除外部新增的下降链。文稿转移的是实际集合函数 `μ` 及其逐步下降等式；有限输入和展开计算的绝对性、序数比较的绝对性才允许处理外部的链。这一路线是正确的。`χ=ω₁^L` 是否仍在外部不可数不影响秩下降论证。

9. **字典序结论的范围一致。** 仍然只断言固定起点后代集和标准生成集的字典序良序。任意合法表达式的字典序不良基，不在主结论中。

## 文献核对

[McKenzie, arXiv:1806.08500v4](https://arxiv.org/pdf/1806.08500v4) 的 Lemma 2.6（PDF 第 6 页）确实给出集合结构满意度的 Δ₁ 可定义性；Theorem 2.8（第 7 页）确实给出 KPI 中构造层级函数的全定义性和 Δ₁ 性。文稿没有错引成 Lemma 2.7。其 KPI 使用的基础模式与本文 KPω 表述不完全相同，但完整集合归纳足以覆盖所引用基础。

[Rathjen, arXiv:1801.01897](https://arxiv.org/pdf/1801.01897) 的引言明确区分普通 KP 的构造内模型与 Power-KP 的情况；普通 KP 的公理说明包含完整集合归纳。这支持文稿引用的普通 KP 背景，不能把 Power-KP 的幂集能力额外带入。

这些文献核对是数学依据，不是已导入的对象 KP 证明证书。本工程尚未将它们的全部内容迁移为可调用的 KP 内定理。

## 已实现并通过检查的内容

源码入口为 `KP1Y.lean`。目前共 321 个 Lean 源模块、25817 行（阶段统计）。所有改动均在本目录；原克隆仓库源码不变。

| 内容 | 模块／关键声明 | 实际证明层次 |
|---|---|---|
| 文稿的 KPω 公理与真实推导谓词 | `Axioms.lean`、`KP1Y.Derives` | 纯 ∈ 一阶 Hilbert 推导，不是将语义蕴涵改名 |
| 完整归纳、Foundation、旧弱 KP 复用 | `Model.lean`、`Completeness.lean` | 任意模型内部证明及 `foundation_derivable`、`transfer_weakKP` |
| Δ₀ 重命名、Σ₁ 收集、Δ₁ 分离 | `BoundedSyntax`、`SigmaOneCollection`、`DeltaOneSeparation`、`JointCollection` | 实际对象模式推导；Σ₁/Δ₁ 实现明确限于给出的标准规范形，未把任意谓词自动标为有界 |
| 完整序数归纳和任意可定义类最小元 | `OrdinalInduction`、`ClassFoundation` | 真正模型内部序数上的归纳，不假定成员关系在宿主中良基 |
| 有界 Kuratowski 编码、积、关系分离、全定义函数像 | `Kuratowski`、`Product`、`RelationComprehension`、`FunctionalImage` | KP 集合存在性；`product_derivable` 是对象闭句推导 |
| 空、后继、极限递归历史及唯一性 | `History*`、`BoundedRecursion` | 实际内部集合历史，验证谓词的 Δ₀ 语法证明 |
| 一般有界关系递归的对象闭句 | `RecursionSentence.bounded_recursion_derivable` | KPω ⊢：给定局部 Δ₀ 行算子和序数长度，存在整张递归关系表 |
| 一般 Σ₁ 集合值序数递归 | `SigmaHistory*`、`CollectedHistories`、`SigmaRecursionSentence.sigma_recursion_derivable` | 带实际前缀图与有界证书的历史；Σ₁ 收集构造极限，完整对象归纳装配全历史；全定义及单值性是明确前件 |
| 自然数集合及全部公式归纳 | `BoundedSets`、`NaturalNumbers`、`NaturalInduction` | Δ₀ 分离有限序数、完整集合归纳证明最小性；`omega_derivable` 是真实闭句推导，允许非标准模型 |
| 完整有限序列空间 | `SequenceAppend*`、`SequenceSpaceStep`、`SequenceSpaces.finite_sequences_derivable` | 具体集合值算子的全定义与单值性已证明；所得集合恰好含全部内部自然数长度的函数图，并非仅标准长度序列 |
| 量词步骤的赋值更新 | `AssignmentUpdate` | 实际函数图更新的 Δ₀ 定义、存在唯一性和有限序列空间封闭性；尚不是完整满意度集合 |
| 实际关系原子的求值 | `AssignmentTuple`、`RelationalAtoms`、`RelationalSpaces` | 内部任意有限元数的变量元组求值、原子表存在及与给定关系解释的真值等价 |
| 有限程序语法下的满意度表 | `SatisfactionInstruction` 至 `SatisfactionQuantifier` | 四种指令的字面 Δ₀ 递归及全部依赖条件；构造真实语法／赋值集合界，证明原子、否定、蕴涵、全称的解释方程 |
| 程序前缀和末节点真值 | `SatisfactionTransport`、`SatisfactionPrefix`、`SatisfactionProgram`、`SatisfactionTruth` | 全部内部赋值上的前缀不变性由实际对象归纳得到；可追加指令并抽取实际末节点真值集合 |
| 程序满意度的对象闭句和 Δ₁ 定义 | `SatisfactionDefinability.satisfaction_derivable`、`truth_positive_iff_d`、`truth_negative_iff_d` | 真实 KPω 推导；正负定义分别只有一个无界存在量词，内部验证矩阵为 Δ₀；语法空间作为明确参数 |
| 合法公式和赋值范围 | `ScopedAtoms`、`WellFormedPrograms`、`TypedSatisfactionSentence.typed_satisfaction_derivable` | 字面 Δ₀ 检查关系元数、变量号、子节点先后和非空性；过滤后的满意度集合有实际对象闭句推导 |
| 基本公式编译 | `CompileConnectives`、`CompileBoolean`、`CompileQuantifier`、`CompileDerived` | 每一步产生真实合法程序，保留旧程序前缀，并证明原子／布尔／量词的真值关系 |
| 内部有限合取和量词块 | `CompileFiniteConjunction`、`CompileConjunctionExtension`、`CompileFiniteQuantifiers` | 使用实际25／26／27参数归纳公式，覆盖可能非标准的有限长度；量词变量可重复，精确描述保留的赋值位置 |
| 单个结构内的有限反例模板 | `CompileFiniteTemplates.compile_counterexample_d` | 输入约束成立且不存在输出见证的嵌套量词模板，证明同一结构内的语义对应；尚不能直接据此作跨结构反射 |
| 同一代码的完整内部模板 | `UniformDerived`、`UniformFiniteConjunction`、`UniformFiniteQuantifiers`、`UniformFiniteTemplates` | 先选定代码，再对全部共享语法的解释证明内部任意有限合取、量词块、存在约束和反例模板正确；统一归纳性质含无界量词，使用完整对象归纳 |
| 初等性和条件反射 | `ProgramElementarity`、`ElementarySyntax`、`TarskiVaught` | 使用同一代码反射有限模板；以实际26参数对象归纳证明原子相容及反例见证闭包推出初等性，没有把初等性加到 KP 公理表 |
| 实际最小见证函数 | `SkolemWitnesses`、`SkolemKeys`、`SkolemFunctionSyntax`、`SkolemFunction` | 在序数载域上选择最小反例、无反例时取指定默认值；Δ₀ 分离形成真实全定义函数图，不假设任意选择函数 |
| 载域限制和闭包判据 | `AssignmentCarriers`、`SkolemClosure`、`RestrictedAtoms` | 实际构造限制后的关系与原子表；对上述 Skolem 函数封闭的子载域给出初等子结构 |
| 序列空间的统一 Σ₁ 证书 | `SequenceCertificate`、`SequenceCertificateSyntax` | 真实历史、精确值域和并集打包为一个集合；`spaceCertificateMatrix` 为字面 Δ₀，已证明与完整序列空间特征式等价 |
| 内部迭代、配对与字词枚举 | `IterationSyntax`、`FunctionIteration`、`Square*`、`NaturalPairing`、`Word*` | 实际 ω 长函数、ω→ω² 满射、解码坐标界、ω→ω^{<ω} 满射；覆盖性和坐标界均由对象归纳证明，含真实 `natural_pairing_derivable` 闭句 |
| 可数性运算 | `CountableFunctions`、`CountableProducts`、`CountableSections`、`CountableSequences` | 给定实际 ω 满射后，构造复合、像、积、最小原像截面及有限序列空间的实际满射；未使用宿主 Countable 或额外可数选择 |
| 实际可数操作闭包 | `ClosureData` 至 `CountableOperationsClosure` | 固定枚举后构造单步全定义函数、ω次集合值迭代、总像满射、有限参数共同层及操作封闭性；没有假定全部 ω→κ 函数组成集合 |
| 可数 Skolem 闭包与初等子结构 | `CountableSyntax`、`SkolemOperations*`、`CountableSkolemHull` | 实际枚举程序与操作元数据，把 Skolem 函数改写为有限元组操作族，构造可数闭包并接入初等子结构定理 |
| 给定 e 的初等高度 | `AugmentedOperations*`、`AugmentedClosure`、`HeightSeed`、`EnumerationInitialSegment`、`ElementaryHeight` | 实际加入 e 操作，构造含 ω∪{ω,γ} 的闭包；证明传递性、δ<κ及载域恰为δ的初等实例。全局e的存在仍是明确前提 |
| 候选良序到全局 e | `SurjectionFamily`、`UniformEnumerationChoice` | 从已给定内部良序的候选满射集合选择并展平，证明全局函数的全定义性、正初段值域和覆盖；候选良序仍待L供给 |
| 相对定义子集与证书 | `DefinableSubsets*`、`DefSetCertificate`、`DefSetMeaning` | 由实际满意度集合构造全部程序定义子集，有相对字面Δ₀证书及Σ₁特征式，并证明与变量更新后的程序真值相符 |
| 纯集合语言后继性质 | `SmallNaturals`、`BinaryTuples`、`SetLanguage*`、`SetAtomicMeaning`、`SetDefStage`、`SetFormulaMeaning`、`SetDefClosure` | 实际0、1、2与二元函数元组；二元等号和隶属的元数图、关系解释及代码／程序语义；纯集合语言的真值及Def集合存在，A∈Def，A传递时A⊆Def且Def传递 |
| 统一Σ₁后继 | `BoundedSubstitution`、`RelationTables`、`AtomicTableSyntax`、`SequenceCertificateTerms`、`SetRelationTable`、`DefStageWitness`、`DefWitnessSyntax`、`DefSuccessorMatrix` | 固定全局语法的存在性；九个载域相关字段全部界于一个实际集合证书，验证为字面Δ₀，形成24参数WitnessMatrix。对任意A全定义、输出唯一；支持约束排除非配对成员，未使用幂集 |
| 层级历史与累计性 | `ConstructibleStepSyntax`、`ConstructibleStep`、`ConstructibleHistory`、`ConstructibleCumulative` | 实际Σ₁序数递归的空／Def后继／历史值域并，任意集合长历史存在且唯一；三条递归方程、各层传递与层间包含已证明。累计性使用显式对象归纳模式 |
| 独立层与全局构造类 | `LevelCertificateSyntax`、`ConstructibleLevels`、`LevelCompatibility`、`ConstructibleClass*`、`ConstructibleBounds` | 显式序数guard的单层统一Σ₁证书、输出唯一、与任意较长历史相容；层间包含及严格层间隶属；全局构造类Σ₁定义、传递性、空集及各层自身属于类；用Δ₀收集证书将任意一集合的构造成员界于共同层 |
| 类结构及绝对性 | `ClassStructures`、`ClassBoundedTruth`、`ClassOrdinals`、`ConstructibleModel` | 实际非空传递类的隶属结构；外延性、空集、单条Foundation、全部Δ₀公式绝对性和类内已有对象的序数性绝对性 |
| 完整类归纳 | `ClosedEnvironments`、`ClassRelativizationSyntax`、`ClassRelativizationTruth`、`DefinableClassInduction`、`ConstructibleInduction` | 对一般含无界量词的公式作实际类相对化，证明参数与自由环境语义相符；构造n+24参数的归纳模式并调用原KPω归纳。inner_setInduction_axiom_d逐个证明构造类满足真正的完整集合归纳公理句子 |
| 构造类配对与并集 | `CompileDisjunction`、`ThreeTuples`、`SetRelationExtensions`、`SetDefPair`、`ConstructiblePair`、`SetUnionProgram`、`SetDefUnion`、`ConstructibleUnion` | 实际编译x=a∨x=b与∃y(x∈y∧y∈a)，验证三个变量名、赋值更新及量词作用域；无序对和并集属于Def后继，进而属于构造类并满足其结构中的对应语义 |
| 一般公式与Def | `NamedFormula`、`NamedAssignments`、`CompileNamedFormula`、`FiniteVariableNames`、`ProjectNaming*`、`ProjectCompilation`、`SetDefComprehension` | 任意普通自由闭合公式经有新变量范围证明的命名转换，编译成实际M程序；全部赋值语义正确。固定有限源语法的名字/赋值图在M中构造，未把这条宿主Nat索引当作全部内部ω。任意带参数定义子集实际属于Def后继 |
| 分离、收集、序数与完整KPω | `ConstructibleParameters`、`SeparationRestriction`、`ConstructibleSeparation`、`ConstructibleCollection*`、`DefOrdinalSlice`、`ConstructibleOrdinalContent`、`ClassInductiveSets`、`ConstructibleInfinity`、`ConstructibleKP` | 每个Δ₀分离和收集公理句子已证明；有效收集见证界于构造层，该层自身为合法输出。对象归纳证明Lα内序数恰为α以下序数，所有M序数进入类，ω对象内外相同。inner_models_kp_d将全部KPω公理装配为实际Models结论 |
| 规范语法与内部V=L | `ClassSchemaTransfer`、`ConstructibleSequences`、`CanonicalSetSyntax`、`ClassSetAbsoluteness`、`ConstructibleRelations`、`CanonicalSyntaxMembers`、`ClassRelationalData`、`ClassContextSpaces`、`CanonicalSyntaxInside`、`ConstructibleVL` | KP实际构造规范语法；全部24参数进入构造类并下降为内模型的规范语法。Σ₁单值证书传输覆盖完整内部有限序列空间；内外各Lα一致，inner_v_equals_l_formula_d证明内模型满足本工程规范程序公式编码下的实际V=L核心公式。构造类中的实际集合良序现已完成，见下行 |
| KP序数算术与排名工具 | `OrdinalIteration*`、`OrdinalAdditionKP`、`OrdinalMultiplication*`、`OrdinalArithmeticLimits`、`SigmaFunctionGraph`、`OrdinalRectangle*`、`OrdinalRank` | 从已证明的Σ₁集合值递归构造连续迭代及单值证书；对象归纳证明序数性、严格增长和索引下界。加/乘法有存在唯一性、零/后继/极限方程；实际单射I×κ→κ·I及序数排名诱导的内部良序已证明，没有调用仅在ZF下证明的算术存在性 |
| 全部内部有限元组排名 | `OrdinalArithmeticTerms`、`WordBoundGrowth`、`WordBudgets`、`WordFold*`、`WordCodeSyntax`、`OrdinalWordRank`、`RankComposition`、`RankedSequenceSpace` | 实际预算函数ω→C；折叠逐项读取字词并有Σ₁证书。对象归纳证明预算界和同长度单射，最终编码长度排除跨长度碰撞。任意OrdinalRank(A,θ)可提升为A^{<ω}的实际序数排名，覆盖可能非标准的内部长度。全层排名与既有L层识别现已完成，见下行 |
| 规范Def后继排名 | `RankedProduct`、`RankedImage`、`CanonicalProgramRank`、`SigmaGraphCertificate`、`WordCeilingCertificate`、`OrdinalWordCertificate`、`SequenceRank*`、`ProductRank*`、`LeastImageRankCertificate`、`DefRankWitness`、`RankedDefStage`、`RankedDefSuccessor*` | 给定实际程序排名和载域排名，固定算法对参数序列和定义代码排名，再取每个定义集合的最小代码排名。全部计算都有有界证书，不同证书产生相同的Def集合、序数界及函数图。28参数的rankedDefSuccessorMatrix为真实Σ₁关系，已证明合法排名输入下的全定义性、输出唯一性及实际OrdinalRank；极限层与全层递归现已完成，见下行 |
| 全层排名、构造良序与全局枚举 | `RankedPackets`、`RankedFamily*`、`PacketUnionBounds`、`FirstRankedStage`、`LimitRank*`、`RankedUnion*`、`RankedSuccessorPacket`、`RankedLevelStep*`、`RankedHistory*`、`ConstructibleRankedSets`、`ConstructibleWellorder`、`ConstructibleEnumeration`、`ClassCountability`、`InnerEnumeration` | 任意已排名历史的并集按首次出现阶段和旧排名编码；实际Σ₁证书及输出唯一。统一后继/并集/坏历史默认步骤对任意前缀全定义，得到真实集合长历史。对象序数归纳识别其载域逐项就是既有Lα；每个构造集合及内模型集合拥有实际序数排名/良序。外部不可数ν向同ω内模型下降，得到κ≤ν、内部最小不可数性及实际全局e；没有添加Choice或假定κ外部仍不可数 |
| 具体R/FR关系表 | `ReflectionStage*`、`ReflectionIndex`、`ReflectionQuery`、`ReflectionData`、`ReflectionAtoms`、`ReflectionShapes`、`ReflectionLabels`、`ReflectionRepresentation`、`ReflectionEndpoints`、`ReflectionAdmission`、`ReflectionDemand`、`ReflectionClause`、`ReflectionRow`、`ReflectionTable`、`ReflectionSemantics`、`ReflectionLabelDomain` | 实际(b,K,θ)阶段索引图与三类严格先后关系；完整内部有限图、端点模板、所有列均在D中的递增表示及FR输入/输出均有字面Δ₀公式。对任意历史证明Local后实际构造唯一集合表，推出方程(5)、反射与根弱化。标签域D及有限原子集合/枚举表对应已验证 |
| 第6引理的已完成部分 | `ReflectionTopInduction` | 给定较早层/根的顶端等价归纳假设，证明P(K,θ,a)推出R(K,θ,a,δ)的前向步骤；有效元组上否定R实际给出有限反例。具体有限签名与初等高度现已完成；一阶反例公式的完整原子块组装、反向反射和(8)仍未完成，不能声称第6引理完成 |
| 实际有限结构、初等高度与原子编译接口 | `FiniteSignatureFormulas`、`ReflectionNumerals`、`ReflectionSignature`、`ReflectionEnumeration`、`ReflectionModel*`、`ReflectionInterpretation*`、`ReflectionBodySemantics`、`ReflectionTupleTools`、`ReflectionStructure`、`ElementaryAtomicAgreement`、`ReflectionAtomicBridge`、`ReflectionAtomCode`、`ReflectionAtomEvaluation`、`ReflectionVariableNames`、`ReflectionAdjacentLabels` | 实际六符号解释逐项等于=、<、R、固定κ顶截面P、规范化总二元e和ω谓词；满意度、程序枚举、Skolem函数及高于任意γ的初等高度已装配。原子表一致从程序初等性推出；固定元数原子码有真实Δ₀构造/唯一性/作用域及大小结构求值桥。变量族无碰撞且内部有限族有自然数作用域界；相邻递增等价于全体递增由对象归纳证明。完整图形反例/存在公式仍待组装 |
| 最小不可数序数与初段满射 | `Countability`、`CountableSegments`、`LeastUncountableSentence` | 满射图定义有明确集合界；`least_uncountable_derivable` 为实际对象推导 |
| 已有候选良序上的最小见证选择 | `LeastChoice.least_choice_graph_d` | 给定内部良序时构造实际选择图；没有假定无条件 AC |

`UncountableOrdinal M ω ν` 是相对于指定 `ω` 的条件。现已证明实际最小归纳集的存在与唯一性；最终不可数序数主句子还须明确携带 `IsOmega ω` 并使用这一存在定理，不能省略该条件。

## 信任范围与执行证据

- 官方工具链为 Lean 4.33.1，路径 `/home/dev/ggg/.tools/lean-4.33.1-linux/bin`。
- 阶段前部的增量构建曾通过 236 jobs。按照用户的新要求，之后改为完整模块的直接检查，不再每次运行整体 `lake build`；依赖该模块时才输出 `.olean`。各 `*-check.log` 为记录。
- 最新入口已经直接重新检查。`Audit.lean` 的 **1209 个互异声明**全部通过，只依赖 `propext`、`Classical.choice`、`Quot.sound` 的子集；详见 `audit.log` 与 `audit-results.json`。`audit.py` 检查声明清单是否完整及依赖白名单，不重编译依赖。所审计依赖中不存在 `sorryAx` 或额外原生计算公理。
- 直接检查已显式加入 `autoImplicit=false`。`verify-local-stage.py` 的当前清单为 **322 个自建模块及入口**，全部通过。本阶段只检查20项、复用302项；所有当前严格日志为空。脚本明确报告实际检查数与缓存复用数；`strict-stage/results.json` 记录源码及依赖指纹，只重查变化模块。该阶段没有调用 `lake build`。
- 首次引入 `YesMetaZFC.SetTheory.Ord.Natural` 时，只定向编译其 9 个缺少缓存的依赖模块；日志总数 203 中其余 194 个复用缓存。新工程模块均直接检查，未运行本阶段的全项目构建。
- 隔离依赖中只修改 `sentence!` 的闭合性证书：`native_decide` → `decide_cbv`，公式不变，哈希见 `third_party-provenance.json`。
- 旧序数分类引理中的原生自动化证书没有使用；在 `BoundedRecursion.lean` 中给出相同陈述的直接逻辑证明。
- 宿主 `Classical.choice` 用于证明元定理等步骤，不是对象 KP 的选择公理。最终对象结论以真实 `Derives` 类型限定其可用理论公理。

## 仍缺的主定理工作

1. 具体R/FR及其实际Local义务现已完成，且已调用有界递归得到表。实际有限签名(κ;<,R,P,e,ω)及各符号解释现已构造并验证，也已得到该结构的初等高度。下一步需把完整固定有限形状的原子块组装为同一一阶程序。
2. 实例化文稿实际有限图模板，完成第 6 引理。给定全局 e 后的初等高度已构造；现已实际证明内模型中的候选集合良序与全局e。具体有界R/FR已完成，(7)前向归纳步骤及有限反例提取也已证明；原子代码与大小结构求值桥现也已完成，但完整反例原子块的一阶编译/反射、(7)反向、(8)及初始表示仍缺，不能声称第 6 引理或主定理完成。
3. 同序数、同ω的KPω构造类、规范语法下的内部V=L、全部构造层排名、集合良序及所需全局枚举已证明。仍须完成有限1-Y计算及最终实际μ秩函数的内外转移；这些后续结论不能由V=L或集合良序直接替代。
4. 将引用的有限 1-Y 几何／复制结果接到对象自然数和有限序列编码。现有宿主 Lean 定理不能不经证明就用于可能非标准的 KP 模型。
5. 编码并推出完整主句子，包括 `μ : E → χ`、`χ≤ν`、空值、任意复制次数下降和生成集字典序良序。

因此，本阶段产物是一套已核验的 KP 基础与文稿所需关键通用引理，不是完整 1-Y 对象证明。

## 现成库与 0-Y

调查和具体复用表见 `LIBRARY-AND-REUSE.md`。已确认可以复用原有的有限父图／复制／编码相容性接口；没有找到可直接调用的完整公开 KPω 库，也没有确认用户提到的“统一 0-Y 良序性在 Z₂ 内可证”的具体对象推导。已询问出处，尚未收到回复。

数学上的可证性上界、一致性强度比较和保留当前句子的对象证明传输应分别核对。尤其需区别“每个固定行数分别可证”和“对所有行数统一可证”。这不妨碍继续复用已有有限组合引理。

## 复现单模块与审计

```sh
cd /home/dev/ggg/kp-simplified-verification
./check-module.sh KP1Y/RecursionSentence.lean
./check-module.sh KP1Y/LeastUncountableSentence.lean
./check-module.sh KP1Y/SequenceSpaces.lean
./check-module.sh KP1Y/SatisfactionDefinability.lean
./check-module.sh KP1Y/CompileFiniteTemplates.lean
./check-module.sh KP1Y/UniformCompile.lean
./check-module.sh KP1Y/UniformFiniteTemplates.lean
./check-module.sh KP1Y/RestrictedAtoms.lean
./check-module.sh KP1Y/SequenceCertificateSyntax.lean
./check-module.sh KP1Y/CountableSequences.lean
./check-module.sh KP1Y/CountableSkolemHull.lean
./check-module.sh KP1Y/ElementaryHeight.lean
./check-module.sh KP1Y/DefSetMeaning.lean
./check-module.sh KP1Y/SetDefClosure.lean
./check-module.sh KP1Y/ConstructibleCumulative.lean
./check-module.sh KP1Y/ConstructibleModel.lean
./check-module.sh KP1Y/ConstructibleUnion.lean
./check-module.sh KP1Y/ConstructibleKP.lean
./check-module.sh KP1Y/ConstructibleVL.lean
./check-module.sh KP1Y/OrdinalRectangleGraph.lean
./check-module.sh KP1Y/RankedSequenceSpace.lean
python3 audit.py
```

`--emit` 只生成该模块的编译产物。阶段收尾复用源码／依赖指纹未变化的结果，只检查新增或受影响模块；公理审计只读已有产物：

```sh
python3 verify-local-stage.py
python3 audit.py
```
