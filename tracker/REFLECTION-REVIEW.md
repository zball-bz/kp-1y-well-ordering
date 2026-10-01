# 反射主线的命题对应审读

范围是用户 PDF 的关系表、初等高度、第 6 引理及推论 7。这里核对形式化的**实际输入、结论与量词范围**；不把已经通过编译等同于整个 1-Y 定理完成。

## 关系与图形

[ReflectionSemantics](../KP1Y/ReflectionSemantics.lean) 的 `Table.paper_equation_d` 对应方程 (5)。输入图边可以有任意内部自然数层号；`Admissible` 只约束端点模板。`Labeling` 要求所有列均在 ω 以上，包括没有边的孤立列。图/模板用实际内部有限列表编码，允许重复原子；已有与有限原子集合/枚举的对应。

[ReflectionTemplateTruth](../KP1Y/ReflectionTemplateTruth.lean) 的四个大小结构等价逐项回到既有 `Demand` / `Response`，没有把它们替换为较弱的原子子集。输入的 `Below κ` 由实际赋值载域包含于 κ 得出；输出仍要求 `Below a`、同一个内部图和保留 cut 之前的全部值。

固定元数 3/4 的代码使用宿主 `Fin`；图形宽度、边/模板数量、变量族和量词块长度全部在模型内部 ω 上。编译产物是真实程序集合，同一个代码用于大小解释。

## 第 6 引理 (7)

[ReflectionHeightAgreement](../KP1Y/ReflectionHeightAgreement.lean) 的 `Height.query_agreement_d` 结论为：对 K∈ω、a∈δ、θ=a 或 θ∈a，顶端 κ 查询当且仅当顶端 δ 查询。其公开前提只有任意 KPω 模型、实际文章背景/结构、实际初等高度及这些参数界。

源码对 K、θ 使用两个明确对象 schema 的序数归纳；最终没有 `TopAgreementBefore` 或反例局部化前提。小于等于 ω 的 a 由查询自带的有效性 guard 处理，没有被静默排除。

反向通过 [ReflectionCounterexampleTransfer](../KP1Y/ReflectionCounterexampleTransfer.lean) 的 `localize_counterexample_d` 实际反射反例。程序的无输出与**不存在任意实际 Response**等价：每个响应 g 都在 a 以下，当 a∈δ 时其图和赋值可收紧到 δ。没有只排除小结构候选却留下外部候选的漏洞。

## 第 6 引理 (8)

[ReflectionPrefixExistence](../KP1Y/ReflectionPrefixExistence.lean) 的存在公式只固定输入前缀。实际准备小结构赋值时，未使用的 a/θ 标量槽填0，其余输入列也填0；δ 和 θ=δ 从未被当作小结构参数。输出量化全部 g，没有 g(c)=δ 条件。

公式使用输出 P，而非试图在公式中命名 δ。返回 `End κ` 后，[ReflectionHeightTop](../KP1Y/ReflectionHeightTop.lean) 才用完整 (7) 改写成 `End δ`，再由真实表方程取得 `Height.top_query_d`。公开结论包含 θ=δ，cut=0 也由同一构造覆盖。

## 推论 7

[ReflectionHeightIteration](../KP1Y/ReflectionHeightIteration.lean) 先把 Skolem 封闭条件写成有界谓词，再以最小序数选择构造实际 κ→κ 高度操作。它通过内部递归返回真实有限高度序列图；没有以宿主重复选择代替任意内部有限长度。

[ReflectionInitialRepresentation](../KP1Y/ReflectionInitialRepresentation.lean) 的 `initial_representation_exists_d` 对任意 `Diagram m A` 返回真实表示、标签序列集合成员及 `Below κ`。每条边在较小 parent 高度使用 (8)，在较大 child 高度使用 (7)。层号 k 没有额外限制，宽度0包含在同一个构造中。

这些结论的文章背景和初等结构均有先前的实际存在性入口；统一枚举 e 仍由构造内模型中的最小不可数 κ 构造，不是在普通 KPω 中凭空假定选择函数存在。

## 最终句子和未完成边界

最终主定理必须写成对 ν 的全称条件：`∀ν (UncountableOrdinal(ν) → ∃χ≤ν ∃μ …)`。前件局部的 `∃ν` 不能支配后件的 ν。秩域是全部合法表达式 E；字典序良序域仅为 Desc(s) 与 G。

当前仍不能声称整个定理已证明。有限山形提取、实际复制塔、复制后父图/相对结构保持、规范重提取和 A(E_N(s)) 对应尚需连接；之后才是实际 μ、全体展开下降、L 的见证回传和最终闭句审计。通用重建、通用后代秩定理及矩阵 expandRaw 不会自动消除这些义务。
