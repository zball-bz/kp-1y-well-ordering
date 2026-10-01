# KPω 基础库与 0-Y 复用调查

日期：2026-09-13。目标保持为对象理论 `KPω + 存在不可数序数` 中的实际推导，不以宿主 Lean 中的良序性代替。

## 找到的基础库

| 项目 | 实际检查的内容 | 对当前目标的用途 |
|---|---|---|
| 随附 `YesMetaZFC` | `SetTheory/Axioms/KP.lean`、`SetTheory/Collection.lean`、`SetTheory/Separation.lean`、一阶 Hilbert 核、强完备性 | 最直接可复用。旧 `KP` 只有单条集合 Foundation，须显式补完整集合归纳模式；多数高级递归、函数构造入口要求 ZF，不能直接当 KP 引理。 |
| [FormalizedFormalLogic/Foundation](https://github.com/FormalizedFormalLogic/Foundation) | `Foundation/FirstOrder/SetTheory/Basic/Axioms.lean`、`Z.lean`、README、代码搜索 | 已有真正对象语言、算术、Z/ZF/ZFC 与模型论。所查集合论公理表没有 KPω；`Z.lean` 的通用环境要求完整 Z。可以借鉴／迁移更弱的单项证明，但不适合把整个模块直接当 KP 库。 |
| [claby2/axiomatic-set-theory](https://github.com/claby2/axiomatic-set-theory) | README 的实际公理声明 | 使用 Lean 全局 `axiom Set`、任意宿主 `P : Set → Prop` 的分离以及幂集。与本次对象 KP 推导目标不同。 |
| [idocoding/ast-lean](https://github.com/idocoding/ast-lean) | README | “Admissible Structure Theory” 是另一个结构／物理项目，不是 Kripke–Platek 可容许集基础。 |
| mathlib4 | 既有本地 SetTheory 库及针对 Platek/Kripke 的代码搜索 | 可用于宿主序数与模型论辅助检查；未查到可直接接入的完整对象 KPω 基础。 |

进行了公开仓库、代码与网页检索，包括 Kripke-Platek、KripkePlatek、KPOmega、admissible 等名称。这里只报告已检查范围，没有据搜索空结果断言全世界不存在此类库。

## 已实施的复用

新工程引用隔离副本 `third_party/YesMetaZFC`，复用其语法、模型、弱 KP 集合构造与 Hilbert 完备性；原始克隆仓库没有更改。隔离副本只有一项有意源码改动：`sentence!` 的 FreeClosed 证书从 `native_decide` 改为 `decide_cbv`，生成的公式不变，详细哈希见 `third_party-provenance.json`。这样新增对象推导的公理审计不再依赖原生计算公理。

阶段前部的增量构建已通过，后续按用户要求改为单模块直接检查。最新 44 项声明的公理审计全部只使用 `propext`、`Classical.choice`、`Quot.sound` 的子集。已实现：

- 文稿的 KPω 公理语法，包括完整集合归纳模式；
- 任意 KPω 模型中的该模式语义；没有加入外部 `WellFounded mem`；
- 从完整归纳推出单条 Foundation，及向旧弱 KP 模型的桥接；
- 从所有任意模型的语义证明经已核验强完备性取得真实纯 `∈` Hilbert `Derives`；
- 一重存在前缀的标准 Σ₁ 收集实例；
- 两个互补 Σ₁ 定义给出的标准 Δ₁ 分离实例；
- 上述基础实例的对象理论实际可推导性。

这些是基础层成果，不是主文稿的 1-Y 定理已经在 KP 内完成的声明。

## 0-Y / BMS 可以复用什么

| 接口 | 已有位置 | 用途与边界 |
|---|---|---|
| 非平凡展开映射、良基传输 | `formalization/ZeroY/Transport.lean` | 通用终止性传输。 |
| 数值 0-Y 与 BMS 编码／展开交换 | `ZeroY/Expansion/Conjugacy.lean`、`ZeroY/Dynamics/Equivalence.lean` | 数值与矩阵的真实对应，含生成路径与后代集。 |
| BM4 父关系复制、深度正规性、阻挡 | `ZeroY/Structural/*` | 原 1-Y 有限复制证明已复用的核心组合引理。 |
| 继承候选森林的帧矩阵 | `OneY/ForestFrameMatrix.lean`、`OneY/TerminalFrame.lean` | 活动层实际转换为 BM4 矩阵，不丢祖先信息。 |
| 固定帧的良基性 | `OneY/RelativeBlocker.lean:573` 的 `framedStep_wellFounded` | 显式消费全部相应 BM4 状态的一步良基性。必须核对已有 0-Y 定理是否覆盖这些带帧／非标准状态。 |
| 完整 1-Y 有限复制接口 | `OneY/RootIndexed/ExpansionWellFounded.lean` 的 `expand_lastRepresentation_lower` | 正是简化文稿 Lemma 3 所需，可沿原证明的有限组合部分迁移，无需重新设计算法。 |

单独 `WF(0-Y)` 不能自动给出 `WF(1-Y)`：多层提取、参考填充、父图变化还需要相容性和新表示的严格下降。文稿的新关系表及初等高度论证负责这部分全局工作。

更重要的是：宿主 Lean 的 `WellFounded YStep` 和对象语言中的 `KPω ⊢ WF(0-Y编码关系)` 不是同一个接口。后者需要已有对象推导或可检查的翻译。即使已有数学上的 Z₂ 证明，也还需要证明解释保持目标句子并把实际证明接入 KPω；不会把 `Z₂ < KPω+ω₁` 当作自动消除这项工作。

## Z₂ 上界：用户于2026-09-14补充的精确范围

用户澄清：已有任意有限 n-row BMS 在 Z₂ 下可证明终止的结果；亦即其指出的 0-Y(1,n) 终止性结果覆盖所有 n。PTO(BMS)=PTO(Z₂) 是广泛猜测的等式，仍按猜想记录。

这份补充覆盖旧记录中笼统的“未确认上界”说法。项目现在记录这个已知数学结果及其n参数；其具体源证明尚未被接入本工程的对象推导。查库未得到机器推导，不能用来否定用户补充的数学结果。

实际接入时要核对原证明中n的量词位置：逐个n的可证明性族、理论内部的统一∀n句子，以及适用的矩阵/初始状态范围，是不同的形式化接口。此处不替用户补充未明确指定的量词形状，也不由终止上界推出PTO等式。

当前有限复制下降的实际源码调用链已确认不消费WF(0-Y/BM4)，而消费其森林、帧、父复制、I/S与数值次序引理。这些对象迁移现已大部分完成。Z₂终止性来源与可检查翻译仍是可选复用支线，不替换当前对象KPω主证明，也不作为新公理加入。

# 后续源码核对：TarskiTruth 接口

`third_party/YesMetaZFC/YesMetaZFC/Logic/FirstOrder/FormalSystem/TarskiTruth.lean` 提供满意度及语法阶段的扩充语言方程，文件末尾通过 `Theory.insert` 将相应 `*_definition_axiom` 加到 `*_semantics_theory` 中。检查该模块和这些理论名的全库引用，没有找到把这些集合／函数的存在性降到本文纯 ∈ KPω 的推导。因此它可供编码对照，不能直接充当已证明的 KP 满意度集合存在定理；本工程未把这些定义公理加入 KP1Y.theory。

## 2026-09-14：DH/BM4 新仓库审读

已克隆 koteitan/dh-bms-wf-formal 的 e1849485 提交并审读。它包含实质 KP 公理代码、Lθ 内满足/层级证书和Σ₁递归工作，但底层为外部ZFSet，最终BM4定理未形式化为任意KP模型或纯∈推导。L构造调用powerset/range，ω₁构造使用宿主正则性/选择，内部ω参数仍需迁移。保留当前对象KP底座，选择性复用证明设计；未运行该仓库全量构建。详见[审读报告](tracker/DHBMS-KP-REVIEW.md)。
