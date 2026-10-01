# C00 · 首批并行接口冻结

2026-09-13，目标已恢复 active。已对当前源码与 341 项严格检查指纹核对；以下现有类型在本批冻结，只读复用。原始克隆和第三方源码只读。

## 数学背景与表示

`namespace KP1Y.ReflectionModel`。统一上下文为任意 `M : SetTheory.Structure.{u}` 与 `hM : M.Models KP1Y.theory`；`C : ArticleData M.Domain` 配合 `hC : C.Valid M`。

大解释输入 `D : RelationalData M.Domain`、`hD : ArticleInterpretation M C A D`；求值使用 `AtomicTable M D Atom`。小解释输入 `S.Valid M C` 和 `Height M C S δ small`。取小载域时 `C.top` 仍为原 κ。

下列已有接口不修改：`Reflection.Data/Table/Query`、`ArticleData`、`ArticleStructure`、`TemplateShape`、`NameFrame`、`GroundParameters`、`AtomCode`、`BinaryCode`、`BinaryBlock`、`TupleValue`、`AgreeOutside`、`CompiledExtension`。

## 精确代码接口

已核对 `ReflectionAtomCode.lean` 中：

```lean
AtomCode M C D (kind : Fin 6) (scope : M.Domain)
  (names : Fin (symbolArity kind).val → M.Domain) (code : M.Domain)
```

其定义为变量元组存在于 `D.variables`，`Codes M code (C.numbers kind.castSucc) vars`，且 `Graph M vars (C.numbers (symbolArity kind)) scope`，逐行读出 `names`。这意味着参数是变量名，不是语义值。

`kind=2` 为四元 R，`kind=3` 为三元 P；P 对应 `Query … k η a C.top`。已核对 `relation_body_at` / `top_body_at` 和 `AtomCode.evaluate_d` / `Height.evaluate_atom_d` 可恢复精确语义。

C01 可增加紧凑 R/P 包装（具体包装名由该 worker 单独负责并交接）；必须包含字面 Δ₀ 公式、freeClosed、语义等价、代码存在/唯一/作用域/代码集成员、大/小赋值求值。它只能新建 `ReflectionRelationCode.lean` 与 `ReflectionRelationCodeTruth.lean`。C04/C05 消费其最终交接后才开工，不各自复制包装。

## 各原子块的共同返回契约

每一块返回实际对象 `B`，证明 `Graph M B n D.codes`，其中 `n` 是模型内部长度。每行的代码语义由选择图和逐行公式给出；还须提供行代码 `ScopedAtom M D code scope` 及 `AllAtoms` 等价。

二元选择块已有完整接口：

```lean
BinaryBlock M C D strict scope n X Y B
-- .left  : Graph M X n scope
-- .right : Graph M Y n scope
-- .graph : Graph M B n D.codes
-- .rows  : 给定 X/Y 的逐行变量名，B 行恰为对应 BinaryCode
```

C02 的递增块和 C03 的可容许性块可以直接消费现有 BinaryCode/BinaryBlock；不依赖 C01。C02 必须处理末列无后继时的边界：可使用仅在后继仍小于宽度时启用 Less、其余用真等式的实际逐行代码选择；不能无条件增加最后一个自小于原子。

组合编译在 C06 统一完成，用现有 `uniform_conjoin_block_d` 追加块；所有块保持同一个 `scope` 和同一解释无关的代码。

## 图形、变量族和参数槽位

`TemplateShape.Valid` 给 `width/edgeLength/needLength ∈ ω`、`cut ∈ width`、实际图边/模板列表。图边条件为 `q≤p<j<width`，层 k 无 `<K` 限制。

`NameFrame.Valid M C F width edgeLength needLength V`：

| tag | 字段 | 定义域 |
|---|---|---|
| 0 | inputs | width |
| 1 | outputs | width |
| 2 | edgeLayers | edgeLength |
| 3 | needLayers | needLength |
| 4 | scalars | C.numbers 3 |

共同值域为内部自然数 `V.scope`。标量槽 0/1/2 分别为 ω/a/θ。`GroundParameters M C T V a θ A s` 包含实际赋值图及上述参数的逐行读出；修改输入族/输出族使用既有 `preserve_family_d`。

## (7) 与 (8) 的边界

C07 的反例编译消费 `a,θ ∈ δ`；候选输出 `<a<δ` 用既有 `frame_restrict_below_cut`。C09 的存在公式只固定原 f 的前缀，不能使用 δ 或 θ=δ 作小结构参数，不能固定 `g(c)=δ`；未用标量以 0 填充。

## 其他支线与所有权

- Y00 worker 独占 `FINITE-PORT-CONTRACT.md`、`finite-port-map.json`，负责实际算法编码和原有限复制依赖。C00 不另行设计第二份算法编码；Y01 及后续必须等待该交接。
- O01 worker 独占 `KP1Y/RankedDynamics.lean`，消费现有集合函数/序数接口。它的结论必须显式保留实际秩图及下降前提，并对任何需要对象模式的谓词提供可定义性。
- 本批主 agent 负责 `KP1Y/ReflectionIncreasingBlock.lean`（C02）及共享集成文件；C01、Y00、O01 三个 worker 的文件互不重叠。
- 只有主 agent 改 `KP1Y.lean`、`Audit.lean`、tracker 计划/状态和阶段清单。各 worker 只生成自己模块的 `.olean`，稳定后检查一次；不运行全量构建。

所有权已与 `plan.py` 核对，无冲突。未来需增加辅助文件时先登记；不要在其他 agent 正在检查时修改其源码或产物。
