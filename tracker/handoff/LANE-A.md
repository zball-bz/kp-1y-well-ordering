# LANE-A 交接（Y04b / Y06）

状态（2026-10-01）：Y04b 完成（无条件）；Y06 完成，**唯一命名前提为 Y05b 的规范边包含 `CanonicalCopyBound`**。
不是 KPω 主定理完成。所有模块单文件 `./check-module.sh KP1Y/X.lean --emit > X-check.log 2>&1`：exit 0、日志空
（按依赖顺序重新 emit 过一遍）。`#print axioms` 对下列主声明仅 `propext, Classical.choice, Quot.sound`。
没有 sorry/admit/新公理；未修改任何他人文件；未运行 lake build / stage / audit。

## 模块（全部为本车道新文件）

| 模块 | 行数 | 内容 |
|---|---|---|
| `KP1Y/OneYCopySeamsSplice.lean` | 348 | `Block`（第b块实际 Width/Encode/next）；MoveColumn 的界、cut前不动、新块、满射、单射、严格；`SpliceLabel`、`splice_label_exists_d`（Δ₀关系分离构造拼接标签）；`splice_representation_d`（旧边/CopyCase含根弱化/SeamCase）；`SpliceLabel.below_d` |
| `KP1Y/OneYCopySeamsStage.lean` | 272 | `Scene`（固定实际数据，无语义字段）；不变量 `EdgesHold/FactsHold/TemplatesHold/ControlHolds/StageAt/Stage`；`copy_diagram_restriction_d`；`tower_old_atom_d`；`control_atom_d`；初始块 `stage_zero_d` |
| `KP1Y/OneYCopySeamsStep.lean` | 158 | `width_le_big_d`；归纳步 `stage_step_d` |
| `KP1Y/OneYCopySeamsSyntax.lean` | 169 | `edgesHoldFormula/factsHoldFormula/templatesHoldFormula/controlHoldsFormula` 及 `_freeClosed/_iff` |
| `KP1Y/OneYCopySeamsInduction.lean` | 165 | `stageFormula`、`stageSchema : Project.UnarySchema 36`、`stageSchema_iff`；对象归纳 `stage_all_d`；**Y04b 出口 `copy_representation_d`** |
| `KP1Y/OneYCopyDescent.lean` | ~145 | `CanonicalCopyBoundIn/CanonicalCopyBound`（Y05b 接口）；`representation_of_edges_subset`；`last_value_below_d`；`drop_branch_d`；`bad_branch_d`；`expand_last_representation_lower_d`；**`copy_descent_of_canonical`** |

导入：`KP1Y.OneYCopySpliceGeometry`、`KP1Y.OneYExpansionPrefix`、`KP1Y.OneYRankDescentStatement`（均已有 olean）。

## 证明结构（忠实性要点）

- 归纳谓词 `Stage b`：∃width∈ω ∃g∈labels，Width(b)=width，g 是 width 上的实际 Labeling、全部标签<β，
  g 在复制图上为真（以统一大图 Width(N) 的限制表达），原图层<B、子列<last 的源事实经 ParentCopy_b 在 g 下成立，
  原末列模板经 ParentCopy_b 以 β 为端点成立，控制边 R_K(g(ParentCopy_b(qControl)), g(cut_b), β)。
  `stageSchema` 是这一谓词的对象公式（`stageSchema_iff`），归纳用 `KP1Y.Naturals.natural_induction_d`，
  对内部 b∈succ(N)；没有选择宿主标签序列，N、b、宽度都是内部ω元素。
- 每一步：实际 `CopySplice.realized_exists_d` / `Realized.geometry_d` 给三座塔、旧/新复制图、Facts、Needs；
  控制查询 `Query K θ a β`（θ=g(control_b)，a=g(cut_b)）经 **`Table.reflect_d`**（实际表FR方程）得 `Reflect`；
  Demand 的六项全部实际证明：Template(Needs)、当前表示、cut 读值、Below β、**精确Adm** `Lists.admissible_d`
  （k<K ∨ k=K ∧ q<cut ∧ f(q)<f(control)）、端点 End：模板（`original_templates_exists_d`+`copied_templates_exists_d`）
  在 β 成立，经 `Lists.virtual_d`/`Virtual.end_d` 根弱化到 Needs。
- 拼接：前 width 列用反射输出，cut 以后旧标签经 MoveColumn 移到新块；新图每条边按 SpliceGeometry 三分：
  旧边、CopyCase（第二支根用 **`Table.root_weaken_d`** 弱化）、SeamCase（端点 a=f(cut)=h(width)）。
  源事实/模板/控制边沿 `move_parent_copy_successor_iff_d` 迁到 b+1。
- 初始块：width(0)=last，g=f↾last（`restrict_graph_d`）；复制塔在 last 以前的原子都是原图原子（`tower_old_atom_d`）；
  控制边来自 BadAt 父边与实际 Control 根（`control_atom_d`）。

## 主要导出定理（完整类型）

```lean
-- KP1Y/OneYCopySeamsInduction.lean，namespace KP1Y.OneYFinite.CopySeams
theorem copy_representation_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {D : Reflection.Data M.Domain} (hD : D.Valid M) (hOmega : D.omega=C.omega) {Tab : M.Domain} (hTable : Table M D Tab)
    {A : Context M.Domain} (hA : A.Valid M C) {m : M.Domain} {L : LayerStateSpace M.Domain} {V P H Original K level B : M.Domain}
    (hLayers : LayerRun M C m L V P H) (hOriginal : ExpressionDiagram.Enumerated M C T D m L V H Original)
    (hBad : BadAt M C m L H K level A.last A.root) (hB : M.mem B C.omega)
    {f beta N width Forests Codes G Old : M.Domain}
    (hRep : Representation M D Tab m Original f) (hLast : MemPair M f A.last beta) (hN : M.mem N C.omega)
    (hWidth : Width M C T A N width) (hTower : CopyTower.Tower M C T A m L H K level B width Forests Codes G)
    (hOld : CopyDiagram.Enumerated M C T D ⟨B,width,Forests,Codes,G⟩ Old) :
    ∃ g, M.mem g D.labels ∧ Representation M D Tab width Old g ∧ Below M D width g beta

theorem stage_all_d (hM) (hS : Scene M C T D Tab A m L V P H Original K level B qControl)
    {N BigWidth BigForests BigCodes BigG Big f beta} (hN : M.mem N C.omega) (hBigWidth : Width M C T A N BigWidth)
    (hBigTower : CopyTower.Tower M C T A m L H K level B BigWidth BigForests BigCodes BigG)
    (hBig : CopyDiagram.Enumerated M C T D ⟨B,BigWidth,BigForests,BigCodes,BigG⟩ Big)
    (hRep : Representation M D Tab m Original f) (hLast : MemPair M f A.last beta) :
    ∀ b, M.mem b C.omega → (b=N ∨ M.mem b N) → Stage M C T D A Tab Original Big B K qControl beta b

-- KP1Y/OneYCopyDescent.lean，namespace KP1Y.OneYFinite.CopyDescent
def CanonicalCopyBoundIn (M : SetTheory.Structure.{u}) : Prop :=
  ∀ (E : ExpressionData M.Domain) (T : MatrixArithmetic M.Domain) (D : Reflection.Data M.Domain),
    E.Valid M → T.Valid M E → D.Valid M → D.omega=E.omega →
    ∀ s m last N t (W : Expansion.SuccessData M.Domain), Expansion.Successful M E T s m last N t W →
    ∀ Old, CopyDiagram.Enumerated M E T D ⟨W.horizon,W.width,W.forests,W.codes,W.tower⟩ Old →
    ∀ n B, ExpressionGraph M E T D t n B → ∀ k q p c, EdgeAt M D B k q p c → EdgeAt M D Old k q p c
def CanonicalCopyBound : Prop := ∀ (M : SetTheory.Structure.{u}), M.Models KP1Y.theory → CanonicalCopyBoundIn M

theorem expand_last_representation_lower_d (hM : M.Models KP1Y.theory) (hCanonical : CanonicalCopyBoundIn M)
    (hE : E.Valid M) (hT : T.Valid M E) (hD : D.Valid M) (hOmega : D.omega=E.omega) (hTable : Table M D Tab)
    (hA : ExpressionGraph M E T D s m A) (hs : s≠E.zero) (hRep : Representation M D Tab m A f)
    (hLastValue : LastValue M E.zero m f beta) (hExpand : Expansion.Expands M E T s N t) (ht : t≠E.zero)
    (hB : ExpressionGraph M E T D t n B) :
    ∃ g b, Representation M D Tab n B g ∧ LastValue M E.zero n g b ∧ M.mem b beta

theorem copy_descent_of_canonical (hCanonical : CanonicalCopyBound.{u}) : KP1Y.OneYRank.CopyDescentStatement.{u}
```

分支覆盖：s 空（与 s≠0 矛盾）、`Expands` 的 m=0 支（矛盾）、末值 1 删除支（`drop_branch_d`，用
`ExpressionGraph.prefix_restriction_d` + `DiagramRestriction.representation_exists_d`，无条件）、
坏根复制支（`bad_branch_d`：`copy_representation_d` 在同一 `Successful` 塔给出 Width(N) 复制图的 <β 表示，
宽度 n=W.width 由 `Successful.legal_d` + `legal_length_unique` 导出，再以 `CanonicalCopyBoundIn` 的边包含限制）。

## 未解除前提（唯一）

`CanonicalCopyBoundIn M`：即原 `expandValues_diagram_of_badRoot` 的边包含部分（原定理对任意层界 J 成立，
此处 A(t) 用其自身严格界，复制图用 `W.horizon`=原 max(1,maxValue s)）。宽度相等不在接口内。
由 Lane C（Y05b）交付 `∀ M, M.Models KP1Y.theory → CanonicalCopyBoundIn M` 后，
`copy_descent_of_canonical` 即无条件给出 `CopyDescentStatement`。

## 越界接口需求

无。未改动任何只读文件。

## 第二项任务：复制塔忠实性复核（已完成）

报告：`tracker/review/COPY-TOWER-FIDELITY.md`。未修改任何 Lean 文件。

- 结论：未发现算法差异。三方逐定义对照一致：坐标 Width/Encode/ParentCopy/MoveColumn/RawDecoded/Decoded、
  Lower/Terminal/Ordinary 的 height/parent、塔的三分支与 horizon、Assembles/Rebuilds/GridColumn 数值方程、Expands 三支。
- 手算例子：(1,3,3) N=0,1,2；(1,3,2) N=1；(1,2,5) N=2。
- 穷举差分：对象层定义的 Python 转写对照独立 JS 引擎，共 246,368 个案例，0 不一致。
  规范边包含在 12,496 个坏根案例中原子集合相等，说明 `CanonicalCopyBoundIn` 为真。
- 四条 FINDING 均为信息或提醒，其中 FINDING 2 是给 Lane C 的提醒：A(t) 的层界可超过 `W.horizon`，
  需证明这些高层无父边。
