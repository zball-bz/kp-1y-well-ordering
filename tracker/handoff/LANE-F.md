# LANE-F 交接（Y07a / Y07b：实际 EN 的序事实与 Seeds）

状态：Y07a、Y07b 的全部有限数值事实已在对象层无条件证明（实际 EN、实际 Reach、实际 Lex）。
所有定理对任意 `M : SetTheory.Structure`、`hM : M.Models KP1Y.theory`；长度、指标、N、行号、层号均为内部 ω 元素
（全部归纳是对象 `natural_induction_d` / `bounded_backward_induction_d`，公式为显式 Δ₀ schema）；
无 sorry/admit/axiom/额外对象公理，不假设 ω 标准或宿主良基。`#print axioms` 只含 propext、Classical.choice、Quot.sound。
**第一接缝事实由本 lane 直接从复制塔重建方程证明，不依赖 LANE-C。**

## 0. 模块与检查（均 `./check-module.sh KP1Y/X.lean --emit > X-check.log 2>&1`：exit 0，日志空）

| 模块（导入顺序） | 行 | 内容 |
|---|---|---|
| `KP1Y/OneYExpansionOrder.lean` | 196 | (a) 前缀单调、宽度单调；(b) 前缀经 E₀ 可达；O02.index_mono |
| `KP1Y/OneYExpansionOrderColumn.lean` | 243 | 重建网格单列比较（行的对象反向归纳）、前缀列格值一致 |
| `KP1Y/OneYExpansionOrderLayer.lean` | 272 | 单层第一接缝：普通层 Y(x)=X(root)，活动层/下层 Y(x)+1=X(x) |
| `KP1Y/OneYExpansionOrderSeam.lean` | 213 | 原塔逐层运行；对层号从 horizon 向下的对象归纳 ⇒ 第一接缝 |
| `KP1Y/OneYExpansionOrderLex.lean` | 148 | (c) E_N(s) <lex s；O02 字段打包、`DescendantSystem` 构造 |
| `KP1Y/OneYSeeds.lean` | 321 | (d) E₁((1,n+2))=(1,n+1)、Seeds 集合、种子链、共同种子祖先、G；LANE-E 三字段 |

外部导入均为已集成模块：`OneYExpansion`、`OneYVirtualNeeds`、`OneYLexOrder`、`OneYReachability`、
`OneYMountainReconstruction`、`OneYNaturalAdditionFacts`（经 `OneYReconstructionCanonical` 已在根闭包）、
`OneYLowerCopy`、`OneYTerminalCopy`、`RankedDescendantOrder`。根导入/Audit 需由 root 加入上表 6 个模块。

## 1. 交给 LANE-E：`OneYTheorem.OrderFacts` 无条件解除

已在临时文件中实测（导入 `KP1Y.OneYSeeds` 与 `KP1Y.OneYWellOrdering`）下式通过类型检查：

```lean
example (hM : M.Models KP1Y.theory) (hC : C.Valid M) (hT : T.Valid M C) : KP1Y.OneYTheorem.OrderFacts M C T :=
  ⟨Seeds.order_index_mono_d hM hC hT, Seeds.order_lex_descent_d hM hC hT, Seeds.order_seed_step_d hM hC hT⟩
```
（`Seeds.PairAt M C s b` 是 `PairAtIn M C.omega C.zero C.one s b`，定义体与 LANE-E `PairExpressionIn` 逐字相同，定义等价自动展开。）
因而 `OrderFactsAt M := fun C T hC hT => ⟨…⟩` 无条件成立。命名空间 `KP1Y.OneYFinite.Seeds`：

```lean
theorem order_index_mono_d (hM) (hC : C.Valid M) (hT : T.Valid M C) :
    ∀ Keys EN Reach, Expansion.Graph M C T Keys EN → Reachability.Relation M C Keys EN Reach →
      ∀ s i j t u, (i=j ∨ M.mem i j) → KP1Y.Dynamics.Expansion M Keys EN s i t →
        KP1Y.Dynamics.Expansion M Keys EN s j u → MemPair M Reach t u
theorem order_lex_descent_d (hM) (hC) (hT) :
    ∀ s, M.mem s C.expressions → s≠C.zero → ∀ N, M.mem N C.omega → ∀ t,
      Expansion.Expands M C T s N t → Lex M C t s
theorem order_seed_step_d (hM) (hC) (hT) :
    ∀ n, M.mem n C.omega → ∀ a b, M.SuccessorOf a n → M.SuccessorOf b a → ∀ s t,
      PairAt M C s b → PairAt M C t a → Expansion.Expands M C T s C.one t
```

## 2. 主要定理（命名空间 `KP1Y.OneYFinite.ExpansionOrder`；`hM : M.Models KP1Y.theory`，`hC : C.Valid M`，`hT : T.Valid M C`）

```lean
-- (a) i≤j ⇒ E_i(s) 是 E_j(s) 的前缀
theorem Expands.nested_d (hM) (hC) (hT) {s i j t u : M.Domain}
    (h : Expansion.Expands M C T s i t) (h' : Expansion.Expands M C T s j u) (hij : i=j ∨ M.mem i j) :
    ∃n p, LegalAt M C.omega C.zero C.one t n ∧ LegalAt M C.omega C.zero C.one u p ∧
      M.MemberSubset n p ∧ KP1Y.Functions.Prefix M t u n C.omega
theorem width_mono_d (hM) (hC) (hT) (hA : A.Valid M C) (hW : CopyCoordinates.Width M C T A i n)
    (hW' : CopyCoordinates.Width M C T A j n') (hij : M.MemberSubset i j) : M.MemberSubset n n'

-- (b) 每个前缀经有限次实际 E₀ 步可达
theorem prefix_reachable_d (hM) (hC) (hT) (hEN : Expansion.Graph M C T Keys EN)
    (hR : Reachability.Relation M C Keys EN Reach) {s m n t : M.Domain}
    (hLegal : LegalAt M C.omega C.zero C.one s m) (hn : M.mem n C.omega) (hnm : M.MemberSubset n m)
    (hPrefix : KP1Y.Functions.Prefix M t s n C.omega) : MemPair M Reach t s
theorem index_mono_d (hM) (hC) (hT) (hEN) (hR) {s i j t u : M.Domain} (hij : i=j ∨ M.mem i j)
    (ht : KP1Y.Dynamics.Expansion M Keys EN s i t) (hu : KP1Y.Dynamics.Expansion M Keys EN s j u) : MemPair M Reach t u

-- 第一接缝（x=last=|s|-1；N≥1）
theorem Successful.first_seam_d (hM) (hC) (hT) {s m last N t : M.Domain} {W : Expansion.SuccessData M.Domain}
    (h : Expansion.Successful M C T s m last N t W) (hLast : M.SuccessorOf m last) (hN : N≠C.zero) :
    M.mem last W.width ∧ ∀a b, MemPair M t last a → MemPair M s last b → M.SuccessorOf b a
theorem Expands.first_seam_d (hM) (hC) (hT) {s N t m last b : M.Domain} (h : Expansion.Expands M C T s N t)
    (hN : N≠C.zero) (hLegal : LegalAt M C.omega C.zero C.one s m) (hLast : M.SuccessorOf m last)
    (hB : MemPair M s last b) (hAbove : M.mem C.one b) :
    ∃n, LegalAt M C.omega C.zero C.one t n ∧ M.mem last n ∧ RowsAgreeOn M t s last ∧
      ∀a, MemPair M t last a → M.SuccessorOf b a

-- (c) 字典序下降
theorem Expands.lex_d (hM) (hC) (hT) {s N t : M.Domain} (h : Expansion.Expands M C T s N t) (hs : s≠C.zero) : Lex M C t s
theorem Expands.lex_of_ne_d (hM) (hC) (hT) {s N t : M.Domain} (h : Expansion.Expands M C T s N t) (hne : t≠s) : Lex M C t s

-- O02 字段包与 DescendantSystem
structure OrderFacts (M) (ω E Keys F Reach Lex : M.Domain) : Prop  -- index_mono/lex_step/lex_irrefl/lex_trans，逐字同 O02
theorem order_facts_d (hM) (hC) (hT) (hEN) (hR) (hLex : LexRelation M C Lex) :
    OrderFacts M C.omega C.expressions Keys EN Reach Lex
theorem descendant_system_d (hM) (hC) (hT) (hEN) (hR) (hLex) (hχ : M.IsOrdinal χ) (hμ : Graph M μ C.expressions χ)
    (hRank : ∀s, M.mem s C.expressions → ∀N, M.mem N C.omega → ∀t, M.mem t C.expressions →
      ∀a, M.mem a χ → ∀b, M.mem b χ → KP1Y.Dynamics.Expansion M Keys EN s N t → t≠s →
        MemPair M μ s a → MemPair M μ t b → M.mem b a) :
    KP1Y.Dynamics.DescendantSystem M C.omega C.expressions χ μ Keys EN Reach Lex
theorem descendant_system_of_descends_d (hM) (hC) (hT) (hEN) (hR) (hLex) (hχ) (hμ)
    (hDesc : ∀s, M.mem s C.expressions → s≠C.zero → ∀N, M.mem N C.omega → ∀t, Expansion.Expands M C T s N t →
      ∀a b, MemPair M μ s a → MemPair M μ t b → M.mem b a) :      -- 即 LANE-D RankDescends 的定义体
    KP1Y.Dynamics.DescendantSystem M C.omega C.expressions χ μ Keys EN Reach Lex
```

## 3. Seeds（命名空间 `KP1Y.OneYFinite.Seeds`）

```lean
def PairAtIn (M) (w z o s b) := ∃two, two∈w ∧ SuccessorOf two o ∧ Graph s two w ∧ s(z)=o ∧ s(o)=b
abbrev PairAt M C s b := PairAtIn M C.omega C.zero C.one s b               -- s=(1,b)
def IsSeed M C r := ∃m, m∈C.omega ∧ C.one∈m ∧ PairAt M C r m              -- (1,m), m≥2
theorem seed_step_d (hM) (hC) (hT) : ∀n∈ω, ∀a b, SuccessorOf a n → SuccessorOf b a → ∀s t,
    PairAt M C s b → PairAt M C t a → Expansion.Expands M C T s C.one t      -- E₁((1,n+2))=(1,n+1)
theorem seed_set_exists_d (hM) (C) : ∃Seeds, ∀r, M.mem r Seeds ↔ M.mem r C.expressions ∧ IsSeed M C r
theorem seed_chain_d (hM) (hC) (hT) (hEN) (hR) (hm : m∈ω) (hk : k∈ω) (h1m : C.one∈m) (hmk : m=k ∨ m∈k)
    (hP : PairAt M C r m) (hP' : PairAt M C r' k) : MemPair M Reach r r'
theorem seeds_join_d (hM) (hC) (hT) (hEN) (hR) (hSeeds : ∀r, r∈Seeds ↔ r∈C.expressions ∧ IsSeed M C r) :
    ∀s∈Seeds, ∀t∈Seeds, ∃u, u∈Seeds ∧ MemPair M Reach s u ∧ MemPair M Reach t u
theorem generated_set_d (hM) (Reach Seeds) : ∃G, ∀x, x∈G ↔ x∈C.expressions ∧ ∃s, s∈Seeds ∧ MemPair M Reach x s
theorem generated_wellorder_d (hM) (hC) (hT) (hEN) (hR)
    (hSys : KP1Y.Dynamics.DescendantSystem M C.omega C.expressions χ μ Keys EN Reach Lex) :
    ∃Seeds G, (∀r, r∈Seeds ↔ r∈C.expressions ∧ IsSeed M C r) ∧ (∀x, x∈G ↔ x∈C.expressions ∧ ∃s∈Seeds, Reach x s) ∧
      M.MemberSubset Seeds G ∧ KP1Y.InternalWellOrder M Lex G ∧ ∀x∈G, ∀y∈G, (Lex x y ↔ x≠y ∧ Reach x y)
```
G 恰为 Seeds 的实际可达后代之并，不扩大为 E。

## 4. 证明路线（第一接缝）

原塔运行 J0(k)=第 k 层数值行（`original_run_exists_d`），复制塔运行 J；`Run.prefix_d` 给逐层 x 之前一致。
对层号 k≤B 作对象反向归纳，Δ₀ 公式同时携带两条：K<k 时 J(k)[x]=J0(k)[root]；k≤K 时 J(k)[x]+1=J0(k)[x]。
- 普通层：复制列 x 读原 root 列高度与父项（父在 root 左侧，ParentCopy 不平移）。
- 活动层：高行 [level,height(root)] 读原 root 列；原 x 列高度=level+1、level 行父为 root、上层 x 值为 1（`BadAt.next_layer_one_d`）
  ⇒ X(level,x)=X(level,root)+1；低行 [0,level] 保留原父项，差一下传。
- 下层：x 列高度/父项保持（`Lower.Copies.original_*_d`，c≤last），顶部差一下传。
单列比较 `Grid.shift_d`：两列在 [lo,hi) 每行父贡献相同，则 hi 处差 δ 原样传到 lo（行号对象反向归纳）。

## 5. 未解除前提

Y07a/Y07b 本身无剩余前提。`descendant_system_d` / `generated_wellorder_d` 只是打包，秩下降 μ 字段（M02）作为参数传入。

## 6. 待审计声明

`ExpansionOrder`：`le_subset_d width_mono_d Successful.nested_d Expands.nested_d prefix_full_eq prefix_reachable_d index_mono_d
shifted_columns_d Grid Grid.unique_d Grid.column Grid.cell_unique Grid.height_bound Grid.cell_exists_d Grid.cell_top
Grid.parent_equation_d Grid.shift_d Grid.prefix_cells_d rebuilds_grid GCell add_zero_iff_d add_one_iff_d LayerPair
LayerPair.grids_d ordinary_seam_column_d LayerPair.ordinary_seam_d LayerPair.kept_seam_d parent_copy_zero_iff_d
terminal_seam_column_d LayerPair.terminal_seam_d layer_pair_d original_run_exists_d Successful.first_seam_d Successful.lex_d
prefix_last_lex_d Expands.lex_of_nonempty_length_d Expands.lex_d Expands.lex_of_ne_d Expands.first_seam_d OrderFacts
order_facts_d descendant_system_d descendant_system_of_descends_d`；
`Seeds`：`PairAtIn PairAt pairAtFormula pairAtFormula_delta0 pairAtFormula_iff PairAt.legal PairAt.unique pair_at_exists_d
PairAt.expression seed_step_d IsSeed seed_set_exists_d IsSeed.expression seed_chain_d seeds_join_d generated_set_d
generated_wellorder_d order_index_mono_d order_lex_descent_d order_seed_step_d`。

## 7. Helper for LANE-B（Y05b lower 层的 bound / extract 两字段）

模块（均 `./check-module.sh KP1Y/X.lean --emit > X-check.log 2>&1`：exit 0，日志空；`#print axioms` 仅 propext/Classical.choice/Quot.sound）：
`KP1Y/OneYLowerHelpForest.lean`(309) → `OneYLowerHelpRoot.lean`(148) → `OneYLowerHelpExtract.lean`(152) →
`OneYLowerHelpBound.lean`(115) → `OneYLowerHelpMain.lean`（出口）。命名空间 `KP1Y.OneYFinite.LowerHelp`。
`Main` 额外 import LANE-B 的 `KP1Y.OneYLowerCanonPseudo`（新列伪父公式 `Copies.canon_pseudo_copy_formula_d`）。

**出口（import `KP1Y.OneYLowerHelpMain`）**，与 LANE-B.md "Available for helper" 的环境一致；无额外假设
（`_hA` 只为签名对齐保留，未使用）：
```lean
theorem lower_layer_pseudo_top_bound_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {m : M.Domain} {L : LayerStateSpace M.Domain} {V P H K level N n : M.Domain} {A : CopyCoordinates.Context M.Domain}
    (hLayers : LayerRun M C m L V P H) (_hA : A.Valid M C) (hBad : BadAt M C m L H K level A.last A.root)
    (hN : CopyCoordinates.Width M C T A N n)
    {k W Q J oldTop Qnext newTop Pnext : M.Domain} {D : CopiedMountain.Lower.Context M.Domain} {Y : CopiedMountain.Data M.Domain}
    (hData : TowerCanon.LowerLayerData M C T A m L H K k n W Q J oldTop Qnext D Y)
    (hNew : Graph M newTop n C.omega) (hPos : ∀ c v, MemPair M newTop c v → M.mem C.zero v)
    (hInputs : TowerCanon.LowerInputs M C T D m N n oldTop Qnext newTop Pnext) :
    ReconstructionSelection.PseudoTopBound M C Y newTop
theorem lower_layer_extract_d … (同上环境) {k W Q J oldTop Qnext newTop Pnext G : M.Domain} {D} {Y}
    (hData …) (hNew …) (hPos …) (hInputs …) (hG : GraphPseudoForest M C Y G) :
    ∃ F F', Selects true M C m F oldTop Qnext ∧ FrameCopy.Copies M C T A F N n F' ∧
      ∀ Q', Selects true M C n G newTop Q' ↔ Selects true M C n F' newTop Q'
```
已在草稿中验证直接实例化 `LowerLayer.BoundPart`/`LowerLayer.ExtractPart`：
`fun hData hNew hPos hInputs => lower_layer_pseudo_top_bound_d hM hC hT hLayers hA hBad hN hData hNew hPos hInputs`，
`fun hData hNew hPos hInputs hG => lower_layer_extract_d hM hC hT hLayers hA hBad hN hData hNew hPos hInputs hG`。

中间出口（可单独复用）：
* `Forest`：`single_contraction_d`（单收缩受限父相等，对象∈归纳）、`selects_self_d`、`select_of_refinements_d`、
  `ancestor_height_decrease_d`、`ancestor_transfer_on_chain_d`、`greatest_map_iff_d`、`selects_to_false`。
* `Root`：`lower_layer_source_d`（源提取统一到 `D.mountain`：GraphPseudoForest/PseudoForest/TopValueGraph/Selects/基行正值）、
  `lower_layer_next_root_d`（`Ancestor m Qnext A.root A.last`，由 BadAt+LayerRun 下降）、
  `frame_root_seam_d`（帧复制中 root 是其任意块副本的祖先或相等，块号对象归纳）、
  `contracted_selected_good_d`（伪父为root且同高的列，其已选源父在好部）。
* `Extract`：`PseudoCopyFormula M C T D Y`（新列伪父公式命题）、`pseudo_select_eq_frame_copy_d`、
  `lower_layer_extract_of_formula_d`。
* `Bound`：`frame_next_height_decrease_d`（Qnext 的帧复制每条边严格降目标高度）、`lower_layer_pseudo_top_bound_of_formula_d`。

证明路线：extract 取 F=源伪父森林、F'=其帧复制；原列与非收缩新列伪父逐项等于 F' 父，收缩列（H(s)=floor 且源伪父=root）
目标父为 root，F' 中 root 为其祖先（`frame_root_seam_d`+`lower_layer_next_root_d`），F' 的受限父经 `UpperSelect` 两项落入好部
（`contracted_selected_good_d`：同高伪父Top单调）；`single_contraction_d` 得受限父相等，从而 Selects 相等。
bound 以 Qnext 自身为继承帧（`selects_self_d`），`UpperSelect.1` 给出其帧复制选出 Pnext；帧复制边降高（锥内同抬升量、锥外父不在锥内），
沿祖先降高，配合 extract 得 `Selects n G newTop Pnext`，由 `pseudo_top_bound_of_decreasing_selection_d` 结束。
