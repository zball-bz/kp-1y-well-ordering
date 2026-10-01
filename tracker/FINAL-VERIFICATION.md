# Q02 最终核验记录（2026-10-01）

## 结论

在纯 ∈ 一阶语言中，对象理论 KPω（外延、空集、配对、并集、无穷、Δ₀ 分离、Δ₀ 收集、完整集合归纳；`KP1Y/Axioms.lean`）推出定理 1 的闭句：

```lean
-- KP1Y/OneYMainTheorem.lean
theorem KP1Y.OneYTheorem.theorem1_derivable : KP1Y.Derives mainSentence
theorem KP1Y.OneYTheorem.main_semantic_actual_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory) :
    MainSemantic M
```

`KP1Y.Derives` 是 YesMetaZFC 的 Hilbert 推导谓词（`Project.Derives theory`），由 `derives_of_all_models`（强完备性）从“任意 KPω 模型满足”得到。`mainSentence`（`KP1Y/OneYTheoremSentence.lean`）没有自由变量；`mainSentence_iff` 证明任意 KPω 模型满足它当且仅当 `MainSemantic M`：

- 辅助集合（ω、0、1、有限序列空间、E、六个算术表、森林/列表/网格空间、Keys=E×ω、EN）由显式公式定义，存在且唯一；
- 对每个 `UncountableOrdinal ν`：存在序数 χ（χ=ν 或 χ∈ν）与集合函数图 μ:E→χ，μ(∅)=0，且对每个非空 s∈E、每个内部 N∈ω、实际 t=E_N(s)，μ(t)∈μ(s)（`RankWitness`）；
- ≺（t≠s 且 t=E_N(s)）在 E 上良基：每个非空集合子集有 ≺-极小元；每个集合编码的展开轨迹 ω→E 到达 ∅；
- 字典序（真前缀较小）良序每个 Desc(s)（含 s 的有限步后代）与 G（种子 (1,m)，m≥2 的后代）；没有对整个 E 断言良序。

## 依赖链（全部为实际对象证明，无剩余前提）

| 环节 | 定理 | 文件 |
|---|---|---|
| 规范重提取 Y05b | `canonical_copy_bound` ← `canonical_copy_bound_last_d`、`terminal_exits_d`、`lower_steps_d` | OneYCanonicalExpansion、OneYCanonHelperExits、OneYLowerLayerFinal |
| 引理 3（Y04b/Y06） | `copy_descent` ← `copy_descent_of_canonical`、`copy_representation_d` | OneYCopyDescent、OneYCopySeamsInduction |
| μ 下降（M02） | `minimum_rank_descent_of_copy_descent` | OneYRankDescent |
| L 回传（Y08/M03） | `rank_transfer_of_copy_descent_d`、`inner_rank_witness_up_d` | OneYRankTransfer、OneYInnerAbsoluteness* |
| 次序事实（Y07a/b） | `order_index_mono_d`、`order_lex_descent_d`、`order_seed_step_d` | OneYSeeds、OneYExpansionOrder* |
| 推论（M04/M04b） | `witness_wellFounded_clause_d`、`witness_termination_clause_d`、`desc_clause_d`、`gen_clause_d` | OneYWellFounded、OneYWellOrdering |
| 闭句与推导（M05） | `mainSentence_iff`、`main_derivable_of_steps`、`theorem1_derivable` | OneYTheoremSentence、OneYMainAssembly*、OneYMainTheorem |

## 机器核验证据

- 第十九批增量阶段：`parallel-stage-19.log` —— **567 项本地模块（含根）PASS**，44 checked / 523 cached，`autoImplicit=false`；第三方 YesMetaZFC 产物复用，未重建。
- 公理审计：`parallel-audit-19.log`、`audit-results.json` —— **4,216 项所列声明**，全部仅依赖 `propext`、`Classical.choice`、`Quot.sound`（Lean 元理论公理，不是对象理论公理）。`theorem1_derivable`、`main_semantic_actual_d`、`canonical_copy_bound`、`copy_descent`、`mainSentence_iff` 均在列。
- **冷启动全量复核**：`final-cold-stage.log` —— 移开 `strict-stage/results.json` 后对全部模块逐一重新 `check-module.sh --emit`：**567 checked / 0 cached，PASS**（约 4 分钟）。随后对新产物重跑审计 `final-audit.log`：**4,216 项 PASS**，全部声明所用公理之并恰为 {propext, Classical.choice, Quot.sound}。
- 源码中没有 `sorry`/`admit`/`axiom`/`opaque`（整词扫描）；任何 `sorry` 都会以 `sorryAx` 出现在审计中。
- 规模：566 个 KP1Y 模块，88,901 行。

## 忠实性审读

- `tracker/FINAL-STATEMENT-REVIEW.md`（Q01）：逐项对照文稿定理 1 与原仓库算法定义（E、三分支、宽度 last+N·(last−root)、山形/继承祖先/伪父提取、坏根、复制坐标与差一约定、复制塔分支、重建、A(s)），无 FINDING。
- `tracker/review/COPY-TOWER-FIDELITY.md`：复制塔/重建定义的独立复核，无算法差异；`tracker/review/kpsim.py 7 6 jsref.cjs` 将 Lean 定义的 Python 转写与原作者独立 JS 引擎 `y1/engine.js` 差分，223,952 例 0 不符（协调者复跑，日志 `tracker/review/differential-7-6.log`）。该差分依赖审阅者对 Lean 定义的阅读，仅作辅助证据。

## 复现

```bash
cd /home/dev/ggg/kp-simplified-verification
./check-module.sh KP1Y/OneYMainTheorem.lean          # 主定理模块
./check-module.sh KP1Y.lean --emit                   # 根
python3 verify-local-stage.py --root KP1Y            # 严格阶段（按指纹复用）
python3 audit.py                                     # 公理白名单审计
python3 tracker/refresh.py                           # 看板（不调用 Lean）
```

## 不能由机器核验替代的部分

- Lean 闭句与文稿定理 1 的语义对应由 `mainSentence_iff` 精确化为 Lean 谓词，再由 Q01 人工审读这些谓词与文稿/原算法一致。
- 证书公式内部的 de Bruijn 编码通过各自已证的 `_iff` 引理信任。
- 引用 [1] 的中文手稿未直接阅读；对照对象是原仓库的宿主 Lean 定义及其已检查示例。
- 本证明不声称任何证明论强度极小性；Z₂ 相关事项（Z01）为可选调查，未作前提。
