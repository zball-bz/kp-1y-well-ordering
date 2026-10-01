# 复制塔忠实性复核（第二意见，LANE-A，2026-10-01）

**结论：未发现算法差异。** 对象层复制构造与宿主原算法一一对应，不只是“自洽的另一种构造”。
所有 off-by-one 约定都有显式对应。全部内部宽度和 N 都覆盖。下面 §6 的四条 FINDING 只是信息或提醒：
**没有一条需要修改 Lean**。

范围包括：
- `OneYCopyCoordinates`（Width/Encode/ParentCopy/MoveColumn/RawDecoded）
- `OneYOrdinaryCoordinates`
- `OneYCopiedMountain` 与 Lower/Terminal/Ordinary `Copies`
- `OneYCopyTower`
- `OneYTowerReconstruction`
- `OneYMountainReconstruction` 与 `OneYReconstructionGrid`
- `OneYExpansionCore`

宿主原文为 `/home/dev/ggg/1Y-Well-Ordering-Lean/formalization/OneY` 下的 CopyCoordinates、LowerCopy、TerminalCopy、
OrdinaryCopy、Expansion、TowerReconstruction、Reconstruction，均只读。山形提取（Y02：Select、差分、height、
伪父、顶部值）不在本次范围，按 FINITE-PORT-CONTRACT §4 作为输入。

方法分三步：
- (a) 逐个定义逐字对照，见 §1–§5。
- (b) 手算例子，见 §7。
- (c) 把对象定义逐条转写成 Python（附录 A），与作者独立实现的 JS 引擎 `y1/engine.js` 做穷举差分，见 §8。
  JS 引擎与宿主 kernel 已验证的 `ExpansionExamples` 五条定理一致。

## 1. 坐标（宿主 `CopyCoordinates.lean:12-28`）

| 宿主 | 对象层 | 对应 |
|---|---|---|
| `Context ⟨y,x⟩`, `root_lt_last` | `CopyCoordinates.Context ⟨last,root,length,first⟩` + `Context.Valid`（`OneYCopyCoordinates.lean:51`：root∈last、`difference: last−root=length`、`first=succ root`） | x=last, y=root, L=length, first=y+1 |
| `width N = x+N*L` | `Width A N w := Encode A A.last N w`（`:443`） | 相同 |
| `encode s b = s+b*L` | `Encode A s b t`（`:141`）：∃off=b·L, s+off=t（内部乘/加表） | 相同；无 root 判断，与宿主一致 |
| `parentCopy b p = if p<y then p else p+b*L` | `ParentCopy A b p t`（`:858`）：`(p∈root ∧ t=p) ∨ (¬p∈root ∧ Encode p b t)` | 相同 |
| `source/block`（区间 (y,x]）：`y+1+(c−y−1)%L`，`(c−y−1)/L` | `RawDecoded A c s b`（`:255`）：c≤y 时 (s,b)=(first,0)；y<c 时 `Source s`（y<s≤x）∧ `Encode s b c` | c≤y 的分支照抄宿主截断减法 (y+1,0)。c>y 由唯一性（`source_encode_injective_d`）和存在性（`raw_decode_exists_d`）与 div/mod 等价 |
| `OrdinaryCopy.source0/block0`（区间 [y,x)） | `OrdinaryCoordinates.Decoded`（`OneYOrdinaryCoordinates.lean:12`）：c<y 时 (c,0)；否则 c=y+b·L+slot、slot<L、s=y+slot（`CopyPosition`） | 相同 |
| RootIndexed `moveColumn n cut i` | `MoveColumn n cut i t`（`:1004`）：i<cut 则 t=i，否则 t=n+(i−cut)（`DifferenceRead`+加表） | 相同 |
| RootIndexed `blockCut b = y+b*L` | `Encode A A.root b cut` | 相同 |

## 2. 三种单层复制

山形数据：对象层 `Data ⟨width,heights,forests,parents⟩`（`OneYCopiedMountain.lean:10`）。
`Data.Valid.source` 的约定是“行 r 有父 ⇔ r<height”，`endpoint` 是“r≤height(p)”。
这与宿主 `RowMountain.parent_exists/parent_source/parent_endpoint` 的 height 约定相同。
源山形取自同一个 `LayerRun` 的第 k 层（`CopyTower.SourceAt`，`OneYCopyTower.lean:16`），对应宿主 `mountain (layers a k).row`。

### 2.1 Lower（k<K；宿主 `LowerCopy.lean:15-147`，`ActiveGeometry.activeLowerContext`）

- **floor/rise**：宿主 `floor = height y`，`rise = height x − floor`。
  对象层 `Lower.Context.Valid.floor/rise`（`OneYLowerCopy.lean:99`）由同一源层实际高度读出（`context_from_bad_exists_d`），不是假设。
- **last_root / last_higher**：对象层 `last_root : RootAt floor last root`，`rise` 字段含 floor∈h(last)。
- **InCone**：宿主 `floor ≤ height c ∧ rootAt floor c = y`，且 `rootAt r c = (row r).root c`（`RootGeometry.lean:24`）。
  对象层 `InCone`（`:152`）是 h(c)≥floor ∧ `RootAt floor c root`，即 floor 行森林中 c 的根。二者相同。
- **height**：宿主 `c≤x` 原样；否则 InCone s 时为 `h(s)+b*rise`，否则 `h(s)`，其中 (s,b)=raw。
  对象层 `Lower.Height`（`:250`）逐字相同：保留区为 `c=last ∨ c∈last`。
- **parent**：宿主 `c≤x` 原样；InCone s ∧ floor≤r 时：
  - r<floor+b·rise 读 `row floor` 中 s 的父；
  - 否则读 `row (r−b·rise)`；
  - 两种情况都平移 `+b·L`，不用 parentCopy；
  - 其余情况为 `parentCopy b ∘ row r`。

  对象层 `Lower.Parent`（`:603`）、`MovedParent`（`:596`）、`ShiftedRow`（`OneYLowerRowShift.lean:53`）：
  - level=floor+off，其中 off=b·rise；
  - r<level 时 u=floor，否则 u=r−off；
  - 平移用 `Encode p b q`，即 p+b·L，不经 root 判断，与宿主相同；
  - 非移动分支用 `ParentCopy`。

### 2.2 Terminal（k=K；宿主 `TerminalCopy.lean:17-44`，`TerminalCopyNumeric.badAtTerminalContext`）

- **level**：宿主 `level = d`，`last_height : height x = level+1`，`last_parent`。
  对象层 `Active`（`OneYTerminalCopy.lean:105`）的 `parent : ParentAt level last root` 与
  `lastHeight : height(last)=succ level` 均由 `active_from_bad_d` 从真实 BadAt 证明。
- **height**：宿主 c<x 原样；source c=x 时取 `height y`；否则取 `height(source c)`。
  对象层 `Terminal.Height := Ordinary.Height`（`:11`，即 h(source0 c)）。等价理由：
  - c<x 时 source0 c=c；
  - raw 源 s<x 时 source0=s；
  - raw 源 s=x 时 c=x+bL=y+(b+1)L，source0=y。

  因此与宿主分支化定义逐列相等。
- **parent**：宿主 c<x 原样；source c=x ∧ level≤r 时读 `(row r).parent y`，**不平移**；其余为 `map (parentCopy (block c))`。
  对象层 `Terminal.Parent`（`:20`）：`c∈last` 原样；否则 `RawDecoded c s b` 后，`HighSeam`（s=last ∧ level≤r）读 `ParentAt r root`，
  其余为 `MappedParent b r s`。逐字相同。
- **列 x 本身**：b=0、source=x，是接缝列（高度取 y 的高度），与宿主一致。

### 2.3 Ordinary（k>K；宿主 `OrdinaryCopy.lean:106-112`）

- **height**：宿主 `copyValue height = h(source0 c)`；对象层 `Ordinary.Height`（`OneYCopiedMountain.lean:176`）相同。
- **parent**：宿主 `map (parentCopy (block0 c)) (row r).parent (source0 c)`；对象层 `Ordinary.Parent`（`:180`）相同。
- 宿主没有单列的保留区，c<x 时 source0=c、block0=0，parentCopy 0 为恒等。对象层同样由 Decoded 给出，不另设分支。

### 2.4 有限宽度

宿主 `RowMountain` 在 ℕ 上全定义；对象层三种 `Copies`（Lower `:928`，Terminal `:309`，Ordinary `OneYOrdinaryCopy.lean:96`）
只在 `c∈n` 上定义 heights/parents。由于父边左向，宽度 n 内的值只依赖 <n 的列。
对象层已证明不同宽度的塔在公共列上逐值、逐父一致（`CopyNeeds.branch_same_columns_d`、`tower_family_prefix_d`，
`OneYVirtualNeeds.lean:258/280`）。这正是宿主 `assemble_family_prefix` 的有限版本。

## 3. 塔（宿主 `Expansion.lean:20-29`）

- **expandedMountain**：宿主按 `k<K` / `k=K` / 其他分支，取 Lower / Terminal / Ordinary 的 `toRowMountain`。
  对象层 `Branch`（`OneYCopyTower.lean:170`）为 `k∈K` / `k=K` / `K∈k`，分别对应 `Lower.Copies` / `Terminal.Copies` / `Ordinary.Copies`。
  K 与 level 来自同一 `BadAt`。
- **expandedGraphs bound**：宿主为 `(range bound).map expandedMountain`，其中 bound=`sequenceBound s = max 1 (maxValue s)`。
  对象层 `Tower … B n`（`:307`）对每个 k∈B 由 `ExpandedAt` 给出唯一代码。
  在 `Successful` 中 B=`W.horizon`，`Horizon`（`OneYExpansionCore.lean:11`）定义为最小严格界 `SequenceBound`
  （`OneYExtractionBounds.lean:231`：0∈B 且全部值<B，取最小）的前驱。
  - 坏根分支 s 非空，最小严格界为 max s+1，所以 horizon=max s=max(1, max s)。
  - `Horizon.original_sequence_bound_d` 已证明这一点。
- **坏根**：宿主 `BadAt a K d x y`（`BadRoot.lean:18`）为父边且值差 1；`findBadRoot` 在 k<sequenceBound 内取第一项，
  `rootAddress_unique` 证明结果与遍历顺序无关。
  对象层 `BadAt/RowBadAt`（`OneYBadRoot.lean:25/58`）为同一条件；唯一性见 `BadAt.unique_d`，在 horizon 内见 `bad_in_horizon_d`。

## 4. 数值重建（宿主 `TowerReconstruction.assemble`、`Reconstruction.value`）

- **assemble**：宿主 `assemble (M₀::rest) top = value M₀ (assemble rest top) 0`，其中 `top = fun _ => 1`；
  `reconstructedValues g w = (range w).map …`。
  对象层 `Run`（`OneYTowerReconstruction.lean:425`）给出：
  - H : succ(B) → 行，H(B)=Top，`AllOne`（`:548`）表示宽度上全为 1；
  - 对每个 i∈B，`CodeStep`（`:269`）要求 `Rebuilds (G(i)) (H(i+1)) (H(i))`；
  - `Assembles`（`:448`）中 t=H(0)。

  层序、顶部和输出都与宿主相同。
- **value**：宿主 `value r c` 在 r≤h(c) 时为 `top c + Σ_{u∈[r,h(c))} value u (parent_u c)`，否则为 0。
  等价的递推是 `value r c = value (r+1) c + parentValue r c`，见 `value_eq_succ_parentValue`。
  对象层 `Rebuilds`（`OneYMountainReconstruction.lean:88`）→ `Reconstructs` → `GridColumn`（`OneYReconstructionGrid.lean:473`）：
  - `top`：f(h(c))=top(c)；
  - `absent`：r>h(c) 时 f(r)=0；
  - `step`：r<h(c) 时 f(r)=f(r+1)+Contributes；
  - `Contributes`（`:194`）读父列 p 在第 r 行的值，即 `PreviousValue`（`:141`）。

  三条方程与宿主相同，输出取第 0 行（`BottomGraph`）。
  网格行界取 heights 的最小严格界，所以每列所需的 0..h(c) 行都在网格内。

## 5. 展开分支（宿主 `Expansion.expandValues:46`）

- **宿主**：x=len−1。`findBadRoot=none` 时输出 `take x`，空序列也走这一支；否则在宽度 x+N(x−y) 上重建。
- **对象层** `Expands`（`OneYExpansionCore.lean:80`）有三支：
  1. m=0 时 t=s；
  2. s(last)=1 时 t=s↾last；
  3. 否则走 `SuccessAt`/`Successful`（`:62`）。`Successful` 打包 linear、Select、LayerRun、BadAt、Horizon、
     coordinates（last=last、root=坏根）、`Width N W.width`、`Tower … W.horizon W.width`、`AllOne`、`Assembles`。
- **对应**：
  - 宿主 none ⇔ 第 0 层父森林中 x 无父（`findBadRoot_none_iff`）。由于 s(0)=1 且值全正，这又等价于 s(x)=1，
    对象层对应 `no_bad_iff_one_d`。
  - 空序列：宿主 x=0−1=0，取 take 0=[]；对象层走 m=0 支，输出相同。
  - N=0 在坏根分支：两边都在宽度 x 上重建，并都证明结果等于 take x（对象层 `Successful.zero_prefix_d`）。
- **唯一性与全域**：`Expands.unique_d`、`expands_exists_d`。N 和全部宽度都是内部 ω 元素，算术走内部表
  （`MatrixArithmetic.Valid`）。Width/Encode/塔/拷贝对任意 n∈ω 都有存在性（`encode_exists_d`、`tower_exists_d`、
  `*.copy_exists_d`），没有宿主 Nat 递归，也不要求 ω 标准。

## 6. FINDINGS

**FINDING 1（信息，不需修复）**
- 对象层规范图 A(s) 的层预算是 `SequenceBound`，即最小严格界 max s+1（`OneYExpressionDiagram.lean:775` 的 `Enumerated`）；
  宿主 `exprDiagram` 用 `sequenceBound = max(1,max s)`。
- 多出的层上全部值为 1、无父边，因此**原子集合相同**。边表长度不同，但 `Representation/RealizesLast` 只读 `EdgeAt`。
- 无反例。如果以后需要宣称“μ 与宿主 exprDiagram 逐字相同”，可补一条“层 ≥ max s 无原子”的引理；目前不需要。

**FINDING 2（Y05b 证明义务提醒，不是差异）**
- 展开值可以超过 max s。例如 `[1,3][3]=[1,2,4,8]`（宿主 kernel 定理 `ExpansionExamples.three`），所以 A(t) 自身的严格界 9
  远大于 `W.horizon=3`。
- 因此 `CopyDescent.CanonicalCopyBoundIn` 的证明必须包括“t 的重新提取在层 ≥ W.horizon 上没有父边”。
  宿主对应 `expandedMountain_height_zero_above_bound`（`ExpansionRebuildPrefix.lean:33`），以及对任意 J 成立的
  `reconstructedValues_diagram`（`ExpansionCanonical.lean:100`）。
- 数值核对（§8）：在 12,496 个坏根案例中，A(t) 的原子集合与 Width(N) 复制图的原子集合**完全相等**，包含关系无反例。
  所以该接口命题为真，没有提错。

**FINDING 3（信息）**
- Lower 的非移动分支中，“父在好部 p<y”（宿主 `parentCopy` 的不变支）在穷举测试中**从未出现**。
- 推测不可能出现：锥内源在 floor 行以 y 为祖先，各行逐行细化，所以低行父 ≥ y；非锥源同样未观察到 p<y。
- 定义仍与宿主逐字一致，因此不构成风险。非锥源分支本身出现过 285 次（长度 7），并已纳入差分比较。

**FINDING 4（核验限度说明）**
- 差分参照是作者的独立 JS 实现，未直接执行宿主 Lean 的 `expand`。
- JS 与宿主 kernel 已验证的 `[1,2][3]`、`[1,3][3]`、`[1,3,1][3]`、`[1,3,2][3]`、`[1,3,3][1]` 五例一致。
- Python 转写依据我对对象层定义的阅读；提取阶段（Y02）按契约转写，未逐行复核对象层 Y02 源码。

## 7. 手算例子（按对象层定义）

### s=(1,3,3)

**第 0 层**
- 父：c1→0，c2→0（值 3 不小于 3，故跳过 1）；
- 差分行 [0,2,2]，该行无父；
- 高度 [0,1,1]，顶部值 [1,2,2]。

**第 1 层**
- 伪父均为 0；底行 [1,2,2]，父 c1→0、c2→0；
- 第 0 行 2=1+1，得坏根 **K=1，level=0，y=0，x=2，L=2**；
- 高度 [0,1,1]，顶部值全 1；
- 第 2 层全 1。horizon=3。

**N=1**（宽度 4；c3 的 raw 坐标为 (s=1,b=1)）
- Lower（k=0）：
  - floor=h(0)=0，rise=h(2)−0=1；
  - c3 在锥内，高度 1+1=2；
  - 第 0 行：0<floor+off=1，u=floor=0，父 0+2=2；
  - 第 1 行：u=1−1=0，父 2。
- Terminal（k=1）：
  - c2=(x,0) 是接缝，高度 h(0)=0，r≥level 时读 y 的父，结果为无；
  - c3：高度 h(1)=1，第 0 行父 parentCopy₁(0)=2。
- 重建：
  - 第 2 层 [1,1,1,1]；
  - 第 1 层 [1,2,1,2]，与宿主定理 `repeated_output_extracted` 一致；
  - 第 0 层：c1=2+1=3，c2=1+1=2，c3：v2=2，v1=2+v1(c2)=3，v0=3+v0(c2)=5；
  - 输出 **[1,3,2,5]**，与宿主 kernel 定理 `ExpansionExamples.repeated` 一致。

**N=0**：输出 [1,3]，等于 take 2。

**N=2**：
- c4=(2,1)，在 Lower 中高度 2；在 Terminal 中是接缝，高度 0。
- c5=(1,2)：Lower 高度 3，第 0、1 行落在 gap，读 floor 行父 0+4=4；第 2 行读 row(2−2)=0 的父，也是 4。
- 输出 **[1,3,2,5,4,9]**，与 JS 一致。

### s=(1,3,2)，N=1

- 坏根在**第 0 层**：K=0，Terminal，y=0，x=2，L=2。
- 第 1、2 层为 Ordinary：c2 的 source0=0，c3 的 source0=1。
- 输出 **[1,3,1,3]**；N=3 时与宿主 `ExpansionExamples.ordinary` 一致。

### s=(1,2,5)，N=2（floor>0）

- 坏根 K=1，y=1，x=2，L=1。Lower 中 floor=1，rise=1。
- c3：
  - 第 0 行 floor≤0 不成立，不移动，父 parentCopy₁(1)=2；
  - 第 1、2 行移动，父 2；
  - 在 Terminal 中 c2、c3 都是接缝，高度为 0。
- 输出 **[1,2,4,8]**，与 JS 一致。

## 8. 穷举差分（附录 A 脚本：对象层定义的 Python 转写，对照 `y1/engine.js`）

| 范围 | 案例数 | 坏根案例 | 不一致 |
|---|---|---|---|
| 长度≤7，值≤6，N≤3（全部合法序列） | 223,952 | 186,620 | **0** |
| 长度≤5，值≤7，N≤7 | 22,416 | 19,200 | **0** |

分支覆盖（长度≤6、值≤5、N≤3）：
- Lower gap 行 24,500；Lower 平移行 15,858；Lower 锥内低行 858；
- Terminal 高接缝 4,980；Terminal 低接缝 1,908；
- Ordinary 边 40,112，其中好部父 17,072；
- Lower 非锥源在长度 7 时出现 285 次。

规范边包含（Y05b 接口）：12,496 个坏根案例中原子集合全部相等。

## 附录 A：转写脚本要点

以下 Python 是对象层定义的逐条转写，复现需要 node 与 `y1/engine.js`。

```python
def expand(s, N):
    m=len(s)
    if m==0: return []
    x=m-1
    if s[x]==1: return s[:x]                       # Expands 第2支
    Ls=layers(s)                                    # Y02 提取（契约§4）
    K,level,y = 唯一满足 par_{K,level}(x)=y 且 V(x)=V(y)+1 的 (K,level,y)
    L=x-y; B=max(s); width=x+N*L                    # Horizon / Width
    raw(c)= (y+1,0) if c<=y else (y+1+(c-y-1)%L,(c-y-1)//L)     # RawDecoded
    dec(c)= (c,0) if c<y else (y+(c-y)%L,(c-y)//L)              # OrdinaryCoordinates.Decoded
    pc(b,p)= p if p<y else p+b*L                                 # ParentCopy
    k<K : Lower.Height/Parent/MovedParent/ShiftedRow；floor=h(y)，rise=h(x)-floor，
          InCone(c)= h(c)>=floor ∧ root_{floor}(c)=y
    k=K : Terminal.Height=h(dec(c)[0])；Parent：c<x 原样；s=x ∧ level<=r → par_r(y)；否则 pc(b,par_r(s))
    k>K : Ordinary：h(dec(c)[0])，pc(b,par_r(dec(c)[0]))
    重建：top=全1；k 从 B-1 降到 0：f_c(h_c)=top_c，f_c(r)=f_c(r+1)+f_{par_r c}(r)；top:=f(0)
```

## 附录 B：完整可运行脚本

`kpsim.py`（运行：`python3 kpsim.py 7 6 jsref.cjs`；也可配合附录中的 `jsref.cjs`）：

```python
# Transliteration of the KP1Y object definitions (as read from the Lean sources) into Python,
# used only to cross-check against the independent JS engine y1/engine.js.
import json, sys, itertools, subprocess

def select(frame, value, n):
    # greatest ancestor p of c in frame with 0<value(p)<value(c)
    par = [None]*n
    for c in range(n):
        p = frame[c]
        best = None
        while p is not None:
            if 0 < value[p] < value[c]:
                best = p; break   # ancestors visited in decreasing order -> first hit is greatest
            p = frame[p]
        par[c] = best
    return par

def rows_of(base_vals, base_forest, n):
    rows = [(base_vals, base_forest)]
    while True:
        V, P = rows[-1]
        d = [ (V[c]-V[P[c]]) if P[c] is not None else 0 for c in range(n)]
        if all(x == 0 for x in d):
            rows.append((d, [None]*n)); break
        rows.append((d, select(P, d, n)))
    return rows

def mountain(base_vals, base_forest, n):
    R = rows_of(base_vals, base_forest, n)
    def val(r, c): return R[r][0][c] if r < len(R) else 0
    def par(r, c): return R[r][1][c] if r < len(R) else None
    height = []
    for c in range(n):
        h = 0
        while val(h+1, c) > 0: h += 1
        height.append(h)
    return {'n': n, 'val': val, 'par': par, 'height': height}

def ancestors(par, r, c):
    out = []; p = par(r, c)
    while p is not None: out.append(p); p = par(r, p)
    return out

def root_at(Mt, r, c):
    q = c
    while Mt['par'](r, q) is not None: q = Mt['par'](r, q)
    return q

def next_layer(Mt):
    n = Mt['n']; h = Mt['height']
    top = [Mt['val'](h[c], c) for c in range(n)]
    pseudo = [None]*n
    for c in range(n):
        if h[c] == 0: continue
        cands = [p for p in ancestors(Mt['par'], h[c]-1, c) if h[p] == h[c] or h[p]+1 == h[c]]
        pseudo[c] = max(cands) if cands else None
    return top, select(pseudo, top, n)

def layers(s):
    n = len(s)
    lin = [None] + list(range(n-1))
    base = (list(s), select(lin, s, n))
    out = []
    while True:
        Mt = mountain(base[0], base[1], n)
        out.append(Mt)
        if all(v == 1 for v in base[0]): break
        base = next_layer(Mt)
    return out

def expand(s, N):
    m = len(s)
    if m == 0: return []
    x = m-1
    if s[x] == 1: return s[:x]
    Ls = layers(s)
    bad = None
    for k, Mt in enumerate(Ls):
        for r in range(Mt['height'][x]):
            p = Mt['par'](r, x)
            if p is not None and Mt['val'](r, x) == Mt['val'](r, p) + 1:
                bad = (k, r, p)
    K, level, y = bad
    L = x - y
    B = max(s)        # horizon = predecessor of strict SequenceBound
    width = x + N*L
    def raw(c):        # RawDecoded: (y,x] sources
        if c <= y: return (y+1, 0)
        return (y+1 + (c-y-1) % L, (c-y-1)//L)
    def dec(c):        # OrdinaryCoordinates.Decoded: [y,x) sources
        if c < y: return (c, 0)
        return (y + (c-y) % L, (c-y)//L)
    def pc(b, p):      # ParentCopy
        return p if p < y else p + b*L
    tower = []
    for k in range(B):
        X = Ls[k] if k < len(Ls) else None
        if X is None:   # beyond computed layers: all ones, no parents
            tower.append(([0]*width, lambda r, c: None)); continue
        hX = X['height']; pX = X['par']
        if k < K:      # Lower
            floor = hX[y]; rise = hX[x] - floor
            def incone(c, X=X, floor=floor, hX=hX): return hX[c] >= floor and root_at(X, floor, c) == y
            H = []; 
            for c in range(width):
                if c <= x: H.append(hX[c])
                else:
                    s_, b = raw(c); H.append(hX[s_] + b*rise if incone(s_) else hX[s_])
            def P(r, c, pX=pX, floor=floor, rise=rise, incone=incone, H=H):
                if r >= H[c]: return None
                if c <= x: return pX(r, c)
                s_, b = raw(c)
                if incone(s_) and floor <= r:
                    off = b*rise
                    u = floor if r < floor + off else r - off
                    p = pX(u, s_); return None if p is None else p + b*L
                p = pX(r, s_); return None if p is None else pc(b, p)
            tower.append((H, P))
        elif k == K:   # Terminal
            H = [hX[dec(c)[0]] for c in range(width)]
            def P(r, c, pX=pX, H=H):
                if r >= H[c]: return None
                if c < x: return pX(r, c)
                s_, b = raw(c)
                if s_ == x and level <= r: return pX(r, y)
                p = pX(r, s_); return None if p is None else pc(b, p)
            tower.append((H, P))
        else:          # Ordinary
            H = [hX[dec(c)[0]] for c in range(width)]
            def P(r, c, pX=pX, H=H):
                if r >= H[c]: return None
                s_, b = dec(c); p = pX(r, s_); return None if p is None else pc(b, p)
            tower.append((H, P))
    # reconstruction: Run with top all-one at layer B, Rebuilds downward (GridColumn equations)
    top = [1]*width
    for k in reversed(range(B)):
        H, P = tower[k]
        F = {}
        for c in range(width):
            col = {}
            col[H[c]] = top[c]
            for r in reversed(range(H[c])):
                p = P(r, c)
                assert p is not None and p < c, (k, r, c, p)
                col[r] = col[r+1] + F[p].get(r, 0)
            F[c] = col
        top = [F[c][0] for c in range(width)]
    return top

def legal_seqs(maxlen, maxval):
    for L_ in range(0, maxlen+1):
        for t in itertools.product(range(1, maxval+1), repeat=L_):
            if L_ == 0 or t[0] == 1: yield list(t)

if __name__ == '__main__':
    tests = []
    for s in legal_seqs(int(sys.argv[1]), int(sys.argv[2])):
        for N in range(0, 4): tests.append((s, N))
    js = subprocess.run(['node', sys.argv[3]], input=json.dumps(tests), capture_output=True, text=True)
    ref = json.loads(js.stdout)
    bad = 0
    for (s, N), r in zip(tests, ref):
        mine = expand(s, N)
        if r is None: continue
        if mine != r:
            bad += 1
            if bad <= 10: print('MISMATCH', s, N, mine, r)
    print('cases', len(tests), 'mismatches', bad)
```

`jsref.cjs`：

```js
const Y1 = require('/home/dev/ggg/1Y-Well-Ordering-Lean/y1/engine.js');
let data=''; process.stdin.on('data',d=>data+=d); process.stdin.on('end',()=>{
  const tests = JSON.parse(data); const out = [];
  for (const [s,n] of tests) { try { out.push(Y1.expand(s.map(BigInt), n).result.map(Number)); } catch(e) { out.push(null); } }
  console.log(JSON.stringify(out));
});
```
