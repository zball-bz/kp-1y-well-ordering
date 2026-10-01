# DH/BM4 仓库与对象 KPω + 不可数序数目标的比较

审读日期：2026-09-14。固定提交：`e1849485ee1d54f92dc4eb42ee93b702c71e67a9`（2026-09-12）。本地只读克隆：`/home/dev/ggg/dh-bms-wf-formal`。

结论：**这是有实质 KP 相关内容、值得参考的 BMS 形式化；现有成品仍是外部 ZFSet/Lθ 语义上的证明，不能直接作为 KPω + 存在不可数序数内部的 BMS 推导导入。** 它可以提供证明设计和独立核对材料；当前对象 KP 基础、内部自然数编码及 1-Y 规范重提取仍需我们自己的证明。

本次为固定提交的源码审读及第二位 agent 的独立集合论复核，没有全量编译该仓库。扫描 `lean/Bm4` 的 65 个 Lean 文件（25,838 行），未发现 `axiom`、`opaque` 声明或 `sorry`、`admit`、`native_decide` 字样；这项扫描不等同于重新运行内核审计。克隆工作树保持干净。

## 它实际完成了什么

最终 `terminates_unconditional` 量化 Lean 的行数 `r : ℕ`、`A : Arr r`、`Reachable r A` 和控制函数 `n : ℕ → ℕ`，断言存在有限终止时刻。另有所有行数的合并版本和一步关系良基性。`unconditional` 表示已构造并代入具体 `bm4LabelSystem`，不需要调用方另给标签系统；它没有移除 `Reachable`，也不表示证明只依赖对象 KP 公理。[最终定理](https://github.com/koteitan/dh-bms-wf-formal/blob/e1849485ee1d54f92dc4eb42ee93b702c71e67a9/lean/Bm4/SetTheory/Reflect.lean#L446-L476)

BM4 的输入域是从二列初始矩阵 `E r` 经有限次实际展开得到的矩阵。复制宽度为 `p + (N+1)*s`，其中 `s=last-p`；这与我们区分“额外 N 份”及“总计 N+1 份”的约定相容，仍须分别核对算法桥和状态范围。它不是任意自然数矩形矩阵终止的声明。[实际定义](https://github.com/koteitan/dh-bms-wf-formal/blob/e1849485ee1d54f92dc4eb42ee93b702c71e67a9/lean/Bm4/Defs.lean#L54-L105)

集合论部分确有实质证明：KP 公理代码和识别器、admissibility 与 KP 满足关系的等价、Δ₀/Σ₁ 复杂度、Lθ 中满足关系/层级代码的存在、Σ₁ 递归及有限模式反射。不能把这一部分误读成只是把所需结果放进一个假设结构。

## 与“KPω 内可证”的关键差别

| 源码位置 | 实际实现 | 对对象 KP 迁移的含义 |
|---|---|---|
| `AdmKP.lean:350` | `KPModel θ` 的 θ 是宿主 Ordinal；它说真实 `L θ` 满足 KP 代码对应的公式 | 这是特定外部传递模型的语义，不是任意 `M.Models KP` 的推导框架 |
| `L.lean:22`、`:56` | `Def M` 用 `ZFSet.powerset` 后分离；L 的极限步用 `ZFSet.range` | 必须用 KP 可用的公式枚举、函数像收集及对象递归重建这些集合存在性 |
| `Omega1.lean:105`、`:132` | 从 Mathlib 的实际 ω₁ 和其正则性证明 admissibility；先选择见证，再取序数上界 | 不能直接替换为任意 KP 模型中给定的不可数序数 ν；需内部 L、κ≤ν 和相应界/枚举证明 |
| `Stable.lean:20`、`Main.lean:54` | 标签良基性继承宿主 Ordinal；用 `Classical.choose` 与 `Nat.rec` 构造整条下降标签链 | 需对象内的选取/递归/成集证明，或改用实际最小秩及集合归纳 |
| `Fm.lean`、`HF.lean`、`Recursion.lean` | 公式、行数和递归索引使用宿主 ℕ/Ordinal；自然数集合与宿主 natZ 对应 | 不自动涵盖任意 KP 模型内可能非标准的全部 ω 参数 |

关键源码：[KPModel](https://github.com/koteitan/dh-bms-wf-formal/blob/e1849485ee1d54f92dc4eb42ee93b702c71e67a9/lean/Bm4/SetTheory/AdmKP.lean#L344-L360)、[L 的构造](https://github.com/koteitan/dh-bms-wf-formal/blob/e1849485ee1d54f92dc4eb42ee93b702c71e67a9/lean/Bm4/SetTheory/L.lean#L14-L58)、[ω₁ 的使用](https://github.com/koteitan/dh-bms-wf-formal/blob/e1849485ee1d54f92dc4eb42ee93b702c71e67a9/lean/Bm4/SetTheory/Omega1.lean#L104-L139)、[下降标签链](https://github.com/koteitan/dh-bms-wf-formal/blob/e1849485ee1d54f92dc4eb42ee93b702c71e67a9/lean/Bm4/Main.lean#L48-L93)。

作者的 D-1 记录也明确把原文“KP 证明”的满足关系引理改成了外部 admissible Lθ 上的结果，并未实现内部可证明性。我们此次从具体代码独立确认了这一点。该区别对作者的 ZFC 终止性目标未必造成缺口，对当前“完整对象 KPω 内推导”的目标却不能省略。[D-1 说明](https://github.com/koteitan/dh-bms-wf-formal/blob/e1849485ee1d54f92dc4eb42ee93b702c71e67a9/plan/formalization-detours.md#L10-L20)

`#print axioms` 只列出 `propext`、`Classical.choice`、`Quot.sound`，不能识别上述对象集合论强度差别。KP 内证明与使用 ZFSet 的强背景证明，都可能得到同样的 Lean 公理名单。判断依据应是定理所量化的模型、集合存在性的来源及对象推导出口。

这些代码用法也不说明 BMS 终止性本身需要幂集或选择公理；它们说明本仓库尚未证明其使用可在弱理论中消去。

## 最值得复用的内容

1. **KP 公理代码与变量侧条件。** `KPAx.lean` 的识别与 `kpAxCode_iff` 可用于独立核对我们的语法及 schema；`DerSeqBW` 是公式构造序列，不能当成 Hilbert Derives。[KPAx](https://github.com/koteitan/dh-bms-wf-formal/blob/e1849485ee1d54f92dc4eb42ee93b702c71e67a9/lean/Bm4/SetTheory/KPAx.lean)
2. **满足关系、L 代码及 Σ₁ 递归的证明设计。** `satCode_exists_in_L`、`lcode_exists_in_L`、`sigma1_recursion_paper` 都真正构造所需内部见证，并非预先假设有递归函数；迁移时仍要替换外部模型/索引。[递归存在性](https://github.com/koteitan/dh-bms-wf-formal/blob/e1849485ee1d54f92dc4eb42ee93b702c71e67a9/lean/Bm4/SetTheory/Recursion.lean#L800)
3. **有限复制与标签下降的模块划分。** `CopyPaper`、`LabelSystem`、有限模式反射可作独立交叉核对。`LabelSystem` 的标签与二元稳定关系，和当前 1-Y 的根索引三元 R 并非现成相同接口。[标签系统](https://github.com/koteitan/dh-bms-wf-formal/blob/e1849485ee1d54f92dc4eb42ee93b702c71e67a9/lean/Bm4/Label.lean#L13-L35)

## 对当前工程的决定

保留现有任意 KP 模型底座和实际内部 ω 编码，选择性参考此仓库的公理代码、满足关系/递归与复制证明。当前已完成的内部 L、反射、实际 μ、EN、Reach 和多数有限结构证明，无须换回 ZFSet 语义重做。

BMS 终止性本身也不能代替当前 1-Y 所需的重建、重新提取、外部候选帧选择及精确复制几何。我们的复制支线消费这些有限结构性质；还需要证明具体输入属于任何拟复用的终止定理的适用状态域。

用户此前给出的 n-row BMS/0-Y(1,n) 的 Z₂ 上界继续按已有结果记录；PTO(BMS)=PTO(Z₂)仍为猜想。本仓库最终定理既不是 Z₂ 内推导，也不是 KPω 内推导，不能用来直接核实这两种对象强度声明。
