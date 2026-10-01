import KP1Y.OneYTheoremClauses

/-! 定理 1 的纯 ∈ 闭句。16 个辅助集合（ω,0,1,有限序列空间,E,六个算术表,森林/列表/网格空间,Keys,EN）
按 `theoremDataFormula` 定义；闭句同时断言：(i) 满足定义的一组集合存在；(ii) 对任意满足定义的一组集合，
∀ν (UncountableOrdinal(ν) → ∃ 序数 χ≤ν ∃ μ:E→χ … ∧ ≺ 良基 ∧ 轨迹终止 ∧ Desc(s)/G 字典序良序)。
定义公式确定唯一的一组集合（`TheoremData.Valid.unique`），故全称与存在读法一致。闭句没有自由参数。 -/
namespace KP1Y.OneYTheorem
open YesMetaZFC YesMetaZFC.SetTheory YesMetaZFC.SetTheory.Definitional
open KP1Y.Kuratowski KP1Y.Functions KP1Y.Naturals KP1Y.Bounded KP1Y.Cardinal
open KP1Y.OneYFinite KP1Y.OneYRank
universe u

/-- 深度 16 处的辅助集合变量：bound 15 是 ω，bound 0 是 EN。 -/
def boundData : TheoremData (Project.Term 16) :=
  ⟨⟨.bound 15,.bound 14,.bound 13,.bound 12,.bound 11⟩,⟨.bound 10,.bound 9,.bound 8,.bound 7,.bound 6,.bound 5⟩,
    .bound 4,.bound 3,.bound 2,.bound 1,.bound 0⟩

theorem boundData_closed : boundData.Closed :=
  ⟨⟨rfl,rfl,rfl,rfl,rfl⟩,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

/-- 依 `boundData` 的顺序压入一组集合。 -/
def pushData {M : SetTheory.Structure.{u}} (e : Env M 0) (D : TheoremData M.Domain) : Env M 16 :=
  (((((((((((((((e.push D.expr.omega).push D.expr.zero).push D.expr.one).push D.expr.sequences).push D.expr.expressions).push
    D.arith.addPairs).push D.arith.plus).push D.arith.mulPairs).push D.arith.times).push D.arith.diffPairs).push
    D.arith.difference).push D.forests).push D.forestLists).push D.grids).push D.keys).push D.expansion

theorem boundData_eval {M : SetTheory.Structure.{u}} (e : Env M 0) (D : TheoremData M.Domain) :
    boundData.eval (pushData e D)=D := by
  rcases D with ⟨⟨w,z,o,s,x⟩,⟨ap,p,mp,t,dp,d⟩,f,fl,g,k,en⟩
  rfl

/-- 16 个全称量词。 -/
def forallData (φ : Project.Formula 1 16) : Project.Formula 1 0 :=
  .forallE (.forallE (.forallE (.forallE (.forallE (.forallE (.forallE (.forallE
    (.forallE (.forallE (.forallE (.forallE (.forallE (.forallE (.forallE (.forallE φ)))))))))))))))

/-- 16 个存在量词。 -/
def existsData (φ : Project.Formula 1 16) : Project.Formula 1 0 :=
  .existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE
    (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE φ)))))))))))))))

theorem satisfies_forallData_iff {M : SetTheory.Structure.{u}} (e : Env M 0) (φ : Project.Formula 1 16) :
    Project.Formula.satisfies e (forallData φ) ↔ ∀ D : TheoremData M.Domain, Project.Formula.satisfies (pushData e D) φ := by
  simp only [forallData,Project.Formula.satisfies_forall_iff]
  constructor
  · intro h D
    exact h D.expr.omega D.expr.zero D.expr.one D.expr.sequences D.expr.expressions D.arith.addPairs D.arith.plus
      D.arith.mulPairs D.arith.times D.arith.diffPairs D.arith.difference D.forests D.forestLists D.grids D.keys D.expansion
  · intro h x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16
    exact h ⟨⟨x1,x2,x3,x4,x5⟩,⟨x6,x7,x8,x9,x10,x11⟩,x12,x13,x14,x15,x16⟩

theorem satisfies_existsData_iff {M : SetTheory.Structure.{u}} (e : Env M 0) (φ : Project.Formula 1 16) :
    Project.Formula.satisfies e (existsData φ) ↔ ∃ D : TheoremData M.Domain, Project.Formula.satisfies (pushData e D) φ := by
  simp only [existsData,Project.Formula.satisfies_exists_iff]
  constructor
  · rintro ⟨x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11,x12,x13,x14,x15,x16,h⟩
    exact ⟨⟨⟨x1,x2,x3,x4,x5⟩,⟨x6,x7,x8,x9,x10,x11⟩,x12,x13,x14,x15,x16⟩,h⟩
  · rintro ⟨D,h⟩
    exact ⟨D.expr.omega,D.expr.zero,D.expr.one,D.expr.sequences,D.expr.expressions,D.arith.addPairs,D.arith.plus,
      D.arith.mulPairs,D.arith.times,D.arith.diffPairs,D.arith.difference,D.forests,D.forestLists,D.grids,D.keys,
      D.expansion,h⟩

/-- 主体：辅助集合满足定义 → 定理 1 的全部结论。 -/
def mainCore : Project.Formula 1 16 :=
  .imp (theoremDataFormula boundData) (conclusionFormula boundData.expr boundData.keys boundData.expansion)

/-- (∃ 辅助集合满足定义) ∧ (∀ 辅助集合 (满足定义 → 结论))。 -/
def mainFormula : Project.Formula 1 0 :=
  .conj (existsData (theoremDataFormula boundData)) (forallData mainCore)

theorem mainFormula_freeClosed : mainFormula.FreeClosed := by
  have hData := theoremDataFormula_freeClosed boundData_closed
  have hConc := conclusionFormula_freeClosed boundData_closed.expr boundData.keys boundData.expansion rfl rfl
  simp only [mainFormula,mainCore,existsData,forallData,Definitional.Formula.FreeClosed]
  exact ⟨hData,hData,hConc⟩

/-- 定理 1 的纯 ∈ 闭句。 -/
def mainSentence : Project.Sentence := Project.Sentence.ofFormula mainFormula mainFormula_freeClosed

/-- 闭句的精确语义，全部以项目中的实际 Lean 谓词表述。 -/
def MainSemantic (M : SetTheory.Structure.{u}) : Prop :=
  (∃ D : TheoremData M.Domain, D.Valid M) ∧ ∀ D : TheoremData M.Domain, D.Valid M → ConclusionClause M D

theorem mainFormula_iff {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory) (e : Env M 0) :
    Project.Formula.satisfies e mainFormula ↔ MainSemantic M := by
  simp only [mainFormula,Project.Formula.satisfies_conj_iff,satisfies_existsData_iff,satisfies_forallData_iff,mainCore,
    Project.Formula.satisfies_imp_iff,theoremDataFormula_iff hM,boundData_eval]
  apply and_congr Iff.rfl
  apply forall_congr'
  intro D
  constructor
  · intro h hD
    have hD' : (boundData.eval (pushData e D)).Valid M := (boundData_eval e D).symm ▸ hD
    have hC := (conclusionFormula_iff hM (pushData e D) boundData hD').mp (h hD)
    rw [boundData_eval] at hC
    exact hC
  · intro h hD
    have hD' : (boundData.eval (pushData e D)).Valid M := (boundData_eval e D).symm ▸ hD
    apply (conclusionFormula_iff hM (pushData e D) boundData hD').mpr
    rw [boundData_eval]
    exact h hD

/-- 每个 KPω 模型满足闭句当且仅当其中成立 `MainSemantic`。 -/
theorem mainSentence_iff {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory) (free : FreeVarId → M.Domain) :
    Project.Formula.satisfies ({bound := Fin.elim0,free := free} : Env M 0) mainSentence.formula ↔ MainSemantic M :=
  mainFormula_iff hM _

end KP1Y.OneYTheorem
