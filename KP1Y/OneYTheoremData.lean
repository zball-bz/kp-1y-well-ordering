import KP1Y.OneYReachability
import KP1Y.OneYLexOrder

/-! 主定理闭句的辅助集合：内部 ω、0、1、有限序列空间、合法表达式集 E、加/乘/截断减法表、
全部内部有限宽度森林、森林列表与网格空间、键集 E×ω 和实际展开图 EN。
每一项都由显式纯 ∈ 公式刻画；公式语义恰为项目中已有的 Lean 谓词，
EN 的行由 `expansionMatrix` 的 Σ₁ 证书给出。任意 KPω 模型中这些集合实际存在且唯一。
不假设 ω 标准，不新增对象公理。 -/
namespace KP1Y.OneYTheorem
open YesMetaZFC YesMetaZFC.SetTheory YesMetaZFC.SetTheory.Definitional
open KP1Y.Kuratowski KP1Y.Functions KP1Y.Naturals KP1Y.Bounded
open KP1Y.OneYFinite
universe u v

/-- 闭句中出现的全部辅助集合，按此顺序约束。 -/
structure TheoremData (α : Type u) where
  expr : ExpressionData α
  arith : MatrixArithmetic α
  forests : α
  forestLists : α
  grids : α
  keys : α
  expansion : α

namespace TheoremData

def map {α : Type u} {β : Type v} (D : TheoremData α) (f : α → β) : TheoremData β :=
  ⟨D.expr.map f,D.arith.map f,f D.forests,f D.forestLists,f D.grids,f D.keys,f D.expansion⟩

def eval {M : SetTheory.Structure.{u}} {n : Nat} (D : TheoremData (Project.Term n)) (e : Env M n) :
    TheoremData M.Domain := D.map (fun t => t.eval e)

def weaken {n : Nat} (D : TheoremData (Project.Term n)) : TheoremData (Project.Term (n+1)) :=
  D.map (fun t => t.weaken)

theorem eval_weaken {M : SetTheory.Structure.{u}} {n : Nat} (D : TheoremData (Project.Term n))
    (e : Env M n) (a : M.Domain) : D.weaken.eval (e.push a)=D.eval e := by
  rcases D with ⟨⟨w,z,o,s,x⟩,⟨ap,p,mp,t,dp,d⟩,f,fl,g,k,en⟩
  simp [weaken,eval,map,ExpressionData.map,MatrixArithmetic.map,Term.eval_weaken]

structure Closed {n : Nat} (D : TheoremData (Project.Term n)) : Prop where
  expr : D.expr.Closed
  addPairs : D.arith.addPairs.freeSupport=[]
  plus : D.arith.plus.freeSupport=[]
  mulPairs : D.arith.mulPairs.freeSupport=[]
  times : D.arith.times.freeSupport=[]
  diffPairs : D.arith.diffPairs.freeSupport=[]
  difference : D.arith.difference.freeSupport=[]
  forests : D.forests.freeSupport=[]
  forestLists : D.forestLists.freeSupport=[]
  grids : D.grids.freeSupport=[]
  keys : D.keys.freeSupport=[]
  expansion : D.expansion.freeSupport=[]

theorem Closed.weaken {n : Nat} {D : TheoremData (Project.Term n)} (h : D.Closed) : D.weaken.Closed := by
  rcases h with ⟨hC,h1,h2,h3,h4,h5,h6,h7,h8,h9,h10,h11⟩
  have hC' := hC.weaken
  constructor <;> simp_all [TheoremData.weaken,TheoremData.map,MatrixArithmetic.map,ExpressionData.weaken]

end TheoremData

/-- 实际数据：E、算术表、森林/网格空间与 EN 图均为项目既有谓词。 -/
structure TheoremData.Valid (M : SetTheory.Structure.{u}) (D : TheoremData M.Domain) : Prop where
  expr : D.expr.Valid M
  arith : D.arith.Valid M D.expr
  forests : ExpressionDiagram.AllForests M D.expr.omega D.forests
  spaces : MountainReconstruction.Spaces.Valid M D.expr D.forests ⟨D.forestLists,D.grids⟩
  graph : Expansion.Graph M D.expr D.arith D.keys D.expansion

/-- 一步实际展开 t=E_N(s)，直接读取 EN 集合。 -/
abbrev Step (M : SetTheory.Structure.{u}) (D : TheoremData M.Domain) (s N t : M.Domain) : Prop :=
  KP1Y.Dynamics.Expansion M D.keys D.expansion s N t

theorem TheoremData.Valid.step_iff_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {D : TheoremData M.Domain} (hD : D.Valid M) {s N t : M.Domain} :
    Step M D s N t ↔ Expansion.Expands M D.expr D.arith s N t :=
  Reachability.expansion_step_iff_d hM hD.expr hD.graph

/-! ### 各项定义公式 -/

def cartesianFormula {n : Nat} (P X Y : Project.Term n) : Project.Formula 1 n :=
  .forallE (.iff (.mem (.bound 0) P.weaken)
    (Project.Formula.existsMem X.weaken (Project.Formula.existsMem Y.weaken.weaken
      (codeFormula (.bound 2) (.bound 1) (.bound 0)))))

theorem cartesianFormula_freeClosed {n : Nat} (P X Y : Project.Term n)
    (hP : P.freeSupport=[]) (hX : X.freeSupport=[]) (hY : Y.freeSupport=[]) : (cartesianFormula P X Y).FreeClosed := by
  simp [cartesianFormula,codeFormula,pairFormula,Project.Formula.forallMem,Project.Formula.existsMem,
    Definitional.Formula.FreeClosed,hP,hX,hY]

theorem cartesianFormula_iff {M : SetTheory.Structure.{u}} (he : Extensional M) {n : Nat}
    (e : Env M n) (P X Y : Project.Term n) :
    Project.Formula.satisfies e (cartesianFormula P X Y) ↔ IsProduct M (P.eval e) (X.eval e) (Y.eval e) := by
  simp only [cartesianFormula,Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_iff_iff,
    Project.Formula.satisfies_mem_iff,Project.Formula.satisfies_existsMem_iff,codeFormula_iff he,Term.eval_weaken]
  rfl

def expressionValidFormula {n : Nat} (C : ExpressionData (Project.Term n)) : Project.Formula 1 n :=
  .conj (Project.Formula.isOmega C.omega) (.conj (emptyFormula C.zero) (.conj (.mem C.zero C.omega)
    (.conj (successorFormula C.one C.zero) (.conj (.mem C.one C.omega)
      (.conj (.forallE (.iff (.mem (.bound 0) C.sequences.weaken)
          (Project.Formula.existsMem C.omega.weaken (graphFormula (.bound 1) (.bound 0) C.omega.weaken.weaken))))
        (.forallE (.iff (.mem (.bound 0) C.expressions.weaken)
          (legalFormula C.omega.weaken C.zero.weaken C.one.weaken (.bound 0)))))))))

theorem expressionValidFormula_freeClosed {n : Nat} {C : ExpressionData (Project.Term n)} (hC : C.Closed) :
    (expressionValidFormula C).FreeClosed := by
  have hL := legalFormula_freeClosed C.omega.weaken C.zero.weaken C.one.weaken (.bound 0)
    (by simpa using hC.omega) (by simpa using hC.zero) (by simpa using hC.one) rfl
  simp [expressionValidFormula,emptyFormula,successorFormula,graphFormula,codeFormula,pairFormula,memPairFormula,
    Project.Formula.isOmega,Project.Formula.isInductive,Project.Formula.isEmpty,Project.Formula.isSuccessor,
    Project.Formula.forallMem,Project.Formula.existsMem,Definitional.Formula.FreeClosed,
    hC.omega,hC.zero,hC.one,hC.sequences,hC.expressions,hL]

theorem expressionValidFormula_iff {M : SetTheory.Structure.{u}} (he : Extensional M) {n : Nat}
    (e : Env M n) (C : ExpressionData (Project.Term n)) :
    Project.Formula.satisfies e (expressionValidFormula C) ↔ (C.eval e).Valid M := by
  simp only [expressionValidFormula,Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_isOmega_iff,
    emptyFormula_iff,Project.Formula.satisfies_mem_iff,successorFormula_iff he,Project.Formula.satisfies_forall_iff,
    Project.Formula.satisfies_iff_iff,Project.Formula.satisfies_existsMem_iff,graphFormula_iff he,
    legalFormula_iff he,Term.eval_weaken]
  constructor
  · rintro ⟨h1,h2,h3,h4,h5,h6,h7⟩
    exact ⟨h1,h2,h3,h4,h5,h6,h7⟩
  · rintro ⟨h1,h2,h3,h4,h5,h6,h7⟩
    exact ⟨h1,h2,h3,h4,h5,h6,h7⟩

def naturalProductFormula {n : Nat} (a b c : Project.Term n) : Project.Formula 1 n :=
  .existsE (KP1Y.Arithmetic.productCertificateFormula a.weaken b.weaken c.weaken (.bound 0))

theorem naturalProductFormula_freeClosed {n : Nat} (a b c : Project.Term n)
    (ha : a.freeSupport=[]) (hb : b.freeSupport=[]) (hc : c.freeSupport=[]) : (naturalProductFormula a b c).FreeClosed := by
  unfold naturalProductFormula
  simpa only [Definitional.Formula.FreeClosed] using
    (KP1Y.Arithmetic.productCertificateFormula_freeClosed (n := n+1) a.weaken b.weaken c.weaken (.bound 0)
      (by simpa using ha) (by simpa using hb) (by simpa using hc) rfl)

theorem naturalProductFormula_iff {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory) {n : Nat}
    (e : Env M n) (a b c : Project.Term n) :
    Project.Formula.satisfies e (naturalProductFormula a b c) ↔ KP1Y.Arithmetic.Product M (a.eval e) (b.eval e) (c.eval e) := by
  simp only [naturalProductFormula,Project.Formula.satisfies_exists_iff,
    KP1Y.Arithmetic.productCertificateFormula_iff hM,Term.eval_weaken]
  have h := KP1Y.Arithmetic.product_sigmaOne_iff_d hM (oneEnv (a.eval e)) (b.eval e) (c.eval e)
  simp only [KP1Y.Arithmetic.productMatrix_iff hM] at h
  exact h.symm

/-- 共同形状：Pairs=ω×ω，Op:Pairs→ω，每个编码 (a,b) 的行由给定公式 φ(a,b,c) 确定。 -/
def tableFormula {n : Nat} (w Pairs Op : Project.Term n) (row : Project.Formula 1 (n+4)) : Project.Formula 1 n :=
  .conj (cartesianFormula Pairs w w) (.conj (graphFormula Op Pairs w)
    (Project.Formula.forallMem w (Project.Formula.forallMem w.weaken (.forallE (.imp
      (codeFormula (.bound 0) (.bound 2) (.bound 1))
      (.forallE (.iff (memPairFormula Op.weaken.weaken.weaken.weaken (.bound 1) (.bound 0)) row)))))))

theorem tableFormula_freeClosed {n : Nat} (w Pairs Op : Project.Term n) (row : Project.Formula 1 (n+4))
    (hw : w.freeSupport=[]) (hP : Pairs.freeSupport=[]) (hO : Op.freeSupport=[]) (hRow : row.FreeClosed) :
    (tableFormula w Pairs Op row).FreeClosed := by
  have hC := cartesianFormula_freeClosed Pairs w w hP hw hw
  simp [tableFormula,graphFormula,codeFormula,pairFormula,memPairFormula,Project.Formula.forallMem,
    Project.Formula.existsMem,Definitional.Formula.FreeClosed,hw,hP,hO,hC,hRow]

theorem tableFormula_iff {M : SetTheory.Structure.{u}} (he : Extensional M) {n : Nat}
    (e : Env M n) (w Pairs Op : Project.Term n) (row : Project.Formula 1 (n+4))
    (R : M.Domain → M.Domain → M.Domain → Prop)
    (hRow : ∀ a b key c, Project.Formula.satisfies ((((e.push a).push b).push key).push c) row ↔ R a b c) :
    Project.Formula.satisfies e (tableFormula w Pairs Op row) ↔
      IsProduct M (Pairs.eval e) (w.eval e) (w.eval e) ∧ Graph M (Op.eval e) (Pairs.eval e) (w.eval e) ∧
        ∀ a, M.mem a (w.eval e) → ∀ b, M.mem b (w.eval e) → ∀ key, Codes M key a b →
          ∀ c, MemPair M (Op.eval e) key c ↔ R a b c := by
  simp only [tableFormula,Project.Formula.satisfies_conj_iff,cartesianFormula_iff he,graphFormula_iff he,
    Project.Formula.satisfies_forallMem_iff,Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_imp_iff,
    Project.Formula.satisfies_iff_iff,codeFormula_iff he,memPairFormula_iff he,hRow,Term.eval_weaken]
  rfl

def arithmeticFormula {n : Nat} (C : ExpressionData (Project.Term n)) (T : MatrixArithmetic (Project.Term n)) :
    Project.Formula 1 n :=
  .conj (tableFormula C.omega T.addPairs T.plus (sumFormula (.bound 3) (.bound 2) (.bound 0)))
    (.conj (tableFormula C.omega T.mulPairs T.times (naturalProductFormula (.bound 3) (.bound 2) (.bound 0)))
      (tableFormula C.omega T.diffPairs T.difference
        (differenceFormula C.omega.weaken.weaken.weaken.weaken C.zero.weaken.weaken.weaken.weaken (.bound 3) (.bound 2) (.bound 0))))

theorem arithmeticFormula_freeClosed {n : Nat} {D : TheoremData (Project.Term n)} (hD : D.Closed) :
    (arithmeticFormula D.expr D.arith).FreeClosed := by
  simp only [arithmeticFormula,Definitional.Formula.FreeClosed]
  exact ⟨tableFormula_freeClosed _ _ _ _ hD.expr.omega hD.addPairs hD.plus (sumFormula_freeClosed _ _ _ rfl rfl rfl),
    tableFormula_freeClosed _ _ _ _ hD.expr.omega hD.mulPairs hD.times (naturalProductFormula_freeClosed _ _ _ rfl rfl rfl),
    tableFormula_freeClosed _ _ _ _ hD.expr.omega hD.diffPairs hD.difference
      (differenceFormula_freeClosed _ _ _ _ _ (by simpa using hD.expr.omega) (by simpa using hD.expr.zero) rfl rfl rfl)⟩

theorem arithmeticFormula_iff {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory) {n : Nat}
    (e : Env M n) (C : ExpressionData (Project.Term n)) (T : MatrixArithmetic (Project.Term n)) :
    Project.Formula.satisfies e (arithmeticFormula C T) ↔ (T.eval e).Valid M (C.eval e) := by
  simp only [arithmeticFormula,Project.Formula.satisfies_conj_iff]
  rw [tableFormula_iff hM.1 e _ _ _ _ (fun a b c => KP1Y.Arithmetic.Sum M a b c)
      (fun a b key c => sumFormula_iff hM _ _ _ _),
    tableFormula_iff hM.1 e _ _ _ _ (fun a b c => KP1Y.Arithmetic.Product M a b c)
      (fun a b key c => naturalProductFormula_iff hM _ _ _ _),
    tableFormula_iff hM.1 e _ _ _ _ (fun a b c => TruncatedDifference M (C.omega.eval e) (C.zero.eval e) a b c)
      (fun a b key c => by simp only [differenceFormula_iff hM.1,Term.eval_weaken]; rfl)]
  constructor
  · rintro ⟨⟨a1,a2,a3⟩,⟨m1,m2,m3⟩,⟨d1,d2,d3⟩⟩
    exact ⟨⟨a1,a2,a3⟩,⟨m1,m2,m3⟩,⟨d1,d2,d3⟩⟩
  · rintro ⟨⟨a1,a2,a3⟩,⟨m1,m2,m3⟩,⟨d1,d2,d3⟩⟩
    exact ⟨⟨a1,a2,a3⟩,⟨m1,m2,m3⟩,⟨d1,d2,d3⟩⟩

/-- 全部森林、森林列表与网格空间。 -/
def spacesFormula {n : Nat} (C : ExpressionData (Project.Term n)) (F FL G : Project.Term n) : Project.Formula 1 n :=
  .conj (.forallE (.iff (.mem (.bound 0) F.weaken)
      (Project.Formula.existsMem C.omega.weaken (forestFormula C.omega.weaken.weaken (.bound 0) (.bound 1)))))
    (.conj (.forallE (.iff (.mem (.bound 0) FL.weaken)
        (Project.Formula.existsMem C.omega.weaken (graphFormula (.bound 1) (.bound 0) F.weaken.weaken))))
      (.forallE (.iff (.mem (.bound 0) G.weaken)
        (Project.Formula.existsMem C.omega.weaken (graphFormula (.bound 1) (.bound 0) C.sequences.weaken.weaken)))))

theorem spacesFormula_freeClosed {n : Nat} {D : TheoremData (Project.Term n)} (hD : D.Closed) :
    (spacesFormula D.expr D.forests D.forestLists D.grids).FreeClosed := by
  have hF := forestFormula_freeClosed (n := n+2) D.expr.omega.weaken.weaken (.bound 0) (.bound 1)
    (by simpa using hD.expr.omega) rfl rfl
  simp [spacesFormula,graphFormula,codeFormula,pairFormula,memPairFormula,Project.Formula.forallMem,
    Project.Formula.existsMem,Definitional.Formula.FreeClosed,hD.expr.omega,hD.expr.sequences,
    hD.forests,hD.forestLists,hD.grids,hF]

theorem spacesFormula_iff {M : SetTheory.Structure.{u}} (he : Extensional M) {n : Nat}
    (e : Env M n) (C : ExpressionData (Project.Term n)) (F FL G : Project.Term n) :
    Project.Formula.satisfies e (spacesFormula C F FL G) ↔
      ExpressionDiagram.AllForests M (C.eval e).omega (F.eval e) ∧
        MountainReconstruction.Spaces.Valid M (C.eval e) (F.eval e) ⟨FL.eval e,G.eval e⟩ := by
  simp only [spacesFormula,Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_forall_iff,
    Project.Formula.satisfies_iff_iff,Project.Formula.satisfies_mem_iff,Project.Formula.satisfies_existsMem_iff,
    forestFormula_iff he,graphFormula_iff he,Term.eval_weaken]
  constructor
  · rintro ⟨h1,h2,h3⟩
    exact ⟨h1,h2,h3⟩
  · rintro ⟨h1,h2,h3⟩
    exact ⟨h1,h2,h3⟩

/-- `expansionEnv` 的14个参数槽，自内向外。 -/
def expansionParams {k : Nat} (D : TheoremData (Project.Term k)) : Fin 14 → Project.Term k :=
  Fin.cases D.grids (Fin.cases D.forestLists (Fin.cases D.forests (Fin.cases D.arith.difference
    (Fin.cases D.arith.diffPairs (Fin.cases D.arith.times (Fin.cases D.arith.mulPairs (Fin.cases D.arith.plus
      (Fin.cases D.arith.addPairs (Fin.cases D.expr.expressions (Fin.cases D.expr.sequences (Fin.cases D.expr.one
        (Fin.cases D.expr.zero (fun _ => D.expr.omega)))))))))))))

theorem expansionParams_eval {M : SetTheory.Structure.{u}} {k : Nat} (D : TheoremData (Project.Term k))
    (e : Env M k) (i : Fin 14) :
    (expansionParams D i).eval e=(Expansion.expansionEnv (D.eval e).expr (D.eval e).arith
      (D.eval e).forests (D.eval e).forestLists (D.eval e).grids).bound i := by
  match i with
  | ⟨0,_⟩ => rfl | ⟨1,_⟩ => rfl | ⟨2,_⟩ => rfl | ⟨3,_⟩ => rfl | ⟨4,_⟩ => rfl | ⟨5,_⟩ => rfl | ⟨6,_⟩ => rfl
  | ⟨7,_⟩ => rfl | ⟨8,_⟩ => rfl | ⟨9,_⟩ => rfl | ⟨10,_⟩ => rfl | ⟨11,_⟩ => rfl | ⟨12,_⟩ => rfl | ⟨13,_⟩ => rfl
  | ⟨j+14,h⟩ => exact absurd h (Nat.not_lt.mpr (Nat.le_add_left 14 j))

theorem expansionParams_closed {k : Nat} {D : TheoremData (Project.Term k)} (hD : D.Closed) (i : Fin 14) :
    (expansionParams D i).freeSupport=[] := by
  match i with
  | ⟨0,_⟩ => exact hD.grids | ⟨1,_⟩ => exact hD.forestLists | ⟨2,_⟩ => exact hD.forests
  | ⟨3,_⟩ => exact hD.difference | ⟨4,_⟩ => exact hD.diffPairs | ⟨5,_⟩ => exact hD.times
  | ⟨6,_⟩ => exact hD.mulPairs | ⟨7,_⟩ => exact hD.plus | ⟨8,_⟩ => exact hD.addPairs
  | ⟨9,_⟩ => exact hD.expr.expressions | ⟨10,_⟩ => exact hD.expr.sequences | ⟨11,_⟩ => exact hD.expr.one
  | ⟨12,_⟩ => exact hD.expr.zero | ⟨13,_⟩ => exact hD.expr.omega
  | ⟨j+14,h⟩ => exact absurd h (Nat.not_lt.mpr (Nat.le_add_left 14 j))

/-- EN 的一行：存在 Box 使 `expansionMatrix` 的 Δ₀ 证书成立。 -/
def expansionRowFormula {k : Nat} (D : TheoremData (Project.Term k)) (key t : Project.Term k) : Project.Formula 1 k :=
  .existsE (KP1Y.Functions.witnessInstanceFormula Expansion.expansionMatrix (fun i => (expansionParams D i).weaken)
    key.weaken t.weaken (.bound 0))

theorem expansionRowFormula_freeClosed {k : Nat} {D : TheoremData (Project.Term k)} (hD : D.Closed)
    (key t : Project.Term k) (hKey : key.freeSupport=[]) (ht : t.freeSupport=[]) :
    (expansionRowFormula D key t).FreeClosed := by
  unfold expansionRowFormula
  simpa only [Definitional.Formula.FreeClosed] using
    (KP1Y.Functions.witnessInstanceFormula_freeClosed Expansion.expansionMatrix (fun i => (expansionParams D i).weaken)
      key.weaken t.weaken (.bound 0) (fun i => by simpa using expansionParams_closed hD i)
      (by simpa using hKey) (by simpa using ht) rfl)

theorem expansionRowFormula_iff {M : SetTheory.Structure.{u}} {k : Nat} (e : Env M k)
    (D : TheoremData (Project.Term k)) (key t : Project.Term k) :
    Project.Formula.satisfies e (expansionRowFormula D key t) ↔
      ∃ Box, Project.Formula.satisfies ((((Expansion.expansionEnv (D.eval e).expr (D.eval e).arith
        (D.eval e).forests (D.eval e).forestLists (D.eval e).grids).push (key.eval e)).push (t.eval e)).push Box)
        Expansion.expansionMatrix.body := by
  simp only [expansionRowFormula,Project.Formula.satisfies_exists_iff,KP1Y.Functions.witnessInstanceFormula_iff]
  apply exists_congr
  intro Box
  apply KP1Y.formula_bound_congr _ Expansion.expansionMatrix.freeClosed
  intro i
  refine Fin.cases ?_ (fun i => ?_) i
  · rfl
  · refine Fin.cases ?_ (fun i => ?_) i
    · exact Term.eval_weaken _ _ _
    · refine Fin.cases ?_ (fun i => ?_) i
      · exact Term.eval_weaken _ _ _
      · exact (Term.eval_weaken _ _ _).trans (expansionParams_eval D e i)

def expansionGraphFormula {k : Nat} (D : TheoremData (Project.Term k)) : Project.Formula 1 k :=
  .conj (cartesianFormula D.keys D.expr.expressions D.expr.omega)
    (.conj (graphFormula D.expansion D.keys D.expr.expressions)
      (Project.Formula.forallMem D.keys (Project.Formula.forallMem D.expr.expressions.weaken
        (.iff (memPairFormula D.expansion.weaken.weaken (.bound 1) (.bound 0))
          (expansionRowFormula D.weaken.weaken (.bound 1) (.bound 0))))))

theorem expansionGraphFormula_freeClosed {k : Nat} {D : TheoremData (Project.Term k)} (hD : D.Closed) :
    (expansionGraphFormula D).FreeClosed := by
  have hC := cartesianFormula_freeClosed D.keys D.expr.expressions D.expr.omega hD.keys hD.expr.expressions hD.expr.omega
  have hR := expansionRowFormula_freeClosed hD.weaken.weaken (.bound 1) (.bound 0) rfl rfl
  simp [expansionGraphFormula,graphFormula,codeFormula,pairFormula,memPairFormula,Project.Formula.forallMem,
    Project.Formula.existsMem,Definitional.Formula.FreeClosed,hD.keys,hD.expansion,hD.expr.expressions,hC,hR]

/-- 在其余数据有效时，EN 公式恰为 `Expansion.Graph`。 -/
theorem expansionGraphFormula_iff {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory) {k : Nat}
    (e : Env M k) (D : TheoremData (Project.Term k)) (hC : (D.eval e).expr.Valid M)
    (hT : (D.eval e).arith.Valid M (D.eval e).expr)
    (hAF : ExpressionDiagram.AllForests M (D.eval e).expr.omega (D.eval e).forests)
    (hS : MountainReconstruction.Spaces.Valid M (D.eval e).expr (D.eval e).forests ⟨(D.eval e).forestLists,(D.eval e).grids⟩) :
    Project.Formula.satisfies e (expansionGraphFormula D) ↔
      Expansion.Graph M (D.eval e).expr (D.eval e).arith (D.eval e).keys (D.eval e).expansion := by
  have hRow (key t : M.Domain) : Project.Formula.satisfies ((e.push key).push t)
      (expansionRowFormula D.weaken.weaken (.bound 1) (.bound 0)) ↔
        Expansion.CodedExpands M (D.eval e).expr (D.eval e).arith key t := by
    rw [expansionRowFormula_iff,TheoremData.eval_weaken,TheoremData.eval_weaken]
    exact Expansion.expansion_sigmaOne_iff_d hM hC hT hAF hS key t
  simp only [expansionGraphFormula,Project.Formula.satisfies_conj_iff,cartesianFormula_iff hM.1,graphFormula_iff hM.1,
    Project.Formula.satisfies_forallMem_iff,Project.Formula.satisfies_iff_iff,memPairFormula_iff hM.1,hRow,Term.eval_weaken]
  constructor
  · rintro ⟨hKeys,hGraph,hRows⟩
    refine ⟨hKeys,hGraph,fun key t => ⟨fun h => hRows key (hGraph.bounds hM.1 h).1 t (hGraph.bounds hM.1 h).2 |>.mp h,
      fun h => ?_⟩⟩
    obtain ⟨s,hs,N,hN,hCode,hExpand⟩ := h
    exact (hRows key ((hKeys key).mpr ⟨s,hs,N,hN,hCode⟩) t (hExpand.legal_d hM hC hT).2.2).mpr ⟨s,hs,N,hN,hCode,hExpand⟩
  · intro h
    exact ⟨h.keys,h.graph,fun key _ t _ => h.rows key t⟩

def theoremDataFormula {k : Nat} (D : TheoremData (Project.Term k)) : Project.Formula 1 k :=
  .conj (expressionValidFormula D.expr) (.conj (arithmeticFormula D.expr D.arith)
    (.conj (spacesFormula D.expr D.forests D.forestLists D.grids) (expansionGraphFormula D)))

theorem theoremDataFormula_freeClosed {k : Nat} {D : TheoremData (Project.Term k)} (hD : D.Closed) :
    (theoremDataFormula D).FreeClosed := by
  simp only [theoremDataFormula,Definitional.Formula.FreeClosed]
  exact ⟨expressionValidFormula_freeClosed hD.expr,arithmeticFormula_freeClosed hD,spacesFormula_freeClosed hD,
    expansionGraphFormula_freeClosed hD⟩

theorem theoremDataFormula_iff {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory) {k : Nat}
    (e : Env M k) (D : TheoremData (Project.Term k)) :
    Project.Formula.satisfies e (theoremDataFormula D) ↔ (D.eval e).Valid M := by
  simp only [theoremDataFormula,Project.Formula.satisfies_conj_iff,expressionValidFormula_iff hM.1,
    arithmeticFormula_iff hM,spacesFormula_iff hM.1]
  constructor
  · rintro ⟨hC,hT,⟨hAF,hS⟩,hG⟩
    exact ⟨hC,hT,hAF,hS,(expansionGraphFormula_iff hM e D hC hT hAF hS).mp hG⟩
  · intro h
    exact ⟨h.expr,h.arith,⟨h.forests,h.spaces⟩,(expansionGraphFormula_iff hM e D h.expr h.arith h.forests h.spaces).mpr h.graph⟩

/-! ### 实际存在 -/

theorem theorem_data_exists_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory) :
    ∃ D : TheoremData M.Domain, D.Valid M := by
  obtain ⟨w,hw,_⟩ := exists_omega_d hM
  obtain ⟨C,_,hC⟩ := expression_data_exists_d hM hw
  obtain ⟨T,hT⟩ := matrix_arithmetic_exists_d hM hC
  obtain ⟨AF,hAF⟩ := ExpressionDiagram.all_forests_exists_d hM hC
  obtain ⟨S,hS⟩ := MountainReconstruction.spaces_exists_d hM hC AF
  obtain ⟨Keys,EN,hG⟩ := Expansion.expansion_graph_exists_d hM hC hT
  exact ⟨⟨C,T,AF,S.forestLists,S.grids,Keys,EN⟩,hC,hT,hAF,hS,hG⟩

/-! ### 唯一性：全称与存在两种量化读法指向同一组集合 -/

theorem omega_unique {M : SetTheory.Structure.{u}} (he : Extensional M) {w w' : M.Domain}
    (h : M.IsOmega w) (h' : M.IsOmega w') : w=w' :=
  he.eq_of_same_members w w' (fun x => ⟨fun hx => h.2 w' h'.1 x hx,fun hx => h'.2 w h.1 x hx⟩)

theorem ExpressionData.Valid.unique {M : SetTheory.Structure.{u}} (he : Extensional M)
    {C C' : ExpressionData M.Domain} (h : C.Valid M) (h' : C'.Valid M) : C=C' := by
  rcases C with ⟨w,z,o,S,E⟩
  rcases C' with ⟨w',z',o',S',E'⟩
  have hw : w=w' := omega_unique he h.omega h'.omega
  have hz : z=z' := he.eq_of_same_members z z' (fun x => iff_of_false (h.zero_empty x) (h'.zero_empty x))
  subst w'
  subst z'
  have ho : o=o' := Structure.SuccessorOf.eq he h.one_succ h'.one_succ
  subst o'
  have hS : S=S' := he.eq_of_same_members S S' (fun x => (h.sequences x).trans (h'.sequences x).symm)
  have hE : E=E' := he.eq_of_same_members E E' (fun x => (h.expressions x).trans (h'.expressions x).symm)
  subst S'
  subst E'
  rfl

theorem product_unique {M : SetTheory.Structure.{u}} (he : Extensional M) {P P' X Y : M.Domain}
    (h : IsProduct M P X Y) (h' : IsProduct M P' X Y) : P=P' :=
  he.eq_of_same_members P P' (fun p => (h p).trans (h' p).symm)

theorem table_unique {M : SetTheory.Structure.{u}} (he : Extensional M) {w P P' F F' : M.Domain}
    {R : M.Domain → M.Domain → M.Domain → Prop} (hP : IsProduct M P w w) (hP' : IsProduct M P' w w)
    (hF : Graph M F P w) (hF' : Graph M F' P' w)
    (hR : ∀ a, M.mem a w → ∀ b, M.mem b w → ∀ key, Codes M key a b → ∀ c, MemPair M F key c ↔ R a b c)
    (hR' : ∀ a, M.mem a w → ∀ b, M.mem b w → ∀ key, Codes M key a b → ∀ c, MemPair M F' key c ↔ R a b c) :
    P=P' ∧ F=F' := by
  have hPP := product_unique he hP hP'
  subst P'
  refine ⟨rfl,hF.ext he hF' (fun key hk c => ?_)⟩
  obtain ⟨a,ha,b,hb,hCode⟩ := (hP key).mp hk
  exact (hR a ha b hb key hCode c).trans (hR' a ha b hb key hCode c).symm

theorem MatrixArithmetic.Valid.unique {M : SetTheory.Structure.{u}} (he : Extensional M)
    {C : ExpressionData M.Domain} {T T' : MatrixArithmetic M.Domain} (h : T.Valid M C) (h' : T'.Valid M C) : T=T' := by
  rcases T with ⟨ap,p,mp,t,dp,d⟩
  rcases T' with ⟨ap',p',mp',t',dp',d'⟩
  obtain ⟨h1,h2⟩ := table_unique he h.add.pairs h'.add.pairs h.add.graph h'.add.graph h.add.rows h'.add.rows
  obtain ⟨h3,h4⟩ := table_unique he h.mul.pairs h'.mul.pairs h.mul.graph h'.mul.graph h.mul.rows h'.mul.rows
  obtain ⟨h5,h6⟩ := table_unique he h.diff.pairs h'.diff.pairs h.diff.graph h'.diff.graph h.diff.rows h'.diff.rows
  subst h1 h2 h3 h4 h5 h6
  rfl

/-- 定义公式确定唯一一组辅助集合。 -/
theorem TheoremData.Valid.unique {M : SetTheory.Structure.{u}} (he : Extensional M)
    {D D' : TheoremData M.Domain} (h : D.Valid M) (h' : D'.Valid M) : D=D' := by
  rcases D with ⟨C,T,F,FL,G,K,EN⟩
  rcases D' with ⟨C',T',F',FL',G',K',EN'⟩
  have hC : C=C' := ExpressionData.Valid.unique he h.expr h'.expr
  subst C'
  have hT : T=T' := MatrixArithmetic.Valid.unique he h.arith h'.arith
  subst T'
  have hF : F=F' := he.eq_of_same_members F F' (fun x => (h.forests x).trans (h'.forests x).symm)
  subst F'
  have hFL : FL=FL' := he.eq_of_same_members FL FL' (fun x => (h.spaces.forestLists x).trans (h'.spaces.forestLists x).symm)
  have hG : G=G' := he.eq_of_same_members G G' (fun x => (h.spaces.grids x).trans (h'.spaces.grids x).symm)
  obtain ⟨hK,hEN⟩ := h.graph.unique he h'.graph
  have hK' : K=K' := hK
  have hEN' : EN=EN' := hEN
  subst FL' G' K' EN'
  rfl

end KP1Y.OneYTheorem
