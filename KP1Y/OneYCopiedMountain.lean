import KP1Y.OneYOrdinaryCoordinates
import KP1Y.OneYMountainLayers

/-! 实际有限宽度山形的公共 height/parent 家族接口，以及三种复制的单层构造。 -/
namespace KP1Y.OneYFinite.CopiedMountain
open YesMetaZFC YesMetaZFC.SetTheory YesMetaZFC.SetTheory.Definitional
open KP1Y.Kuratowski KP1Y.Functions KP1Y.Naturals KP1Y.Bounded
universe u v

structure Data (α : Type u) where
  width : α
  heights : α
  forests : α
  parents : α

def Data.map {α : Type u} {β : Type v} (X : Data α) (f : α → β) : Data β := ⟨f X.width,f X.heights,f X.forests,f X.parents⟩
def Data.eval {M : SetTheory.Structure.{u}} {n : Nat} (X : Data (Project.Term n)) (e : Env M n) : Data M.Domain := X.map (fun t => t.eval e)
def Data.weaken {n : Nat} (X : Data (Project.Term n)) : Data (Project.Term (n+1)) := X.map (fun t => t.weaken)

theorem Data.eval_weaken {M : SetTheory.Structure.{u}} {n : Nat} (X : Data (Project.Term n)) (e : Env M n) (a : M.Domain) :
    X.weaken.eval (e.push a)=X.eval e := by
  cases X
  simp [Data.eval,Data.weaken,Data.map,Term.eval_weaken]

structure Data.Closed {n : Nat} (X : Data (Project.Term n)) : Prop where
  width : X.width.freeSupport=[]
  heights : X.heights.freeSupport=[]
  forests : X.forests.freeSupport=[]
  parents : X.parents.freeSupport=[]

def ParentAt (M : SetTheory.Structure.{u}) (X : Data M.Domain) (r c p : M.Domain) : Prop :=
  ∃ F, M.mem F X.forests ∧ MemPair M X.parents r F ∧ MemPair M F c p

def parentAtFormula {n : Nat} (X : Data (Project.Term n)) (r c p : Project.Term n) : Project.Formula 1 n :=
  Project.Formula.existsMem X.forests (.conj (memPairFormula X.parents.weaken r.weaken (.bound 0))
    (memPairFormula (.bound 0) c.weaken p.weaken))

theorem parentAtFormula_delta0 {n : Nat} (X : Data (Project.Term n)) (r c p : Project.Term n) :
    (parentAtFormula X r c p).IsDelta0 := .existsMem _ (.conj (memPairFormula_delta0 _ _ _) (memPairFormula_delta0 _ _ _))

theorem parentAtFormula_freeClosed {n : Nat} {X : Data (Project.Term n)} (hX : X.Closed)
    (r c p : Project.Term n) (hr : r.freeSupport=[]) (hc : c.freeSupport=[]) (hp : p.freeSupport=[]) :
    (parentAtFormula X r c p).FreeClosed := by
  simp [parentAtFormula,memPairFormula,codeFormula,pairFormula,Project.Formula.forallMem,Project.Formula.existsMem,
    Definitional.Formula.FreeClosed,hX.forests,hX.parents,hr,hc,hp]

theorem parentAtFormula_iff {M : SetTheory.Structure.{u}} (he : Extensional M) {n : Nat} (e : Env M n)
    (X : Data (Project.Term n)) (r c p : Project.Term n) :
    Project.Formula.satisfies e (parentAtFormula X r c p) ↔ ParentAt M (X.eval e) (r.eval e) (c.eval e) (p.eval e) := by
  simp only [parentAtFormula,Project.Formula.satisfies_existsMem_iff,Project.Formula.satisfies_conj_iff,memPairFormula_iff he,Term.eval_weaken]
  rfl

/-- 仅记录真实父森林与可重建的局部高度几何；不要求输入是重新提取出的 NumericRow。 -/
structure Data.Valid (M : SetTheory.Structure.{u}) (C : ExpressionData M.Domain) (X : Data M.Domain) : Prop where
  width : M.mem X.width C.omega
  heights : Graph M X.heights X.width C.omega
  parents : Graph M X.parents C.omega X.forests
  forest : ∀ r F, MemPair M X.parents r F → Forest M C.omega X.width F
  source : ∀ r c h, MemPair M X.heights c h → ((∃ p, ParentAt M X r c p) ↔ M.mem r h)
  endpoint : ∀ r c p h, ParentAt M X r c p → MemPair M X.heights p h → r=h ∨ M.mem r h

theorem ParentAt.bounds {M : SetTheory.Structure.{u}} (he : Extensional M) {C : ExpressionData M.Domain}
    {X : Data M.Domain} (hX : X.Valid M C) {r c p : M.Domain} (h : ParentAt M X r c p) :
    M.mem r C.omega ∧ M.mem c X.width ∧ M.mem p X.width ∧ M.mem p c := by
  obtain ⟨F,_,hRow,hParent⟩ := h
  have hForest := hX.forest r F hRow
  exact ⟨(hX.parents.bounds he hRow).1,(hForest.bounds he hParent).1,(hForest.bounds he hParent).2,hForest.left c p hParent⟩

theorem ParentAt.unique {M : SetTheory.Structure.{u}} {C : ExpressionData M.Domain}
    {X : Data M.Domain} (hX : X.Valid M C) {r c p q : M.Domain} (h : ParentAt M X r c p) (h' : ParentAt M X r c q) : p=q := by
  obtain ⟨F,_,hRow,hParent⟩ := h
  obtain ⟨F',_,hRow',hParent'⟩ := h'
  have hFF := hX.parents.unique r F F' hRow hRow'
  subst F'
  exact (hX.forest r F hRow).unique c p q hParent hParent'

private def rowParentSchema : Project.Delta0BinarySchema 4 where
  body := Project.Formula.existsMem (.bound 5)
    (rowAtFormula (.bound 4) (.bound 3) (.bound 2) (.bound 0) (.bound 1))
  freeClosed := by
    simp [rowAtFormula,memPairFormula,codeFormula,pairFormula,Project.Formula.forallMem,
      Project.Formula.existsMem,Definitional.Formula.FreeClosed]
  delta0 := .existsMem _ (rowAtFormula_delta0 _ _ _ _ _)

/-- 从实际数值行运行读取整条内部 ω 父行家族，不使用宿主 r↦forest 函数。 -/
theorem row_parent_graph_exists_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} {m : M.Domain} {R : RowStateSpace M.Domain} {V P H : M.Domain}
    (hRun : RowRun M C m R V P H) : ∃ Parents, Graph M Parents C.omega R.forests ∧
      ∀ r F, MemPair M Parents r F ↔ ∃ U, RowAt M R.states H r U F := by
  let e := (((oneEnv R.values).push R.forests).push R.states).push H
  have hφ (r F : M.Domain) : Project.Formula.satisfies ((e.push r).push F) rowParentSchema.body ↔
      ∃ U, M.mem U R.values ∧ RowAt M R.states H r U F := by
    simp only [rowParentSchema,Project.Formula.satisfies_existsMem_iff,rowAtFormula_iff hM.1]
    rfl
  obtain ⟨Parents,hSupport,hRaw⟩ := relation_comprehension_d hM rowParentSchema e C.omega R.forests
  have hRows (r F : M.Domain) : MemPair M Parents r F ↔ ∃ U, RowAt M R.states H r U F := by
    have hr := hRaw r F
    rw [hφ] at hr
    refine hr.trans ⟨?_,?_⟩
    · rintro ⟨_,_,U,_,hRow⟩
      exact ⟨U,hRow⟩
    · rintro ⟨U,state,hState,hAt,hCode⟩
      obtain ⟨U',hU',F',hF',hCode'⟩ := (hRun.space.states state).mp hState
      obtain ⟨hUU,hFF⟩ := codes_injective hM.1 hCode hCode'
      subst U'
      subst F'
      exact ⟨(hRun.graph.bounds hM.1 hAt).1,hF',U,hU',state,hState,hAt,hCode⟩
  refine ⟨Parents,⟨hSupport,?_,?_⟩,hRows⟩
  · intro r hr
    obtain ⟨U,F,hAt⟩ := hRun.at_exists_d hr
    obtain ⟨state,hState,hStateAt,hCode⟩ := hAt
    obtain ⟨U',_,F',hF',hCode'⟩ := (hRun.space.states state).mp hState
    obtain ⟨_,hFF⟩ := codes_injective hM.1 hCode hCode'
    subst F'
    exact ⟨F,hF',(hRows r F).mpr ⟨U,state,hState,hStateAt,hCode⟩⟩
  · intro r F F' hAt hAt'
    obtain ⟨U,hRow⟩ := (hRows r F).mp hAt
    obtain ⟨U',hRow'⟩ := (hRows r F').mp hAt'
    exact (hRun.at_unique hM.1 hRow hRow').2


structure FromRun (M : SetTheory.Structure.{u}) (C : ExpressionData M.Domain) (m : M.Domain)
    (R : RowStateSpace M.Domain) (V H : M.Domain) (X : Data M.Domain) : Prop where
  width : X.width=m
  heights : HeightGraph M C m R V H X.heights
  parents : ∀ r F, MemPair M X.parents r F ↔ ∃ U, RowAt M R.states H r U F

theorem from_run_exists_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {m : M.Domain} {R : RowStateSpace M.Domain} {V P H : M.Domain}
    (hRun : RowRun M C m R V P H) (hPositive : ∀ c v, MemPair M V c v → M.mem C.zero v) :
    ∃ X, X.Valid M C ∧ FromRun M C m R V H X := by
  obtain ⟨Heights,hHeights⟩ := height_graph_exists_d hM hC hRun
  obtain ⟨Parents,hParents,hRows⟩ := row_parent_graph_exists_d hM hRun
  let X : Data M.Domain := ⟨m,Heights,R.forests,Parents⟩
  have hForest (r F : M.Domain) (hAt : MemPair M Parents r F) : Forest M C.omega m F := by
    obtain ⟨U,hRow⟩ := (hRows r F).mp hAt
    exact (hRun.at_numeric_d hM hC hRow).forest
  refine ⟨X,⟨hRun.space.width,hHeights.graph,hParents,hForest,?_,?_⟩,rfl,hHeights,hRows⟩
  · intro r c height hHeight
    obtain ⟨hc,hHeightAt⟩ := (hHeights.rows c height).mp hHeight
    obtain ⟨a,_,hA⟩ := hRun.base.values.total c hc
    constructor
    · rintro ⟨p,F,_,hF,hParent⟩
      obtain ⟨U,hRow⟩ := (hRows r F).mp hF
      exact (hRun.parent_iff_lt_height_d hM hC hRow hA (hPositive c a hA) hHeightAt).mp ⟨p,hParent⟩
    · intro hr
      have hrNat := (omega_isOrdinal_d hM hC.omega).transitive height (hHeights.graph.bounds hM.1 hHeight).2 r hr
      obtain ⟨U,F,hRow⟩ := hRun.at_exists_d hrNat
      obtain ⟨p,hParent⟩ := (hRun.parent_iff_lt_height_d hM hC hRow hA (hPositive c a hA) hHeightAt).mpr hr
      have hF := (hRows r F).mpr ⟨U,hRow⟩
      exact ⟨p,F,(hParents.bounds hM.1 hF).2,hF,hParent⟩
  · rintro r c p height ⟨F,_,hF,hParent⟩ hHeight
    obtain ⟨U,hRow⟩ := (hRows r F).mp hF
    obtain ⟨hc,_,hHC⟩ := hHeights.graph.total c ((hForest r F hF).bounds hM.1 hParent).1
    exact (hHeights.parent_height_bounds_d hM hC hRun hPositive hRow hParent hHC hHeight).2

theorem FromRun.parent_iff {M : SetTheory.Structure.{u}} (he : Extensional M)
    {C : ExpressionData M.Domain} {m : M.Domain} {R : RowStateSpace M.Domain} {V H : M.Domain} {X : Data M.Domain}
    (hX : X.Valid M C) (h : FromRun M C m R V H X) (r c p : M.Domain) :
    ParentAt M X r c p ↔ ∃ U F, RowAt M R.states H r U F ∧ MemPair M F c p := by
  constructor
  · rintro ⟨F,_,hF,hParent⟩
    obtain ⟨U,hRow⟩ := (h.parents r F).mp hF
    exact ⟨U,F,hRow,hParent⟩
  · rintro ⟨U,F,hRow,hParent⟩
    have hF := (h.parents r F).mpr ⟨U,hRow⟩
    exact ⟨F,(hX.parents.bounds he hF).2,hF,hParent⟩


theorem Data.Closed.weaken {n : Nat} {X : Data (Project.Term n)} (h : X.Closed) : X.weaken.Closed := by
  constructor <;> simp [Data.weaken,Data.map,h.width,h.heights,h.forests,h.parents]

namespace Ordinary
open KP1Y.OneYFinite.CopyCoordinates

def Height (M : SetTheory.Structure.{u}) (C : ExpressionData M.Domain) (T : MatrixArithmetic M.Domain)
    (A : Context M.Domain) (X : Data M.Domain) (c h : M.Domain) : Prop :=
  ∃ s, M.mem s C.omega ∧ ∃ b, M.mem b C.omega ∧ OrdinaryCoordinates.Decoded M C T A c s b ∧ MemPair M X.heights s h

def Parent (M : SetTheory.Structure.{u}) (C : ExpressionData M.Domain) (T : MatrixArithmetic M.Domain)
    (A : Context M.Domain) (X : Data M.Domain) (r c q : M.Domain) : Prop :=
  ∃ s, M.mem s C.omega ∧ ∃ b, M.mem b C.omega ∧ ∃ p, M.mem p C.omega ∧
    OrdinaryCoordinates.Decoded M C T A c s b ∧ ParentAt M X r s p ∧ ParentCopy M C T A b p q

def heightFormula {n : Nat} (C : ExpressionData (Project.Term n)) (T : MatrixArithmetic (Project.Term n))
    (A : Context (Project.Term n)) (X : Data (Project.Term n)) (c h : Project.Term n) : Project.Formula 1 n :=
  Project.Formula.existsMem C.omega (Project.Formula.existsMem C.omega.weaken
    (.conj (OrdinaryCoordinates.decodedFormula C.weaken.weaken T.weaken.weaken A.weaken.weaken c.weaken.weaken (.bound 1) (.bound 0))
      (memPairFormula X.heights.weaken.weaken (.bound 1) h.weaken.weaken)))

def parentFormula {n : Nat} (C : ExpressionData (Project.Term n)) (T : MatrixArithmetic (Project.Term n))
    (A : Context (Project.Term n)) (X : Data (Project.Term n)) (r c q : Project.Term n) : Project.Formula 1 n :=
  Project.Formula.existsMem C.omega (Project.Formula.existsMem C.omega.weaken (Project.Formula.existsMem C.omega.weaken.weaken
    (.conj (OrdinaryCoordinates.decodedFormula C.weaken.weaken.weaken T.weaken.weaken.weaken A.weaken.weaken.weaken
      c.weaken.weaken.weaken (.bound 2) (.bound 1))
      (.conj (parentAtFormula X.weaken.weaken.weaken r.weaken.weaken.weaken (.bound 2) (.bound 0))
        (parentCopyFormula C.weaken.weaken.weaken T.weaken.weaken.weaken A.weaken.weaken.weaken (.bound 1) (.bound 0) q.weaken.weaken.weaken)))))

theorem heightFormula_delta0 {n : Nat} (C : ExpressionData (Project.Term n)) (T : MatrixArithmetic (Project.Term n))
    (A : Context (Project.Term n)) (X : Data (Project.Term n)) (c h : Project.Term n) : (heightFormula C T A X c h).IsDelta0 :=
  .existsMem _ (.existsMem _ (.conj (OrdinaryCoordinates.decodedFormula_delta0 _ _ _ _ _ _) (memPairFormula_delta0 _ _ _)))

theorem parentFormula_delta0 {n : Nat} (C : ExpressionData (Project.Term n)) (T : MatrixArithmetic (Project.Term n))
    (A : Context (Project.Term n)) (X : Data (Project.Term n)) (r c q : Project.Term n) : (parentFormula C T A X r c q).IsDelta0 :=
  .existsMem _ (.existsMem _ (.existsMem _ (.conj (OrdinaryCoordinates.decodedFormula_delta0 _ _ _ _ _ _)
    (.conj (parentAtFormula_delta0 _ _ _ _) (parentCopyFormula_delta0 _ _ _ _ _ _)))))

theorem heightFormula_freeClosed {n : Nat} {C : ExpressionData (Project.Term n)} (hC : C.Closed)
    {T : MatrixArithmetic (Project.Term n)} (hT : ArithmeticClosed T) {A : Context (Project.Term n)} (hA : A.Closed)
    {X : Data (Project.Term n)} (hX : X.Closed) (c h : Project.Term n) (hc : c.freeSupport=[]) (hh : h.freeSupport=[]) :
    (heightFormula C T A X c h).FreeClosed := by
  have hDec := OrdinaryCoordinates.decodedFormula_freeClosed hC.weaken.weaken hT.weaken.weaken hA.weaken.weaken
    c.weaken.weaken (.bound 1) (.bound 0) (by simpa using hc) rfl rfl
  simp [heightFormula,Project.Formula.existsMem,Definitional.Formula.FreeClosed,memPairFormula,codeFormula,pairFormula,
    Project.Formula.forallMem,hC.omega,hX.heights,hh,hDec]

theorem parentFormula_freeClosed {n : Nat} {C : ExpressionData (Project.Term n)} (hC : C.Closed)
    {T : MatrixArithmetic (Project.Term n)} (hT : ArithmeticClosed T) {A : Context (Project.Term n)} (hA : A.Closed)
    {X : Data (Project.Term n)} (hX : X.Closed) (r c q : Project.Term n)
    (hr : r.freeSupport=[]) (hc : c.freeSupport=[]) (hq : q.freeSupport=[]) : (parentFormula C T A X r c q).FreeClosed := by
  have hDec := OrdinaryCoordinates.decodedFormula_freeClosed hC.weaken.weaken.weaken hT.weaken.weaken.weaken hA.weaken.weaken.weaken
    c.weaken.weaken.weaken (.bound 2) (.bound 1) (by simpa using hc) rfl rfl
  have hPar := parentAtFormula_freeClosed hX.weaken.weaken.weaken r.weaken.weaken.weaken (.bound 2) (.bound 0) (by simpa using hr) rfl rfl
  have hCopy := parentCopyFormula_freeClosed hC.weaken.weaken.weaken hT.weaken.weaken.weaken hA.weaken.weaken.weaken
    (.bound 1) (.bound 0) q.weaken.weaken.weaken rfl rfl (by simpa using hq)
  simp [parentFormula,Project.Formula.existsMem,Definitional.Formula.FreeClosed,hC.omega,hDec,hPar,hCopy]

theorem heightFormula_iff {M : SetTheory.Structure.{u}} (he : Extensional M) {n : Nat} (e : Env M n)
    (C : ExpressionData (Project.Term n)) (T : MatrixArithmetic (Project.Term n)) (A : Context (Project.Term n))
    (X : Data (Project.Term n)) (c h : Project.Term n) : Project.Formula.satisfies e (heightFormula C T A X c h) ↔
      Height M (C.eval e) (T.eval e) (A.eval e) (X.eval e) (c.eval e) (h.eval e) := by
  simp only [heightFormula,Project.Formula.satisfies_existsMem_iff,Project.Formula.satisfies_conj_iff,
    OrdinaryCoordinates.decodedFormula_iff he,memPairFormula_iff he,
    ExpressionData.eval_weaken,MatrixArithmetic.eval_weaken,Context.eval_weaken,Term.eval_weaken]
  rfl

theorem parentFormula_iff {M : SetTheory.Structure.{u}} (he : Extensional M) {n : Nat} (e : Env M n)
    (C : ExpressionData (Project.Term n)) (T : MatrixArithmetic (Project.Term n)) (A : Context (Project.Term n))
    (X : Data (Project.Term n)) (r c q : Project.Term n) : Project.Formula.satisfies e (parentFormula C T A X r c q) ↔
      Parent M (C.eval e) (T.eval e) (A.eval e) (X.eval e) (r.eval e) (c.eval e) (q.eval e) := by
  simp only [parentFormula,Project.Formula.satisfies_existsMem_iff,Project.Formula.satisfies_conj_iff,
    OrdinaryCoordinates.decodedFormula_iff he,parentAtFormula_iff he,parentCopyFormula_iff he,
    ExpressionData.eval_weaken,MatrixArithmetic.eval_weaken,Context.eval_weaken,Data.eval_weaken,Term.eval_weaken]
  rfl

theorem height_exists_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {A : Context M.Domain} (hA : A.Valid M C) {X : Data M.Domain} (hX : X.Valid M C)
    (hLast : M.mem A.last X.width) {c : M.Domain} (hc : M.mem c C.omega) : ∃ h, M.mem h C.omega ∧ Height M C T A X c h := by
  obtain ⟨s,b,hDec⟩ := OrdinaryCoordinates.decoded_exists_d hM hC hT hA hc
  have hs := ((omega_isOrdinal_d hM hC.omega).mem hX.width).transitive A.last hLast s (hDec.source_lt_last_d hM hC hT hA)
  obtain ⟨h,hh,hAt⟩ := hX.heights.total s hs
  exact ⟨h,hh,s,hDec.2.1,b,hDec.2.2.1,hDec,hAt⟩

theorem Height.unique_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {A : Context M.Domain} (hA : A.Valid M C) {X : Data M.Domain} (hX : X.Valid M C) {c h h' : M.Domain}
    (hHeight : Height M C T A X c h) (hHeight' : Height M C T A X c h') : h=h' := by
  obtain ⟨s,_,b,_,hDec,hAt⟩ := hHeight
  obtain ⟨s',_,b',_,hDec',hAt'⟩ := hHeight'
  obtain ⟨hss,_⟩ := hDec.unique_d hM hC hT hA hDec'
  subst s'
  exact hX.heights.unique s h h' hAt hAt'

theorem Parent.left_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {A : Context M.Domain} (hA : A.Valid M C) {X : Data M.Domain} (hX : X.Valid M C) {r c q : M.Domain}
    (h : Parent M C T A X r c q) : M.mem q c := by
  obtain ⟨s,_,b,_,p,_,hDec,hParent,hCopy⟩ := h
  exact hDec.parent_left_d hM hC hT hA hCopy (hParent.bounds hM.1 hX).2.2.2

theorem Parent.unique_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {A : Context M.Domain} (hA : A.Valid M C) {X : Data M.Domain} (hX : X.Valid M C) {r c q q' : M.Domain}
    (h : Parent M C T A X r c q) (h' : Parent M C T A X r c q') : q=q' := by
  obtain ⟨s,_,b,hb,p,hp,hDec,hParent,hCopy⟩ := h
  obtain ⟨s',_,b',_,p',_,hDec',hParent',hCopy'⟩ := h'
  obtain ⟨hss,hbb⟩ := hDec.unique_d hM hC hT hA hDec'
  subst s'
  subst b'
  have hpp := hParent.unique hX hParent'
  subst p'
  obtain ⟨J,hJ,hRows⟩ := parent_copy_graph_exists_d hM hC hT hA hb
  exact hJ.graph.unique p q q' ((hRows p q).mpr hCopy) ((hRows p q').mpr hCopy')

end Ordinary

/-- 有界单行定义的实际 ω 长有限森林家族；各复制分支共享同一收集构造。 -/
def ForestRow {M : SetTheory.Structure.{u}} {n : Nat} (φ : Project.Delta0BinarySchema (n+1))
    (e : Env M n) (w width r F : M.Domain) : Prop :=
  Forest M w width F ∧ ∀ c, M.mem c width → ∀ p, M.mem p width →
    (MemPair M F c p ↔ Project.Formula.satisfies (((e.push r).push c).push p) φ.body)

private def forestRowSlots {n : Nat} : Fin (n+3) → Fin (n+6) :=
  Fin.cases 0 (Fin.cases 1 (Fin.cases 3 (fun i => ⟨i.val+6,by omega⟩)))

private def forestRowSchema {n : Nat} (φ : Project.Delta0BinarySchema (n+1)) : Project.Delta0BinarySchema (n+2) where
  body := .conj (forestFormula (.bound 3) (.bound 2) (.bound 0))
    (Project.Formula.forallMem (.bound 2) (Project.Formula.forallMem (.bound 3)
      (.iff (memPairFormula (.bound 2) (.bound 1) (.bound 0)) (φ.body.rename forestRowSlots))))
  freeClosed := by
    have hForest := forestFormula_freeClosed (Project.Term.bound (depth := n+4) 3) (.bound 2) (.bound 0) rfl rfl rfl
    simp [Project.Formula.forallMem,Definitional.Formula.FreeClosed,memPairFormula,codeFormula,pairFormula,
      Project.Formula.existsMem,hForest,φ.freeClosed]
  delta0 := .conj (forestFormula_delta0 _ _ _) (.forallMem _ (.forallMem _
    (.iff (memPairFormula_delta0 _ _ _) (KP1Y.delta0_rename φ.delta0 _))))

private theorem forestRowSchema_iff {M : SetTheory.Structure.{u}} (he : Extensional M) {n : Nat}
    (φ : Project.Delta0BinarySchema (n+1)) (e : Env M n) (w width r F : M.Domain) :
    Project.Formula.satisfies (((((e.push w).push width).push r).push F)) (forestRowSchema φ).body ↔ ForestRow φ e w width r F := by
  have hEnv (c p : M.Domain) : ((((((e.push w).push width).push r).push F).push c).push p).reindex forestRowSlots =
      ((e.push r).push c).push p := by
    rw [Env.mk.injEq]
    constructor
    · funext i
      refine Fin.cases ?_ (fun i => ?_) i
      · rfl
      · refine Fin.cases ?_ (fun i => ?_) i
        · rfl
        · refine Fin.cases ?_ (fun i => ?_) i <;> rfl
    · rfl
  simp only [forestRowSchema,Project.Formula.satisfies_conj_iff,forestFormula_iff he,
    Project.Formula.satisfies_forallMem_iff,Project.Formula.satisfies_iff_iff,memPairFormula_iff he,
    Project.Formula.satisfies_rename,hEnv]
  rfl

theorem forest_row_exists_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory) {n : Nat}
    (φ : Project.Delta0BinarySchema (n+1)) (e : Env M n) {C : ExpressionData M.Domain} {width r : M.Domain}
    (hWidth : M.mem width C.omega)
    (hLeft : ∀ c, M.mem c width → ∀ p, M.mem p width → Project.Formula.satisfies (((e.push r).push c).push p) φ.body → M.mem p c)
    (hUnique : ∀ c, M.mem c width → ∀ p, M.mem p width → ∀ q, M.mem q width →
      Project.Formula.satisfies (((e.push r).push c).push p) φ.body → Project.Formula.satisfies (((e.push r).push c).push q) φ.body → p=q) :
    ∃ F, ForestRow φ e C.omega width r F := by
  obtain ⟨F,hSupport,hRows⟩ := relation_comprehension_d hM φ (e.push r) width width
  refine ⟨F,⟨hWidth,hSupport,?_,?_⟩,fun c hc p hp => (hRows c p).trans ⟨fun h => h.2.2,fun h => ⟨hc,hp,h⟩⟩⟩
  · intro c p q hcp hcq
    obtain ⟨hc,hp,hP⟩ := (hRows c p).mp hcp
    obtain ⟨_,hq,hQ⟩ := (hRows c q).mp hcq
    exact hUnique c hc p hp q hq hP hQ
  · intro c p hcp
    obtain ⟨hc,hp,hP⟩ := (hRows c p).mp hcp
    exact hLeft c hc p hp hP

theorem ForestRow.unique {M : SetTheory.Structure.{u}} (he : Extensional M) {n : Nat}
    {φ : Project.Delta0BinarySchema (n+1)} {e : Env M n} {w width r F G : M.Domain}
    (h : ForestRow φ e w width r F) (h' : ForestRow φ e w width r G) : F=G := by
  apply h.1.ext he h'.1
  intro c p
  classical
  by_cases hc : M.mem c width
  · by_cases hp : M.mem p width
    · exact (h.2 c hc p hp).trans (h'.2 c hc p hp).symm
    · exact iff_of_false (fun hAt => hp (h.1.bounds he hAt).2) (fun hAt => hp (h'.1.bounds he hAt).2)
  · exact iff_of_false (fun hAt => hc (h.1.bounds he hAt).1) (fun hAt => hc (h'.1.bounds he hAt).1)

theorem forest_family_exists_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {n : Nat} (φ : Project.Delta0BinarySchema (n+1)) (e : Env M n)
    {width : M.Domain} (hWidth : M.mem width C.omega)
    (hLeft : ∀ r, M.mem r C.omega → ∀ c, M.mem c width → ∀ p, M.mem p width →
      Project.Formula.satisfies (((e.push r).push c).push p) φ.body → M.mem p c)
    (hUnique : ∀ r, M.mem r C.omega → ∀ c, M.mem c width → ∀ p, M.mem p width → ∀ q, M.mem q width →
      Project.Formula.satisfies (((e.push r).push c).push p) φ.body → Project.Formula.satisfies (((e.push r).push c).push q) φ.body → p=q) :
    ∃ Forests Parents, Graph M Parents C.omega Forests ∧ (∀ F, M.mem F Forests ↔ Forest M C.omega width F) ∧
      ∀ r F, MemPair M Parents r F ↔ M.mem r C.omega ∧ ForestRow φ e C.omega width r F := by
  obtain ⟨Forests,hForests⟩ := forest_space_exists_d hM hC hWidth
  obtain ⟨Parents,hSupport,hRaw⟩ := relation_comprehension_d hM (forestRowSchema φ) ((e.push C.omega).push width) C.omega Forests
  have hRows (r F : M.Domain) : MemPair M Parents r F ↔ M.mem r C.omega ∧ ForestRow φ e C.omega width r F := by
    have h := hRaw r F
    rw [forestRowSchema_iff hM.1] at h
    exact h.trans ⟨fun h => ⟨h.1,h.2.2⟩,fun h => ⟨h.1,(hForests F).mpr h.2.1,h.2⟩⟩
  refine ⟨Forests,Parents,⟨hSupport,?_,?_⟩,hForests,hRows⟩
  · intro r hr
    obtain ⟨F,hF⟩ := forest_row_exists_d hM φ e hWidth (hLeft r hr) (hUnique r hr)
    exact ⟨F,(hForests F).mpr hF.1,(hRows r F).mpr ⟨hr,hF⟩⟩
  · intro r F G hF hG
    exact ((hRows r F).mp hF).2.unique hM.1 ((hRows r G).mp hG).2

end KP1Y.OneYFinite.CopiedMountain
