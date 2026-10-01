import KP1Y.OneYCopyTower
import KP1Y.OneYExpressionDiagram
import KP1Y.OneYMountainPrefix

/-! 复制山形塔的实际根图原子枚举；不要求输入已经成为Numeric/RowRun。
槽位按(k,column,row)稳定过滤，允许不同row产生重复的同一个四元原子。 -/
namespace KP1Y.OneYFinite.CopyDiagram
open YesMetaZFC YesMetaZFC.SetTheory YesMetaZFC.SetTheory.Definitional
open KP1Y.Kuratowski KP1Y.Functions KP1Y.Naturals KP1Y.Bounded
open KP1Y.OneYFinite
universe u v

structure Input (α : Type u) where
  horizon : α
  width : α
  forests : α
  codes : α
  tower : α

def Input.map {α : Type u} {β : Type v} (I : Input α) (f : α → β) : Input β := ⟨f I.horizon,f I.width,f I.forests,f I.codes,f I.tower⟩
def Input.eval {M : SetTheory.Structure.{u}} {n : Nat} (I : Input (Project.Term n)) (e : Env M n) : Input M.Domain := I.map (fun t => t.eval e)
def Input.weaken {n : Nat} (I : Input (Project.Term n)) : Input (Project.Term (n+1)) := I.map (fun t => t.weaken)

theorem Input.eval_weaken {M : SetTheory.Structure.{u}} {n : Nat} (I : Input (Project.Term n)) (e : Env M n) (a : M.Domain) : I.weaken.eval (e.push a)=I.eval e := by
  cases I
  simp [Input.weaken,Input.eval,Input.map,Term.eval_weaken]

structure Input.Closed {n : Nat} (I : Input (Project.Term n)) : Prop where
  horizon : I.horizon.freeSupport=[]
  width : I.width.freeSupport=[]
  forests : I.forests.freeSupport=[]
  codes : I.codes.freeSupport=[]
  tower : I.tower.freeSupport=[]

theorem Input.Closed.weaken {n : Nat} {I : Input (Project.Term n)} (h : I.Closed) : I.weaken.Closed := by
  constructor <;> simp [Input.weaken,Input.map,h.horizon,h.width,h.forests,h.codes,h.tower]

structure Input.Valid (M : SetTheory.Structure.{u}) (C : ExpressionData M.Domain) (I : Input M.Domain) : Prop where
  horizon : M.mem I.horizon C.omega
  width : M.mem I.width C.omega
  tower : Graph M I.tower I.horizon I.codes
  values : ∀k code, MemPair M I.tower k code → CopiedMountain.CodeValid M C I.width I.forests code

def RowAtom (M : SetTheory.Structure.{u}) (C : ExpressionData M.Domain) (I : Input M.Domain) (k r q p c : M.Domain) : Prop :=
  ∃code, M.mem code I.codes ∧ MemPair M I.tower k code ∧ ∃heights parents, Codes M code heights parents ∧
    ∃F, M.mem F I.forests ∧ MemPair M parents r F ∧ MemPair M F c p ∧ Root M C I.width F c q

def Atom (M : SetTheory.Structure.{u}) (C : ExpressionData M.Domain) (I : Input M.Domain) (k q p c : M.Domain) : Prop :=
  M.mem k I.horizon ∧ ∃r, M.mem r C.omega ∧ RowAtom M C I k r q p c

def rowAtomFormula {n : Nat} (C : ExpressionData (Project.Term n)) (I : Input (Project.Term n)) (k r q p c : Project.Term n) : Project.Formula 1 n :=
  Project.Formula.existsMem I.codes (.conj (memPairFormula I.tower.weaken k.weaken (.bound 0))
    (CopiedMountain.withCodeFormula (.bound 0) (Project.Formula.existsMem I.forests.weaken.weaken.weaken.weaken
      (.conj (memPairFormula (.bound 1) r.weaken.weaken.weaken.weaken.weaken (.bound 0))
        (.conj (memPairFormula (.bound 0) c.weaken.weaken.weaken.weaken.weaken p.weaken.weaken.weaken.weaken.weaken)
          (rootFormula C.weaken.weaken.weaken.weaken.weaken I.width.weaken.weaken.weaken.weaken.weaken (.bound 0)
            c.weaken.weaken.weaken.weaken.weaken q.weaken.weaken.weaken.weaken.weaken))))))

theorem rowAtomFormula_delta0 {n : Nat} (C : ExpressionData (Project.Term n)) (I : Input (Project.Term n)) (k r q p c : Project.Term n) :
    (rowAtomFormula C I k r q p c).IsDelta0 := .existsMem _ (.conj (memPairFormula_delta0 _ _ _)
      (CopiedMountain.withCodeFormula_delta0 _ (.existsMem _ (.conj (memPairFormula_delta0 _ _ _) (.conj (memPairFormula_delta0 _ _ _) (rootFormula_delta0 _ _ _ _ _))))))

theorem rowAtomFormula_freeClosed {n : Nat} {C : ExpressionData (Project.Term n)} (hC : C.Closed)
    {I : Input (Project.Term n)} (hI : I.Closed) (k r q p c : Project.Term n)
    (hk : k.freeSupport=[]) (hr : r.freeSupport=[]) (hq : q.freeSupport=[]) (hp : p.freeSupport=[]) (hc : c.freeSupport=[]) :
    (rowAtomFormula C I k r q p c).FreeClosed := by
  have hRoot := rootFormula_freeClosed hC.weaken.weaken.weaken.weaken.weaken I.width.weaken.weaken.weaken.weaken.weaken (.bound 0)
    c.weaken.weaken.weaken.weaken.weaken q.weaken.weaken.weaken.weaken.weaken (by simpa using hI.width) rfl (by simpa using hc) (by simpa using hq)
  simp [rowAtomFormula,CopiedMountain.withCodeFormula,memPairFormula,codeFormula,pairFormula,Project.Formula.forallMem,
    Project.Formula.existsMem,Definitional.Formula.FreeClosed,hI.codes,hI.tower,hI.forests,hk,hr,hp,hc,hRoot]

theorem rowAtomFormula_iff {M : SetTheory.Structure.{u}} (he : Extensional M) {n : Nat} (e : Env M n)
    (C : ExpressionData (Project.Term n)) (I : Input (Project.Term n)) (k r q p c : Project.Term n) :
    Project.Formula.satisfies e (rowAtomFormula C I k r q p c) ↔ RowAtom M (C.eval e) (I.eval e) (k.eval e) (r.eval e) (q.eval e) (p.eval e) (c.eval e) := by
  have hBody (code : M.Domain) : Project.Formula.satisfies (e.push code) (CopiedMountain.withCodeFormula (.bound 0)
      (Project.Formula.existsMem I.forests.weaken.weaken.weaken.weaken
        (.conj (memPairFormula (.bound 1) r.weaken.weaken.weaken.weaken.weaken (.bound 0))
          (.conj (memPairFormula (.bound 0) c.weaken.weaken.weaken.weaken.weaken p.weaken.weaken.weaken.weaken.weaken)
            (rootFormula C.weaken.weaken.weaken.weaken.weaken I.width.weaken.weaken.weaken.weaken.weaken (.bound 0)
              c.weaken.weaken.weaken.weaken.weaken q.weaken.weaken.weaken.weaken.weaken))))) ↔
      ∃heights parents, Codes M code heights parents ∧ ∃F, M.mem F (I.eval e).forests ∧ MemPair M parents (r.eval e) F ∧
        MemPair M F (c.eval e) (p.eval e) ∧ Root M (C.eval e) (I.eval e).width F (c.eval e) (q.eval e) := by
    apply CopiedMountain.withCodeFormula_iff_exists he (e.push code) (.bound 0) _ _
    intro container heights parents
    simp only [Project.Formula.satisfies_existsMem_iff,Project.Formula.satisfies_conj_iff,memPairFormula_iff he,
      rootFormula_iff he,ExpressionData.eval_weaken,Term.eval_weaken]
    rfl
  simp only [rowAtomFormula,Project.Formula.satisfies_existsMem_iff,Project.Formula.satisfies_conj_iff,memPairFormula_iff he,Term.eval_weaken,hBody]
  rfl

theorem RowAtom.bounds_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {I : Input M.Domain} (hI : I.Valid M C) {k r q p c : M.Domain}
    (h : RowAtom M C I k r q p c) : M.mem k I.horizon ∧ M.mem r C.omega ∧ M.mem c I.width ∧ M.mem p I.width ∧ M.mem q I.width ∧
      M.mem p c ∧ (q=p ∨ M.mem q p) := by
  obtain ⟨code,_,hCode,heights,parents,hDecode,F,hF,hRow,hParent,hRoot⟩ := h
  have hX := (hI.values k code hCode).read hM.1 hDecode
  have hForest := hX.forest r F hRow
  have hP : CopiedMountain.ParentAt M ⟨I.width,heights,I.forests,parents⟩ r c p := ⟨F,hF,hRow,hParent⟩
  have hBounds := hP.bounds hM.1 hX
  have hRootP := (root_parent_iff_d hM hC hForest hParent).mp hRoot
  exact ⟨(hI.tower.bounds hM.1 hCode).1,hBounds.1,hBounds.2.1,hBounds.2.2.1,hRoot.1,hBounds.2.2.2,hRootP.2.2.imp_right And.left⟩

theorem RowAtom.unique_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {I : Input M.Domain} (hI : I.Valid M C) {k r q p c q' p' : M.Domain}
    (h : RowAtom M C I k r q p c) (h' : RowAtom M C I k r q' p' c) : q=q' ∧ p=p' := by
  obtain ⟨code,_,hCode,heights,parents,hDecode,F,_,hRow,hParent,hRoot⟩ := h
  obtain ⟨code',_,hCode',heights',parents',hDecode',F',_,hRow',hParent',hRoot'⟩ := h'
  have he := hI.tower.unique k code code' hCode hCode'
  subst code'
  obtain ⟨hh,hp⟩ := codes_injective hM.1 hDecode hDecode'
  subst heights'
  subst parents'
  have hX := (hI.values k code hCode).read hM.1 hDecode
  have hFF := hX.parents.unique r F F' hRow hRow'
  subst F'
  have hForest := hX.forest r F hRow
  exact ⟨root_unique_d hM hC hForest hRoot hRoot',hForest.unique c p p' hParent hParent'⟩

end KP1Y.OneYFinite.CopyDiagram
