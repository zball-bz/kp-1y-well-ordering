import KP1Y.OneYExpansionPrefix
import KP1Y.OneYExpressionDiagramGraph
import KP1Y.OneYCopyTowerCertificates

/-! 实际E×ω→E展开图的Σ₁计算证书。无界运行对象只作为外层Box见证。 -/
namespace KP1Y.OneYFinite.Expansion
open YesMetaZFC YesMetaZFC.SetTheory YesMetaZFC.SetTheory.Definitional
open KP1Y.Kuratowski KP1Y.Functions KP1Y.Naturals KP1Y.Bounded KP1Y.Ranking
open KP1Y.OneYFinite
universe u v

theorem broad_rebuildsFormula_iff {M : SetTheory.Structure.{u}} (he : Extensional M) {n : Nat} (e : Env M n)
    (C : ExpressionData (Project.Term n)) (Pairs Plus : Project.Term n) (X : CopiedMountain.Data (Project.Term n))
    (Top F ForestLists Grids : Project.Term n) {AllForests : M.Domain}
    (hSpaces : MountainReconstruction.Spaces.Valid M (C.eval e) AllForests ⟨ForestLists.eval e,Grids.eval e⟩)
    (hSub : M.MemberSubset (X.eval e).forests AllForests) (hWidth : M.mem (X.eval e).width (C.eval e).omega) :
    Project.Formula.satisfies e (MountainReconstruction.rebuildsFormula C Pairs Plus X Top F ForestLists Grids) ↔
      MountainReconstruction.Rebuilds M (C.eval e) (Pairs.eval e) (Plus.eval e) (X.eval e) (Top.eval e) (F.eval e) := by
  simp only [MountainReconstruction.rebuildsFormula,Project.Formula.satisfies_existsMem_iff,MountainReconstruction.rebuildCertificateFormula_iff he,
    ExpressionData.eval_weaken,CopiedMountain.Data.eval_weaken,Term.eval_weaken]
  constructor
  · rintro ⟨B,_,Parents,_,H,_,hB,hP,hH,hF⟩
    exact ⟨B,Parents,H,hB,hP,hH,hF⟩
  · rintro ⟨B,Parents,H,hB,hP,hH,hF⟩
    exact ⟨B,hB.1.1,Parents,(hSpaces.forestLists Parents).mpr ⟨B,hB.1.1,hP.graph.mono_values hSub⟩,
      H,(hSpaces.grids H).mpr ⟨(X.eval e).width,hWidth,hH.graph⟩,hB,hP,hH,hF⟩

theorem broad_codeStepFormula_iff {M : SetTheory.Structure.{u}} (he : Extensional M) {n : Nat} (e : Env M n)
    (C : ExpressionData (Project.Term n)) (Pairs Plus width Forests Codes G ForestLists Grids i upper lower : Project.Term n)
    {AllForests : M.Domain} (hSpaces : MountainReconstruction.Spaces.Valid M (C.eval e) AllForests ⟨ForestLists.eval e,Grids.eval e⟩)
    (hSub : M.MemberSubset (Forests.eval e) AllForests) (hWidth : M.mem (width.eval e) (C.eval e).omega) :
    Project.Formula.satisfies e (TowerReconstruction.codeStepFormula C Pairs Plus width Forests Codes G ForestLists Grids i upper lower) ↔
      TowerReconstruction.CodeStep M (C.eval e) (Pairs.eval e) (Plus.eval e) (width.eval e) (Forests.eval e) (Codes.eval e) (G.eval e) (i.eval e) (upper.eval e) (lower.eval e) := by
  have hBody (code : M.Domain) : Project.Formula.satisfies (e.push code) (CopiedMountain.withCodeFormula (.bound 0)
      (MountainReconstruction.rebuildsFormula C.weaken.weaken.weaken.weaken Pairs.weaken.weaken.weaken.weaken Plus.weaken.weaken.weaken.weaken
        ⟨width.weaken.weaken.weaken.weaken,.bound 1,Forests.weaken.weaken.weaken.weaken,.bound 0⟩
        upper.weaken.weaken.weaken.weaken lower.weaken.weaken.weaken.weaken ForestLists.weaken.weaken.weaken.weaken Grids.weaken.weaken.weaken.weaken)) ↔
      ∃heights parents, KP1Y.Kuratowski.Codes M code heights parents ∧ MountainReconstruction.Rebuilds M (C.eval e) (Pairs.eval e) (Plus.eval e)
        ⟨width.eval e,heights,Forests.eval e,parents⟩ (upper.eval e) (lower.eval e) := by
    apply CopiedMountain.withCodeFormula_iff_exists he (e.push code) (.bound 0) _ _
    intro container heights parents
    have h := broad_rebuildsFormula_iff he ((((e.push code).push container).push heights).push parents)
      C.weaken.weaken.weaken.weaken Pairs.weaken.weaken.weaken.weaken Plus.weaken.weaken.weaken.weaken
      ⟨width.weaken.weaken.weaken.weaken,.bound 1,Forests.weaken.weaken.weaken.weaken,.bound 0⟩
      upper.weaken.weaken.weaken.weaken lower.weaken.weaken.weaken.weaken ForestLists.weaken.weaken.weaken.weaken Grids.weaken.weaken.weaken.weaken
      (by simpa only [ExpressionData.eval_weaken,CopiedMountain.Data.eval,CopiedMountain.Data.map,Term.eval_weaken] using hSpaces)
      (by simpa only [CopiedMountain.Data.eval,CopiedMountain.Data.map,Term.eval_weaken] using hSub)
      (by simpa only [ExpressionData.eval_weaken,CopiedMountain.Data.eval,CopiedMountain.Data.map,Term.eval_weaken] using hWidth)
    simpa only [ExpressionData.eval_weaken,CopiedMountain.Data.eval,CopiedMountain.Data.map,Term.eval_weaken,
      Project.Term.eval_bound_one_push,Project.Term.eval_bound_zero_push] using h
  simp only [TowerReconstruction.codeStepFormula,Project.Formula.satisfies_existsMem_iff,Project.Formula.satisfies_conj_iff,
    memPairFormula_iff he,Term.eval_weaken,hBody]
  rfl

def towerRunFormula {n : Nat} (C : ExpressionData (Project.Term n))
    (Pairs Plus width Forests Codes G B N Top H ForestLists Grids : Project.Term n) : Project.Formula 1 n :=
  .conj (successorFormula N B) (.conj (graphFormula H N C.sequences)
    (.conj (Project.Formula.forallMem N (Project.Formula.forallMem C.sequences.weaken
      (.imp (memPairFormula H.weaken.weaken (.bound 1) (.bound 0)) (graphFormula (.bound 0) width.weaken.weaken C.omega.weaken.weaken))))
      (.conj (memPairFormula H B Top)
        (Project.Formula.forallMem B (Project.Formula.forallMem N.weaken (Project.Formula.forallMem C.sequences.weaken.weaken
          (Project.Formula.forallMem C.sequences.weaken.weaken.weaken
            (.imp (.conj (successorFormula (.bound 2) (.bound 3))
              (.conj (memPairFormula H.weaken.weaken.weaken.weaken (.bound 2) (.bound 1)) (memPairFormula H.weaken.weaken.weaken.weaken (.bound 3) (.bound 0))))
              (TowerReconstruction.codeStepFormula C.weaken.weaken.weaken.weaken Pairs.weaken.weaken.weaken.weaken Plus.weaken.weaken.weaken.weaken
                width.weaken.weaken.weaken.weaken Forests.weaken.weaken.weaken.weaken Codes.weaken.weaken.weaken.weaken G.weaken.weaken.weaken.weaken
                ForestLists.weaken.weaken.weaken.weaken Grids.weaken.weaken.weaken.weaken (.bound 3) (.bound 1) (.bound 0))))))))))

theorem towerRunFormula_delta0 {n : Nat} (C : ExpressionData (Project.Term n))
    (Pairs Plus width Forests Codes G B N Top H ForestLists Grids : Project.Term n) :
    (towerRunFormula C Pairs Plus width Forests Codes G B N Top H ForestLists Grids).IsDelta0 :=
  .conj (successorFormula_delta0 _ _) (.conj (graphFormula_delta0 _ _ _) (.conj
    (.forallMem _ (.forallMem _ (.imp (memPairFormula_delta0 _ _ _) (graphFormula_delta0 _ _ _))))
    (.conj (memPairFormula_delta0 _ _ _) (.forallMem _ (.forallMem _ (.forallMem _ (.forallMem _
      (.imp (.conj (successorFormula_delta0 _ _) (.conj (memPairFormula_delta0 _ _ _) (memPairFormula_delta0 _ _ _)))
        (TowerReconstruction.codeStepFormula_delta0 _ _ _ _ _ _ _ _ _ _ _ _)))))))))

theorem towerRunFormula_freeClosed {n : Nat} {C : ExpressionData (Project.Term n)} (hC : C.Closed)
    (Pairs Plus width Forests Codes G B N Top H ForestLists Grids : Project.Term n)
    (hPairs : Pairs.freeSupport=[]) (hPlus : Plus.freeSupport=[]) (hWidth : width.freeSupport=[]) (hForests : Forests.freeSupport=[])
    (hCodes : Codes.freeSupport=[]) (hG : G.freeSupport=[]) (hB : B.freeSupport=[]) (hN : N.freeSupport=[])
    (hTop : Top.freeSupport=[]) (hH : H.freeSupport=[]) (hFL : ForestLists.freeSupport=[]) (hGrids : Grids.freeSupport=[]) :
    (towerRunFormula C Pairs Plus width Forests Codes G B N Top H ForestLists Grids).FreeClosed := by
  have hStep := TowerReconstruction.codeStepFormula_freeClosed hC.weaken.weaken.weaken.weaken
    Pairs.weaken.weaken.weaken.weaken Plus.weaken.weaken.weaken.weaken width.weaken.weaken.weaken.weaken Forests.weaken.weaken.weaken.weaken
    Codes.weaken.weaken.weaken.weaken G.weaken.weaken.weaken.weaken ForestLists.weaken.weaken.weaken.weaken Grids.weaken.weaken.weaken.weaken
    (.bound 3) (.bound 1) (.bound 0) (by simpa using hPairs) (by simpa using hPlus) (by simpa using hWidth) (by simpa using hForests)
    (by simpa using hCodes) (by simpa using hG) (by simpa using hFL) (by simpa using hGrids) rfl rfl rfl
  simp [towerRunFormula,successorFormula,graphFormula,memPairFormula,codeFormula,pairFormula,Project.Formula.forallMem,
    Project.Formula.existsMem,Definitional.Formula.FreeClosed,hN,hB,hH,hTop,hWidth,hC.omega,hC.sequences,hStep]

theorem towerRunFormula_iff {M : SetTheory.Structure.{u}} (he : Extensional M) {n : Nat} (e : Env M n)
    (C : ExpressionData (Project.Term n)) (Pairs Plus width Forests Codes G B N Top H ForestLists Grids : Project.Term n)
    {AllForests : M.Domain} (hSpaces : MountainReconstruction.Spaces.Valid M (C.eval e) AllForests ⟨ForestLists.eval e,Grids.eval e⟩)
    (hSub : M.MemberSubset (Forests.eval e) AllForests) (hWidth : M.mem (width.eval e) (C.eval e).omega) :
    Project.Formula.satisfies e (towerRunFormula C Pairs Plus width Forests Codes G B N Top H ForestLists Grids) ↔
      TowerReconstruction.Run M (C.eval e) (Pairs.eval e) (Plus.eval e) (width.eval e) (Forests.eval e) (Codes.eval e) (G.eval e)
        (B.eval e) (N.eval e) (Top.eval e) (H.eval e) := by
  have hStep (i j upper lower : M.Domain) := broad_codeStepFormula_iff he ((((e.push i).push j).push upper).push lower)
    C.weaken.weaken.weaken.weaken Pairs.weaken.weaken.weaken.weaken Plus.weaken.weaken.weaken.weaken width.weaken.weaken.weaken.weaken
    Forests.weaken.weaken.weaken.weaken Codes.weaken.weaken.weaken.weaken G.weaken.weaken.weaken.weaken
    ForestLists.weaken.weaken.weaken.weaken Grids.weaken.weaken.weaken.weaken (.bound 3) (.bound 1) (.bound 0)
    (by simpa only [ExpressionData.eval_weaken,Term.eval_weaken] using hSpaces)
    (by simpa only [Term.eval_weaken] using hSub) (by simpa only [ExpressionData.eval_weaken,Term.eval_weaken] using hWidth)
  simp only [towerRunFormula,Project.Formula.satisfies_conj_iff,successorFormula_iff he,graphFormula_iff he,
    Project.Formula.satisfies_forallMem_iff,Project.Formula.satisfies_imp_iff,memPairFormula_iff he,Term.eval_weaken,hStep,
    ExpressionData.eval_weaken]
  constructor
  · rintro ⟨hN,hH,hValues,hTop,hSteps⟩
    exact ⟨hN,hH,fun i F hAt => hValues i (hH.bounds he hAt).1 F (hH.bounds he hAt).2 hAt,hTop,
      fun i hi j hs upper lower hU hL => hSteps i hi j (hH.bounds he hU).1 upper (hH.bounds he hU).2 lower (hH.bounds he hL).2 ⟨hs,hU,hL⟩⟩
  · intro h
    exact ⟨h.length,h.graph,fun i _ F _ hAt => h.values i F hAt,h.top,
      fun i hi j _ upper _ lower _ hs => h.transition i hi j hs.1 upper lower hs.2.1 hs.2.2⟩

def horizonFormula {n : Nat} (C : ExpressionData (Project.Term n)) (s m horizon : Project.Term n) : Project.Formula 1 n :=
  Project.Formula.existsMem C.omega (.conj (sequenceBoundFormula C.omega.weaken C.zero.weaken m.weaken s.weaken (.bound 0))
    (successorFormula (.bound 0) horizon.weaken))

theorem horizonFormula_delta0 {n : Nat} (C : ExpressionData (Project.Term n)) (s m horizon : Project.Term n) :
    (horizonFormula C s m horizon).IsDelta0 := .existsMem _ (.conj (sequenceBoundFormula_delta0 _ _ _ _ _) (successorFormula_delta0 _ _))

theorem horizonFormula_freeClosed {n : Nat} {C : ExpressionData (Project.Term n)} (hC : C.Closed)
    (s m horizon : Project.Term n) (hs : s.freeSupport=[]) (hm : m.freeSupport=[]) (hh : horizon.freeSupport=[]) :
    (horizonFormula C s m horizon).FreeClosed := by
  have h := sequenceBoundFormula_freeClosed C.omega.weaken C.zero.weaken m.weaken s.weaken (.bound 0)
    (by simpa using hC.omega) (by simpa using hC.zero) (by simpa using hm) (by simpa using hs) rfl
  simp [horizonFormula,successorFormula,Project.Formula.existsMem,Project.Formula.forallMem,Definitional.Formula.FreeClosed,hC.omega,hh,h]

theorem horizonFormula_iff {M : SetTheory.Structure.{u}} (he : Extensional M) {n : Nat} (e : Env M n)
    (C : ExpressionData (Project.Term n)) (s m horizon : Project.Term n) :
    Project.Formula.satisfies e (horizonFormula C s m horizon) ↔ Horizon M (C.eval e) (s.eval e) (m.eval e) (horizon.eval e) := by
  have hBound (strict : M.Domain) : Project.Formula.satisfies (e.push strict)
      (sequenceBoundFormula C.omega.weaken C.zero.weaken m.weaken s.weaken (.bound 0)) ↔
      SequenceBound M (C.eval e) (m.eval e) (s.eval e) strict := by
    simpa only [ExpressionData.eval,ExpressionData.weaken,ExpressionData.map,Term.eval_weaken,Project.Term.eval_bound_zero_push] using
      sequenceBoundFormula_iff he (e.push strict) C.weaken m.weaken s.weaken (.bound 0)
  simp only [horizonFormula,Project.Formula.satisfies_existsMem_iff,Project.Formula.satisfies_conj_iff,
    hBound,successorFormula_iff he,Term.eval_weaken]
  rfl

def allOneFormula {n : Nat} (C : ExpressionData (Project.Term n)) (width Top : Project.Term n) : Project.Formula 1 n :=
  .conj (graphFormula Top width C.omega) (Project.Formula.forallMem width (memPairFormula Top.weaken (.bound 0) C.one.weaken))

theorem allOneFormula_delta0 {n : Nat} (C : ExpressionData (Project.Term n)) (width Top : Project.Term n) :
    (allOneFormula C width Top).IsDelta0 := .conj (graphFormula_delta0 _ _ _) (.forallMem _ (memPairFormula_delta0 _ _ _))

theorem allOneFormula_freeClosed {n : Nat} {C : ExpressionData (Project.Term n)} (hC : C.Closed)
    (width Top : Project.Term n) (hw : width.freeSupport=[]) (hTop : Top.freeSupport=[]) : (allOneFormula C width Top).FreeClosed := by
  simp [allOneFormula,graphFormula,memPairFormula,codeFormula,pairFormula,Project.Formula.forallMem,Project.Formula.existsMem,
    Definitional.Formula.FreeClosed,hC.omega,hC.one,hw,hTop]

theorem allOneFormula_iff {M : SetTheory.Structure.{u}} (he : Extensional M) {n : Nat} (e : Env M n)
    (C : ExpressionData (Project.Term n)) (width Top : Project.Term n) :
    Project.Formula.satisfies e (allOneFormula C width Top) ↔ TowerReconstruction.AllOne M (C.eval e) (width.eval e) (Top.eval e) := by
  simp only [allOneFormula,Project.Formula.satisfies_conj_iff,graphFormula_iff he,Project.Formula.satisfies_forallMem_iff,memPairFormula_iff he,Term.eval_weaken]
  constructor
  · rintro ⟨hG,hRows⟩
    refine ⟨hG,fun c v => ?_⟩
    exact ⟨fun h => ⟨(hG.bounds he h).1,hG.unique c v (C.eval e).one h (hRows c (hG.bounds he h).1)⟩,
      fun h => h.2.symm ▸ hRows c h.1⟩
  · exact fun h => ⟨h.1,fun c hc => (h.2 c (C.eval e).one).mpr ⟨hc,rfl⟩⟩

def assemblyFormula {n : Nat} (C : ExpressionData (Project.Term n))
    (Pairs Plus width Forests Codes G B Top F ForestLists Grids : Project.Term n) : Project.Formula 1 n :=
  Project.Formula.existsMem C.omega (Project.Formula.existsMem Grids.weaken
    (.conj (towerRunFormula C.weaken.weaken Pairs.weaken.weaken Plus.weaken.weaken width.weaken.weaken Forests.weaken.weaken Codes.weaken.weaken G.weaken.weaken
      B.weaken.weaken (.bound 1) Top.weaken.weaken (.bound 0) ForestLists.weaken.weaken Grids.weaken.weaken)
      (memPairFormula (.bound 0) C.zero.weaken.weaken F.weaken.weaken)))

theorem assemblyFormula_delta0 {n : Nat} (C : ExpressionData (Project.Term n))
    (Pairs Plus width Forests Codes G B Top F ForestLists Grids : Project.Term n) :
    (assemblyFormula C Pairs Plus width Forests Codes G B Top F ForestLists Grids).IsDelta0 :=
  .existsMem _ (.existsMem _ (.conj (towerRunFormula_delta0 _ _ _ _ _ _ _ _ _ _ _ _ _) (memPairFormula_delta0 _ _ _)))

theorem assemblyFormula_freeClosed {n : Nat} {C : ExpressionData (Project.Term n)} (hC : C.Closed)
    (Pairs Plus width Forests Codes G B Top F ForestLists Grids : Project.Term n)
    (hPairs : Pairs.freeSupport=[]) (hPlus : Plus.freeSupport=[]) (hWidth : width.freeSupport=[]) (hForests : Forests.freeSupport=[])
    (hCodes : Codes.freeSupport=[]) (hG : G.freeSupport=[]) (hB : B.freeSupport=[])
    (hTop : Top.freeSupport=[]) (hF : F.freeSupport=[]) (hFL : ForestLists.freeSupport=[]) (hGrids : Grids.freeSupport=[]) :
    (assemblyFormula C Pairs Plus width Forests Codes G B Top F ForestLists Grids).FreeClosed := by
  have hRun := towerRunFormula_freeClosed hC.weaken.weaken Pairs.weaken.weaken Plus.weaken.weaken width.weaken.weaken Forests.weaken.weaken Codes.weaken.weaken G.weaken.weaken
    B.weaken.weaken (.bound 1) Top.weaken.weaken (.bound 0) ForestLists.weaken.weaken Grids.weaken.weaken
    (by simpa using hPairs) (by simpa using hPlus) (by simpa using hWidth) (by simpa using hForests) (by simpa using hCodes)
    (by simpa using hG) (by simpa using hB) rfl (by simpa using hTop) rfl (by simpa using hFL) (by simpa using hGrids)
  simp [assemblyFormula,memPairFormula,codeFormula,pairFormula,Project.Formula.existsMem,Project.Formula.forallMem,
    Definitional.Formula.FreeClosed,hC.omega,hC.zero,hGrids,hF,hRun]

theorem assemblyFormula_iff {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory) {n : Nat} (e : Env M n)
    (C : ExpressionData (Project.Term n)) (Pairs Plus width Forests Codes G B Top F ForestLists Grids : Project.Term n)
    (hC : (C.eval e).Valid M) {AllForests : M.Domain}
    (hSpaces : MountainReconstruction.Spaces.Valid M (C.eval e) AllForests ⟨ForestLists.eval e,Grids.eval e⟩)
    (hSub : M.MemberSubset (Forests.eval e) AllForests) (hWidth : M.mem (width.eval e) (C.eval e).omega) (hB : M.mem (B.eval e) (C.eval e).omega) :
    Project.Formula.satisfies e (assemblyFormula C Pairs Plus width Forests Codes G B Top F ForestLists Grids) ↔
      TowerReconstruction.Assembles M (C.eval e) (Pairs.eval e) (Plus.eval e) (width.eval e) (Forests.eval e) (Codes.eval e) (G.eval e) (B.eval e) (Top.eval e) (F.eval e) := by
  have hRun (N H : M.Domain) := towerRunFormula_iff hM.1 ((e.push N).push H) C.weaken.weaken Pairs.weaken.weaken Plus.weaken.weaken width.weaken.weaken
    Forests.weaken.weaken Codes.weaken.weaken G.weaken.weaken B.weaken.weaken (.bound 1) Top.weaken.weaken (.bound 0) ForestLists.weaken.weaken Grids.weaken.weaken
    (by simpa only [ExpressionData.eval_weaken,Term.eval_weaken] using hSpaces) (by simpa only [Term.eval_weaken] using hSub)
    (by simpa only [ExpressionData.eval_weaken,Term.eval_weaken] using hWidth)
  simp only [assemblyFormula,Project.Formula.satisfies_existsMem_iff,Project.Formula.satisfies_conj_iff,memPairFormula_iff hM.1,
    hRun,ExpressionData.eval_weaken,Term.eval_weaken]
  constructor
  · rintro ⟨N,_,H,_,hRun,hAt⟩
    exact ⟨N,H,hRun,hAt⟩
  · rintro ⟨N,H,hRun,hAt⟩
    have hN := natural_successor_mem_d hM hC hB hRun.length
    exact ⟨N,hN,H,(hSpaces.grids H).mpr ⟨N,hN,hRun.graph⟩,hRun,hAt⟩

structure LayerData (α : Type u) where
  linear : α
  initial : α
  rowValues : α
  rowForests : α
  rowStates : α
  layerStates : α
  layers : α
  step : α
  stepBound : α
  histories : α
  runs : α

def LayerData.map {α : Type u} {β : Type v} (W : LayerData α) (f : α → β) : LayerData β :=
  ⟨f W.linear,f W.initial,f W.rowValues,f W.rowForests,f W.rowStates,f W.layerStates,f W.layers,f W.step,f W.stepBound,f W.histories,f W.runs⟩
def LayerData.eval {M : SetTheory.Structure.{u}} {n : Nat} (W : LayerData (Project.Term n)) (e : Env M n) : LayerData M.Domain := W.map (fun t => t.eval e)
def LayerData.weaken {n : Nat} (W : LayerData (Project.Term n)) : LayerData (Project.Term (n+1)) := W.map (fun t => t.weaken)
def LayerData.rows {α : Type u} (W : LayerData α) : RowStateSpace α := ⟨W.rowValues,W.rowForests,W.rowStates⟩
def LayerData.space {α : Type u} (W : LayerData α) : LayerStateSpace α := ⟨W.rows,W.layerStates⟩

theorem LayerData.eval_weaken {M : SetTheory.Structure.{u}} {n : Nat} (W : LayerData (Project.Term n)) (e : Env M n) (a : M.Domain) :
    W.weaken.eval (e.push a)=W.eval e := by
  cases W
  simp [LayerData.weaken,LayerData.eval,LayerData.map,Term.eval_weaken]

structure LayerData.Closed {n : Nat} (W : LayerData (Project.Term n)) : Prop where
  linear : W.linear.freeSupport=[]
  initial : W.initial.freeSupport=[]
  rowValues : W.rowValues.freeSupport=[]
  rowForests : W.rowForests.freeSupport=[]
  rowStates : W.rowStates.freeSupport=[]
  layerStates : W.layerStates.freeSupport=[]
  layers : W.layers.freeSupport=[]
  step : W.step.freeSupport=[]
  stepBound : W.stepBound.freeSupport=[]
  histories : W.histories.freeSupport=[]
  runs : W.runs.freeSupport=[]

theorem LayerData.Closed.rows {n : Nat} {W : LayerData (Project.Term n)} (h : W.Closed) : W.rows.Closed := ⟨h.rowValues,h.rowForests,h.rowStates⟩

structure LayerCalculation (M : SetTheory.Structure.{u}) (C : ExpressionData M.Domain) (T : MatrixArithmetic M.Domain)
    (Forests s m B : M.Domain) (W : LayerData M.Domain) : Prop where
  legal : LegalAt M C.omega C.zero C.one s m
  bound : M.mem B C.omega
  linear : LinearForest M C.omega m W.linear
  selected : Selects true M C m W.linear s W.initial
  space : ExpressionDiagram.LayerSpaceCertificate M C Forests m W.space
  base : RootedRow M C m s W.initial
  step : SigmaGraphCertificate extractionStepMatrix (extractionStepEnv C m W.rows T.diffPairs T.difference) W.step W.layerStates W.layerStates W.stepBound
  run : ExpressionDiagram.RunAlong M C.omega C.zero W.layerStates W.step s W.initial W.layers
  family : ExpressionDiagram.RowFamily M C m W.space W.layers B W.histories W.runs

theorem LayerCalculation.layer_run_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {Forests s m B : M.Domain} {W : LayerData M.Domain} (hForests : ExpressionDiagram.AllForests M C.omega Forests)
    (h : LayerCalculation M C T Forests s m B W) : LayerRun M C m W.space s W.initial W.layers :=
  (ExpressionDiagram.run_along_iff_layer_run_d hM hC ((ExpressionDiagram.layer_space_certificate_iff hC hForests).mp h.space) hT.diff h.step h.base).mp h.run

theorem layer_calculation_exists_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {Forests s m B F P H : M.Domain} {L : LayerStateSpace M.Domain} (hForests : ExpressionDiagram.AllForests M C.omega Forests)
    (hLegal : LegalAt M C.omega C.zero C.one s m) (hB : M.mem B C.omega)
    (hF : LinearForest M C.omega m F) (hP : Selects true M C m F s P) (hRun : LayerRun M C m L s P H) :
    ∃W : LayerData M.Domain, W.linear=F ∧ W.initial=P ∧ W.space=L ∧ W.layers=H ∧ LayerCalculation M C T Forests s m B W := by
  obtain ⟨Step,Bound,hStep⟩ := ExpressionDiagram.layer_step_certificate_exists_d hM hC hRun.space hT.diff
  obtain ⟨Histories,Runs,hFamily⟩ := ExpressionDiagram.row_family_exists_d hM hC hRun hB
  refine ⟨⟨F,P,L.rows.values,L.rows.forests,L.rows.states,L.states,H,Step,Bound,Histories,Runs⟩,rfl,rfl,rfl,rfl,
    hLegal,hB,hF,hP,(ExpressionDiagram.layer_space_certificate_iff hC hForests).mpr hRun.space,hRun.base,hStep,?_,hFamily⟩
  exact (ExpressionDiagram.run_along_iff_layer_run_d hM hC hRun.space hT.diff hStep hRun.base).mpr hRun

def layerCalculationFormula {n : Nat} (C : ExpressionData (Project.Term n)) (T : MatrixArithmetic (Project.Term n))
    (Forests s m B : Project.Term n) (W : LayerData (Project.Term n)) : Project.Formula 1 n :=
  .conj (legalAtFormula C.omega C.zero C.one s m) (.conj (.mem B C.omega)
    (.conj (ExpressionDiagram.linearForestFormula C.omega m W.linear) (.conj (selectsFormula true C m W.linear s W.initial)
      (.conj (ExpressionDiagram.layerSpaceCertificateFormula C Forests m W.rows W.layerStates) (.conj (rootedRowFormula C m s W.initial)
        (.conj (ExpressionDiagram.stepCertificateFormula C m W.rows T.diffPairs T.difference W.step W.layerStates W.stepBound)
          (.conj (ExpressionDiagram.runAlongFormula C.omega C.zero W.layerStates W.step s W.initial W.layers)
            (ExpressionDiagram.rowFamilyFormula C m W.rows W.layerStates W.layers B W.histories W.runs T.diffPairs T.difference))))))))

theorem layerCalculationFormula_delta0 {n : Nat} (C : ExpressionData (Project.Term n)) (T : MatrixArithmetic (Project.Term n))
    (Forests s m B : Project.Term n) (W : LayerData (Project.Term n)) : (layerCalculationFormula C T Forests s m B W).IsDelta0 :=
  .conj (legalAtFormula_delta0 _ _ _ _ _) (.conj (.mem _ _) (.conj (ExpressionDiagram.linearForestFormula_delta0 _ _ _)
    (.conj (selectsFormula_delta0 _ _ _ _ _ _) (.conj (ExpressionDiagram.layerSpaceCertificateFormula_delta0 _ _ _ _ _)
      (.conj (rootedRowFormula_delta0 _ _ _ _) (.conj (ExpressionDiagram.stepCertificateFormula_delta0 _ _ _ _ _ _ _ _)
        (.conj (ExpressionDiagram.runAlongFormula_delta0 _ _ _ _ _ _ _) (ExpressionDiagram.rowFamilyFormula_delta0 _ _ _ _ _ _ _ _ _ _))))))))

theorem layerCalculationFormula_freeClosed {n : Nat} {C : ExpressionData (Project.Term n)} (hC : C.Closed)
    {T : MatrixArithmetic (Project.Term n)} (hT : CopyCoordinates.ArithmeticClosed T) {W : LayerData (Project.Term n)} (hW : W.Closed)
    (Forests s m B : Project.Term n) (hForests : Forests.freeSupport=[]) (hs : s.freeSupport=[]) (hm : m.freeSupport=[]) (hB : B.freeSupport=[]) :
    (layerCalculationFormula C T Forests s m B W).FreeClosed := by
  have hLegal := legalAtFormula_freeClosed C.omega C.zero C.one s m hC.omega hC.zero hC.one hs hm
  have hLinear := ExpressionDiagram.linearForestFormula_freeClosed C.omega m W.linear hC.omega hm hW.linear
  have hSelect := selectsFormula_freeClosed true hC m W.linear s W.initial hm hW.linear hs hW.initial
  have hSpace := ExpressionDiagram.layerSpaceCertificateFormula_freeClosed hC hW.rows Forests m W.layerStates hForests hm hW.layerStates
  have hBase := rootedRowFormula_freeClosed hC m s W.initial hm hs hW.initial
  have hStep := ExpressionDiagram.stepCertificateFormula_freeClosed hC hW.rows m T.diffPairs T.difference W.step W.layerStates W.stepBound hm hT.diffPairs hT.difference hW.step hW.layerStates hW.stepBound
  have hRun := ExpressionDiagram.runAlongFormula_freeClosed C.omega C.zero W.layerStates W.step s W.initial W.layers hC.omega hC.zero hW.layerStates hW.step hs hW.initial hW.layers
  have hFamily := ExpressionDiagram.rowFamilyFormula_freeClosed hC hW.rows m W.layerStates W.layers B W.histories W.runs T.diffPairs T.difference
    hm hW.layerStates hW.layers hB hW.histories hW.runs hT.diffPairs hT.difference
  simp [layerCalculationFormula,Definitional.Formula.FreeClosed,hLegal,hLinear,hSelect,hSpace,hBase,hStep,hRun,hFamily,hB,hC.omega]

theorem layerCalculationFormula_iff {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory) {n : Nat} (e : Env M n)
    (C : ExpressionData (Project.Term n)) (T : MatrixArithmetic (Project.Term n)) (Forests s m B : Project.Term n) (W : LayerData (Project.Term n))
    (hC : (C.eval e).Valid M) (hT : (T.eval e).Valid M (C.eval e)) (hForests : ExpressionDiagram.AllForests M (C.eval e).omega (Forests.eval e)) :
    Project.Formula.satisfies e (layerCalculationFormula C T Forests s m B W) ↔ LayerCalculation M (C.eval e) (T.eval e) (Forests.eval e) (s.eval e) (m.eval e) (B.eval e) (W.eval e) := by
  have hLinear := ExpressionDiagram.linearForestFormula_iff hM e C.omega m W.linear hC.omega
  simp only [layerCalculationFormula,Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_mem_iff,legalAtFormula_iff hM.1,hLinear,
    selectsFormula_iff hM.1,ExpressionDiagram.layerSpaceCertificateFormula_iff hM,rootedRowFormula_iff hM.1,
    ExpressionDiagram.stepCertificateFormula_iff hM.1,ExpressionDiagram.runAlongFormula_iff hM.1]
  constructor
  · rintro ⟨hLegal,hB,hF,hP,hSpace,hBase,hStep,hRun,hFamily⟩
    have hL := (ExpressionDiagram.layer_space_certificate_iff hC hForests).mp hSpace
    have hLayers := (ExpressionDiagram.run_along_iff_layer_run_d hM hC hL hT.diff hStep hBase).mp hRun
    have hFamily' := (ExpressionDiagram.rowFamilyFormula_iff hM e C m W.rows W.layerStates W.layers B W.histories W.runs T.diffPairs T.difference
      hC hL.rows hT.diff (fun _ _ _ hAt => hLayers.at_rooted hM.1 hAt)).mp hFamily
    exact ⟨hLegal,hB,hF,hP,hSpace,hBase,hStep,hRun,hFamily'⟩
  · intro h
    have hL := (ExpressionDiagram.layer_space_certificate_iff hC hForests).mp h.space
    have hLayers := h.layer_run_d hM hC hT hForests
    refine ⟨h.legal,h.bound,h.linear,h.selected,h.space,h.base,h.step,h.run,?_⟩
    exact (ExpressionDiagram.rowFamilyFormula_iff hM e C m W.rows W.layerStates W.layers B W.histories W.runs T.diffPairs T.difference
      hC hL.rows hT.diff (fun _ _ _ hAt => hLayers.at_rooted hM.1 hAt)).mpr h.family

def coordinatesFormula {n : Nat} (C : ExpressionData (Project.Term n)) (T : MatrixArithmetic (Project.Term n))
    (A : CopyCoordinates.Context (Project.Term n)) : Project.Formula 1 n :=
  .conj (.mem A.last C.omega) (.conj (.mem A.root C.omega) (.conj (.mem A.root A.last)
    (.conj (CopyCoordinates.differenceReadFormula T A.last A.root A.length) (successorFormula A.first A.root))))

theorem coordinatesFormula_delta0 {n : Nat} (C : ExpressionData (Project.Term n)) (T : MatrixArithmetic (Project.Term n))
    (A : CopyCoordinates.Context (Project.Term n)) : (coordinatesFormula C T A).IsDelta0 :=
  .conj (.mem _ _) (.conj (.mem _ _) (.conj (.mem _ _) (.conj (CopyCoordinates.differenceReadFormula_delta0 _ _ _ _) (successorFormula_delta0 _ _))))

theorem coordinatesFormula_freeClosed {n : Nat} {C : ExpressionData (Project.Term n)} (hC : C.Closed)
    {T : MatrixArithmetic (Project.Term n)} (hT : CopyCoordinates.ArithmeticClosed T)
    {A : CopyCoordinates.Context (Project.Term n)} (hA : A.Closed) : (coordinatesFormula C T A).FreeClosed := by
  simp [coordinatesFormula,CopyCoordinates.differenceReadFormula,addAtFormula,successorFormula,memPairFormula,codeFormula,pairFormula,
    Project.Formula.forallMem,Project.Formula.existsMem,Definitional.Formula.FreeClosed,hC.omega,hT.diffPairs,hT.difference,hA.last,hA.root,hA.length,hA.first]

theorem coordinatesFormula_iff {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory) {n : Nat} (e : Env M n)
    (C : ExpressionData (Project.Term n)) (T : MatrixArithmetic (Project.Term n)) (A : CopyCoordinates.Context (Project.Term n))
    (hT : (T.eval e).Valid M (C.eval e)) : Project.Formula.satisfies e (coordinatesFormula C T A) ↔ (A.eval e).Valid M (C.eval e) := by
  simp only [coordinatesFormula,Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_mem_iff,
    CopyCoordinates.differenceReadFormula_iff hM.1,successorFormula_iff hM.1]
  exact ⟨fun h => ⟨h.1,h.2.1,h.2.2.1,(CopyCoordinates.difference_read_iff_d hM hT h.1 h.2.1).mp h.2.2.2.1,h.2.2.2.2⟩,
    fun h => ⟨h.last,h.root,h.below,(CopyCoordinates.difference_read_iff_d hM hT h.last h.root).mpr h.difference,h.first⟩⟩

def forestSpaceFormula {n : Nat} (w AllForests width Forests : Project.Term n) : Project.Formula 1 n :=
  .conj (Project.Formula.forallMem Forests (.mem (.bound 0) AllForests.weaken))
    (Project.Formula.forallMem AllForests (.iff (.mem (.bound 0) Forests.weaken) (forestFormula w.weaken width.weaken (.bound 0))))

theorem forestSpaceFormula_delta0 {n : Nat} (w AllForests width Forests : Project.Term n) : (forestSpaceFormula w AllForests width Forests).IsDelta0 :=
  .conj (.forallMem _ (.mem _ _)) (.forallMem _ (.iff (.mem _ _) (forestFormula_delta0 _ _ _)))

theorem forestSpaceFormula_freeClosed {n : Nat} (w AllForests width Forests : Project.Term n)
    (hw : w.freeSupport=[]) (hA : AllForests.freeSupport=[]) (hn : width.freeSupport=[]) (hF : Forests.freeSupport=[]) :
    (forestSpaceFormula w AllForests width Forests).FreeClosed := by
  simp [forestSpaceFormula,forestFormula,memPairFormula,codeFormula,pairFormula,Project.Formula.forallMem,Project.Formula.existsMem,
    Definitional.Formula.FreeClosed,hw,hA,hn,hF]

theorem forestSpaceFormula_iff {M : SetTheory.Structure.{u}} (he : Extensional M) {n : Nat} (e : Env M n)
    (w AllForests width Forests : Project.Term n) (hA : ExpressionDiagram.AllForests M (w.eval e) (AllForests.eval e)) :
    Project.Formula.satisfies e (forestSpaceFormula w AllForests width Forests) ↔ ∀F, M.mem F (Forests.eval e) ↔ Forest M (w.eval e) (width.eval e) F := by
  simp only [forestSpaceFormula,Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_forallMem_iff,
    Project.Formula.satisfies_iff_iff,Project.Formula.satisfies_mem_iff,forestFormula_iff he,Term.eval_weaken]
  exact ⟨fun h F => ⟨fun hF => (h.2 F (h.1 F hF)).mp hF,fun hF => (h.2 F ((hA F).mpr ⟨width.eval e,hF.width,hF⟩)).mpr hF⟩,
    fun h => ⟨fun F hF => (hA F).mpr ⟨width.eval e,((h F).mp hF).width,(h F).mp hF⟩,fun F _ => h F⟩⟩

theorem bad_in_horizon_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {m : M.Domain} {L : LayerStateSpace M.Domain} {s P H K level last root B : M.Domain}
    (hLayers : LayerRun M C m L s P H) (hBad : BadAt M C m L H K level last root) (hB : Horizon M C s m B) : M.mem K B := by
  obtain ⟨v,_,hValue,hAbove⟩ := hBad.layer_value_d hM hC
  have hc := (hValue.bounds hM.1 hLayers.space).1
  obtain ⟨a,_,hOriginal⟩ := hLayers.base.row.values.total last hc
  have hKa := hLayers.above_one_layer_lt_initial_d hM hC (hBad.layer_natural hM.1 hLayers) hValue hOriginal hAbove
  rcases (hB.maximum_d hM hC hLayers.base.row.values ⟨last,hc⟩).2 last a hOriginal with he | haB
  · exact he ▸ hKa
  · exact ((omega_isOrdinal_d hM hC.omega).mem (hB.natural_d hM hC)).transitive a haB K hKa

def badFormula {n : Nat} (C : ExpressionData (Project.Term n)) (W : LayerData (Project.Term n))
    (K level last root : Project.Term n) : Project.Formula 1 n :=
  Project.Formula.existsMem W.histories (.conj (memPairFormula W.runs.weaken K.weaken (.bound 0))
    (rowBadAtFormula C.weaken W.rows.weaken (.bound 0) level.weaken last.weaken root.weaken))

theorem badFormula_delta0 {n : Nat} (C : ExpressionData (Project.Term n)) (W : LayerData (Project.Term n))
    (K level last root : Project.Term n) : (badFormula C W K level last root).IsDelta0 :=
  .existsMem _ (.conj (memPairFormula_delta0 _ _ _) (rowBadAtFormula_delta0 _ _ _ _ _ _))

theorem badFormula_freeClosed {n : Nat} {C : ExpressionData (Project.Term n)} (hC : C.Closed)
    {W : LayerData (Project.Term n)} (hW : W.Closed) (K level last root : Project.Term n)
    (hK : K.freeSupport=[]) (hd : level.freeSupport=[]) (hx : last.freeSupport=[]) (hy : root.freeSupport=[]) : (badFormula C W K level last root).FreeClosed := by
  have hBad := rowBadAtFormula_freeClosed hC.weaken hW.rows.weaken (.bound 0) level.weaken last.weaken root.weaken rfl
    (by simpa using hd) (by simpa using hx) (by simpa using hy)
  simp [badFormula,memPairFormula,codeFormula,pairFormula,Project.Formula.forallMem,Project.Formula.existsMem,
    Definitional.Formula.FreeClosed,hW.histories,hW.runs,hK,hBad]

theorem badFormula_iff {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory) {n : Nat} (e : Env M n)
    (C : ExpressionData (Project.Term n)) (W : LayerData (Project.Term n)) (K level last root : Project.Term n)
    (hC : (C.eval e).Valid M) {s P m B : M.Domain}
    (hLayers : LayerRun M (C.eval e) m (W.eval e).space s P (W.layers.eval e))
    (hFamily : ExpressionDiagram.RowFamily M (C.eval e) m (W.eval e).space (W.layers.eval e) B (W.histories.eval e) (W.runs.eval e)) :
    Project.Formula.satisfies e (badFormula C W K level last root) ↔ M.mem (K.eval e) B ∧
      BadAt M (C.eval e) m (W.eval e).space (W.layers.eval e) (K.eval e) (level.eval e) (last.eval e) (root.eval e) := by
  simp only [badFormula,Project.Formula.satisfies_existsMem_iff,Project.Formula.satisfies_conj_iff,memPairFormula_iff hM.1,
    rowBadAtFormula_iff hM.1,ExpressionData.eval_weaken,RowStateSpace.eval_weaken,Term.eval_weaken]
  constructor
  · rintro ⟨J,_,hAt,hBad⟩
    obtain ⟨U,Q,hLayer,hRun⟩ := hFamily.rows (K.eval e) J hAt
    exact ⟨(hFamily.graph.bounds hM.1 hAt).1,U,(hRun.space.values U).mpr hRun.base.values,Q,(hRun.space.forests Q).mpr hRun.base.forest,hLayer,J,hRun,hBad⟩
  · rintro ⟨hk,hBad⟩
    obtain ⟨J,U,Q,hJ,hAt,hLayer,hRun⟩ := hFamily.at_d hk
    exact ⟨J,hJ,hAt,hBad.in_run_d hM hC hLayers hLayer hRun⟩

structure ExecutionData (α : Type u) where
  layer : LayerData α
  last : α
  K : α
  level : α
  root : α
  horizon : α
  coordinates : CopyCoordinates.Context α
  width : α
  forests : α
  sources : α
  sourceMap : α
  codes : α
  tower : α
  top : α

def ExecutionData.map {α : Type u} {β : Type v} (W : ExecutionData α) (f : α → β) : ExecutionData β :=
  ⟨W.layer.map f,f W.last,f W.K,f W.level,f W.root,f W.horizon,W.coordinates.map f,f W.width,f W.forests,f W.sources,f W.sourceMap,f W.codes,f W.tower,f W.top⟩
def ExecutionData.eval {M : SetTheory.Structure.{u}} {n : Nat} (W : ExecutionData (Project.Term n)) (e : Env M n) : ExecutionData M.Domain := W.map (fun t => t.eval e)
def ExecutionData.success {α : Type u} (W : ExecutionData α) : SuccessData α :=
  ⟨W.layer.linear,W.layer.initial,W.layer.space,W.layer.layers,W.K,W.level,W.root,W.horizon,W.coordinates,W.width,W.forests,W.codes,W.tower,W.top⟩

structure ExecutionData.Closed {n : Nat} (W : ExecutionData (Project.Term n)) : Prop where
  layer : W.layer.Closed
  last : W.last.freeSupport=[]
  K : W.K.freeSupport=[]
  level : W.level.freeSupport=[]
  root : W.root.freeSupport=[]
  horizon : W.horizon.freeSupport=[]
  coordinates : W.coordinates.Closed
  width : W.width.freeSupport=[]
  forests : W.forests.freeSupport=[]
  sources : W.sources.freeSupport=[]
  sourceMap : W.sourceMap.freeSupport=[]
  codes : W.codes.freeSupport=[]
  tower : W.tower.freeSupport=[]
  top : W.top.freeSupport=[]

structure CompleteCalculation (M : SetTheory.Structure.{u}) (C : ExpressionData M.Domain) (T : MatrixArithmetic M.Domain)
    (AllForests s m N t : M.Domain) (W : ExecutionData M.Domain) : Prop where
  last_nat : M.mem W.last C.omega
  last_succ : M.SuccessorOf m W.last
  layer : LayerCalculation M C T AllForests s m W.horizon W.layer
  horizon : Horizon M C s m W.horizon
  bad : M.mem W.K W.horizon ∧ BadAt M C m W.layer.space W.layer.layers W.K W.level W.last W.root
  last : W.coordinates.last=W.last
  root : W.coordinates.root=W.root
  coordinates : W.coordinates.Valid M C
  width_nat : M.mem W.width C.omega
  width : CopyCoordinates.Width M C T W.coordinates N W.width
  forests : ∀F, M.mem F W.forests ↔ Forest M C.omega W.width F
  source : CopyTower.SourceGraph M C m W.layer.space W.layer.layers W.horizon W.sources W.sourceMap
  tower : CopyTower.Tower M C T W.coordinates m W.layer.space W.layer.layers W.K W.level W.horizon W.width W.forests W.codes W.tower
  top : TowerReconstruction.AllOne M C W.width W.top
  assembly : TowerReconstruction.Assembles M C T.addPairs T.plus W.width W.forests W.codes W.tower W.horizon W.top t

theorem CompleteCalculation.successful_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {AllForests s m N t : M.Domain} (hForests : ExpressionDiagram.AllForests M C.omega AllForests)
    {W : ExecutionData M.Domain} (h : CompleteCalculation M C T AllForests s m N t W) : Successful M C T s m W.last N t W.success :=
  ⟨h.layer.linear,h.layer.selected,h.layer.layer_run_d hM hC hT hForests,h.bad.2,h.horizon,h.last,h.root,h.coordinates,h.width,h.tower,h.top,h.assembly⟩

theorem complete_calculation_exists_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {AllForests s m last N t : M.Domain} (hForests : ExpressionDiagram.AllForests M C.omega AllForests)
    (hLegal : LegalAt M C.omega C.zero C.one s m) (hLast : M.SuccessorOf m last) (h : SuccessAt M C T s m last N t) :
    ∃W : ExecutionData M.Domain, CompleteCalculation M C T AllForests s m N t W := by
  obtain ⟨W,hW⟩ := h
  have hB := hW.horizon.natural_d hM hC
  obtain ⟨LD,_,_,hSpace,hLayers,hLD⟩ := layer_calculation_exists_d hM hC hT hForests hLegal hB hW.linear hW.selected hW.run
  have hRun := hLD.layer_run_d hM hC hT hForests
  obtain ⟨Sources,SourceMap,hSources⟩ := CopyTower.source_graph_exists_d hM hC hRun hB
  have hBad : BadAt M C m LD.space LD.layers W.K W.level last W.root := by simpa only [hSpace,hLayers] using hW.bad
  have hTower : CopyTower.Tower M C T W.coordinates m LD.space LD.layers W.K W.level W.horizon W.width W.forests W.codes W.tower := by
    simpa only [hSpace,hLayers] using hW.tower
  exact ⟨⟨LD,last,W.K,W.level,W.root,W.horizon,W.coordinates,W.width,W.forests,Sources,SourceMap,W.codes,W.tower,W.top⟩,
    hW.last ▸ hW.coordinates.last,hLast,hLD,hW.horizon,⟨bad_in_horizon_d hM hC hRun hBad hW.horizon,hBad⟩,
    hW.last,hW.root,hW.coordinates,hW.tower.width,hW.width,hW.tower.forests,hSources,hTower,hW.top,hW.reconstruction⟩

def completeFormula {n : Nat} (C : ExpressionData (Project.Term n)) (T : MatrixArithmetic (Project.Term n))
    (AllForests ForestLists Grids s m N t : Project.Term n) (W : ExecutionData (Project.Term n)) : Project.Formula 1 n :=
  (.conj (.mem W.last C.omega)
    (.conj (successorFormula m W.last)
    (.conj (layerCalculationFormula C T AllForests s m W.horizon W.layer)
    (.conj (horizonFormula C s m W.horizon)
    (.conj (badFormula C W.layer W.K W.level W.last W.root)
    (.conj (Project.Formula.extensionalEq W.coordinates.last W.last)
    (.conj (Project.Formula.extensionalEq W.coordinates.root W.root)
    (.conj (coordinatesFormula C T W.coordinates)
    (.conj (.mem W.width C.omega)
    (.conj (CopyCoordinates.encodeFormula C T W.coordinates W.coordinates.last N W.width)
    (.conj (forestSpaceFormula C.omega AllForests W.width W.forests)
    (.conj (CopyTower.sourceGraphCertificateFormula C m W.layer.rows W.layer.layerStates W.layer.layers W.horizon W.layer.histories W.layer.runs W.sources W.sourceMap)
    (.conj (CopyTower.towerCertificateFormula C T W.coordinates m W.layer.rowForests W.K W.level W.horizon W.width W.forests W.sources W.sourceMap W.codes W.tower)
    (.conj (allOneFormula C W.width W.top)
    (assemblyFormula C T.addPairs T.plus W.width W.forests W.codes W.tower W.horizon W.top t ForestLists Grids)))))))))))))))

theorem completeFormula_delta0 {n : Nat} (C : ExpressionData (Project.Term n)) (T : MatrixArithmetic (Project.Term n))
    (AllForests ForestLists Grids s m N t : Project.Term n) (W : ExecutionData (Project.Term n)) :
    (completeFormula C T AllForests ForestLists Grids s m N t W).IsDelta0 :=
  (.conj (.mem _ _)
    (.conj (successorFormula_delta0 _ _)
    (.conj (layerCalculationFormula_delta0 _ _ _ _ _ _ _)
    (.conj (horizonFormula_delta0 _ _ _ _)
    (.conj (badFormula_delta0 _ _ _ _ _ _)
    (.conj (.atom _ _ _)
    (.conj (.atom _ _ _)
    (.conj (coordinatesFormula_delta0 _ _ _)
    (.conj (.mem _ _)
    (.conj (CopyCoordinates.encodeFormula_delta0 _ _ _ _ _ _)
    (.conj (forestSpaceFormula_delta0 _ _ _ _)
    (.conj (CopyTower.sourceGraphCertificateFormula_delta0 _ _ _ _ _ _ _ _ _ _)
    (.conj (CopyTower.towerCertificateFormula_delta0 _ _ _ _ _ _ _ _ _ _ _ _ _ _)
    (.conj (allOneFormula_delta0 _ _ _)
    (assemblyFormula_delta0 _ _ _ _ _ _ _ _ _ _ _ _)))))))))))))))

theorem completeFormula_freeClosed {n : Nat} {C : ExpressionData (Project.Term n)} (hC : C.Closed)
    {T : MatrixArithmetic (Project.Term n)} (hT : CopyCoordinates.ArithmeticClosed T) {W : ExecutionData (Project.Term n)} (hW : W.Closed)
    (AllForests ForestLists Grids s m N t : Project.Term n) (hAF : AllForests.freeSupport=[]) (hFL : ForestLists.freeSupport=[])
    (hGrids : Grids.freeSupport=[]) (hs : s.freeSupport=[]) (hm : m.freeSupport=[]) (hN : N.freeSupport=[]) (ht : t.freeSupport=[]) :
    (completeFormula C T AllForests ForestLists Grids s m N t W).FreeClosed := by
  have hLC := layerCalculationFormula_freeClosed hC hT hW.layer AllForests s m W.horizon hAF hs hm hW.horizon
  have hHor := horizonFormula_freeClosed hC s m W.horizon hs hm hW.horizon
  have hBad := badFormula_freeClosed hC hW.layer W.K W.level W.last W.root hW.K hW.level hW.last hW.root
  have hCoords := coordinatesFormula_freeClosed hC hT hW.coordinates
  have hWidth := CopyCoordinates.encodeFormula_freeClosed hC hT hW.coordinates W.coordinates.last N W.width hW.coordinates.last hN hW.width
  have hForests := forestSpaceFormula_freeClosed C.omega AllForests W.width W.forests hC.omega hAF hW.width hW.forests
  have hSource := CopyTower.sourceGraphCertificateFormula_freeClosed hC hW.layer.rows m W.layer.layerStates W.layer.layers W.horizon W.layer.histories W.layer.runs W.sources W.sourceMap
    hm hW.layer.layerStates hW.layer.layers hW.horizon hW.layer.histories hW.layer.runs hW.sources hW.sourceMap
  have hTower := CopyTower.towerCertificateFormula_freeClosed hC hT hW.coordinates m W.layer.rowForests W.K W.level W.horizon W.width W.forests W.sources W.sourceMap W.codes W.tower
    hm hW.layer.rowForests hW.K hW.level hW.horizon hW.width hW.forests hW.sources hW.sourceMap hW.codes hW.tower
  have hTop := allOneFormula_freeClosed hC W.width W.top hW.width hW.top
  have hAssembly := assemblyFormula_freeClosed hC T.addPairs T.plus W.width W.forests W.codes W.tower W.horizon W.top t ForestLists Grids
    hT.addPairs hT.plus hW.width hW.forests hW.codes hW.tower hW.horizon hW.top ht hFL hGrids
  simp [completeFormula,successorFormula,Project.Formula.forallMem,Definitional.Formula.FreeClosed,hW.last,hW.root,hW.width,
    hW.coordinates.last,hW.coordinates.root,hC.omega,hm,hLC,hHor,hBad,hCoords,hWidth,hForests,hSource,hTower,hTop,hAssembly]

theorem completeFormula_iff {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory) {n : Nat} (e : Env M n)
    (C : ExpressionData (Project.Term n)) (T : MatrixArithmetic (Project.Term n))
    (AllForests ForestLists Grids s m N t : Project.Term n) (W : ExecutionData (Project.Term n))
    (hC : (C.eval e).Valid M) (hT : (T.eval e).Valid M (C.eval e))
    (hAF : ExpressionDiagram.AllForests M (C.eval e).omega (AllForests.eval e))
    (hSpaces : MountainReconstruction.Spaces.Valid M (C.eval e) (AllForests.eval e) ⟨ForestLists.eval e,Grids.eval e⟩) :
    Project.Formula.satisfies e (completeFormula C T AllForests ForestLists Grids s m N t W) ↔
      CompleteCalculation M (C.eval e) (T.eval e) (AllForests.eval e) (s.eval e) (m.eval e) (N.eval e) (t.eval e) (W.eval e) := by
  simp only [completeFormula,Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_mem_iff,successorFormula_iff hM.1,
    layerCalculationFormula_iff hM e C T AllForests s m W.horizon W.layer hC hT hAF,horizonFormula_iff hM.1,
    Project.Formula.satisfies_extensionalEq_iff_eq hM.1,coordinatesFormula_iff hM e C T W.coordinates hT,
    CopyCoordinates.encodeFormula_iff hM.1,forestSpaceFormula_iff hM.1 e C.omega AllForests W.width W.forests hAF,allOneFormula_iff hM.1]
  constructor
  · rintro ⟨hl,hSucc,hLC,hHor,hBadRaw,hLast,hRoot,hA,hn,hWidth,hForests,hSourceRaw,hTowerRaw,hTop,hAssemblyRaw⟩
    have hRun := hLC.layer_run_d hM hC hT hAF
    have hBad := (badFormula_iff hM e C W.layer W.K W.level W.last W.root hC hRun hLC.family).mp hBadRaw
    have hBadA : BadAt M (C.eval e) (m.eval e) (W.eval e).layer.space (W.layer.layers.eval e)
        (W.K.eval e) (W.level.eval e) (W.coordinates.eval e).last (W.coordinates.eval e).root := by
      change BadAt M (C.eval e) (m.eval e) (W.layer.eval e).space (W.layer.layers.eval e) (W.K.eval e) (W.level.eval e) (W.coordinates.last.eval e) (W.coordinates.root.eval e)
      rw [hLast,hRoot]
      exact hBad.2
    have hSources := (CopyTower.sourceGraphCertificateFormula_iff hM e C m W.layer.rows W.layer.layerStates W.layer.layers W.horizon W.layer.histories W.layer.runs W.sources W.sourceMap
      hC hRun hLC.family).mp hSourceRaw
    have hTower := (CopyTower.towerCertificateFormula_iff hM e C T W.coordinates m W.layer.rowForests W.K W.level W.horizon W.width W.forests W.sources W.sourceMap W.codes W.tower
      hC hT hA hRun hBadA hSources rfl hForests hLC.bound hn).mp hTowerRaw
    have hSub : M.MemberSubset (W.forests.eval e) (AllForests.eval e) := fun F hF => (hAF F).mpr ⟨W.width.eval e,hn,(hForests F).mp hF⟩
    have hAssembly := (assemblyFormula_iff hM e C T.addPairs T.plus W.width W.forests W.codes W.tower W.horizon W.top t ForestLists Grids
      hC hSpaces hSub hn hLC.bound).mp hAssemblyRaw
    exact ⟨hl,hSucc,hLC,hHor,hBad,hLast,hRoot,hA,hn,hWidth,hForests,hSources,hTower,hTop,hAssembly⟩
  · intro h
    have hRun := h.layer.layer_run_d hM hC hT hAF
    have hBadA : BadAt M (C.eval e) (m.eval e) (W.eval e).layer.space (W.layer.layers.eval e)
        (W.K.eval e) (W.level.eval e) (W.coordinates.eval e).last (W.coordinates.eval e).root := by
      change BadAt M (C.eval e) (m.eval e) (W.eval e).layer.space (W.eval e).layer.layers (W.eval e).K (W.eval e).level (W.eval e).coordinates.last (W.eval e).coordinates.root
      rw [h.last,h.root]
      exact h.bad.2
    have hSub : M.MemberSubset (W.forests.eval e) (AllForests.eval e) := fun F hF => (hAF F).mpr ⟨W.width.eval e,h.width_nat,(h.forests F).mp hF⟩
    refine ⟨h.last_nat,h.last_succ,h.layer,h.horizon,?_,h.last,h.root,h.coordinates,h.width_nat,h.width,h.forests,?_,?_,h.top,?_⟩
    · exact (badFormula_iff hM e C W.layer W.K W.level W.last W.root hC hRun h.layer.family).mpr h.bad
    · exact (CopyTower.sourceGraphCertificateFormula_iff hM e C m W.layer.rows W.layer.layerStates W.layer.layers W.horizon W.layer.histories W.layer.runs W.sources W.sourceMap
        hC hRun h.layer.family).mpr h.source
    · exact (CopyTower.towerCertificateFormula_iff hM e C T W.coordinates m W.layer.rowForests W.K W.level W.horizon W.width W.forests W.sources W.sourceMap W.codes W.tower
        hC hT h.coordinates hRun hBadA h.source rfl h.forests h.layer.bound h.width_nat).mpr h.tower
    · exact (assemblyFormula_iff hM e C T.addPairs T.plus W.width W.forests W.codes W.tower W.horizon W.top t ForestLists Grids
        hC hSpaces hSub h.width_nat h.layer.bound).mpr h.assembly

structure ExecutionData.InBox (M : SetTheory.Structure.{u}) (Box : M.Domain) (W : ExecutionData M.Domain) : Prop where
  layer_linear : M.mem W.layer.linear Box
  layer_initial : M.mem W.layer.initial Box
  layer_rowValues : M.mem W.layer.rowValues Box
  layer_rowForests : M.mem W.layer.rowForests Box
  layer_rowStates : M.mem W.layer.rowStates Box
  layer_layerStates : M.mem W.layer.layerStates Box
  layer_layers : M.mem W.layer.layers Box
  layer_step : M.mem W.layer.step Box
  layer_stepBound : M.mem W.layer.stepBound Box
  layer_histories : M.mem W.layer.histories Box
  layer_runs : M.mem W.layer.runs Box
  last : M.mem W.last Box
  K : M.mem W.K Box
  level : M.mem W.level Box
  root : M.mem W.root Box
  horizon : M.mem W.horizon Box
  coordinates_last : M.mem W.coordinates.last Box
  coordinates_root : M.mem W.coordinates.root Box
  coordinates_length : M.mem W.coordinates.length Box
  coordinates_first : M.mem W.coordinates.first Box
  width : M.mem W.width Box
  forests : M.mem W.forests Box
  sources : M.mem W.sources Box
  sourceMap : M.mem W.sourceMap Box
  codes : M.mem W.codes Box
  tower : M.mem W.tower Box
  top : M.mem W.top Box

theorem execution_box_exists_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory) (W : ExecutionData M.Domain) :
    ∃Box, W.InBox M Box := by
  obtain ⟨Box,hBox⟩ := KP1Y.Ranking.finite_list_container_d hM [W.layer.linear,W.layer.initial,W.layer.rowValues,W.layer.rowForests,W.layer.rowStates,W.layer.layerStates,W.layer.layers,W.layer.step,W.layer.stepBound,W.layer.histories,W.layer.runs,W.last,W.K,W.level,W.root,W.horizon,W.coordinates.last,W.coordinates.root,W.coordinates.length,W.coordinates.first,W.width,W.forests,W.sources,W.sourceMap,W.codes,W.tower,W.top]
  exact ⟨Box,hBox _ (by simp),hBox _ (by simp),hBox _ (by simp),hBox _ (by simp),hBox _ (by simp),hBox _ (by simp),hBox _ (by simp),hBox _ (by simp),hBox _ (by simp),hBox _ (by simp),hBox _ (by simp),hBox _ (by simp),hBox _ (by simp),hBox _ (by simp),hBox _ (by simp),hBox _ (by simp),hBox _ (by simp),hBox _ (by simp),hBox _ (by simp),hBox _ (by simp),hBox _ (by simp),hBox _ (by simp),hBox _ (by simp),hBox _ (by simp),hBox _ (by simp),hBox _ (by simp),hBox _ (by simp)⟩

def Certificate (M : SetTheory.Structure.{u}) (C : ExpressionData M.Domain) (T : MatrixArithmetic M.Domain)
    (AllForests key t Box : M.Domain) : Prop :=
  ∃s, M.mem s C.expressions ∧ ∃N, M.mem N C.omega ∧ KP1Y.Kuratowski.Codes M key s N ∧
    ∃m, M.mem m C.omega ∧ LegalAt M C.omega C.zero C.one s m ∧
      ((m=C.zero ∧ t=s) ∨ (∃last, M.mem last C.omega ∧ M.SuccessorOf m last ∧ MemPair M s last C.one ∧ Prefix M t s last C.omega) ∨
        ∃W : ExecutionData M.Domain, W.InBox M Box ∧ CompleteCalculation M C T AllForests s m N t W)

def CodedExpands (M : SetTheory.Structure.{u}) (C : ExpressionData M.Domain) (T : MatrixArithmetic M.Domain) (key t : M.Domain) : Prop :=
  ∃s, M.mem s C.expressions ∧ ∃N, M.mem N C.omega ∧ KP1Y.Kuratowski.Codes M key s N ∧ Expands M C T s N t

theorem certificate_sound_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {AllForests key t Box : M.Domain} (hAF : ExpressionDiagram.AllForests M C.omega AllForests)
    (h : Certificate M C T AllForests key t Box) : CodedExpands M C T key t := by
  obtain ⟨s,hs,N,hN,hCode,m,hm,hLegal,hEmpty | hDrop | hComplete⟩ := h
  · exact ⟨s,hs,N,hN,hCode,hN,m,hm,hLegal,.inl hEmpty⟩
  · obtain ⟨last,hl,hSucc,hOne,hPrefix⟩ := hDrop
    exact ⟨s,hs,N,hN,hCode,hN,m,hm,hLegal,.inr ⟨last,hl,hSucc,.inl ⟨hOne,hPrefix⟩⟩⟩
  · obtain ⟨W,_,hComplete⟩ := hComplete
    exact ⟨s,hs,N,hN,hCode,hN,m,hm,hLegal,.inr ⟨W.last,hComplete.last_nat,hComplete.last_succ,
      .inr ⟨W.success,hComplete.successful_d hM hC hT hAF⟩⟩⟩

theorem certificate_exists_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {AllForests key t : M.Domain} (hAF : ExpressionDiagram.AllForests M C.omega AllForests)
    (h : CodedExpands M C T key t) : ∃Box, Certificate M C T AllForests key t Box := by
  obtain ⟨s,hs,N,hN,hCode,_,m,hm,hLegal,hEmpty | ⟨last,hl,hSucc,hDrop | hSuccess⟩⟩ := h
  · exact ⟨C.zero,s,hs,N,hN,hCode,m,hm,hLegal,.inl hEmpty⟩
  · exact ⟨C.zero,s,hs,N,hN,hCode,m,hm,hLegal,.inr (.inl ⟨last,hl,hSucc,hDrop.1,hDrop.2⟩)⟩
  · obtain ⟨W,hW⟩ := complete_calculation_exists_d hM hC hT hAF hLegal hSucc hSuccess
    obtain ⟨Box,hBox⟩ := execution_box_exists_d hM W
    exact ⟨Box,s,hs,N,hN,hCode,m,hm,hLegal,.inr (.inr ⟨W,hBox,hW⟩)⟩

private def certificateC : ExpressionData (Project.Term 47) := ⟨.bound 46,.bound 45,.bound 44,.bound 43,.bound 42⟩
private def certificateT : MatrixArithmetic (Project.Term 47) := ⟨.bound 41,.bound 40,.bound 39,.bound 38,.bound 37,.bound 36⟩
private def certificateW : ExecutionData (Project.Term 47) :=
  ⟨⟨.bound 26,.bound 25,.bound 24,.bound 23,.bound 22,.bound 21,.bound 20,.bound 19,.bound 18,.bound 17,.bound 16⟩,.bound 15,.bound 14,.bound 13,.bound 12,.bound 11,⟨.bound 10,.bound 9,.bound 8,.bound 7⟩,.bound 6,.bound 5,.bound 4,.bound 3,.bound 2,.bound 1,.bound 0⟩

private def boxedComplete : Project.Formula 1 20 :=
  (Project.Formula.existsMem (.bound 3)
    (Project.Formula.existsMem (.bound 4)
    (Project.Formula.existsMem (.bound 5)
    (Project.Formula.existsMem (.bound 6)
    (Project.Formula.existsMem (.bound 7)
    (Project.Formula.existsMem (.bound 8)
    (Project.Formula.existsMem (.bound 9)
    (Project.Formula.existsMem (.bound 10)
    (Project.Formula.existsMem (.bound 11)
    (Project.Formula.existsMem (.bound 12)
    (Project.Formula.existsMem (.bound 13)
    (Project.Formula.existsMem (.bound 14)
    (Project.Formula.existsMem (.bound 15)
    (Project.Formula.existsMem (.bound 16)
    (Project.Formula.existsMem (.bound 17)
    (Project.Formula.existsMem (.bound 18)
    (Project.Formula.existsMem (.bound 19)
    (Project.Formula.existsMem (.bound 20)
    (Project.Formula.existsMem (.bound 21)
    (Project.Formula.existsMem (.bound 22)
    (Project.Formula.existsMem (.bound 23)
    (Project.Formula.existsMem (.bound 24)
    (Project.Formula.existsMem (.bound 25)
    (Project.Formula.existsMem (.bound 26)
    (Project.Formula.existsMem (.bound 27)
    (Project.Formula.existsMem (.bound 28)
    (Project.Formula.existsMem (.bound 29)
    (completeFormula certificateC certificateT (.bound 35) (.bound 34) (.bound 33) (.bound 29) (.bound 27) (.bound 28) (.bound 31) certificateW))))))))))))))))))))))))))))

private theorem boxedComplete_delta0 : boxedComplete.IsDelta0 :=
  .existsMem _ (.existsMem _ (.existsMem _ (.existsMem _ (.existsMem _ (.existsMem _ (.existsMem _ (.existsMem _ (.existsMem _ (.existsMem _ (.existsMem _ (.existsMem _ (.existsMem _ (.existsMem _ (.existsMem _ (.existsMem _ (.existsMem _ (.existsMem _ (.existsMem _ (.existsMem _ (.existsMem _ (.existsMem _ (.existsMem _ (.existsMem _ (.existsMem _ (.existsMem _ (.existsMem _ (completeFormula_delta0 _ _ _ _ _ _ _ _ _ _)))))))))))))))))))))))))))

def expansionMatrix : KP1Y.WitnessMatrix 14 where
  body := Project.Formula.existsMem (.bound 12) (Project.Formula.existsMem (.bound 17)
    (.conj (codeFormula (.bound 4) (.bound 1) (.bound 0)) (Project.Formula.existsMem (.bound 18)
      (.conj (legalAtFormula (.bound 19) (.bound 18) (.bound 17) (.bound 2) (.bound 0))
        (.disj (.conj (Project.Formula.extensionalEq (.bound 0) (.bound 18)) (Project.Formula.extensionalEq (.bound 4) (.bound 2)))
          (.disj (Project.Formula.existsMem (.bound 19) (.conj (successorFormula (.bound 1) (.bound 0))
            (.conj (memPairFormula (.bound 3) (.bound 0) (.bound 18)) (prefixFormula (.bound 5) (.bound 3) (.bound 0) (.bound 20))))) boxedComplete))))))
  freeClosed := by
    have hBox := completeFormula_freeClosed (C := certificateC) ⟨rfl,rfl,rfl,rfl,rfl⟩
      (T := certificateT) ⟨rfl,rfl,rfl,rfl,rfl,rfl⟩
      (W := certificateW) ⟨⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩,rfl,rfl,rfl,rfl,rfl,⟨rfl,rfl,rfl,rfl⟩,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩
      (.bound 35) (.bound 34) (.bound 33) (.bound 29) (.bound 27) (.bound 28) (.bound 31) rfl rfl rfl rfl rfl rfl rfl
    have hLegal := legalAtFormula_freeClosed (n := 20) (.bound 19) (.bound 18) (.bound 17) (.bound 2) (.bound 0) rfl rfl rfl rfl rfl
    simp [boxedComplete,successorFormula,prefixFormula,graphFormula,memPairFormula,codeFormula,pairFormula,
      Project.Formula.forallMem,Project.Formula.existsMem,Definitional.Formula.FreeClosed,hBox,hLegal]
  delta0 := .existsMem _ (.existsMem _ (.conj (codeFormula_delta0 _ _ _) (.existsMem _
    (.conj (legalAtFormula_delta0 _ _ _ _ _) (.disj (.conj (.atom _ _ _) (.atom _ _ _))
      (.disj (.existsMem _ (.conj (successorFormula_delta0 _ _) (.conj (memPairFormula_delta0 _ _ _) (prefixFormula_delta0 _ _ _ _))))
        boxedComplete_delta0))))))

def expansionEnv {M : SetTheory.Structure.{u}} (C : ExpressionData M.Domain) (T : MatrixArithmetic M.Domain)
    (AllForests ForestLists Grids : M.Domain) : Env M 14 :=
  ((((((((((((((oneEnv C.omega).push C.zero).push C.one).push C.sequences).push C.expressions).push T.addPairs).push T.plus).push T.mulPairs).push T.times).push T.diffPairs).push T.difference).push AllForests).push ForestLists).push Grids)

private theorem boxedComplete_iff {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {AllForests ForestLists Grids : M.Domain} (hAF : ExpressionDiagram.AllForests M C.omega AllForests)
    (hSpaces : MountainReconstruction.Spaces.Valid M C AllForests ⟨ForestLists,Grids⟩) (key t Box s N m : M.Domain) :
    Project.Formula.satisfies (((((((expansionEnv C T AllForests ForestLists Grids).push key).push t).push Box).push s).push N).push m) boxedComplete ↔
      ∃W : ExecutionData M.Domain, W.InBox M Box ∧ CompleteCalculation M C T AllForests s m N t W := by
  have hCalc (v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20 v21 v22 v23 v24 v25 v26 : M.Domain) := completeFormula_iff hM ((((((((((((((((((((((((((((((((((expansionEnv C T AllForests ForestLists Grids).push key).push t).push Box).push s).push N).push m).push v0).push v1).push v2).push v3).push v4).push v5).push v6).push v7).push v8).push v9).push v10).push v11).push v12).push v13).push v14).push v15).push v16).push v17).push v18).push v19).push v20).push v21).push v22).push v23).push v24).push v25).push v26)
    certificateC certificateT (.bound 35) (.bound 34) (.bound 33) (.bound 29) (.bound 27) (.bound 28) (.bound 31) certificateW hC hT hAF hSpaces
  simp only [boxedComplete,Project.Formula.satisfies_existsMem_iff,hCalc]
  constructor
  · rintro ⟨v0,h0,v1,h1,v2,h2,v3,h3,v4,h4,v5,h5,v6,h6,v7,h7,v8,h8,v9,h9,v10,h10,v11,h11,v12,h12,v13,h13,v14,h14,v15,h15,v16,h16,v17,h17,v18,h18,v19,h19,v20,h20,v21,h21,v22,h22,v23,h23,v24,h24,v25,h25,v26,h26,hComplete⟩
    exact ⟨⟨⟨v0,v1,v2,v3,v4,v5,v6,v7,v8,v9,v10⟩,v11,v12,v13,v14,v15,⟨v16,v17,v18,v19⟩,v20,v21,v22,v23,v24,v25,v26⟩,⟨h0,h1,h2,h3,h4,h5,h6,h7,h8,h9,h10,h11,h12,h13,h14,h15,h16,h17,h18,h19,h20,h21,h22,h23,h24,h25,h26⟩,hComplete⟩
  · rintro ⟨W,hBox,hComplete⟩
    rcases W with ⟨⟨v0,v1,v2,v3,v4,v5,v6,v7,v8,v9,v10⟩,v11,v12,v13,v14,v15,⟨v16,v17,v18,v19⟩,v20,v21,v22,v23,v24,v25,v26⟩
    exact ⟨v0,hBox.layer_linear,v1,hBox.layer_initial,v2,hBox.layer_rowValues,v3,hBox.layer_rowForests,v4,hBox.layer_rowStates,v5,hBox.layer_layerStates,v6,hBox.layer_layers,v7,hBox.layer_step,v8,hBox.layer_stepBound,v9,hBox.layer_histories,v10,hBox.layer_runs,v11,hBox.last,v12,hBox.K,v13,hBox.level,v14,hBox.root,v15,hBox.horizon,v16,hBox.coordinates_last,v17,hBox.coordinates_root,v18,hBox.coordinates_length,v19,hBox.coordinates_first,v20,hBox.width,v21,hBox.forests,v22,hBox.sources,v23,hBox.sourceMap,v24,hBox.codes,v25,hBox.tower,v26,hBox.top,hComplete⟩

theorem expansionMatrix_iff {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {AllForests ForestLists Grids : M.Domain} (hAF : ExpressionDiagram.AllForests M C.omega AllForests)
    (hSpaces : MountainReconstruction.Spaces.Valid M C AllForests ⟨ForestLists,Grids⟩) (key t Box : M.Domain) :
    Project.Formula.satisfies ((((expansionEnv C T AllForests ForestLists Grids).push key).push t).push Box) expansionMatrix.body ↔
      Certificate M C T AllForests key t Box := by
  have hBox := boxedComplete_iff hM hC hT hAF hSpaces key t Box
  simp only [expansionMatrix,Project.Formula.satisfies_existsMem_iff,Project.Formula.satisfies_conj_iff,
    codeFormula_iff hM.1,legalAtFormula_iff hM.1,Project.Formula.satisfies_disj_iff,Project.Formula.satisfies_extensionalEq_iff_eq hM.1,
    successorFormula_iff hM.1,memPairFormula_iff hM.1,prefixFormula_iff hM.1,hBox]
  rfl

theorem expansion_sigmaOne_iff_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {AllForests ForestLists Grids : M.Domain} (hAF : ExpressionDiagram.AllForests M C.omega AllForests)
    (hSpaces : MountainReconstruction.Spaces.Valid M C AllForests ⟨ForestLists,Grids⟩) (key t : M.Domain) :
    (∃Box, Project.Formula.satisfies ((((expansionEnv C T AllForests ForestLists Grids).push key).push t).push Box) expansionMatrix.body) ↔
      CodedExpands M C T key t := by
  constructor
  · rintro ⟨Box,hBox⟩
    exact certificate_sound_d hM hC hT hAF ((expansionMatrix_iff hM hC hT hAF hSpaces key t Box).mp hBox)
  · intro h
    obtain ⟨Box,hBox⟩ := certificate_exists_d hM hC hT hAF h
    exact ⟨Box,(expansionMatrix_iff hM hC hT hAF hSpaces key t Box).mpr hBox⟩

theorem CodedExpands.at_iff {M : SetTheory.Structure.{u}} (he : Extensional M)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} {key s N t : M.Domain}
    (hCode : KP1Y.Kuratowski.Codes M key s N) : CodedExpands M C T key t ↔ Expands M C T s N t := by
  constructor
  · rintro ⟨s',_,N',_,hCode',hExpand⟩
    obtain ⟨hss,hNN⟩ := codes_injective he hCode' hCode
    subst s'
    subst N'
    exact hExpand
  · rintro ⟨hN,m,hm,hLegal,hRest⟩
    exact ⟨s,(hC.expressions s).mpr ⟨m,hm,hLegal⟩,N,hN,hCode,hN,m,hm,hLegal,hRest⟩

theorem CodedExpands.unique_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {key t u : M.Domain} (h : CodedExpands M C T key t) (h' : CodedExpands M C T key u) : t=u := by
  obtain ⟨s,_,N,_,hCode,hExpand⟩ := h
  exact hExpand.unique_d hM hC hT ((CodedExpands.at_iff hM.1 hC hCode).mp h')

/-- Keys是实际E×ω；EN是到同一个合法表达式集合E的实际函数图。 -/
structure Graph (M : SetTheory.Structure.{u}) (C : ExpressionData M.Domain) (T : MatrixArithmetic M.Domain) (Keys EN : M.Domain) : Prop where
  keys : IsProduct M Keys C.expressions C.omega
  graph : KP1Y.Functions.Graph M EN Keys C.expressions
  rows : ∀key t, MemPair M EN key t ↔ CodedExpands M C T key t

/-- 由实际Σ₁证书的共同收集构造全局展开图，输出和证书一同成集。 -/
theorem expansion_graph_exists_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C) :
    ∃Keys EN, Graph M C T Keys EN := by
  obtain ⟨AllForests,hAF⟩ := ExpressionDiagram.all_forests_exists_d hM hC
  obtain ⟨S,hS⟩ := MountainReconstruction.spaces_exists_d hM hC AllForests
  obtain ⟨Keys,hKeys⟩ := product_exists hM C.expressions C.omega
  let e := expansionEnv C T AllForests S.forestLists S.grids
  have hMeaning (key t : M.Domain) : (∃Box, Project.Formula.satisfies (((e.push key).push t).push Box) expansionMatrix.body) ↔ CodedExpands M C T key t :=
    expansion_sigmaOne_iff_d hM hC hT hAF hS key t
  have hTotal (key : M.Domain) (hk : M.mem key Keys) : ∃t Box, Project.Formula.satisfies (((e.push key).push t).push Box) expansionMatrix.body := by
    obtain ⟨s,hs,N,hN,hCode⟩ := (hKeys key).mp hk
    obtain ⟨t,hExpand⟩ := expands_exists_d hM hC hT hs hN
    obtain ⟨Box,hBox⟩ := (hMeaning key t).mpr ⟨s,hs,N,hN,hCode,hExpand⟩
    exact ⟨t,Box,hBox⟩
  have hBounds (key t : M.Domain) (h : CodedExpands M C T key t) : M.mem key Keys ∧ M.mem t C.expressions := by
    obtain ⟨s,hs,N,hN,hCode,hExpand⟩ := h
    exact ⟨(hKeys key).mpr ⟨s,hs,N,hN,hCode⟩,(hExpand.legal_d hM hC hT).2.2⟩
  obtain ⟨EN,hEN,hRows⟩ := sigma_function_graph_d hM expansionMatrix e Keys C.expressions hTotal
    (fun key _ t Box hBox => (hBounds key t ((hMeaning key t).mp ⟨Box,hBox⟩)).2)
    (fun key _ t u Box Box' hBox hBox' => ((hMeaning key t).mp ⟨Box,hBox⟩).unique_d hM hC hT ((hMeaning key u).mp ⟨Box',hBox'⟩))
  refine ⟨Keys,EN,hKeys,hEN,fun key t => ?_⟩
  rw [hRows key t,hMeaning key t]
  exact ⟨fun h => h.2.2,fun h => ⟨(hBounds key t h).1,(hBounds key t h).2,h⟩⟩

theorem Graph.at_iff {M : SetTheory.Structure.{u}} (he : Extensional M)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} {Keys EN key s N t : M.Domain}
    (h : Graph M C T Keys EN) (hCode : KP1Y.Kuratowski.Codes M key s N) : MemPair M EN key t ↔ Expands M C T s N t :=
  (h.rows key t).trans (CodedExpands.at_iff he hC hCode)

theorem Graph.total_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} {Keys EN s N : M.Domain}
    (h : Graph M C T Keys EN) (hs : M.mem s C.expressions) (hN : M.mem N C.omega) :
    ∃key t, KP1Y.Kuratowski.Codes M key s N ∧ M.mem t C.expressions ∧ MemPair M EN key t ∧ Expands M C T s N t := by
  obtain ⟨key,hCode⟩ := codes_total hM s N
  obtain ⟨t,ht,hAt⟩ := h.graph.total key ((h.keys key).mpr ⟨s,hs,N,hN,hCode⟩)
  exact ⟨key,t,hCode,ht,hAt,(h.at_iff hM.1 hC hCode).mp hAt⟩

theorem Graph.unique {M : SetTheory.Structure.{u}} (he : Extensional M)
    {C : ExpressionData M.Domain} {T : MatrixArithmetic M.Domain} {Keys EN Keys' EN' : M.Domain}
    (h : Graph M C T Keys EN) (h' : Graph M C T Keys' EN') : Keys=Keys' ∧ EN=EN' :=
  ⟨he.eq_of_same_members Keys Keys' (fun key => (h.keys key).trans (h'.keys key).symm),
    relation_ext he h.graph.support h'.graph.support (fun key t => (h.rows key t).trans (h'.rows key t).symm)⟩

theorem Graph.empty_iff_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C) {Keys EN key N t : M.Domain}
    (h : Graph M C T Keys EN) (hN : M.mem N C.omega) (hCode : KP1Y.Kuratowski.Codes M key C.zero N) :
    MemPair M EN key t ↔ t=C.zero := (h.at_iff hM.1 hC hCode).trans (Expands.empty_iff_d hM hC hT hN)

theorem Graph.zero_iff_drop_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C) {Keys EN key s m t : M.Domain}
    (h : Graph M C T Keys EN) (hLegal : LegalAt M C.omega C.zero C.one s m) (hCode : KP1Y.Kuratowski.Codes M key s C.zero) :
    MemPair M EN key t ↔ DropLast M C s m t := (h.at_iff hM.1 hC hCode).trans (expands_zero_iff_drop_d hM hC hT hLegal)

theorem Graph.keeps_prefix_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {Keys EN key s m last N t : M.Domain} (h : Graph M C T Keys EN) (hLegal : LegalAt M C.omega C.zero C.one s m)
    (hLast : M.SuccessorOf m last) (hCode : KP1Y.Kuratowski.Codes M key s N) (hAt : MemPair M EN key t) : RowsAgreeOn M t s last := by
  obtain ⟨_,m',_,hLegal',hEmpty | ⟨last',hl',hSucc,hDrop | ⟨W,hSuccess⟩⟩⟩ := (h.at_iff hM.1 hC hCode).mp hAt
  · have hmm := legal_length_unique hM.1 hLegal' hLegal
    exact False.elim (hC.zero_empty last ((hmm.symm.trans hEmpty.1) ▸ hLast.predecessor_mem))
  · have hmm := legal_length_unique hM.1 hLegal' hLegal
    subst m'
    have hll := Structure.SuccessorOf.predecessor_eq hM.1 ((omega_isOrdinal_d hM hC.omega).mem hl') hSucc hLast
    subst last'
    exact fun c hc v => hDrop.2.all_rows hM.1 hLegal.1.2 c hc v
  · have hmm := legal_length_unique hM.1 hLegal' hLegal
    subst m'
    have hll := Structure.SuccessorOf.predecessor_eq hM.1 ((omega_isOrdinal_d hM hC.omega).mem hl') hSucc hLast
    subst last'
    exact hSuccess.prefix_old_d hM hC hT hLast

/-- 非空合法输入的horizon是实际最大值且至少1，故精确对应原max(1,maxValue)。 -/
theorem Horizon.original_sequence_bound_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {s m horizon : M.Domain}
    (hLegal : LegalAt M C.omega C.zero C.one s m) (hNe : ∃c, M.mem c m) (h : Horizon M C s m horizon) :
    (C.one=horizon ∨ M.mem C.one horizon) ∧ (∃c, M.mem c m ∧ MemPair M s c horizon) ∧
      ∀c v, MemPair M s c v → v=horizon ∨ M.mem v horizon := by
  have hMax := h.maximum_d hM hC hLegal.1.2 hNe
  obtain ⟨c,_,hAt⟩ := hMax.1
  have hPos := legal_values_positive hM.1 hLegal hAt
  refine ⟨?_,hMax⟩
  by_cases he : horizon=C.one
  · exact .inl he.symm
  · exact .inr (positive_ne_one_above_d hM hC (h.natural_d hM hC) hPos he)

end KP1Y.OneYFinite.Expansion
