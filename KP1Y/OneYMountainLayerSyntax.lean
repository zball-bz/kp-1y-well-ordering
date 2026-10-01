import KP1Y.OneYMountainExtraction
import KP1Y.BoundedSubstitution
import KP1Y.ClosedEnvironments

/-! 提取层迭代的固定集合参数及字面证书语法。无界行历史作为 Σ₁ 见证单独打包。 -/
namespace KP1Y.OneYFinite
open YesMetaZFC YesMetaZFC.SetTheory YesMetaZFC.SetTheory.Definitional
open KP1Y.Kuratowski KP1Y.Functions KP1Y.Naturals KP1Y.Bounded
universe u

def numericRowFormula {n : Nat} (C : ExpressionData (Project.Term n)) (m V P : Project.Term n) : Project.Formula 1 n :=
  .conj (graphFormula V m C.omega) (.conj (forestFormula C.omega m P)
    (Project.Formula.forallMem m (Project.Formula.forallMem m.weaken (Project.Formula.forallMem C.omega.weaken.weaken
      (Project.Formula.forallMem C.omega.weaken.weaken.weaken (.imp
        (.conj (memPairFormula P.weaken.weaken.weaken.weaken (.bound 3) (.bound 2))
          (.conj (memPairFormula V.weaken.weaken.weaken.weaken (.bound 2) (.bound 1))
            (memPairFormula V.weaken.weaken.weaken.weaken (.bound 3) (.bound 0))))
        (.conj (.mem C.zero.weaken.weaken.weaken.weaken (.bound 1)) (.mem (.bound 1) (.bound 0)))))))))

theorem numericRowFormula_delta0 {n : Nat} (C : ExpressionData (Project.Term n)) (m V P : Project.Term n) :
    (numericRowFormula C m V P).IsDelta0 :=
  .conj (graphFormula_delta0 _ _ _) (.conj (forestFormula_delta0 _ _ _) (.forallMem _ (.forallMem _ (.forallMem _ (.forallMem _
    (.imp (.conj (memPairFormula_delta0 _ _ _) (.conj (memPairFormula_delta0 _ _ _) (memPairFormula_delta0 _ _ _)))
      (.conj (.mem _ _) (.mem _ _))))))))

theorem numericRowFormula_freeClosed {n : Nat} {C : ExpressionData (Project.Term n)} (hC : C.Closed)
    (m V P : Project.Term n) (hm : m.freeSupport=[]) (hV : V.freeSupport=[]) (hP : P.freeSupport=[]) :
    (numericRowFormula C m V P).FreeClosed := by
  simp [numericRowFormula,forestFormula,graphFormula,memPairFormula,codeFormula,pairFormula,
    Project.Formula.forallMem,Project.Formula.existsMem,Definitional.Formula.FreeClosed,hC.omega,hC.zero,hm,hV,hP]

theorem numericRowFormula_iff {M : SetTheory.Structure.{u}} (he : Extensional M) {n : Nat} (e : Env M n)
    (C : ExpressionData (Project.Term n)) (m V P : Project.Term n) :
    Project.Formula.satisfies e (numericRowFormula C m V P) ↔ NumericRow M (C.eval e) (m.eval e) (V.eval e) (P.eval e) := by
  simp only [numericRowFormula,Project.Formula.satisfies_conj_iff,graphFormula_iff he,forestFormula_iff he,
    Project.Formula.satisfies_forallMem_iff,Project.Formula.satisfies_imp_iff,memPairFormula_iff he,Project.Formula.satisfies_mem_iff,Term.eval_weaken]
  constructor
  · rintro ⟨hV,hP,hValues⟩
    exact ⟨hV,hP,fun c p x y hParent hPx hCy => hValues c (hP.bounds he hParent).1 p (hP.bounds he hParent).2
      x (hV.bounds he hPx).2 y (hV.bounds he hCy).2 ⟨hParent,hPx,hCy⟩⟩
  · intro h
    exact ⟨h.values,h.forest,fun c _ p _ x _ y _ hAt => h.parentValues c p x y hAt.1 hAt.2.1 hAt.2.2⟩

def rootedRowFormula {n : Nat} (C : ExpressionData (Project.Term n)) (m V P : Project.Term n) : Project.Formula 1 n :=
  .conj (numericRowFormula C m V P)
    (.conj (Project.Formula.forallMem m (Project.Formula.forallMem C.omega.weaken
      (.imp (memPairFormula V.weaken.weaken (.bound 1) (.bound 0)) (.mem C.zero.weaken.weaken (.bound 0)))))
      (Project.Formula.forallMem m (Project.Formula.forallMem C.omega.weaken
        (.imp (memPairFormula V.weaken.weaken (.bound 1) (.bound 0))
          (.imp (noParentFormula m.weaken.weaken P.weaken.weaken (.bound 1))
            (Project.Formula.extensionalEq (.bound 0) C.one.weaken.weaken))))))

theorem rootedRowFormula_delta0 {n : Nat} (C : ExpressionData (Project.Term n)) (m V P : Project.Term n) :
    (rootedRowFormula C m V P).IsDelta0 :=
  .conj (numericRowFormula_delta0 _ _ _ _) (.conj
    (.forallMem _ (.forallMem _ (.imp (memPairFormula_delta0 _ _ _) (.mem _ _))))
    (.forallMem _ (.forallMem _ (.imp (memPairFormula_delta0 _ _ _) (.imp (noParentFormula_delta0 _ _ _) (.atom _ _ _))))))

theorem rootedRowFormula_freeClosed {n : Nat} {C : ExpressionData (Project.Term n)} (hC : C.Closed)
    (m V P : Project.Term n) (hm : m.freeSupport=[]) (hV : V.freeSupport=[]) (hP : P.freeSupport=[]) :
    (rootedRowFormula C m V P).FreeClosed := by
  have hRow := numericRowFormula_freeClosed hC m V P hm hV hP
  simp [rootedRowFormula,noParentFormula,memPairFormula,codeFormula,pairFormula,Project.Formula.forallMem,
    Project.Formula.existsMem,Definitional.Formula.FreeClosed,hC.omega,hC.zero,hC.one,hm,hV,hP,hRow]

theorem rootedRowFormula_iff {M : SetTheory.Structure.{u}} (he : Extensional M) {n : Nat} (e : Env M n)
    (C : ExpressionData (Project.Term n)) (m V P : Project.Term n) :
    Project.Formula.satisfies e (rootedRowFormula C m V P) ↔ RootedRow M (C.eval e) (m.eval e) (V.eval e) (P.eval e) := by
  simp only [rootedRowFormula,Project.Formula.satisfies_conj_iff,numericRowFormula_iff he,
    Project.Formula.satisfies_forallMem_iff,Project.Formula.satisfies_imp_iff,memPairFormula_iff he,
    Project.Formula.satisfies_mem_iff,noParentFormula_iff he,Project.Formula.satisfies_extensionalEq_iff_eq he,Term.eval_weaken]
  constructor
  · rintro ⟨hRow,hPositive,hRoots⟩
    exact ⟨hRow,fun c v hAt => hPositive c (hRow.values.bounds he hAt).1 v (hRow.values.bounds he hAt).2 hAt,
      fun c v hAt hNo => hRoots c (hRow.values.bounds he hAt).1 v (hRow.values.bounds he hAt).2 hAt hNo⟩
  · intro h
    exact ⟨h.row,fun c _ v _ hAt => h.positive c v hAt,fun c _ v _ hAt hNo => h.rootsOne c v hAt hNo⟩

structure LayerStateSpace (α : Type u) where
  rows : RowStateSpace α
  states : α

structure LayerStateSpace.Valid (M : SetTheory.Structure.{u}) (C : ExpressionData M.Domain) (m : M.Domain)
    (L : LayerStateSpace M.Domain) : Prop where
  rows : L.rows.Valid M C m
  states : ∀ state, M.mem state L.states ↔ ∃ V P, Codes M state V P ∧ RootedRow M C m V P

private def layerStateSchema : Project.Delta0UnarySchema 8 where
  body := Project.Formula.existsMem (.bound 2) (Project.Formula.existsMem (.bound 2)
    (.conj (codeFormula (.bound 2) (.bound 1) (.bound 0))
      (rootedRowFormula ⟨.bound 10,.bound 9,.bound 8,.bound 7,.bound 6⟩ (.bound 5) (.bound 1) (.bound 0))))
  freeClosed := by
    have hRooted := rootedRowFormula_freeClosed (n := 11) (C := ⟨.bound 10,.bound 9,.bound 8,.bound 7,.bound 6⟩)
      ⟨rfl,rfl,rfl,rfl,rfl⟩ (.bound 5) (.bound 1) (.bound 0) rfl rfl rfl
    simp [Project.Formula.existsMem,Definitional.Formula.FreeClosed,codeFormula,pairFormula,Project.Formula.forallMem,hRooted]
  delta0 := .existsMem _ (.existsMem _ (.conj (codeFormula_delta0 _ _ _) (rootedRowFormula_delta0 _ _ _ _)))

theorem layer_state_space_exists_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory) {C : ExpressionData M.Domain} (hC : C.Valid M)
    {m : M.Domain} (hm : M.mem m C.omega) : ∃ L, LayerStateSpace.Valid M C m L := by
  obtain ⟨R,hR⟩ := row_state_space_exists_d hM hC hm
  let e := (((((((oneEnv C.omega).push C.zero).push C.one).push C.sequences).push C.expressions).push m).push R.values).push R.forests
  have hφ (state : M.Domain) : Project.Formula.satisfies (e.push state) layerStateSchema.body ↔
      ∃ V, M.mem V R.values ∧ ∃ P, M.mem P R.forests ∧ Codes M state V P ∧ RootedRow M C m V P := by
    simp only [layerStateSchema,Project.Formula.satisfies_existsMem_iff,Project.Formula.satisfies_conj_iff,
      codeFormula_iff hM.1,rootedRowFormula_iff hM.1]
    rfl
  obtain ⟨States,hStates⟩ := SetTheory.KP.separation_exists_d (KP1Y.models_weakKP hM) layerStateSchema e R.states
  refine ⟨⟨R,States⟩,hR,?_⟩
  intro state
  have hDef := hStates state
  rw [hφ] at hDef
  refine hDef.trans ⟨?_,?_⟩
  · rintro ⟨_,V,_,P,_,hCode,hRooted⟩
    exact ⟨V,P,hCode,hRooted⟩
  · rintro ⟨V,P,hCode,hRooted⟩
    have hV := (hR.values V).mpr hRooted.row.values
    have hP := (hR.forests P).mpr hRooted.row.forest
    exact ⟨(hR.states state).mpr ⟨V,hV,P,hP,hCode⟩,V,hV,P,hP,hCode,hRooted⟩

theorem LayerStateSpace.Valid.encode_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} {m : M.Domain} {L : LayerStateSpace M.Domain} (hL : L.Valid M C m) {V P : M.Domain}
    (hRooted : RootedRow M C m V P) : ∃ state, M.mem state L.states ∧ Codes M state V P := by
  obtain ⟨state,hCode⟩ := codes_total hM V P
  exact ⟨state,(hL.states state).mpr ⟨V,P,hCode,hRooted⟩,hCode⟩

def RowStateSpace.eval {M : SetTheory.Structure.{u}} {n : Nat} (R : RowStateSpace (Project.Term n)) (e : Env M n) : RowStateSpace M.Domain :=
  ⟨R.values.eval e,R.forests.eval e,R.states.eval e⟩

def RowStateSpace.weaken {n : Nat} (R : RowStateSpace (Project.Term n)) : RowStateSpace (Project.Term (n+1)) :=
  ⟨R.values.weaken,R.forests.weaken,R.states.weaken⟩

theorem RowStateSpace.eval_weaken {M : SetTheory.Structure.{u}} {n : Nat} (R : RowStateSpace (Project.Term n)) (e : Env M n) (x : M.Domain) :
    R.weaken.eval (e.push x)=R.eval e := by
  cases R
  simp [RowStateSpace.weaken,RowStateSpace.eval,Term.eval_weaken]

structure RowStateSpace.Closed {n : Nat} (R : RowStateSpace (Project.Term n)) : Prop where
  values : R.values.freeSupport=[]
  forests : R.forests.freeSupport=[]
  states : R.states.freeSupport=[]

theorem RowStateSpace.Closed.weaken {n : Nat} {R : RowStateSpace (Project.Term n)} (h : R.Closed) : R.weaken.Closed := by
  constructor <;> simp [RowStateSpace.weaken,h.values,h.forests,h.states]

def heightGraphFormula {n : Nat} (C : ExpressionData (Project.Term n)) (m : Project.Term n) (R : RowStateSpace (Project.Term n))
    (V H Heights : Project.Term n) : Project.Formula 1 n :=
  .conj (graphFormula Heights m C.omega) (Project.Formula.forallMem m (Project.Formula.forallMem C.omega.weaken
    (.iff (memPairFormula Heights.weaken.weaken (.bound 1) (.bound 0))
      (heightAtFormula C.omega.weaken.weaken C.zero.weaken.weaken R.states.weaken.weaken R.values.weaken.weaken R.forests.weaken.weaken
        V.weaken.weaken H.weaken.weaken (.bound 1) (.bound 0)))))

theorem heightGraphFormula_delta0 {n : Nat} (C : ExpressionData (Project.Term n)) (m : Project.Term n) (R : RowStateSpace (Project.Term n))
    (V H Heights : Project.Term n) : (heightGraphFormula C m R V H Heights).IsDelta0 :=
  .conj (graphFormula_delta0 _ _ _) (.forallMem _ (.forallMem _ (.iff (memPairFormula_delta0 _ _ _)
    (heightAtFormula_delta0 _ _ _ _ _ _ _ _ _))))

theorem heightGraphFormula_freeClosed {n : Nat} {C : ExpressionData (Project.Term n)} (hC : C.Closed)
    {R : RowStateSpace (Project.Term n)} (hR : R.Closed) (m V H Heights : Project.Term n)
    (hm : m.freeSupport=[]) (hV : V.freeSupport=[]) (hH : H.freeSupport=[]) (hHeights : Heights.freeSupport=[]) :
    (heightGraphFormula C m R V H Heights).FreeClosed := by
  have hAt := heightAtFormula_freeClosed C.omega.weaken.weaken C.zero.weaken.weaken R.states.weaken.weaken R.values.weaken.weaken R.forests.weaken.weaken
    V.weaken.weaken H.weaken.weaken (Project.Term.bound (depth := n+2) 1) (.bound 0)
    (by simpa using hC.omega) (by simpa using hC.zero) (by simpa using hR.states) (by simpa using hR.values)
    (by simpa using hR.forests) (by simpa using hV) (by simpa using hH) rfl rfl
  simp [heightGraphFormula,graphFormula,memPairFormula,codeFormula,pairFormula,Project.Formula.forallMem,
    Project.Formula.existsMem,Definitional.Formula.FreeClosed,hC.omega,hm,hHeights,hAt]

theorem heightGraphFormula_iff {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory) {n : Nat} (e : Env M n)
    (C : ExpressionData (Project.Term n)) (m : Project.Term n) (R : RowStateSpace (Project.Term n)) (V H Heights : Project.Term n)
    (hC : (C.eval e).Valid M) : Project.Formula.satisfies e (heightGraphFormula C m R V H Heights) ↔
      HeightGraph M (C.eval e) (m.eval e) (R.eval e) (V.eval e) (H.eval e) (Heights.eval e) := by
  have hAt (c height : M.Domain) : Project.Formula.satisfies ((e.push c).push height)
      (heightAtFormula C.omega.weaken.weaken C.zero.weaken.weaken R.states.weaken.weaken R.values.weaken.weaken R.forests.weaken.weaken
        V.weaken.weaken H.weaken.weaken (.bound 1) (.bound 0)) ↔
        HeightAt M (C.eval e) (R.eval e) (V.eval e) (H.eval e) c height := by
    have ht := heightAtFormula_iff hM.1 ((e.push c).push height) C.weaken.weaken
      R.states.weaken.weaken R.values.weaken.weaken R.forests.weaken.weaken V.weaken.weaken H.weaken.weaken (.bound 1) (.bound 0)
    simp only [ExpressionData.eval_weaken,Term.eval_weaken,Project.Term.eval_bound_one_push,Project.Term.eval_bound_zero_push] at ht
    exact ht
  simp only [heightGraphFormula,Project.Formula.satisfies_conj_iff,graphFormula_iff hM.1,Project.Formula.satisfies_forallMem_iff,
    Project.Formula.satisfies_iff_iff,memPairFormula_iff hM.1,Term.eval_weaken,hAt]
  constructor
  · rintro ⟨hGraph,hRows⟩
    refine ⟨hGraph,?_⟩
    intro c height
    constructor
    · intro hAt
      obtain ⟨hc,hh⟩ := hGraph.bounds hM.1 hAt
      exact ⟨hc,(hRows c hc height hh).mp hAt⟩
    · rintro ⟨hc,hHeight⟩
      exact (hRows c hc height (hHeight.natural_d hM hC)).mpr hHeight
  · intro h
    exact ⟨h.graph,fun c hc height _ => (h.rows c height).trans ⟨And.right,fun h => ⟨hc,h⟩⟩⟩

def topValueGraphFormula {n : Nat} (C : ExpressionData (Project.Term n)) (m : Project.Term n) (R : RowStateSpace (Project.Term n))
    (H Heights Top : Project.Term n) : Project.Formula 1 n :=
  .conj (graphFormula Top m C.omega) (Project.Formula.forallMem m (Project.Formula.forallMem C.omega.weaken
    (.iff (memPairFormula Top.weaken.weaken (.bound 1) (.bound 0)) (Project.Formula.existsMem C.omega.weaken.weaken
      (.conj (memPairFormula Heights.weaken.weaken.weaken (.bound 2) (.bound 0))
        (rowValueFormula R.states.weaken.weaken.weaken R.values.weaken.weaken.weaken R.forests.weaken.weaken.weaken
          H.weaken.weaken.weaken (.bound 0) (.bound 2) (.bound 1)))))))

theorem topValueGraphFormula_delta0 {n : Nat} (C : ExpressionData (Project.Term n)) (m : Project.Term n) (R : RowStateSpace (Project.Term n))
    (H Heights Top : Project.Term n) : (topValueGraphFormula C m R H Heights Top).IsDelta0 :=
  .conj (graphFormula_delta0 _ _ _) (.forallMem _ (.forallMem _ (.iff (memPairFormula_delta0 _ _ _)
    (.existsMem _ (.conj (memPairFormula_delta0 _ _ _) (rowValueFormula_delta0 _ _ _ _ _ _ _))))))

theorem topValueGraphFormula_freeClosed {n : Nat} {C : ExpressionData (Project.Term n)} (hC : C.Closed)
    {R : RowStateSpace (Project.Term n)} (hR : R.Closed) (m H Heights Top : Project.Term n)
    (hm : m.freeSupport=[]) (hH : H.freeSupport=[]) (hHeights : Heights.freeSupport=[]) (hTop : Top.freeSupport=[]) :
    (topValueGraphFormula C m R H Heights Top).FreeClosed := by
  have hValue := rowValueFormula_freeClosed R.states.weaken.weaken.weaken R.values.weaken.weaken.weaken R.forests.weaken.weaken.weaken
    H.weaken.weaken.weaken (Project.Term.bound (depth := n+3) 0) (.bound 2) (.bound 1)
    (by simpa using hR.states) (by simpa using hR.values) (by simpa using hR.forests) (by simpa using hH) rfl rfl rfl
  simp [topValueGraphFormula,graphFormula,memPairFormula,codeFormula,pairFormula,Project.Formula.forallMem,
    Project.Formula.existsMem,Definitional.Formula.FreeClosed,hC.omega,hm,hHeights,hTop,hValue]

theorem topValueGraphFormula_iff {M : SetTheory.Structure.{u}} (he : Extensional M) {n : Nat} (e : Env M n)
    (C : ExpressionData (Project.Term n)) (m : Project.Term n) (R : RowStateSpace (Project.Term n)) (H Heights Top : Project.Term n)
    (hR : (R.eval e).Valid M (C.eval e) (m.eval e)) (hHeights : Graph M (Heights.eval e) (m.eval e) (C.omega.eval e)) :
    Project.Formula.satisfies e (topValueGraphFormula C m R H Heights Top) ↔
      TopValueGraph M (C.eval e) (m.eval e) (R.eval e) (H.eval e) (Heights.eval e) (Top.eval e) := by
  simp only [topValueGraphFormula,Project.Formula.satisfies_conj_iff,graphFormula_iff he,Project.Formula.satisfies_forallMem_iff,
    Project.Formula.satisfies_iff_iff,memPairFormula_iff he,Project.Formula.satisfies_existsMem_iff,rowValueFormula_iff he,Term.eval_weaken]
  constructor
  · rintro ⟨hGraph,hRows⟩
    refine ⟨hGraph,?_⟩
    intro c v
    constructor
    · intro hAt
      obtain ⟨hc,hv⟩ := hGraph.bounds he hAt
      exact (hRows c hc v hv).mp hAt
    · rintro ⟨height,hh,hHeight,hValue⟩
      exact (hRows c (hHeights.bounds he hHeight).1 v (hValue.bounds he hR).2).mpr ⟨height,hh,hHeight,hValue⟩
  · intro h
    exact ⟨h.graph,fun c _ v _ => h.rows c v⟩

def pseudoForestFormula {n : Nat} (C : ExpressionData (Project.Term n)) (m : Project.Term n) (R : RowStateSpace (Project.Term n))
    (H Heights F : Project.Term n) : Project.Formula 1 n :=
  .conj (forestFormula C.omega m F) (Project.Formula.forallMem m (Project.Formula.forallMem m.weaken
    (.iff (memPairFormula F.weaken.weaken (.bound 1) (.bound 0))
      (pseudoParentFormula C.weaken.weaken m.weaken.weaken R.states.weaken.weaken R.values.weaken.weaken R.forests.weaken.weaken
        H.weaken.weaken Heights.weaken.weaken (.bound 1) (.bound 0)))))

theorem pseudoForestFormula_delta0 {n : Nat} (C : ExpressionData (Project.Term n)) (m : Project.Term n) (R : RowStateSpace (Project.Term n))
    (H Heights F : Project.Term n) : (pseudoForestFormula C m R H Heights F).IsDelta0 :=
  .conj (forestFormula_delta0 _ _ _) (.forallMem _ (.forallMem _ (.iff (memPairFormula_delta0 _ _ _)
    (pseudoParentFormula_delta0 _ _ _ _ _ _ _ _ _))))

theorem pseudoForestFormula_freeClosed {n : Nat} {C : ExpressionData (Project.Term n)} (hC : C.Closed)
    {R : RowStateSpace (Project.Term n)} (hR : R.Closed) (m H Heights F : Project.Term n)
    (hm : m.freeSupport=[]) (hH : H.freeSupport=[]) (hHeights : Heights.freeSupport=[]) (hF : F.freeSupport=[]) :
    (pseudoForestFormula C m R H Heights F).FreeClosed := by
  have hParent := pseudoParentFormula_freeClosed hC.weaken.weaken m.weaken.weaken R.states.weaken.weaken R.values.weaken.weaken R.forests.weaken.weaken
    H.weaken.weaken Heights.weaken.weaken (Project.Term.bound (depth := n+2) 1) (.bound 0)
    (by simpa using hm) (by simpa using hR.states) (by simpa using hR.values) (by simpa using hR.forests)
    (by simpa using hH) (by simpa using hHeights) rfl rfl
  simp [pseudoForestFormula,forestFormula,memPairFormula,codeFormula,pairFormula,Project.Formula.forallMem,
    Project.Formula.existsMem,Definitional.Formula.FreeClosed,hC.omega,hm,hF,hParent]

theorem pseudoForestFormula_iff {M : SetTheory.Structure.{u}} (he : Extensional M) {n : Nat} (e : Env M n)
    (C : ExpressionData (Project.Term n)) (m : Project.Term n) (R : RowStateSpace (Project.Term n)) (H Heights F : Project.Term n) :
    Project.Formula.satisfies e (pseudoForestFormula C m R H Heights F) ↔
      PseudoForest M (C.eval e) (m.eval e) (R.eval e) (H.eval e) (Heights.eval e) (F.eval e) := by
  simp only [pseudoForestFormula,Project.Formula.satisfies_conj_iff,forestFormula_iff he,Project.Formula.satisfies_forallMem_iff,
    Project.Formula.satisfies_iff_iff,memPairFormula_iff he,pseudoParentFormula_iff he,ExpressionData.eval_weaken,Term.eval_weaken]
  constructor
  · rintro ⟨hForest,hRows⟩
    refine ⟨hForest,?_⟩
    intro c p
    constructor
    · intro hAt
      obtain ⟨hc,hp⟩ := hForest.bounds he hAt
      exact (hRows c hc p hp).mp hAt
    · intro hParent
      have hb := hParent.2.1.bounds he
      exact (hRows c hb.2.1 p hb.1).mpr hParent
  · intro h
    exact ⟨h.forest,fun c _ p _ => h.parents c p⟩

private def rowStepArgs {n : Nat} (C : ExpressionData (Project.Term n)) (m : Project.Term n) (R : RowStateSpace (Project.Term n))
    (Pairs Table source target : Project.Term n) : Fin 12 → Project.Term n :=
  Fin.cases target (Fin.cases source (Fin.cases Table (Fin.cases Pairs (Fin.cases R.forests (Fin.cases R.values
    (Fin.cases m (Fin.cases C.expressions (Fin.cases C.sequences (Fin.cases C.one (Fin.cases C.zero (fun _ => C.omega)))))))))))

def rowTransitionFormula {n : Nat} (C : ExpressionData (Project.Term n)) (m : Project.Term n) (R : RowStateSpace (Project.Term n))
    (Pairs Table source target : Project.Term n) : Project.Formula 1 n := rowStepSchema_public.body.bind (rowStepArgs C m R Pairs Table source target)

theorem rowTransitionFormula_delta0 {n : Nat} (C : ExpressionData (Project.Term n)) (m : Project.Term n) (R : RowStateSpace (Project.Term n))
    (Pairs Table source target : Project.Term n) : (rowTransitionFormula C m R Pairs Table source target).IsDelta0 :=
  KP1Y.delta0_bind rowStepSchema_public.delta0 _

theorem rowTransitionFormula_freeClosed {n : Nat} {C : ExpressionData (Project.Term n)} (hC : C.Closed)
    {R : RowStateSpace (Project.Term n)} (hR : R.Closed) (m Pairs Table source target : Project.Term n)
    (hm : m.freeSupport=[]) (hp : Pairs.freeSupport=[]) (ht : Table.freeSupport=[]) (hs : source.freeSupport=[]) (hy : target.freeSupport=[]) :
    (rowTransitionFormula C m R Pairs Table source target).FreeClosed := by
  apply (Definitional.Formula.freeClosed_bind_iff_of_closed _ ?_ rowStepSchema_public.body).mpr rowStepSchema_public.freeClosed
  exact Fin.cases hy (Fin.cases hs (Fin.cases ht (Fin.cases hp (Fin.cases hR.forests (Fin.cases hR.values
    (Fin.cases hm (Fin.cases hC.expressions (Fin.cases hC.sequences (Fin.cases hC.one (Fin.cases hC.zero (fun _ => hC.omega)))))))))))

theorem rowTransitionFormula_iff {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory) {n : Nat} (e : Env M n)
    (C : ExpressionData (Project.Term n)) (m : Project.Term n) (R : RowStateSpace (Project.Term n)) (Pairs Table source target : Project.Term n)
    (hC : (C.eval e).Valid M) (hR : (R.eval e).Valid M (C.eval e) (m.eval e))
    (hTable : DifferenceTable M (C.eval e) (Pairs.eval e) (Table.eval e)) (hSource : M.mem (source.eval e) (R.states.eval e)) :
    Project.Formula.satisfies e (rowTransitionFormula C m R Pairs Table source target) ↔
      RowTransition M (C.eval e) (m.eval e) (source.eval e) (target.eval e) := by
  rw [rowTransitionFormula,Project.Formula.satisfies_bind]
  have hBound : ∀ i, (Env.substitute e (rowStepArgs C m R Pairs Table source target)).bound i =
      (((rowStepEnv_public (C.eval e) (m.eval e) (R.eval e) (Pairs.eval e) (Table.eval e)).push (source.eval e)).push (target.eval e)).bound i := by
    intro i
    have hi : i=0 ∨ i=1 ∨ i=2 ∨ i=3 ∨ i=4 ∨ i=5 ∨ i=6 ∨ i=7 ∨ i=8 ∨ i=9 ∨ i=10 ∨ i=11 := by omega
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
  exact (KP1Y.formula_bound_congr rowStepSchema_public.body rowStepSchema_public.freeClosed _ _ hBound).trans
    (rowStepSchema_public_iff hM hC hR hTable hSource)

def rowRunFormula {n : Nat} (C : ExpressionData (Project.Term n)) (m : Project.Term n) (R : RowStateSpace (Project.Term n))
    (Pairs Table V P H : Project.Term n) : Project.Formula 1 n :=
  .conj (graphFormula H C.omega R.states)
    (.conj (Project.Formula.forallMem R.states (.imp (codeFormula (.bound 0) V.weaken P.weaken)
      (memPairFormula H.weaken C.zero.weaken (.bound 0))))
      (Project.Formula.forallMem C.omega (Project.Formula.forallMem C.omega.weaken
        (Project.Formula.forallMem R.states.weaken.weaken (Project.Formula.forallMem R.states.weaken.weaken.weaken
          (.imp (.conj (successorFormula (.bound 2) (.bound 3))
            (.conj (memPairFormula H.weaken.weaken.weaken.weaken (.bound 3) (.bound 1))
              (memPairFormula H.weaken.weaken.weaken.weaken (.bound 2) (.bound 0))))
            (rowTransitionFormula C.weaken.weaken.weaken.weaken m.weaken.weaken.weaken.weaken R.weaken.weaken.weaken.weaken
              Pairs.weaken.weaken.weaken.weaken Table.weaken.weaken.weaken.weaken (.bound 1) (.bound 0))))))))

theorem rowRunFormula_delta0 {n : Nat} (C : ExpressionData (Project.Term n)) (m : Project.Term n) (R : RowStateSpace (Project.Term n))
    (Pairs Table V P H : Project.Term n) : (rowRunFormula C m R Pairs Table V P H).IsDelta0 :=
  .conj (graphFormula_delta0 _ _ _) (.conj (.forallMem _ (.imp (codeFormula_delta0 _ _ _) (memPairFormula_delta0 _ _ _)))
    (.forallMem _ (.forallMem _ (.forallMem _ (.forallMem _ (.imp
      (.conj (successorFormula_delta0 _ _) (.conj (memPairFormula_delta0 _ _ _) (memPairFormula_delta0 _ _ _)))
      (rowTransitionFormula_delta0 _ _ _ _ _ _ _)))))))

theorem rowRunFormula_freeClosed {n : Nat} {C : ExpressionData (Project.Term n)} (hC : C.Closed)
    {R : RowStateSpace (Project.Term n)} (hR : R.Closed) (m Pairs Table V P H : Project.Term n)
    (hm : m.freeSupport=[]) (hpairs : Pairs.freeSupport=[]) (htable : Table.freeSupport=[])
    (hV : V.freeSupport=[]) (hP : P.freeSupport=[]) (hH : H.freeSupport=[]) : (rowRunFormula C m R Pairs Table V P H).FreeClosed := by
  have hNext := rowTransitionFormula_freeClosed hC.weaken.weaken.weaken.weaken hR.weaken.weaken.weaken.weaken
    m.weaken.weaken.weaken.weaken Pairs.weaken.weaken.weaken.weaken Table.weaken.weaken.weaken.weaken (.bound 1) (.bound 0)
    (by simpa using hm) (by simpa using hpairs) (by simpa using htable) rfl rfl
  simp [rowRunFormula,graphFormula,memPairFormula,codeFormula,pairFormula,successorFormula,
    Project.Formula.forallMem,Project.Formula.existsMem,Definitional.Formula.FreeClosed,hC.omega,hC.zero,hR.states,hV,hP,hH,hNext]

theorem rowRunFormula_iff {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory) {n : Nat} (e : Env M n)
    (C : ExpressionData (Project.Term n)) (m : Project.Term n) (R : RowStateSpace (Project.Term n)) (Pairs Table V P H : Project.Term n)
    (hC : (C.eval e).Valid M) (hR : (R.eval e).Valid M (C.eval e) (m.eval e))
    (hTable : DifferenceTable M (C.eval e) (Pairs.eval e) (Table.eval e))
    (hBase : NumericRow M (C.eval e) (m.eval e) (V.eval e) (P.eval e)) :
    Project.Formula.satisfies e (rowRunFormula C m R Pairs Table V P H) ↔
      RowRun M (C.eval e) (m.eval e) (R.eval e) (V.eval e) (P.eval e) (H.eval e) := by
  have hNext (i j source target : M.Domain) (hSource : M.mem source (R.states.eval e)) :
      Project.Formula.satisfies ((((e.push i).push j).push source).push target)
        (rowTransitionFormula C.weaken.weaken.weaken.weaken m.weaken.weaken.weaken.weaken R.weaken.weaken.weaken.weaken
          Pairs.weaken.weaken.weaken.weaken Table.weaken.weaken.weaken.weaken (.bound 1) (.bound 0)) ↔
      RowTransition M (C.eval e) (m.eval e) source target := by
    have h := rowTransitionFormula_iff hM ((((e.push i).push j).push source).push target)
      C.weaken.weaken.weaken.weaken m.weaken.weaken.weaken.weaken R.weaken.weaken.weaken.weaken
      Pairs.weaken.weaken.weaken.weaken Table.weaken.weaken.weaken.weaken (.bound 1) (.bound 0)
      (by simpa only [ExpressionData.eval_weaken] using hC)
      (by simpa only [ExpressionData.eval_weaken,RowStateSpace.eval_weaken,Term.eval_weaken] using hR)
      (by simpa only [ExpressionData.eval_weaken,Term.eval_weaken] using hTable)
      (by simpa only [RowStateSpace.weaken,Term.eval_weaken,Project.Term.eval_bound_one_push,Project.Term.eval_bound_zero_push] using hSource)
    simpa only [ExpressionData.eval_weaken,Term.eval_weaken,Project.Term.eval_bound_one_push,Project.Term.eval_bound_zero_push] using h
  simp only [rowRunFormula,Project.Formula.satisfies_conj_iff,graphFormula_iff hM.1,Project.Formula.satisfies_forallMem_iff,
    Project.Formula.satisfies_imp_iff,codeFormula_iff hM.1,memPairFormula_iff hM.1,successorFormula_iff hM.1,Term.eval_weaken]
  constructor
  · rintro ⟨hGraph,hInitial,hTransition⟩
    refine ⟨hR,hBase,hGraph,?_,?_⟩
    · intro state hCode
      have hState := (hR.states state).mpr ⟨V.eval e,(hR.values _).mpr hBase.values,P.eval e,(hR.forests _).mpr hBase.forest,hCode⟩
      exact hInitial state hState hCode
    · intro i j source target hs hIn hOut
      obtain ⟨hi,hSource⟩ := hGraph.bounds hM.1 hIn
      obtain ⟨hj,hTarget⟩ := hGraph.bounds hM.1 hOut
      exact (hNext i j source target hSource).mp (hTransition i hi j hj source hSource target hTarget ⟨hs,hIn,hOut⟩)
  · intro h
    exact ⟨h.graph,fun state _ hCode => h.initial state hCode,fun i _ j _ source hSource target _ hAnte =>
      (hNext i j source target hSource).mpr (h.transition i j source target hAnte.1 hAnte.2.1 hAnte.2.2)⟩

private def extractionInnerFormula {n : Nat} (C : ExpressionData (Project.Term n)) (R : RowStateSpace (Project.Term n))
    (m Pairs Table source target V P W Q H Heights F : Project.Term n) : Project.Formula 1 n :=
  .conj (codeFormula source V P) (.conj (codeFormula target W Q) (.conj (rootedRowFormula C m V P)
    (.conj (rowRunFormula C m R Pairs Table V P H) (.conj (heightGraphFormula C m R V H Heights)
      (.conj (topValueGraphFormula C m R H Heights W) (.conj (pseudoForestFormula C m R H Heights F)
        (selectsFormula true C m F W Q)))))))

private theorem extractionInnerFormula_delta0 {n : Nat} (C : ExpressionData (Project.Term n)) (R : RowStateSpace (Project.Term n))
    (m Pairs Table source target V P W Q H Heights F : Project.Term n) :
    (extractionInnerFormula C R m Pairs Table source target V P W Q H Heights F).IsDelta0 :=
  .conj (codeFormula_delta0 _ _ _) (.conj (codeFormula_delta0 _ _ _) (.conj (rootedRowFormula_delta0 _ _ _ _)
    (.conj (rowRunFormula_delta0 _ _ _ _ _ _ _ _) (.conj (heightGraphFormula_delta0 _ _ _ _ _ _)
      (.conj (topValueGraphFormula_delta0 _ _ _ _ _ _) (.conj (pseudoForestFormula_delta0 _ _ _ _ _ _)
        (selectsFormula_delta0 _ _ _ _ _ _)))))))

private theorem extractionInnerFormula_freeClosed {n : Nat} {C : ExpressionData (Project.Term n)} (hC : C.Closed)
    {R : RowStateSpace (Project.Term n)} (hR : R.Closed) (m Pairs Table source target V P W Q H Heights F : Project.Term n)
    (hm : m.freeSupport=[]) (hpairs : Pairs.freeSupport=[]) (htable : Table.freeSupport=[])
    (hsource : source.freeSupport=[]) (htarget : target.freeSupport=[]) (hV : V.freeSupport=[]) (hP : P.freeSupport=[])
    (hW : W.freeSupport=[]) (hQ : Q.freeSupport=[]) (hH : H.freeSupport=[]) (hHeights : Heights.freeSupport=[]) (hF : F.freeSupport=[]) :
    (extractionInnerFormula C R m Pairs Table source target V P W Q H Heights F).FreeClosed := by
  simp only [extractionInnerFormula,Definitional.Formula.FreeClosed]
  refine ⟨?_,?_,rootedRowFormula_freeClosed hC m V P hm hV hP,
    rowRunFormula_freeClosed hC hR m Pairs Table V P H hm hpairs htable hV hP hH,
    heightGraphFormula_freeClosed hC hR m V H Heights hm hV hH hHeights,
    topValueGraphFormula_freeClosed hC hR m H Heights W hm hH hHeights hW,
    pseudoForestFormula_freeClosed hC hR m H Heights F hm hH hHeights hF,
    selectsFormula_freeClosed true hC m F W Q hm hF hW hQ⟩ <;>
      simp [codeFormula,pairFormula,Project.Formula.forallMem,Project.Formula.existsMem,Definitional.Formula.FreeClosed,hsource,htarget,hV,hP,hW,hQ]

private theorem extractionInnerFormula_iff {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory) {n : Nat} (e : Env M n)
    (C : ExpressionData (Project.Term n)) (R : RowStateSpace (Project.Term n)) (m Pairs Table source target V P W Q H Heights F : Project.Term n)
    (hC : (C.eval e).Valid M) (hR : (R.eval e).Valid M (C.eval e) (m.eval e))
    (hTable : DifferenceTable M (C.eval e) (Pairs.eval e) (Table.eval e)) :
    Project.Formula.satisfies e (extractionInnerFormula C R m Pairs Table source target V P W Q H Heights F) ↔
      Codes M (source.eval e) (V.eval e) (P.eval e) ∧ Codes M (target.eval e) (W.eval e) (Q.eval e) ∧
        RootedRow M (C.eval e) (m.eval e) (V.eval e) (P.eval e) ∧
          RowRun M (C.eval e) (m.eval e) (R.eval e) (V.eval e) (P.eval e) (H.eval e) ∧
            HeightGraph M (C.eval e) (m.eval e) (R.eval e) (V.eval e) (H.eval e) (Heights.eval e) ∧
              TopValueGraph M (C.eval e) (m.eval e) (R.eval e) (H.eval e) (Heights.eval e) (W.eval e) ∧
                PseudoForest M (C.eval e) (m.eval e) (R.eval e) (H.eval e) (Heights.eval e) (F.eval e) ∧
                  Selects true M (C.eval e) (m.eval e) (F.eval e) (W.eval e) (Q.eval e) := by
  simp only [extractionInnerFormula,Project.Formula.satisfies_conj_iff,codeFormula_iff hM.1,rootedRowFormula_iff hM.1,
    pseudoForestFormula_iff hM.1,selectsFormula_iff hM.1]
  constructor
  · rintro ⟨hIn,hOut,hBase,hRun,hHeights,hTop,hPseudo,hSelected⟩
    have hRun' := (rowRunFormula_iff hM e C m R Pairs Table V P H hC hR hTable hBase.row).mp hRun
    have hHeights' := (heightGraphFormula_iff hM e C m R V H Heights hC).mp hHeights
    exact ⟨hIn,hOut,hBase,hRun',hHeights',(topValueGraphFormula_iff hM.1 e C m R H Heights W hR hHeights'.graph).mp hTop,hPseudo,hSelected⟩
  · rintro ⟨hIn,hOut,hBase,hRun,hHeights,hTop,hPseudo,hSelected⟩
    exact ⟨hIn,hOut,hBase,(rowRunFormula_iff hM e C m R Pairs Table V P H hC hR hTable hBase.row).mpr hRun,
      (heightGraphFormula_iff hM e C m R V H Heights hC).mpr hHeights,
      (topValueGraphFormula_iff hM.1 e C m R H Heights W hR hHeights.graph).mpr hTop,hPseudo,hSelected⟩

private def extractionTerms : ExpressionData (Project.Term 21) := ⟨.bound 20,.bound 19,.bound 18,.bound 17,.bound 16⟩
private def extractionSpaceTerms : RowStateSpace (Project.Term 21) := ⟨.bound 14,.bound 13,.bound 12⟩

/-- 外层唯一无界见证 Box 同时界住实际行历史 H 与高度图；内部证书字面 Δ₀。 -/
def extractionStepMatrix : KP1Y.WitnessMatrix 11 where
  body := Project.Formula.existsMem (.bound 7) (Project.Formula.existsMem (.bound 7)
    (Project.Formula.existsMem (.bound 9) (Project.Formula.existsMem (.bound 9)
      (Project.Formula.existsMem (.bound 4) (Project.Formula.existsMem (.bound 5)
        (Project.Formula.existsMem (.bound 12) (extractionInnerFormula extractionTerms extractionSpaceTerms
          (.bound 15) (.bound 11) (.bound 10) (.bound 9) (.bound 8) (.bound 6) (.bound 5) (.bound 4) (.bound 3) (.bound 2) (.bound 1) (.bound 0))))))))
  freeClosed := by
    have hInner := extractionInnerFormula_freeClosed (C := extractionTerms) ⟨rfl,rfl,rfl,rfl,rfl⟩
      (R := extractionSpaceTerms) ⟨rfl,rfl,rfl⟩ (.bound 15) (.bound 11) (.bound 10) (.bound 9) (.bound 8)
      (.bound 6) (.bound 5) (.bound 4) (.bound 3) (.bound 2) (.bound 1) (.bound 0)
      rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
    simp [Project.Formula.existsMem,Definitional.Formula.FreeClosed,hInner]
  delta0 := .existsMem _ (.existsMem _ (.existsMem _ (.existsMem _ (.existsMem _ (.existsMem _ (.existsMem _
    (extractionInnerFormula_delta0 _ _ _ _ _ _ _ _ _ _ _ _ _ _)))))))

def extractionStepEnv {M : SetTheory.Structure.{u}} (C : ExpressionData M.Domain) (m : M.Domain) (R : RowStateSpace M.Domain)
    (Pairs Table : M.Domain) : Env M 11 :=
  ((((((((((oneEnv C.omega).push C.zero).push C.one).push C.sequences).push C.expressions).push m).push R.values).push R.forests).push R.states).push Pairs).push Table

theorem extractionStepMatrix_iff {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {m : M.Domain} {R : RowStateSpace M.Domain} (hR : R.Valid M C m)
    {Pairs Table : M.Domain} (hTable : DifferenceTable M C Pairs Table) (source target Box : M.Domain) :
    Project.Formula.satisfies ((((extractionStepEnv C m R Pairs Table).push source).push target).push Box) extractionStepMatrix.body ↔
      ∃ V, M.mem V R.values ∧ ∃ P, M.mem P R.forests ∧ ∃ W, M.mem W R.values ∧ ∃ Q, M.mem Q R.forests ∧
        ∃ H, M.mem H Box ∧ ∃ Heights, M.mem Heights Box ∧ ∃ F, M.mem F R.forests ∧
          Codes M source V P ∧ Codes M target W Q ∧ RootedRow M C m V P ∧ RowRun M C m R V P H ∧
            HeightGraph M C m R V H Heights ∧ TopValueGraph M C m R H Heights W ∧ PseudoForest M C m R H Heights F ∧ Selects true M C m F W Q := by
  let e := (((extractionStepEnv C m R Pairs Table).push source).push target).push Box
  have hInner (V P W Q H Heights F : M.Domain) := extractionInnerFormula_iff hM
    (((((((e.push V).push P).push W).push Q).push H).push Heights).push F) extractionTerms extractionSpaceTerms
    (.bound 15) (.bound 11) (.bound 10) (.bound 9) (.bound 8) (.bound 6) (.bound 5) (.bound 4) (.bound 3) (.bound 2) (.bound 1) (.bound 0) hC hR hTable
  simp only [extractionStepMatrix,Project.Formula.satisfies_existsMem_iff]
  constructor
  · rintro ⟨V,hV,P,hP,W,hW,Q,hQ,H,hH,Heights,hHeights,F,hF,hSat⟩
    exact ⟨V,hV,P,hP,W,hW,Q,hQ,H,hH,Heights,hHeights,F,hF,(hInner V P W Q H Heights F).mp hSat⟩
  · rintro ⟨V,hV,P,hP,W,hW,Q,hQ,H,hH,Heights,hHeights,F,hF,hSat⟩
    exact ⟨V,hV,P,hP,W,hW,Q,hQ,H,hH,Heights,hHeights,F,hF,(hInner V P W Q H Heights F).mpr hSat⟩

theorem extraction_step_exists_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory) {C : ExpressionData M.Domain} (hC : C.Valid M)
    {m : M.Domain} {R : RowStateSpace M.Domain} (hR : R.Valid M C m) {Pairs Table : M.Domain} (hTable : DifferenceTable M C Pairs Table)
    {source V P : M.Domain} (hBase : RootedRow M C m V P) (hCode : Codes M source V P) :
    ∃ target Box, Project.Formula.satisfies ((((extractionStepEnv C m R Pairs Table).push source).push target).push Box) extractionStepMatrix.body := by
  obtain ⟨Top,Q,hExtraction⟩ := extraction_exists_d hM hC hBase.row
  obtain ⟨R',H,Heights,F,hRun,hHeights,hTop,hPseudo,hSelected⟩ := hExtraction
  have hRR := row_state_space_unique hM.1 hRun.space hR
  subst R'
  obtain ⟨target,hTarget⟩ := codes_total hM Top Q
  obtain ⟨Box,hBox⟩ := SetTheory.KP.exists_pair (KP1Y.models_weakKP hM) H Heights
  refine ⟨target,Box,(extractionStepMatrix_iff hM hC hR hTable source target Box).mpr ?_⟩
  exact ⟨V,(hR.values V).mpr hBase.row.values,P,(hR.forests P).mpr hBase.row.forest,
    Top,(hR.values Top).mpr hTop.graph,Q,(hR.forests Q).mpr hSelected.forest,
    H,(hBox H).mpr (Or.inl rfl),Heights,(hBox Heights).mpr (Or.inr rfl),F,(hR.forests F).mpr hPseudo.forest,
    hCode,hTarget,hBase,hRun,hHeights,hTop,hPseudo,hSelected⟩

end KP1Y.OneYFinite
