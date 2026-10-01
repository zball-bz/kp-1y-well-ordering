import KP1Y.OneYCopiedMountain

/-! 复制山形的字面有界语法；代码只打包实际高度图与父行图，不预设函数幂集。 -/
namespace KP1Y.OneYFinite.CopiedMountain
open YesMetaZFC YesMetaZFC.SetTheory YesMetaZFC.SetTheory.Definitional
open KP1Y.Kuratowski KP1Y.Functions KP1Y.Naturals KP1Y.Bounded
universe u

def forestRowsFormula {n : Nat} (C : ExpressionData (Project.Term n)) (X : Data (Project.Term n)) : Project.Formula 1 n :=
  Project.Formula.forallMem C.omega (Project.Formula.forallMem X.forests.weaken
    (.imp (memPairFormula X.parents.weaken.weaken (.bound 1) (.bound 0))
      (forestFormula C.omega.weaken.weaken X.width.weaken.weaken (.bound 0))))

def sourceFormula {n : Nat} (C : ExpressionData (Project.Term n)) (X : Data (Project.Term n)) : Project.Formula 1 n :=
  Project.Formula.forallMem C.omega (Project.Formula.forallMem X.width.weaken (Project.Formula.forallMem C.omega.weaken.weaken
    (.imp (memPairFormula X.heights.weaken.weaken.weaken (.bound 1) (.bound 0))
      (.iff (Project.Formula.existsMem X.width.weaken.weaken.weaken
        (parentAtFormula X.weaken.weaken.weaken.weaken (.bound 3) (.bound 2) (.bound 0))) (.mem (.bound 2) (.bound 0))))))

def endpointFormula {n : Nat} (C : ExpressionData (Project.Term n)) (X : Data (Project.Term n)) : Project.Formula 1 n :=
  Project.Formula.forallMem C.omega (Project.Formula.forallMem X.width.weaken (Project.Formula.forallMem X.width.weaken.weaken
    (Project.Formula.forallMem C.omega.weaken.weaken.weaken
      (.imp (.conj (parentAtFormula X.weaken.weaken.weaken.weaken (.bound 3) (.bound 2) (.bound 1))
        (memPairFormula X.heights.weaken.weaken.weaken.weaken (.bound 1) (.bound 0)))
        (.disj (Project.Formula.extensionalEq (.bound 3) (.bound 0)) (.mem (.bound 3) (.bound 0)))))))

def validFormula {n : Nat} (C : ExpressionData (Project.Term n)) (X : Data (Project.Term n)) : Project.Formula 1 n :=
  .conj (.mem X.width C.omega) (.conj (graphFormula X.heights X.width C.omega)
    (.conj (graphFormula X.parents C.omega X.forests)
      (.conj (forestRowsFormula C X) (.conj (sourceFormula C X) (endpointFormula C X)))))

theorem forestRowsFormula_delta0 {n : Nat} (C : ExpressionData (Project.Term n)) (X : Data (Project.Term n)) :
    (forestRowsFormula C X).IsDelta0 := .forallMem _ (.forallMem _ (.imp (memPairFormula_delta0 _ _ _) (forestFormula_delta0 _ _ _)))

theorem sourceFormula_delta0 {n : Nat} (C : ExpressionData (Project.Term n)) (X : Data (Project.Term n)) :
    (sourceFormula C X).IsDelta0 := .forallMem _ (.forallMem _ (.forallMem _ (.imp (memPairFormula_delta0 _ _ _)
      (.iff (.existsMem _ (parentAtFormula_delta0 _ _ _ _)) (.mem _ _)))))

theorem endpointFormula_delta0 {n : Nat} (C : ExpressionData (Project.Term n)) (X : Data (Project.Term n)) :
    (endpointFormula C X).IsDelta0 := .forallMem _ (.forallMem _ (.forallMem _ (.forallMem _
      (.imp (.conj (parentAtFormula_delta0 _ _ _ _) (memPairFormula_delta0 _ _ _)) (.disj (.atom _ _ _) (.mem _ _))))))

theorem validFormula_delta0 {n : Nat} (C : ExpressionData (Project.Term n)) (X : Data (Project.Term n)) :
    (validFormula C X).IsDelta0 := .conj (.mem _ _) (.conj (graphFormula_delta0 _ _ _) (.conj (graphFormula_delta0 _ _ _)
      (.conj (forestRowsFormula_delta0 _ _) (.conj (sourceFormula_delta0 _ _) (endpointFormula_delta0 _ _)))))

theorem forestRowsFormula_freeClosed {n : Nat} {C : ExpressionData (Project.Term n)} (hC : C.Closed)
    {X : Data (Project.Term n)} (hX : X.Closed) : (forestRowsFormula C X).FreeClosed := by
  simp [forestRowsFormula,forestFormula,memPairFormula,codeFormula,pairFormula,Project.Formula.forallMem,
    Project.Formula.existsMem,Definitional.Formula.FreeClosed,hC.omega,hX.width,hX.forests,hX.parents]

theorem sourceFormula_freeClosed {n : Nat} {C : ExpressionData (Project.Term n)} (hC : C.Closed)
    {X : Data (Project.Term n)} (hX : X.Closed) : (sourceFormula C X).FreeClosed := by
  have hParent := parentAtFormula_freeClosed hX.weaken.weaken.weaken.weaken (.bound 3) (.bound 2) (.bound 0) rfl rfl rfl
  simp [sourceFormula,memPairFormula,codeFormula,pairFormula,Project.Formula.forallMem,
    Project.Formula.existsMem,Definitional.Formula.FreeClosed,hC.omega,hX.width,hX.heights,hParent]

theorem endpointFormula_freeClosed {n : Nat} {C : ExpressionData (Project.Term n)} (hC : C.Closed)
    {X : Data (Project.Term n)} (hX : X.Closed) : (endpointFormula C X).FreeClosed := by
  have hParent := parentAtFormula_freeClosed hX.weaken.weaken.weaken.weaken (.bound 3) (.bound 2) (.bound 1) rfl rfl rfl
  simp [endpointFormula,memPairFormula,codeFormula,pairFormula,Project.Formula.forallMem,
    Project.Formula.existsMem,Definitional.Formula.FreeClosed,hC.omega,hX.width,hX.heights,hParent]

theorem validFormula_freeClosed {n : Nat} {C : ExpressionData (Project.Term n)} (hC : C.Closed)
    {X : Data (Project.Term n)} (hX : X.Closed) : (validFormula C X).FreeClosed := by
  have hF := forestRowsFormula_freeClosed hC hX
  have hS := sourceFormula_freeClosed hC hX
  have hE := endpointFormula_freeClosed hC hX
  simp [validFormula,graphFormula,memPairFormula,codeFormula,pairFormula,Project.Formula.forallMem,
    Project.Formula.existsMem,Definitional.Formula.FreeClosed,hC.omega,hX.width,hX.heights,hX.parents,hX.forests,hF,hS,hE]

theorem forestRowsFormula_iff {M : SetTheory.Structure.{u}} (he : Extensional M) {n : Nat} (e : Env M n)
    (C : ExpressionData (Project.Term n)) (X : Data (Project.Term n)) : Project.Formula.satisfies e (forestRowsFormula C X) ↔
      ∀r, M.mem r (C.eval e).omega → ∀F, M.mem F (X.eval e).forests → MemPair M (X.eval e).parents r F → Forest M (C.eval e).omega (X.eval e).width F := by
  simp only [forestRowsFormula,Project.Formula.satisfies_forallMem_iff,Project.Formula.satisfies_imp_iff,
    memPairFormula_iff he,forestFormula_iff he,Term.eval_weaken]
  rfl

theorem sourceFormula_iff {M : SetTheory.Structure.{u}} (he : Extensional M) {n : Nat} (e : Env M n)
    (C : ExpressionData (Project.Term n)) (X : Data (Project.Term n)) : Project.Formula.satisfies e (sourceFormula C X) ↔
      ∀r, M.mem r (C.eval e).omega → ∀c, M.mem c (X.eval e).width → ∀h, M.mem h (C.eval e).omega →
        MemPair M (X.eval e).heights c h → ((∃p, M.mem p (X.eval e).width ∧ ParentAt M (X.eval e) r c p) ↔ M.mem r h) := by
  simp only [sourceFormula,Project.Formula.satisfies_forallMem_iff,Project.Formula.satisfies_imp_iff,
    Project.Formula.satisfies_iff_iff,Project.Formula.satisfies_existsMem_iff,Project.Formula.satisfies_mem_iff,
    memPairFormula_iff he,parentAtFormula_iff he,Data.eval_weaken,Term.eval_weaken]
  rfl

theorem endpointFormula_iff {M : SetTheory.Structure.{u}} (he : Extensional M) {n : Nat} (e : Env M n)
    (C : ExpressionData (Project.Term n)) (X : Data (Project.Term n)) : Project.Formula.satisfies e (endpointFormula C X) ↔
      ∀r, M.mem r (C.eval e).omega → ∀c, M.mem c (X.eval e).width → ∀p, M.mem p (X.eval e).width →
        ∀h, M.mem h (C.eval e).omega → ParentAt M (X.eval e) r c p → MemPair M (X.eval e).heights p h → r=h ∨ M.mem r h := by
  simp only [endpointFormula,Project.Formula.satisfies_forallMem_iff,Project.Formula.satisfies_imp_iff,
    Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_disj_iff,Project.Formula.satisfies_extensionalEq_iff_eq he,
    Project.Formula.satisfies_mem_iff,parentAtFormula_iff he,memPairFormula_iff he,Data.eval_weaken,Term.eval_weaken]
  exact ⟨fun h r hr c hc p hp v hv hP hV => h r hr c hc p hp v hv ⟨hP,hV⟩,
    fun h r hr c hc p hp v hv hs => h r hr c hc p hp v hv hs.1 hs.2⟩

theorem validFormula_iff {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory) {n : Nat} (e : Env M n)
    (C : ExpressionData (Project.Term n)) (X : Data (Project.Term n)) (hC : (C.eval e).Valid M) :
    Project.Formula.satisfies e (validFormula C X) ↔ (X.eval e).Valid M (C.eval e) := by
  simp only [validFormula,Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_mem_iff,
    graphFormula_iff hM.1,forestRowsFormula_iff hM.1,sourceFormula_iff hM.1,endpointFormula_iff hM.1]
  constructor
  · rintro ⟨hWidth,hHeights,hParents,hForests,hSource,hEndpoint⟩
    have hForest (r F : M.Domain) (hAt : MemPair M (X.eval e).parents r F) : Forest M (C.eval e).omega (X.eval e).width F :=
      hForests r (hParents.bounds hM.1 hAt).1 F (hParents.bounds hM.1 hAt).2 hAt
    have hBounds (r c p : M.Domain) (hAt : ParentAt M (X.eval e) r c p) :
        M.mem r (C.eval e).omega ∧ M.mem c (X.eval e).width ∧ M.mem p (X.eval e).width := by
      obtain ⟨F,_,hRow,hAt⟩ := hAt
      exact ⟨(hParents.bounds hM.1 hRow).1,(hForest r F hRow).bounds hM.1 hAt⟩
    refine ⟨hWidth,hHeights,hParents,hForest,?_,?_⟩
    · intro r c h hHeight
      obtain ⟨hc,hh⟩ := hHeights.bounds hM.1 hHeight
      constructor
      · rintro ⟨p,hP⟩
        have hB := hBounds r c p hP
        exact (hSource r hB.1 c hc h hh hHeight).mp ⟨p,hB.2.2,hP⟩
      · intro hrh
        have hr := (omega_isOrdinal_d hM hC.omega).transitive h hh r hrh
        obtain ⟨p,_,hP⟩ := (hSource r hr c hc h hh hHeight).mpr hrh
        exact ⟨p,hP⟩
    · intro r c p h hP hHeight
      have hB := hBounds r c p hP
      exact hEndpoint r hB.1 c hB.2.1 p hB.2.2 h (hHeights.bounds hM.1 hHeight).2 hP hHeight
  · intro h
    refine ⟨h.width,h.heights,h.parents,fun r _ F _ hAt => h.forest r F hAt,?_,?_⟩
    · intro r _ c _ height _ hHeight
      exact ⟨fun ⟨p,_,hP⟩ => (h.source r c height hHeight).mp ⟨p,hP⟩,fun hr => by
        obtain ⟨p,hP⟩ := (h.source r c height hHeight).mpr hr
        exact ⟨p,(hP.bounds hM.1 h).2.2.1,hP⟩⟩
    · exact fun r _ c _ p _ height _ hP hHeight => h.endpoint r c p height hP hHeight

def runRowFormula {n : Nat} (R : RowStateSpace (Project.Term n)) (H r F : Project.Term n) : Project.Formula 1 n :=
  Project.Formula.existsMem R.values (rowAtFormula R.states.weaken H.weaken r.weaken (.bound 0) F.weaken)

def parentRunFormula {n : Nat} (C : ExpressionData (Project.Term n)) (R : RowStateSpace (Project.Term n))
    (H : Project.Term n) (X : Data (Project.Term n)) : Project.Formula 1 n :=
  Project.Formula.forallMem C.omega (.conj
    (Project.Formula.forallMem X.forests.weaken (.imp (memPairFormula X.parents.weaken.weaken (.bound 1) (.bound 0))
      (runRowFormula R.weaken.weaken H.weaken.weaken (.bound 1) (.bound 0))))
    (Project.Formula.forallMem R.forests.weaken (.imp (runRowFormula R.weaken.weaken H.weaken.weaken (.bound 1) (.bound 0))
      (memPairFormula X.parents.weaken.weaken (.bound 1) (.bound 0)))))

def fromRunFormula {n : Nat} (C : ExpressionData (Project.Term n)) (m : Project.Term n) (R : RowStateSpace (Project.Term n))
    (V H : Project.Term n) (X : Data (Project.Term n)) : Project.Formula 1 n :=
  .conj (Project.Formula.extensionalEq X.width m) (.conj (heightGraphFormula C m R V H X.heights) (parentRunFormula C R H X))

def validFromRunFormula {n : Nat} (C : ExpressionData (Project.Term n)) (m : Project.Term n) (R : RowStateSpace (Project.Term n))
    (V H : Project.Term n) (X : Data (Project.Term n)) : Project.Formula 1 n :=
  .conj (validFormula C X) (fromRunFormula C m R V H X)

theorem runRowFormula_delta0 {n : Nat} (R : RowStateSpace (Project.Term n)) (H r F : Project.Term n) :
    (runRowFormula R H r F).IsDelta0 := .existsMem _ (rowAtFormula_delta0 _ _ _ _ _)

theorem parentRunFormula_delta0 {n : Nat} (C : ExpressionData (Project.Term n)) (R : RowStateSpace (Project.Term n))
    (H : Project.Term n) (X : Data (Project.Term n)) : (parentRunFormula C R H X).IsDelta0 :=
  .forallMem _ (.conj (.forallMem _ (.imp (memPairFormula_delta0 _ _ _) (runRowFormula_delta0 _ _ _ _)))
    (.forallMem _ (.imp (runRowFormula_delta0 _ _ _ _) (memPairFormula_delta0 _ _ _))))

theorem fromRunFormula_delta0 {n : Nat} (C : ExpressionData (Project.Term n)) (m : Project.Term n) (R : RowStateSpace (Project.Term n))
    (V H : Project.Term n) (X : Data (Project.Term n)) : (fromRunFormula C m R V H X).IsDelta0 :=
  .conj (.atom _ _ _) (.conj (heightGraphFormula_delta0 _ _ _ _ _ _) (parentRunFormula_delta0 _ _ _ _))

theorem validFromRunFormula_delta0 {n : Nat} (C : ExpressionData (Project.Term n)) (m : Project.Term n) (R : RowStateSpace (Project.Term n))
    (V H : Project.Term n) (X : Data (Project.Term n)) : (validFromRunFormula C m R V H X).IsDelta0 :=
  .conj (validFormula_delta0 _ _) (fromRunFormula_delta0 _ _ _ _ _ _)

theorem runRowFormula_freeClosed {n : Nat} {R : RowStateSpace (Project.Term n)} (hR : R.Closed) (H r F : Project.Term n)
    (hH : H.freeSupport=[]) (hr : r.freeSupport=[]) (hF : F.freeSupport=[]) : (runRowFormula R H r F).FreeClosed := by
  simp [runRowFormula,rowAtFormula,memPairFormula,codeFormula,pairFormula,Project.Formula.forallMem,
    Project.Formula.existsMem,Definitional.Formula.FreeClosed,hR.values,hR.states,hH,hr,hF]

theorem parentRunFormula_freeClosed {n : Nat} {C : ExpressionData (Project.Term n)} (hC : C.Closed)
    {R : RowStateSpace (Project.Term n)} (hR : R.Closed) {X : Data (Project.Term n)} (hX : X.Closed)
    (H : Project.Term n) (hH : H.freeSupport=[]) : (parentRunFormula C R H X).FreeClosed := by
  have hRun := runRowFormula_freeClosed hR.weaken.weaken H.weaken.weaken (.bound 1) (.bound 0) (by simpa using hH) rfl rfl
  simp [parentRunFormula,memPairFormula,codeFormula,pairFormula,Project.Formula.forallMem,
    Project.Formula.existsMem,Definitional.Formula.FreeClosed,hC.omega,hR.forests,hX.forests,hX.parents,hRun]

theorem fromRunFormula_freeClosed {n : Nat} {C : ExpressionData (Project.Term n)} (hC : C.Closed)
    {R : RowStateSpace (Project.Term n)} (hR : R.Closed) {X : Data (Project.Term n)} (hX : X.Closed)
    (m V H : Project.Term n) (hm : m.freeSupport=[]) (hV : V.freeSupport=[]) (hH : H.freeSupport=[]) :
    (fromRunFormula C m R V H X).FreeClosed := by
  have hh := heightGraphFormula_freeClosed hC hR m V H X.heights hm hV hH hX.heights
  have hp := parentRunFormula_freeClosed hC hR hX H hH
  simp [fromRunFormula,Definitional.Formula.FreeClosed,hX.width,hm,hh,hp]

theorem validFromRunFormula_freeClosed {n : Nat} {C : ExpressionData (Project.Term n)} (hC : C.Closed)
    {R : RowStateSpace (Project.Term n)} (hR : R.Closed) {X : Data (Project.Term n)} (hX : X.Closed)
    (m V H : Project.Term n) (hm : m.freeSupport=[]) (hV : V.freeSupport=[]) (hH : H.freeSupport=[]) :
    (validFromRunFormula C m R V H X).FreeClosed := by
  have hv := validFormula_freeClosed hC hX
  have hf := fromRunFormula_freeClosed hC hR hX m V H hm hV hH
  simp [validFromRunFormula,Definitional.Formula.FreeClosed,hv,hf]

theorem runRowFormula_iff {M : SetTheory.Structure.{u}} (he : Extensional M) {n : Nat} (e : Env M n)
    (R : RowStateSpace (Project.Term n)) (H r F : Project.Term n) : Project.Formula.satisfies e (runRowFormula R H r F) ↔
      ∃U, M.mem U (R.eval e).values ∧ RowAt M (R.eval e).states (H.eval e) (r.eval e) U (F.eval e) := by
  simp only [runRowFormula,Project.Formula.satisfies_existsMem_iff,rowAtFormula_iff he,Term.eval_weaken]
  rfl

theorem parentRunFormula_iff {M : SetTheory.Structure.{u}} (he : Extensional M) {n : Nat} (e : Env M n)
    (C : ExpressionData (Project.Term n)) (R : RowStateSpace (Project.Term n)) (H : Project.Term n) (X : Data (Project.Term n)) :
    Project.Formula.satisfies e (parentRunFormula C R H X) ↔
      ∀r, M.mem r (C.eval e).omega →
        (∀F, M.mem F (X.eval e).forests → MemPair M (X.eval e).parents r F → ∃U, M.mem U (R.eval e).values ∧ RowAt M (R.eval e).states (H.eval e) r U F) ∧
        (∀F, M.mem F (R.eval e).forests → (∃U, M.mem U (R.eval e).values ∧ RowAt M (R.eval e).states (H.eval e) r U F) → MemPair M (X.eval e).parents r F) := by
  simp only [parentRunFormula,Project.Formula.satisfies_forallMem_iff,Project.Formula.satisfies_conj_iff,
    Project.Formula.satisfies_imp_iff,memPairFormula_iff he,runRowFormula_iff he,RowStateSpace.eval_weaken,Term.eval_weaken]
  rfl

/-- 原FromRun的无界父行等价，由两边已有实际图的界还原。 -/
theorem fromRunFormula_iff {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory) {n : Nat} (e : Env M n)
    (C : ExpressionData (Project.Term n)) (m : Project.Term n) (R : RowStateSpace (Project.Term n))
    (V H : Project.Term n) (X : Data (Project.Term n)) (hC : (C.eval e).Valid M) {P : M.Domain}
    (hRun : RowRun M (C.eval e) (m.eval e) (R.eval e) (V.eval e) P (H.eval e)) (hX : (X.eval e).Valid M (C.eval e)) :
    Project.Formula.satisfies e (fromRunFormula C m R V H X) ↔ FromRun M (C.eval e) (m.eval e) (R.eval e) (V.eval e) (H.eval e) (X.eval e) := by
  simp only [fromRunFormula,Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_extensionalEq_iff_eq hM.1,
    heightGraphFormula_iff hM _ _ _ _ _ _ _ hC,parentRunFormula_iff hM.1]
  have hBounds {r U F : M.Domain} (hAt : RowAt M (R.eval e).states (H.eval e) r U F) :
      M.mem r (C.eval e).omega ∧ M.mem U (R.eval e).values ∧ M.mem F (R.eval e).forests := by
    have hN := hRun.at_numeric_d hM hC hAt
    obtain ⟨state,_,hState,_⟩ := hAt
    exact ⟨(hRun.graph.bounds hM.1 hState).1,(hRun.space.values U).mpr hN.values,(hRun.space.forests F).mpr hN.forest⟩
  constructor
  · rintro ⟨hWidth,hHeight,hRows⟩
    refine ⟨hWidth,hHeight,fun r F => ?_⟩
    constructor
    · intro hAt
      obtain ⟨U,_,hRow⟩ := (hRows r (hX.parents.bounds hM.1 hAt).1).1 F (hX.parents.bounds hM.1 hAt).2 hAt
      exact ⟨U,hRow⟩
    · rintro ⟨U,hRow⟩
      have hB := hBounds hRow
      exact (hRows r hB.1).2 F hB.2.2 ⟨U,hB.2.1,hRow⟩
  · intro h
    refine ⟨h.width,h.heights,fun r _ => ⟨?_,?_⟩⟩
    · intro F _ hAt
      obtain ⟨U,hRow⟩ := (h.parents r F).mp hAt
      exact ⟨U,(hBounds hRow).2.1,hRow⟩
    · rintro F _ ⟨U,_,hRow⟩
      exact (h.parents r F).mpr ⟨U,hRow⟩

theorem validFromRunFormula_iff {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory) {n : Nat} (e : Env M n)
    (C : ExpressionData (Project.Term n)) (m : Project.Term n) (R : RowStateSpace (Project.Term n))
    (V H : Project.Term n) (X : Data (Project.Term n)) (hC : (C.eval e).Valid M) {P : M.Domain}
    (hRun : RowRun M (C.eval e) (m.eval e) (R.eval e) (V.eval e) P (H.eval e)) :
    Project.Formula.satisfies e (validFromRunFormula C m R V H X) ↔
      (X.eval e).Valid M (C.eval e) ∧ FromRun M (C.eval e) (m.eval e) (R.eval e) (V.eval e) (H.eval e) (X.eval e) := by
  rw [validFromRunFormula,Project.Formula.satisfies_conj_iff,validFormula_iff hM e C X hC]
  exact ⟨fun h => ⟨h.1,(fromRunFormula_iff hM e C m R V H X hC hRun h.1).mp h.2⟩,
    fun h => ⟨h.1,(fromRunFormula_iff hM e C m R V H X hC hRun h.1).mpr h.2⟩⟩

/-- 三个绑定变量依次是代码的双元成员、heights、parents。 -/
def withCodeFormula {n : Nat} (code : Project.Term n) (body : Project.Formula 1 (n+3)) : Project.Formula 1 n :=
  Project.Formula.existsMem code (Project.Formula.existsMem (.bound 0) (Project.Formula.existsMem (.bound 1)
    (.conj (codeFormula code.weaken.weaken.weaken (.bound 1) (.bound 0)) body)))

theorem withCodeFormula_delta0 {n : Nat} (code : Project.Term n) {body : Project.Formula 1 (n+3)} (hBody : body.IsDelta0) :
    (withCodeFormula code body).IsDelta0 := .existsMem _ (.existsMem _ (.existsMem _ (.conj (codeFormula_delta0 _ _ _) hBody)))

theorem withCodeFormula_freeClosed {n : Nat} (code : Project.Term n) {body : Project.Formula 1 (n+3)}
    (hCode : code.freeSupport=[]) (hBody : body.FreeClosed) : (withCodeFormula code body).FreeClosed := by
  simp [withCodeFormula,codeFormula,pairFormula,Project.Formula.existsMem,Project.Formula.forallMem,Definitional.Formula.FreeClosed,hCode,hBody]

theorem code_component_container {M : SetTheory.Structure.{u}} {code heights parents : M.Domain}
    (h : Codes M code heights parents) : ∃b, M.mem b code ∧ M.mem heights b ∧ M.mem parents b := by
  obtain ⟨a,b,_,hB,hCode⟩ := h
  exact ⟨b,(hCode b).mpr (.inr rfl),(hB heights).mpr (.inl rfl),(hB parents).mpr (.inr rfl)⟩

theorem withCodeFormula_iff {M : SetTheory.Structure.{u}} (he : Extensional M) {n : Nat} (e : Env M n)
    (code : Project.Term n) (body : Project.Formula 1 (n+3)) : Project.Formula.satisfies e (withCodeFormula code body) ↔
      ∃b, M.mem b (code.eval e) ∧ ∃heights, M.mem heights b ∧ ∃parents, M.mem parents b ∧ Codes M (code.eval e) heights parents ∧
        Project.Formula.satisfies (((e.push b).push heights).push parents) body := by
  simp only [withCodeFormula,Project.Formula.satisfies_existsMem_iff,Project.Formula.satisfies_conj_iff,codeFormula_iff he,Term.eval_weaken]
  rfl

/-- 代码自身提供组件界；此定理不构造或假设代码的总体空间。 -/
theorem withCodeFormula_iff_exists {M : SetTheory.Structure.{u}} (he : Extensional M) {n : Nat} (e : Env M n)
    (code : Project.Term n) (body : Project.Formula 1 (n+3)) (P : M.Domain → M.Domain → Prop)
    (hBody : ∀b heights parents, Project.Formula.satisfies (((e.push b).push heights).push parents) body ↔ P heights parents) :
    Project.Formula.satisfies e (withCodeFormula code body) ↔ ∃heights parents, Codes M (code.eval e) heights parents ∧ P heights parents := by
  rw [withCodeFormula_iff he]
  constructor
  · rintro ⟨b,_,heights,_,parents,_,hCode,hφ⟩
    exact ⟨heights,parents,hCode,(hBody b heights parents).mp hφ⟩
  · rintro ⟨heights,parents,hCode,hP⟩
    obtain ⟨b,hb,hh,hp⟩ := code_component_container hCode
    exact ⟨b,hb,heights,hh,parents,hp,hCode,(hBody b heights parents).mpr hP⟩

def CodeValid (M : SetTheory.Structure.{u}) (C : ExpressionData M.Domain) (width Forests code : M.Domain) : Prop :=
  ∃heights parents, Codes M code heights parents ∧ (⟨width,heights,Forests,parents⟩ : Data M.Domain).Valid M C

def codeValidFormula {n : Nat} (C : ExpressionData (Project.Term n)) (width Forests code : Project.Term n) : Project.Formula 1 n :=
  withCodeFormula code (validFormula C.weaken.weaken.weaken ⟨width.weaken.weaken.weaken,.bound 1,Forests.weaken.weaken.weaken,.bound 0⟩)

theorem codeValidFormula_delta0 {n : Nat} (C : ExpressionData (Project.Term n)) (width Forests code : Project.Term n) :
    (codeValidFormula C width Forests code).IsDelta0 := withCodeFormula_delta0 _ (validFormula_delta0 _ _)

theorem codeValidFormula_freeClosed {n : Nat} {C : ExpressionData (Project.Term n)} (hC : C.Closed)
    (width Forests code : Project.Term n) (hWidth : width.freeSupport=[]) (hForests : Forests.freeSupport=[]) (hCode : code.freeSupport=[]) :
    (codeValidFormula C width Forests code).FreeClosed :=
  withCodeFormula_freeClosed _ hCode (validFormula_freeClosed hC.weaken.weaken.weaken
    ⟨by simpa using hWidth,rfl,by simpa using hForests,rfl⟩)

theorem codeValidFormula_iff {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory) {n : Nat} (e : Env M n)
    (C : ExpressionData (Project.Term n)) (width Forests code : Project.Term n) (hC : (C.eval e).Valid M) :
    Project.Formula.satisfies e (codeValidFormula C width Forests code) ↔ CodeValid M (C.eval e) (width.eval e) (Forests.eval e) (code.eval e) := by
  apply withCodeFormula_iff_exists hM.1 e code _ (fun heights parents => (⟨width.eval e,heights,Forests.eval e,parents⟩ : Data M.Domain).Valid M (C.eval e))
  intro b heights parents
  have h := validFormula_iff hM (((e.push b).push heights).push parents) C.weaken.weaken.weaken
    ⟨width.weaken.weaken.weaken,.bound 1,Forests.weaken.weaken.weaken,.bound 0⟩ (by simpa only [ExpressionData.eval_weaken] using hC)
  simpa only [ExpressionData.eval_weaken,Data.eval,Data.map,Term.eval_weaken,Project.Term.eval_bound_one_push,Project.Term.eval_bound_zero_push] using h

theorem CodeValid.read {M : SetTheory.Structure.{u}} (he : Extensional M) {C : ExpressionData M.Domain}
    {width Forests code heights parents : M.Domain} (h : CodeValid M C width Forests code) (hCode : Codes M code heights parents) :
    (⟨width,heights,Forests,parents⟩ : Data M.Domain).Valid M C := by
  obtain ⟨heights',parents',hCode',hValid⟩ := h
  obtain ⟨hh,hp⟩ := codes_injective he hCode' hCode
  subst heights'
  subst parents'
  exact hValid

theorem code_valid_exists_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} {X : Data M.Domain} (hX : X.Valid M C) :
    ∃code, Codes M code X.heights X.parents ∧ CodeValid M C X.width X.forests code := by
  obtain ⟨code,hCode⟩ := codes_total hM X.heights X.parents
  exact ⟨code,hCode,X.heights,X.parents,hCode,hX⟩

def CodeFromRun (M : SetTheory.Structure.{u}) (C : ExpressionData M.Domain) (m : M.Domain) (R : RowStateSpace M.Domain)
    (V H Forests code : M.Domain) : Prop :=
  ∃heights parents, Codes M code heights parents ∧ (⟨m,heights,Forests,parents⟩ : Data M.Domain).Valid M C ∧
    FromRun M C m R V H ⟨m,heights,Forests,parents⟩

def codeFromRunFormula {n : Nat} (C : ExpressionData (Project.Term n)) (m : Project.Term n) (R : RowStateSpace (Project.Term n))
    (V H Forests code : Project.Term n) : Project.Formula 1 n :=
  withCodeFormula code (validFromRunFormula C.weaken.weaken.weaken m.weaken.weaken.weaken R.weaken.weaken.weaken
    V.weaken.weaken.weaken H.weaken.weaken.weaken ⟨m.weaken.weaken.weaken,.bound 1,Forests.weaken.weaken.weaken,.bound 0⟩)

theorem codeFromRunFormula_delta0 {n : Nat} (C : ExpressionData (Project.Term n)) (m : Project.Term n) (R : RowStateSpace (Project.Term n))
    (V H Forests code : Project.Term n) : (codeFromRunFormula C m R V H Forests code).IsDelta0 :=
  withCodeFormula_delta0 _ (validFromRunFormula_delta0 _ _ _ _ _ _)

theorem codeFromRunFormula_freeClosed {n : Nat} {C : ExpressionData (Project.Term n)} (hC : C.Closed)
    {R : RowStateSpace (Project.Term n)} (hR : R.Closed) (m V H Forests code : Project.Term n)
    (hm : m.freeSupport=[]) (hV : V.freeSupport=[]) (hH : H.freeSupport=[]) (hForests : Forests.freeSupport=[]) (hCode : code.freeSupport=[]) :
    (codeFromRunFormula C m R V H Forests code).FreeClosed :=
  withCodeFormula_freeClosed _ hCode (validFromRunFormula_freeClosed hC.weaken.weaken.weaken hR.weaken.weaken.weaken
    ⟨by simpa using hm,rfl,by simpa using hForests,rfl⟩ _ _ _ (by simpa using hm) (by simpa using hV) (by simpa using hH))

theorem codeFromRunFormula_iff {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory) {n : Nat} (e : Env M n)
    (C : ExpressionData (Project.Term n)) (m : Project.Term n) (R : RowStateSpace (Project.Term n)) (V H Forests code : Project.Term n)
    (hC : (C.eval e).Valid M) {P : M.Domain} (hRun : RowRun M (C.eval e) (m.eval e) (R.eval e) (V.eval e) P (H.eval e)) :
    Project.Formula.satisfies e (codeFromRunFormula C m R V H Forests code) ↔
      CodeFromRun M (C.eval e) (m.eval e) (R.eval e) (V.eval e) (H.eval e) (Forests.eval e) (code.eval e) := by
  apply withCodeFormula_iff_exists hM.1 e code _ (fun heights parents =>
    (⟨m.eval e,heights,Forests.eval e,parents⟩ : Data M.Domain).Valid M (C.eval e) ∧
      FromRun M (C.eval e) (m.eval e) (R.eval e) (V.eval e) (H.eval e) ⟨m.eval e,heights,Forests.eval e,parents⟩)
  intro b heights parents
  have h := validFromRunFormula_iff hM (((e.push b).push heights).push parents) C.weaken.weaken.weaken m.weaken.weaken.weaken
    R.weaken.weaken.weaken V.weaken.weaken.weaken H.weaken.weaken.weaken ⟨m.weaken.weaken.weaken,.bound 1,Forests.weaken.weaken.weaken,.bound 0⟩
    (by simpa only [ExpressionData.eval_weaken] using hC)
    (by simpa only [ExpressionData.eval_weaken,RowStateSpace.eval_weaken,Term.eval_weaken] using hRun)
  simpa only [ExpressionData.eval_weaken,RowStateSpace.eval_weaken,Data.eval,Data.map,Term.eval_weaken,
    Project.Term.eval_bound_one_push,Project.Term.eval_bound_zero_push] using h

theorem CodeFromRun.read {M : SetTheory.Structure.{u}} (he : Extensional M) {C : ExpressionData M.Domain}
    {m : M.Domain} {R : RowStateSpace M.Domain} {V H Forests code heights parents : M.Domain}
    (h : CodeFromRun M C m R V H Forests code) (hCode : Codes M code heights parents) :
    (⟨m,heights,Forests,parents⟩ : Data M.Domain).Valid M C ∧ FromRun M C m R V H ⟨m,heights,Forests,parents⟩ := by
  obtain ⟨heights',parents',hCode',hValid⟩ := h
  obtain ⟨hh,hp⟩ := codes_injective he hCode' hCode
  subst heights'
  subst parents'
  exact hValid

theorem code_from_run_exists_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} {m : M.Domain} {R : RowStateSpace M.Domain} {V H : M.Domain} {X : Data M.Domain}
    (hX : X.Valid M C) (hFrom : FromRun M C m R V H X) :
    ∃code, Codes M code X.heights X.parents ∧ CodeFromRun M C m R V H X.forests code := by
  obtain ⟨code,hCode⟩ := codes_total hM X.heights X.parents
  have hData : (⟨m,X.heights,X.forests,X.parents⟩ : Data M.Domain)=X := by
    have hWidth := hFrom.width
    cases X
    simp_all
  exact ⟨code,hCode,X.heights,X.parents,hCode,hData.symm ▸ hX,hData.symm ▸ hFrom⟩

theorem CodeFromRun.unique {M : SetTheory.Structure.{u}} (he : Extensional M) {C : ExpressionData M.Domain}
    {m : M.Domain} {R : RowStateSpace M.Domain} {V H Forests code code' : M.Domain}
    (h : CodeFromRun M C m R V H Forests code) (h' : CodeFromRun M C m R V H Forests code') : code=code' := by
  obtain ⟨heights,parents,hCode,hX,hFrom⟩ := h
  obtain ⟨heights',parents',hCode',hX',hFrom'⟩ := h'
  have hh : heights=heights' := hFrom.heights.unique he hFrom'.heights
  have hp : parents=parents' := hX.parents.ext he hX'.parents (fun r _ F => (hFrom.parents r F).trans (hFrom'.parents r F).symm)
  subst heights'
  subst parents'
  exact codes_unique he hCode hCode'

/-- 保留实际高度/父行图，仅将辅助森林载体规范为既有RowStateSpace的森林集合。 -/
theorem FromRun.canonical_forests_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {m : M.Domain} {R : RowStateSpace M.Domain} {V P H : M.Domain}
    (hRun : RowRun M C m R V P H) {X : Data M.Domain} (hX : X.Valid M C) (hFrom : FromRun M C m R V H X) :
    (⟨m,X.heights,R.forests,X.parents⟩ : Data M.Domain).Valid M C ∧
      FromRun M C m R V H ⟨m,X.heights,R.forests,X.parents⟩ := by
  let Y : Data M.Domain := ⟨m,X.heights,R.forests,X.parents⟩
  have hRange (r F : M.Domain) (hAt : MemPair M X.parents r F) : M.mem F R.forests := by
    obtain ⟨U,hRow⟩ := (hFrom.parents r F).mp hAt
    exact (hRun.space.forests F).mpr (hRun.at_numeric_d hM hC hRow).forest
  have hParents : Graph M X.parents C.omega R.forests := KP1Y.Assignments.graph_tighten_values hX.parents hRange
  have hParentIff (r c p : M.Domain) : ParentAt M Y r c p ↔ ParentAt M X r c p := by
    exact ⟨fun ⟨F,_,hAt,hP⟩ => ⟨F,(hX.parents.bounds hM.1 hAt).2,hAt,hP⟩,
      fun ⟨F,_,hAt,hP⟩ => ⟨F,hRange r F hAt,hAt,hP⟩⟩
  refine ⟨⟨hRun.space.width,hFrom.heights.graph,hParents,?_,?_,?_⟩,⟨rfl,hFrom.heights,hFrom.parents⟩⟩
  · intro r F hAt
    exact hFrom.width ▸ hX.forest r F hAt
  · intro r c height hHeight
    exact (⟨fun ⟨p,hP⟩ => ⟨p,(hParentIff r c p).mp hP⟩,fun ⟨p,hP⟩ => ⟨p,(hParentIff r c p).mpr hP⟩⟩ :
      (∃p,ParentAt M Y r c p) ↔ ∃p,ParentAt M X r c p).trans (hX.source r c height hHeight)
  · intro r c p height hP hHeight
    exact hX.endpoint r c p height ((hParentIff r c p).mp hP) hHeight

/-- 固定width=m、Forests=R.forests的实际单点代码构造；不收集所有ω函数。 -/
theorem coded_from_run_exists_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {m : M.Domain} {R : RowStateSpace M.Domain} {V P H : M.Domain}
    (hRun : RowRun M C m R V P H) (hPositive : ∀c v, MemPair M V c v → M.mem C.zero v) :
    ∃code, CodeFromRun M C m R V H R.forests code := by
  obtain ⟨X,hX,hFrom⟩ := from_run_exists_d hM hC hRun hPositive
  obtain ⟨hY,hYFrom⟩ := hFrom.canonical_forests_d hM hC hRun hX
  obtain ⟨code,_,hCode⟩ := code_from_run_exists_d hM hY hYFrom
  exact ⟨code,hCode⟩

end KP1Y.OneYFinite.CopiedMountain
