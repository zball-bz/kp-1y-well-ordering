import KP1Y.OneYExpressionDiagramGraph
import KP1Y.OneYCopiedMountainSyntax
import KP1Y.OneYOrdinaryCopy
import KP1Y.OneYTerminalCopy
import KP1Y.OneYLowerCopy
import KP1Y.OneYCopyBranchSyntax

/-! 原 expandedMountain 的实际三分支有限塔，逐层读取真实计算出的数值山形。 -/
namespace KP1Y.OneYFinite.CopyTower
open YesMetaZFC YesMetaZFC.SetTheory YesMetaZFC.SetTheory.Definitional
open KP1Y.Kuratowski KP1Y.Functions KP1Y.Naturals KP1Y.Bounded
open KP1Y.OneYFinite.CopiedMountain
universe u

/-- 从完整层运行读取源山形的规范两字段code。辅助forest载体固定为L.rows.forests。 -/
def SourceAt (M : SetTheory.Structure.{u}) (C : ExpressionData M.Domain) (m : M.Domain)
    (L : LayerStateSpace M.Domain) (H k code : M.Domain) : Prop :=
  ∃ W Q, RowAt M L.states H k W Q ∧ ∃ J, RowRun M C m L.rows W Q J ∧ CodeFromRun M C m L.rows W J L.rows.forests code

theorem SourceAt.unique_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {m : M.Domain} {L : LayerStateSpace M.Domain} {V P H k code code' : M.Domain}
    (hLayers : LayerRun M C m L V P H) (h : SourceAt M C m L H k code) (h' : SourceAt M C m L H k code') : code=code' := by
  obtain ⟨W,Q,hLayer,J,hRun,hCode⟩ := h
  obtain ⟨W',Q',hLayer',J',hRun',hCode'⟩ := h'
  obtain ⟨hWW,hQQ⟩ := hLayers.at_unique hM.1 hLayer hLayer'
  subst W'
  subst Q'
  have hJJ := hRun.unique_d hM hC hRun'
  subst J'
  exact hCode.unique hM.1 hCode'

theorem SourceAt.read {M : SetTheory.Structure.{u}} (he : Extensional M)
    {C : ExpressionData M.Domain} {m : M.Domain} {L : LayerStateSpace M.Domain} {H k code heights parents : M.Domain}
    (h : SourceAt M C m L H k code) (hCode : Codes M code heights parents) :
    ∃ W Q J, RowAt M L.states H k W Q ∧ RowRun M C m L.rows W Q J ∧
      (⟨m,heights,L.rows.forests,parents⟩ : Data M.Domain).Valid M C ∧
      FromRun M C m L.rows W J ⟨m,heights,L.rows.forests,parents⟩ := by
  obtain ⟨W,Q,hLayer,J,hRun,hSource⟩ := h
  exact ⟨W,Q,J,hLayer,hRun,hSource.read he hCode⟩

def sourceFormula {n : Nat} (C : ExpressionData (Project.Term n)) (m : Project.Term n) (R : RowStateSpace (Project.Term n))
    (States H Histories Runs k code : Project.Term n) : Project.Formula 1 n :=
  Project.Formula.existsMem Histories (.conj (memPairFormula Runs.weaken k.weaken (.bound 0))
    (Project.Formula.existsMem R.values.weaken (Project.Formula.existsMem R.forests.weaken.weaken
      (.conj (rowAtFormula States.weaken.weaken.weaken H.weaken.weaken.weaken k.weaken.weaken.weaken (.bound 1) (.bound 0))
        (codeFromRunFormula C.weaken.weaken.weaken m.weaken.weaken.weaken R.weaken.weaken.weaken
          (.bound 1) (.bound 2) R.forests.weaken.weaken.weaken code.weaken.weaken.weaken)))))

theorem sourceFormula_delta0 {n : Nat} (C : ExpressionData (Project.Term n)) (m : Project.Term n) (R : RowStateSpace (Project.Term n))
    (States H Histories Runs k code : Project.Term n) : (sourceFormula C m R States H Histories Runs k code).IsDelta0 :=
  .existsMem _ (.conj (memPairFormula_delta0 _ _ _) (.existsMem _ (.existsMem _
    (.conj (rowAtFormula_delta0 _ _ _ _ _) (codeFromRunFormula_delta0 _ _ _ _ _ _ _)))))

theorem sourceFormula_freeClosed {n : Nat} {C : ExpressionData (Project.Term n)} (hC : C.Closed)
    {R : RowStateSpace (Project.Term n)} (hR : R.Closed) (m States H Histories Runs k code : Project.Term n)
    (hm : m.freeSupport=[]) (hStates : States.freeSupport=[]) (hH : H.freeSupport=[]) (hHist : Histories.freeSupport=[])
    (hRuns : Runs.freeSupport=[]) (hk : k.freeSupport=[]) (hCode : code.freeSupport=[]) :
    (sourceFormula C m R States H Histories Runs k code).FreeClosed := by
  have hFrom := codeFromRunFormula_freeClosed hC.weaken.weaken.weaken hR.weaken.weaken.weaken m.weaken.weaken.weaken
    (.bound 1) (.bound 2) R.forests.weaken.weaken.weaken code.weaken.weaken.weaken
    (by simpa using hm) rfl rfl (by simpa using hR.forests) (by simpa using hCode)
  simp [sourceFormula,Project.Formula.existsMem,Definitional.Formula.FreeClosed,rowAtFormula,memPairFormula,codeFormula,pairFormula,
    Project.Formula.forallMem,hR.values,hR.forests,hStates,hH,hHist,hRuns,hk,hFrom]

theorem sourceFormula_iff {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory) {n : Nat} (e : Env M n)
    (C : ExpressionData (Project.Term n)) (m : Project.Term n) (R : RowStateSpace (Project.Term n)) (States H Histories Runs k code : Project.Term n)
    (hC : (C.eval e).Valid M) {V P B : M.Domain}
    (hLayers : LayerRun M (C.eval e) (m.eval e) ⟨R.eval e,States.eval e⟩ V P (H.eval e))
    (hFamily : ExpressionDiagram.RowFamily M (C.eval e) (m.eval e) ⟨R.eval e,States.eval e⟩ (H.eval e) B (Histories.eval e) (Runs.eval e)) :
    Project.Formula.satisfies e (sourceFormula C m R States H Histories Runs k code) ↔
      M.mem (k.eval e) B ∧ SourceAt M (C.eval e) (m.eval e) ⟨R.eval e,States.eval e⟩ (H.eval e) (k.eval e) (code.eval e) := by
  have hCodeIff (J W Q : M.Domain) (hJ : MemPair M (Runs.eval e) (k.eval e) J)
      (hLayer : RowAt M (States.eval e) (H.eval e) (k.eval e) W Q) :
      Project.Formula.satisfies (((e.push J).push W).push Q)
        (codeFromRunFormula C.weaken.weaken.weaken m.weaken.weaken.weaken R.weaken.weaken.weaken
          (.bound 1) (.bound 2) R.forests.weaken.weaken.weaken code.weaken.weaken.weaken) ↔
        CodeFromRun M (C.eval e) (m.eval e) (R.eval e) W J (R.forests.eval e) (code.eval e) := by
    obtain ⟨W',Q',hLayer',hRun⟩ := hFamily.rows (k.eval e) J hJ
    obtain ⟨hWW,hQQ⟩ := hLayers.at_unique hM.1 hLayer hLayer'
    subst W'
    subst Q'
    have h := codeFromRunFormula_iff hM (((e.push J).push W).push Q) C.weaken.weaken.weaken m.weaken.weaken.weaken R.weaken.weaken.weaken
      (.bound 1) (.bound 2) R.forests.weaken.weaken.weaken code.weaken.weaken.weaken
      (by simpa only [ExpressionData.eval_weaken] using hC)
      (by simpa only [ExpressionData.eval_weaken,RowStateSpace.eval_weaken,Term.eval_weaken,
        Project.Term.eval_bound_one_push,Project.Term.eval_bound_two_push,Project.Term.eval_bound_zero_push] using hRun)
    simpa only [ExpressionData.eval_weaken,RowStateSpace.eval_weaken,Term.eval_weaken,
      Project.Term.eval_bound_one_push,Project.Term.eval_bound_two_push,Project.Term.eval_bound_zero_push] using h
  simp only [sourceFormula,Project.Formula.satisfies_existsMem_iff,Project.Formula.satisfies_conj_iff,
    memPairFormula_iff hM.1,rowAtFormula_iff hM.1,Term.eval_weaken]
  constructor
  · rintro ⟨J,_,hJ,W,_,Q,_,hLayer,hCert⟩
    obtain ⟨W',Q',hLayer',hRun⟩ := hFamily.rows (k.eval e) J hJ
    obtain ⟨hWW,hQQ⟩ := hLayers.at_unique hM.1 hLayer hLayer'
    subst W'
    subst Q'
    exact ⟨(hFamily.graph.bounds hM.1 hJ).1,W,Q,hLayer,J,hRun,(hCodeIff J W Q hJ hLayer).mp hCert⟩
  · rintro ⟨hk,W,Q,hLayer,J,hRun,hCode⟩
    obtain ⟨J',W',Q',hJ',hJPair,hLayer',hRun'⟩ := hFamily.at_d hk
    obtain ⟨hWW,hQQ⟩ := hLayers.at_unique hM.1 hLayer hLayer'
    subst W'
    subst Q'
    have hJJ := hRun.unique_d hM hC hRun'
    subst J'
    exact ⟨J,hJ',hJPair,W,(hRun.space.values W).mpr hRun.base.values,Q,(hRun.space.forests Q).mpr hRun.base.forest,
      hLayer,(hCodeIff J W Q hJPair hLayer).mpr hCode⟩

private def sourceSchema : Project.Delta0BinarySchema 13 where
  body := sourceFormula ⟨.bound 14,.bound 13,.bound 12,.bound 11,.bound 10⟩ (.bound 9) ⟨.bound 8,.bound 7,.bound 6⟩
    (.bound 5) (.bound 4) (.bound 3) (.bound 2) (.bound 1) (.bound 0)
  freeClosed := sourceFormula_freeClosed ⟨rfl,rfl,rfl,rfl,rfl⟩ ⟨rfl,rfl,rfl⟩ _ _ _ _ _ _ _ rfl rfl rfl rfl rfl rfl rfl
  delta0 := sourceFormula_delta0 _ _ _ _ _ _ _ _ _

structure SourceGraph (M : SetTheory.Structure.{u}) (C : ExpressionData M.Domain) (m : M.Domain)
    (L : LayerStateSpace M.Domain) (H B Sources G : M.Domain) : Prop where
  graph : Graph M G B Sources
  range : ∀ code, M.mem code Sources ↔ ∃ k, M.mem k B ∧ SourceAt M C m L H k code
  rows : ∀ k code, MemPair M G k code ↔ M.mem k B ∧ SourceAt M C m L H k code

theorem source_graph_exists_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {m : M.Domain} {L : LayerStateSpace M.Domain} {V P H B : M.Domain}
    (hLayers : LayerRun M C m L V P H) (hB : M.mem B C.omega) : ∃ Sources G, SourceGraph M C m L H B Sources G := by
  obtain ⟨Histories,Runs,hFamily⟩ := ExpressionDiagram.row_family_exists_d hM hC hLayers hB
  let e := ((((((((((((oneEnv C.omega).push C.zero).push C.one).push C.sequences).push C.expressions).push m).push L.rows.values).push L.rows.forests).push L.rows.states).push L.states).push H).push Histories).push Runs
  have hφ (k code : M.Domain) : Project.Formula.satisfies ((e.push k).push code) sourceSchema.body ↔
      M.mem k B ∧ SourceAt M C m L H k code := sourceFormula_iff hM ((e.push k).push code)
      ⟨.bound 14,.bound 13,.bound 12,.bound 11,.bound 10⟩ (.bound 9) ⟨.bound 8,.bound 7,.bound 6⟩
      (.bound 5) (.bound 4) (.bound 3) (.bound 2) (.bound 1) (.bound 0) hC hLayers hFamily
  have hTotal : ∀ k, M.mem k B → ∃ code, Project.Formula.satisfies ((e.push k).push code) sourceSchema.body := by
    intro k hk
    obtain ⟨J,W,Q,_,_,hLayer,hRun⟩ := hFamily.at_d hk
    obtain ⟨code,hCode⟩ := coded_from_run_exists_d hM hC hRun (hLayers.at_rooted hM.1 hLayer).positive
    exact ⟨code,(hφ k code).mpr ⟨hk,W,Q,hLayer,J,hRun,hCode⟩⟩
  obtain ⟨Sources,hSources⟩ := KP1Y.functional_image_d hM sourceSchema e B hTotal
    (fun k _ code code' hCode hCode' => ((hφ k code).mp hCode).2.unique_d hM hC hLayers ((hφ k code').mp hCode').2)
  have hRange (code : M.Domain) : M.mem code Sources ↔ ∃ k, M.mem k B ∧ SourceAt M C m L H k code := by
    have hr := hSources code
    simp only [hφ] at hr
    exact hr.trans ⟨fun ⟨k,hk,_,h⟩ => ⟨k,hk,h⟩,fun ⟨k,hk,h⟩ => ⟨k,hk,hk,h⟩⟩
  obtain ⟨G,hSupport,hRaw⟩ := relation_comprehension_d hM sourceSchema e B Sources
  have hRows (k code : M.Domain) : MemPair M G k code ↔ M.mem k B ∧ SourceAt M C m L H k code := by
    have hr := hRaw k code
    rw [hφ] at hr
    exact hr.trans ⟨fun h => h.2.2,fun h => ⟨h.1,(hRange code).mpr ⟨k,h⟩,h⟩⟩
  refine ⟨Sources,G,⟨hSupport,?_,?_⟩,hRange,hRows⟩
  · intro k hk
    obtain ⟨code,hCode⟩ := hTotal k hk
    have hSource := (hφ k code).mp hCode
    exact ⟨code,(hRange code).mpr ⟨k,hSource⟩,(hRows k code).mpr hSource⟩
  · intro k code code' hCode hCode'
    exact ((hRows k code).mp hCode).2.unique_d hM hC hLayers ((hRows k code').mp hCode').2


theorem SourceAt.exists_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {m : M.Domain} {L : LayerStateSpace M.Domain} {V P H k : M.Domain}
    (hLayers : LayerRun M C m L V P H) (hk : M.mem k C.omega) : ∃ code, SourceAt M C m L H k code := by
  obtain ⟨W,Q,hLayer⟩ := hLayers.at_exists_d hk
  obtain ⟨J,hRun⟩ := row_run_exists_d hM hC hLayers.space.rows (hLayers.at_rooted hM.1 hLayer).row
  obtain ⟨code,hCode⟩ := coded_from_run_exists_d hM hC hRun (hLayers.at_rooted hM.1 hLayer).positive
  exact ⟨code,W,Q,hLayer,J,hRun,hCode⟩

theorem SourceGraph.unique {M : SetTheory.Structure.{u}} (he : Extensional M)
    {C : ExpressionData M.Domain} {m : M.Domain} {L : LayerStateSpace M.Domain} {H B Sources Sources' G G' : M.Domain}
    (h : SourceGraph M C m L H B Sources G) (h' : SourceGraph M C m L H B Sources' G') : Sources=Sources' ∧ G=G' := by
  have hSources := he.eq_of_same_members _ _ (fun code => (h.range code).trans (h'.range code).symm)
  subst Sources'
  exact ⟨rfl,h.graph.ext he h'.graph (fun k _ code => (h.rows k code).trans (h'.rows k code).symm)⟩

/-- 原expandedMountain三分支；低层的floor/rise是实际源高度读数唯一决定的。 -/
def Branch (M : SetTheory.Structure.{u}) (C : ExpressionData M.Domain) (T : MatrixArithmetic M.Domain)
    (A : CopyCoordinates.Context M.Domain) (X : Data M.Domain) (K level k n : M.Domain) (Y : Data M.Domain) : Prop :=
  (M.mem k K ∧ ∃ D : Lower.Context M.Domain, D.coordinates=A ∧ D.mountain=X ∧ D.Valid M C ∧ Lower.Copies M C T D n Y) ∨
    (k=K ∧ Terminal.Copies M C T A X level n Y) ∨ (M.mem K k ∧ Ordinary.Copies M C T A X n Y)

theorem bad_indices_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {m : M.Domain} {L : LayerStateSpace M.Domain} {V P H K level x y : M.Domain}
    (hLayers : LayerRun M C m L V P H) (hBad : BadAt M C m L H K level x y) :
    M.mem K C.omega ∧ M.mem level C.omega ∧ M.mem x m ∧ M.mem y m := by
  obtain ⟨W,_,Q,_,hLayer,J,hRun,U,_,F,_,hRow,hParent,_⟩ := hBad
  have hk : M.mem K C.omega := by
    obtain ⟨_,_,hAt,_⟩ := hLayer
    exact (hLayers.graph.bounds hM.1 hAt).1
  have hd : M.mem level C.omega := by
    obtain ⟨_,_,hAt,_⟩ := hRow
    exact (hRun.graph.bounds hM.1 hAt).1
  have hBounds := ((hRun.at_numeric_d hM hC hRow).forest.bounds hM.1 hParent)
  exact ⟨hk,hd,hBounds⟩

theorem branch_exists_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {m : M.Domain} {L : LayerStateSpace M.Domain} {V P H K level k W Q J n : M.Domain}
    (hLayers : LayerRun M C m L V P H) {A : CopyCoordinates.Context M.Domain} (hA : A.Valid M C)
    (hBad : BadAt M C m L H K level A.last A.root) (hLayer : RowAt M L.states H k W Q)
    (hRun : RowRun M C m L.rows W Q J) {X : Data M.Domain} (hX : X.Valid M C)
    (hFrom : FromRun M C m L.rows W J X) (hn : M.mem n C.omega) :
    ∃ Y, Y.Valid M C ∧ Branch M C T A X K level k n Y := by
  have hK := (bad_indices_d hM hC hLayers hBad).1
  have hk : M.mem k C.omega := by
    obtain ⟨_,_,hAt,_⟩ := hLayer
    exact (hLayers.graph.bounds hM.1 hAt).1
  rcases (omega_isOrdinal_d hM hC.omega).wellOrder.linear.compare k hk K hK with he | hLow | hHigh
  · have hkK := hM.1.eq_of_same_members k K he
    subst k
    obtain ⟨Y,hY,hCopy⟩ := Terminal.copy_from_bad_d hM hC hT hA hLayers hBad hLayer hRun hX hFrom hn
    exact ⟨Y,hY,Or.inr (Or.inl ⟨rfl,hCopy⟩)⟩
  · obtain ⟨D,Y,hDA,hDX,hD,hY,hCopy⟩ := Lower.copy_from_bad_d hM hC hT hLayers hA hBad hLayer hLow hRun hX hFrom hn
    exact ⟨Y,hY,Or.inl ⟨hLow,D,hDA,hDX,hD,hCopy⟩⟩
  · have hLast : M.mem A.last X.width := hFrom.width.symm ▸ (bad_indices_d hM hC hLayers hBad).2.2.1
    obtain ⟨Y,hY,hCopy⟩ := Ordinary.copy_exists_d hM hC hT hA hX hLast hn
    exact ⟨Y,hY,Or.inr (Or.inr ⟨hHigh,hCopy⟩)⟩

theorem Branch.width {M : SetTheory.Structure.{u}} {C : ExpressionData M.Domain} {T : MatrixArithmetic M.Domain}
    {A : CopyCoordinates.Context M.Domain} {X Y : Data M.Domain} {K level k n : M.Domain}
    (h : Branch M C T A X K level k n Y) : Y.width=n := by
  rcases h with ⟨_,_,_,_,_,h⟩ | ⟨_,h⟩ | ⟨_,h⟩ <;> exact h.width

theorem Branch.forests {M : SetTheory.Structure.{u}} {C : ExpressionData M.Domain} {T : MatrixArithmetic M.Domain}
    {A : CopyCoordinates.Context M.Domain} {X Y : Data M.Domain} {K level k n : M.Domain}
    (h : Branch M C T A X K level k n Y) : ∀ F, M.mem F Y.forests ↔ Forest M C.omega n F := by
  rcases h with ⟨_,_,_,_,_,h⟩ | ⟨_,h⟩ | ⟨_,h⟩ <;> exact h.forests

theorem Branch.unique_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} {A : CopyCoordinates.Context M.Domain}
    {X Y Z : Data M.Domain} {K level k n : M.Domain} (hK : M.mem K C.omega) (hY : Y.Valid M C) (hZ : Z.Valid M C)
    (h : Branch M C T A X K level k n Y) (h' : Branch M C T A X K level k n Z) : Y=Z := by
  have hBoth (hLow : M.mem k K) (hHigh : M.mem K k) : False := SetTheory.KP.mem_irrefl_d (KP1Y.models_weakKP hM) K
    (((omega_isOrdinal_d hM hC.omega).mem hK).transitive k hLow K hHigh)
  rcases h with ⟨hLow,D,hDA,hDX,hD,hCopy⟩ | ⟨hEq,hCopy⟩ | ⟨hHigh,hCopy⟩ <;>
    rcases h' with ⟨hLow',D',hDA',hDX',hD',hCopy'⟩ | ⟨hEq',hCopy'⟩ | ⟨hHigh',hCopy'⟩
  · have hDD := Lower.Context.unique_d hM hC hD hD' (hDA.trans hDA'.symm) (hDX.trans hDX'.symm)
    subst D'
    exact hCopy.unique hM.1 hY hZ hCopy'
  · exact False.elim (SetTheory.KP.mem_irrefl_d (KP1Y.models_weakKP hM) K (hEq' ▸ hLow))
  · exact False.elim (hBoth hLow hHigh')
  · exact False.elim (SetTheory.KP.mem_irrefl_d (KP1Y.models_weakKP hM) K (hEq ▸ hLow'))
  · exact hCopy.unique hM.1 hY hZ hCopy'
  · exact False.elim (SetTheory.KP.mem_irrefl_d (KP1Y.models_weakKP hM) K (hEq ▸ hHigh'))
  · exact False.elim (hBoth hLow' hHigh)
  · exact False.elim (SetTheory.KP.mem_irrefl_d (KP1Y.models_weakKP hM) K (hEq' ▸ hHigh))
  · exact hCopy.unique hM.1 hY hZ hCopy'


theorem SourceAt.contents {M : SetTheory.Structure.{u}} {C : ExpressionData M.Domain} {m : M.Domain}
    {L : LayerStateSpace M.Domain} {H k code : M.Domain} (h : SourceAt M C m L H k code) :
    ∃ heights parents, Codes M code heights parents := by
  obtain ⟨_,_,_,_,_,heights,parents,hCode,_⟩ := h
  exact ⟨heights,parents,hCode⟩

/-- 三分支输出的精确语义；原行运行是实际对象图，所有辅助载体均固定。 -/
def ExpandedAt (M : SetTheory.Structure.{u}) (C : ExpressionData M.Domain) (T : MatrixArithmetic M.Domain)
    (A : CopyCoordinates.Context M.Domain) (m : M.Domain) (L : LayerStateSpace M.Domain) (H K level k n Forests code : M.Domain) : Prop :=
  ∃ source, SourceAt M C m L H k source ∧ ∃ sourceHeights sourceParents, Codes M source sourceHeights sourceParents ∧
    ∃ heights parents, Codes M code heights parents ∧ (⟨n,heights,Forests,parents⟩ : Data M.Domain).Valid M C ∧
      Branch M C T A ⟨m,sourceHeights,L.rows.forests,sourceParents⟩ K level k n ⟨n,heights,Forests,parents⟩

theorem expanded_at_exists_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {m : M.Domain} {L : LayerStateSpace M.Domain} {V P H K level k n Forests : M.Domain}
    (hLayers : LayerRun M C m L V P H) {A : CopyCoordinates.Context M.Domain} (hA : A.Valid M C)
    (hBad : BadAt M C m L H K level A.last A.root) (hk : M.mem k C.omega) (hn : M.mem n C.omega)
    (hForests : ∀ F, M.mem F Forests ↔ Forest M C.omega n F) :
    ∃ code, ExpandedAt M C T A m L H K level k n Forests code := by
  obtain ⟨source,hSource⟩ := SourceAt.exists_d hM hC hLayers hk
  obtain ⟨sourceHeights,sourceParents,hSourceCode⟩ := hSource.contents
  obtain ⟨W,Q,J,hLayer,hRun,hX,hFrom⟩ := hSource.read hM.1 hSourceCode
  obtain ⟨Y,hY,hBranch⟩ := branch_exists_d hM hC hT hLayers hA hBad hLayer hRun hX hFrom hn
  have hWidth := hBranch.width
  have hForestEq : Y.forests=Forests := hM.1.eq_of_same_members _ _ (fun F => (hBranch.forests F).trans (hForests F).symm)
  have hData : (⟨n,Y.heights,Forests,Y.parents⟩ : Data M.Domain)=Y := by
    cases Y
    simp_all
  obtain ⟨code,hCode⟩ := codes_total hM Y.heights Y.parents
  exact ⟨code,source,hSource,sourceHeights,sourceParents,hSourceCode,Y.heights,Y.parents,hCode,hData.symm ▸ hY,hData.symm ▸ hBranch⟩

theorem ExpandedAt.unique_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} {A : CopyCoordinates.Context M.Domain}
    {m : M.Domain} {L : LayerStateSpace M.Domain} {V P H K level k n Forests code code' : M.Domain}
    (hLayers : LayerRun M C m L V P H) (hK : M.mem K C.omega)
    (h : ExpandedAt M C T A m L H K level k n Forests code) (h' : ExpandedAt M C T A m L H K level k n Forests code') : code=code' := by
  obtain ⟨source,hSource,sH,sP,hSC,Hc,Pc,hCode,hY,hBranch⟩ := h
  obtain ⟨source',hSource',sH',sP',hSC',Hc',Pc',hCode',hY',hBranch'⟩ := h'
  have hSources := hSource.unique_d hM hC hLayers hSource'
  subst source'
  obtain ⟨hHs,hPs⟩ := codes_injective hM.1 hSC hSC'
  subst sH'
  subst sP'
  have hYY := hBranch.unique_d hM hC hK hY hY' hBranch'
  have hHeights : Hc=Hc' := congrArg Data.heights hYY
  have hParents : Pc=Pc' := congrArg Data.parents hYY
  subst Hc'
  subst Pc'
  exact codes_unique hM.1 hCode hCode'

theorem ExpandedAt.read {M : SetTheory.Structure.{u}} (he : Extensional M)
    {C : ExpressionData M.Domain} {T : MatrixArithmetic M.Domain} {A : CopyCoordinates.Context M.Domain}
    {m : M.Domain} {L : LayerStateSpace M.Domain} {H K level k n Forests code heights parents : M.Domain}
    (h : ExpandedAt M C T A m L H K level k n Forests code) (hCode : Codes M code heights parents) :
    (⟨n,heights,Forests,parents⟩ : Data M.Domain).Valid M C ∧ ∃ source sourceHeights sourceParents,
      SourceAt M C m L H k source ∧ Codes M source sourceHeights sourceParents ∧
        Branch M C T A ⟨m,sourceHeights,L.rows.forests,sourceParents⟩ K level k n ⟨n,heights,Forests,parents⟩ := by
  obtain ⟨source,hSource,sH,sP,hSC,h,p,hCode',hY,hBranch⟩ := h
  obtain ⟨hhh,hpp⟩ := codes_injective he hCode' hCode
  subst h
  subst p
  exact ⟨hY,source,sH,sP,hSource,hSC,hBranch⟩

structure Tower (M : SetTheory.Structure.{u}) (C : ExpressionData M.Domain) (T : MatrixArithmetic M.Domain)
    (A : CopyCoordinates.Context M.Domain) (m : M.Domain) (L : LayerStateSpace M.Domain) (H K level B n Forests Codes G : M.Domain) : Prop where
  bound : M.mem B C.omega
  width : M.mem n C.omega
  forests : ∀ F, M.mem F Forests ↔ Forest M C.omega n F
  graph : Graph M G B Codes
  range : ∀ code, M.mem code Codes ↔ ∃ k, M.mem k B ∧ ExpandedAt M C T A m L H K level k n Forests code
  rows : ∀ k code, MemPair M G k code ↔ M.mem k B ∧ ExpandedAt M C T A m L H K level k n Forests code

theorem Tower.unique {M : SetTheory.Structure.{u}} (he : Extensional M)
    {C : ExpressionData M.Domain} {T : MatrixArithmetic M.Domain} {A : CopyCoordinates.Context M.Domain}
    {m : M.Domain} {L : LayerStateSpace M.Domain} {H K level B n Forests Forests' Codes Codes' G G' : M.Domain}
    (h : Tower M C T A m L H K level B n Forests Codes G) (h' : Tower M C T A m L H K level B n Forests' Codes' G') :
    Forests=Forests' ∧ Codes=Codes' ∧ G=G' := by
  have hForests := he.eq_of_same_members _ _ (fun F => (h.forests F).trans (h'.forests F).symm)
  subst Forests'
  have hCodes := he.eq_of_same_members _ _ (fun code => (h.range code).trans (h'.range code).symm)
  subst Codes'
  exact ⟨rfl,rfl,h.graph.ext he h'.graph (fun k _ code => (h.rows k code).trans (h'.rows k code).symm)⟩


theorem Branch.lower_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} {A : CopyCoordinates.Context M.Domain}
    {X Y : Data M.Domain} {K level k n : M.Domain} (hK : M.mem K C.omega) (hk : M.mem k K)
    (h : Branch M C T A X K level k n Y) :
    ∃ D : Lower.Context M.Domain, D.coordinates=A ∧ D.mountain=X ∧ D.Valid M C ∧ Lower.Copies M C T D n Y := by
  rcases h with ⟨_,hCopy⟩ | ⟨he,_⟩ | ⟨hHigh,_⟩
  · exact hCopy
  · exact False.elim (SetTheory.KP.mem_irrefl_d (KP1Y.models_weakKP hM) K (he ▸ hk))
  · exact False.elim (SetTheory.KP.mem_irrefl_d (KP1Y.models_weakKP hM) K
      (((omega_isOrdinal_d hM hC.omega).mem hK).transitive k hk K hHigh))

theorem Branch.terminal_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} {T : MatrixArithmetic M.Domain} {A : CopyCoordinates.Context M.Domain}
    {X Y : Data M.Domain} {K level n : M.Domain} (h : Branch M C T A X K level K n Y) : Terminal.Copies M C T A X level n Y := by
  rcases h with ⟨hLow,_⟩ | ⟨_,hCopy⟩ | ⟨hHigh,_⟩
  · exact False.elim (SetTheory.KP.mem_irrefl_d (KP1Y.models_weakKP hM) K hLow)
  · exact hCopy
  · exact False.elim (SetTheory.KP.mem_irrefl_d (KP1Y.models_weakKP hM) K hHigh)

theorem Branch.ordinary_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} {A : CopyCoordinates.Context M.Domain}
    {X Y : Data M.Domain} {K level k n : M.Domain} (hK : M.mem K C.omega) (hk : M.mem K k)
    (h : Branch M C T A X K level k n Y) : Ordinary.Copies M C T A X n Y := by
  rcases h with ⟨hLow,_⟩ | ⟨he,_⟩ | ⟨_,hCopy⟩
  · exact False.elim (SetTheory.KP.mem_irrefl_d (KP1Y.models_weakKP hM) K
      (((omega_isOrdinal_d hM hC.omega).mem hK).transitive k hLow K hk))
  · exact False.elim (SetTheory.KP.mem_irrefl_d (KP1Y.models_weakKP hM) K (he ▸ hk))
  · exact hCopy

theorem Tower.at_exists_d {M : SetTheory.Structure.{u}} {C : ExpressionData M.Domain} {T : MatrixArithmetic M.Domain}
    {A : CopyCoordinates.Context M.Domain} {m : M.Domain} {L : LayerStateSpace M.Domain}
    {H K level B n Forests Codes G k : M.Domain} (h : Tower M C T A m L H K level B n Forests Codes G) (hk : M.mem k B) :
    ∃ code, M.mem code Codes ∧ MemPair M G k code ∧ ExpandedAt M C T A m L H K level k n Forests code := by
  obtain ⟨code,hCode,hAt⟩ := h.graph.total k hk
  exact ⟨code,hCode,hAt,((h.rows k code).mp hAt).2⟩

theorem Tower.mountain_at_d {M : SetTheory.Structure.{u}}
    {C : ExpressionData M.Domain} {T : MatrixArithmetic M.Domain} {A : CopyCoordinates.Context M.Domain}
    {m : M.Domain} {L : LayerStateSpace M.Domain} {H K level B n Forests Codes G k : M.Domain}
    (h : Tower M C T A m L H K level B n Forests Codes G) (hk : M.mem k B) :
    ∃ code heights parents, M.mem code Codes ∧ MemPair M G k code ∧ KP1Y.Kuratowski.Codes M code heights parents ∧
      (⟨n,heights,Forests,parents⟩ : Data M.Domain).Valid M C ∧ ∃ source sourceHeights sourceParents,
        SourceAt M C m L H k source ∧ KP1Y.Kuratowski.Codes M source sourceHeights sourceParents ∧
          Branch M C T A ⟨m,sourceHeights,L.rows.forests,sourceParents⟩ K level k n ⟨n,heights,Forests,parents⟩ := by
  obtain ⟨code,hCode,hAt,hExpanded⟩ := h.at_exists_d hk
  obtain ⟨source,hSource,sH,sP,hSC,heights,parents,hCodePair,hValid,hBranch⟩ := hExpanded
  exact ⟨code,heights,parents,hCode,hAt,hCodePair,hValid,source,sH,sP,hSource,hSC,hBranch⟩


def lowerReadCopiesFormula {n : Nat} (C : ExpressionData (Project.Term n)) (T : MatrixArithmetic (Project.Term n))
    (A : CopyCoordinates.Context (Project.Term n)) (X : Data (Project.Term n)) (width : Project.Term n) (Y : Data (Project.Term n)) : Project.Formula 1 n :=
  Project.Formula.existsMem C.omega (Project.Formula.existsMem C.omega.weaken (Project.Formula.existsMem C.omega.weaken.weaken
    (.conj (memPairFormula X.heights.weaken.weaken.weaken A.root.weaken.weaken.weaken (.bound 2))
      (.conj (memPairFormula X.heights.weaken.weaken.weaken A.last.weaken.weaken.weaken (.bound 0))
        (.conj (CopyCoordinates.differenceReadFormula T.weaken.weaken.weaken (.bound 0) (.bound 2) (.bound 1))
          (lowerCopiesFormula C.weaken.weaken.weaken T.weaken.weaken.weaken
            ⟨A.weaken.weaken.weaken,X.weaken.weaken.weaken,.bound 2,.bound 1⟩ width.weaken.weaken.weaken Y.weaken.weaken.weaken))))))

theorem lowerReadCopiesFormula_delta0 {n : Nat} (C : ExpressionData (Project.Term n)) (T : MatrixArithmetic (Project.Term n))
    (A : CopyCoordinates.Context (Project.Term n)) (X : Data (Project.Term n)) (width : Project.Term n) (Y : Data (Project.Term n)) :
    (lowerReadCopiesFormula C T A X width Y).IsDelta0 :=
  .existsMem _ (.existsMem _ (.existsMem _ (.conj (memPairFormula_delta0 _ _ _) (.conj (memPairFormula_delta0 _ _ _)
    (.conj (CopyCoordinates.differenceReadFormula_delta0 _ _ _ _) (lowerCopiesFormula_delta0 _ _ _ _ _))))))

theorem lowerReadCopiesFormula_freeClosed {n : Nat} {C : ExpressionData (Project.Term n)} (hC : C.Closed)
    {T : MatrixArithmetic (Project.Term n)} (hT : CopyCoordinates.ArithmeticClosed T)
    {A : CopyCoordinates.Context (Project.Term n)} (hA : A.Closed) {X Y : Data (Project.Term n)} (hX : X.Closed) (hY : Y.Closed)
    (width : Project.Term n) (hWidth : width.freeSupport=[]) : (lowerReadCopiesFormula C T A X width Y).FreeClosed := by
  have hLower := lowerCopiesFormula_freeClosed hC.weaken.weaken.weaken hT.weaken.weaken.weaken
    (D := ⟨A.weaken.weaken.weaken,X.weaken.weaken.weaken,.bound 2,.bound 1⟩)
    ⟨hA.weaken.weaken.weaken,hX.weaken.weaken.weaken,rfl,rfl⟩ hY.weaken.weaken.weaken width.weaken.weaken.weaken (by simpa using hWidth)
  have hRead : (CopyCoordinates.differenceReadFormula T.weaken.weaken.weaken
      (Project.Term.bound (depth := n+3) 0) (.bound 2) (.bound 1)).FreeClosed := by
    simp [CopyCoordinates.differenceReadFormula,addAtFormula,Project.Formula.existsMem,Definitional.Formula.FreeClosed,
      memPairFormula,codeFormula,pairFormula,Project.Formula.forallMem,MatrixArithmetic.weaken,MatrixArithmetic.map,hT.diffPairs,hT.difference]
  simp [lowerReadCopiesFormula,Project.Formula.existsMem,Definitional.Formula.FreeClosed,
    memPairFormula,codeFormula,pairFormula,Project.Formula.forallMem,hC.omega,hX.heights,hA.root,hA.last,hRead,hLower]

theorem lowerReadCopiesFormula_iff {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory) {n : Nat} (e : Env M n)
    (C : ExpressionData (Project.Term n)) (T : MatrixArithmetic (Project.Term n)) (A : CopyCoordinates.Context (Project.Term n))
    (X : Data (Project.Term n)) (width : Project.Term n) (Y : Data (Project.Term n))
    (hC : (C.eval e).Valid M) (hT : (T.eval e).Valid M (C.eval e)) (hA : (A.eval e).Valid M (C.eval e))
    {m : M.Domain} {L : LayerStateSpace M.Domain} {V P H K level k W Q J : M.Domain}
    (hLayers : LayerRun M (C.eval e) m L V P H)
    (hBad : BadAt M (C.eval e) m L H K level (A.eval e).last (A.eval e).root)
    (hLayer : RowAt M L.states H k W Q) (hk : M.mem k K) (hRun : RowRun M (C.eval e) m L.rows W Q J)
    (hX : (X.eval e).Valid M (C.eval e)) (hFrom : FromRun M (C.eval e) m L.rows W J (X.eval e))
    (hY : (Y.eval e).Valid M (C.eval e)) (hWidth : (Y.eval e).width=width.eval e)
    (hForests : ∀ F, M.mem F (Y.eval e).forests ↔ Forest M (C.eval e).omega (width.eval e) F) :
    Project.Formula.satisfies e (lowerReadCopiesFormula C T A X width Y) ↔
      ∃ D : Lower.Context M.Domain, D.coordinates=A.eval e ∧ D.mountain=X.eval e ∧ D.Valid M (C.eval e) ∧
        Lower.Copies M (C.eval e) (T.eval e) D (width.eval e) (Y.eval e) := by
  have hLower (floor rise height : M.Domain) (hFloor : MemPair M (X.heights.eval e) (A.root.eval e) floor)
      (hHeight : MemPair M (X.heights.eval e) (A.last.eval e) height)
      (hDiff : TruncatedDifference M (C.omega.eval e) (C.zero.eval e) height floor rise) :
      Project.Formula.satisfies (((e.push floor).push rise).push height)
        (lowerCopiesFormula C.weaken.weaken.weaken T.weaken.weaken.weaken
          ⟨A.weaken.weaken.weaken,X.weaken.weaken.weaken,.bound 2,.bound 1⟩ width.weaken.weaken.weaken Y.weaken.weaken.weaken) ↔
      Lower.Copies M (C.eval e) (T.eval e) ⟨A.eval e,X.eval e,floor,rise⟩ (width.eval e) (Y.eval e) := by
    have hD := Lower.context_valid_of_reads_from_bad_d hM hC hLayers hA hBad hLayer hk hRun hX hFrom hFloor hHeight hDiff
    have h := lowerCopiesFormula_iff hM (((e.push floor).push rise).push height) C.weaken.weaken.weaken T.weaken.weaken.weaken
      ⟨A.weaken.weaken.weaken,X.weaken.weaken.weaken,.bound 2,.bound 1⟩ width.weaken.weaken.weaken Y.weaken.weaken.weaken
      (by simpa only [ExpressionData.eval_weaken] using hC)
      (by simpa only [ExpressionData.eval_weaken,MatrixArithmetic.eval_weaken] using hT)
      (by simpa only [Lower.Context.eval,Lower.Context.map,ExpressionData.eval_weaken,CopyCoordinates.Context.eval,CopyCoordinates.Context.map,CopyCoordinates.Context.weaken,
        Data.eval,Data.map,Data.weaken,Term.eval_weaken,Project.Term.eval_bound_two_push,Project.Term.eval_bound_one_push,Project.Term.eval_bound_zero_push] using hD)
      (by simpa only [ExpressionData.eval_weaken,Data.eval_weaken] using hY)
      (by simpa only [Data.eval_weaken,Term.eval_weaken] using hWidth)
      (by simpa only [ExpressionData.eval_weaken,Data.eval_weaken,Term.eval_weaken] using hForests)
    simpa only [Lower.Context.eval,Lower.Context.map,ExpressionData.eval_weaken,MatrixArithmetic.eval_weaken,Data.eval_weaken,
      CopyCoordinates.Context.eval,CopyCoordinates.Context.map,CopyCoordinates.Context.weaken,Data.eval,Data.map,Data.weaken,Term.eval_weaken,
      Project.Term.eval_bound_two_push,Project.Term.eval_bound_one_push,Project.Term.eval_bound_zero_push] using h
  simp only [lowerReadCopiesFormula,Project.Formula.satisfies_existsMem_iff,Project.Formula.satisfies_conj_iff,
    memPairFormula_iff hM.1,CopyCoordinates.differenceReadFormula_iff hM.1,MatrixArithmetic.eval_weaken,Term.eval_weaken]
  constructor
  · rintro ⟨floor,hf,rise,_,height,hh,hFloor,hHeight,hRead,hCert⟩
    have hDiff := (CopyCoordinates.difference_read_iff_d hM hT hh hf).mp hRead
    have hD := Lower.context_valid_of_reads_from_bad_d hM hC hLayers hA hBad hLayer hk hRun hX hFrom hFloor hHeight hDiff
    exact ⟨⟨A.eval e,X.eval e,floor,rise⟩,rfl,rfl,hD,(hLower floor rise height hFloor hHeight hDiff).mp hCert⟩
  · rintro ⟨D,hDA,hDX,hD,hCopy⟩
    cases D with
    | mk A' X' floor rise =>
      dsimp only at hDA hDX
      subst A'
      subst X'
      obtain ⟨height,hh,hHeight,_,hDiff⟩ := hD.rise
      exact ⟨floor,hD.floor_nat hM.1,rise,hD.rise_nat hM.1,height,hh,hD.floor,hHeight,
        (CopyCoordinates.difference_read_iff_d hM hT hh (hD.floor_nat hM.1)).mpr hDiff,
        (hLower floor rise height hD.floor hHeight hDiff).mpr hCopy⟩


def branchFormula {n : Nat} (C : ExpressionData (Project.Term n)) (T : MatrixArithmetic (Project.Term n))
    (A : CopyCoordinates.Context (Project.Term n)) (X : Data (Project.Term n)) (K level k width : Project.Term n) (Y : Data (Project.Term n)) : Project.Formula 1 n :=
  .disj (.conj (.mem k K) (lowerReadCopiesFormula C T A X width Y))
    (.disj (.conj (Project.Formula.extensionalEq k K) (terminalCopiesFormula C T A X level width Y))
      (.conj (.mem K k) (ordinaryCopiesFormula C T A X width Y)))

theorem branchFormula_delta0 {n : Nat} (C : ExpressionData (Project.Term n)) (T : MatrixArithmetic (Project.Term n))
    (A : CopyCoordinates.Context (Project.Term n)) (X : Data (Project.Term n)) (K level k width : Project.Term n) (Y : Data (Project.Term n)) :
    (branchFormula C T A X K level k width Y).IsDelta0 :=
  .disj (.conj (.mem _ _) (lowerReadCopiesFormula_delta0 _ _ _ _ _ _))
    (.disj (.conj (.atom _ _ _) (terminalCopiesFormula_delta0 _ _ _ _ _ _ _)) (.conj (.mem _ _) (ordinaryCopiesFormula_delta0 _ _ _ _ _ _)))

theorem branchFormula_freeClosed {n : Nat} {C : ExpressionData (Project.Term n)} (hC : C.Closed)
    {T : MatrixArithmetic (Project.Term n)} (hT : CopyCoordinates.ArithmeticClosed T) {A : CopyCoordinates.Context (Project.Term n)} (hA : A.Closed)
    {X Y : Data (Project.Term n)} (hX : X.Closed) (hY : Y.Closed) (K level k width : Project.Term n)
    (hK : K.freeSupport=[]) (hLevel : level.freeSupport=[]) (hk : k.freeSupport=[]) (hWidth : width.freeSupport=[]) :
    (branchFormula C T A X K level k width Y).FreeClosed := by
  have hLower := lowerReadCopiesFormula_freeClosed hC hT hA hX hY width hWidth
  have hTerminal := terminalCopiesFormula_freeClosed hC hT hA hX hY level width hLevel hWidth
  have hOrdinary := ordinaryCopiesFormula_freeClosed hC hT hA hX hY width hWidth
  simp [branchFormula,Definitional.Formula.FreeClosed,hK,hk,hLower,hTerminal,hOrdinary]

theorem branchFormula_iff {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory) {n : Nat} (e : Env M n)
    (C : ExpressionData (Project.Term n)) (T : MatrixArithmetic (Project.Term n)) (A : CopyCoordinates.Context (Project.Term n))
    (X : Data (Project.Term n)) (K level k width : Project.Term n) (Y : Data (Project.Term n))
    (hC : (C.eval e).Valid M) (hT : (T.eval e).Valid M (C.eval e)) (hA : (A.eval e).Valid M (C.eval e))
    {m : M.Domain} {L : LayerStateSpace M.Domain} {V P H W Q J : M.Domain} (hLayers : LayerRun M (C.eval e) m L V P H)
    (hBad : BadAt M (C.eval e) m L H (K.eval e) (level.eval e) (A.eval e).last (A.eval e).root)
    (hLayer : RowAt M L.states H (k.eval e) W Q) (hRun : RowRun M (C.eval e) m L.rows W Q J)
    (hX : (X.eval e).Valid M (C.eval e)) (hFrom : FromRun M (C.eval e) m L.rows W J (X.eval e))
    (hY : (Y.eval e).Valid M (C.eval e)) (hWidth : (Y.eval e).width=width.eval e)
    (hForests : ∀ F, M.mem F (Y.eval e).forests ↔ Forest M (C.eval e).omega (width.eval e) F) :
    Project.Formula.satisfies e (branchFormula C T A X K level k width Y) ↔
      Branch M (C.eval e) (T.eval e) (A.eval e) (X.eval e) (K.eval e) (level.eval e) (k.eval e) (width.eval e) (Y.eval e) := by
  have hTerminal := terminalCopiesFormula_iff hM e C T A X level width Y hC hT hA hX hY hWidth hForests
  have hOrdinary := ordinaryCopiesFormula_iff hM e C T A X width Y hC hT hA hX hY hWidth hForests
  have hLower (hk : M.mem (k.eval e) (K.eval e)) := lowerReadCopiesFormula_iff hM e C T A X width Y hC hT hA
    hLayers hBad hLayer hk hRun hX hFrom hY hWidth hForests
  simp only [branchFormula,Project.Formula.satisfies_disj_iff,Project.Formula.satisfies_conj_iff,
    Project.Formula.satisfies_mem_iff,Project.Formula.satisfies_extensionalEq_iff_eq hM.1,hTerminal,hOrdinary]
  constructor
  · rintro (⟨hk,hLow⟩ | hOthers)
    · exact Or.inl ⟨hk,(hLower hk).mp hLow⟩
    · exact Or.inr hOthers
  · rintro (⟨hk,hLow⟩ | hOthers)
    · exact Or.inl ⟨hk,(hLower hk).mpr hLow⟩
    · exact Or.inr hOthers


def TargetAt (M : SetTheory.Structure.{u}) (C : ExpressionData M.Domain) (T : MatrixArithmetic M.Domain)
    (A : CopyCoordinates.Context M.Domain) (X : Data M.Domain) (K level k width Forests code : M.Domain) : Prop :=
  ∃ heights parents, Codes M code heights parents ∧ (⟨width,heights,Forests,parents⟩ : Data M.Domain).Valid M C ∧
    Branch M C T A X K level k width ⟨width,heights,Forests,parents⟩

def targetFormula {n : Nat} (C : ExpressionData (Project.Term n)) (T : MatrixArithmetic (Project.Term n))
    (A : CopyCoordinates.Context (Project.Term n)) (X : Data (Project.Term n)) (K level k width Forests code : Project.Term n) : Project.Formula 1 n :=
  withCodeFormula code (.conj
    (validFormula C.weaken.weaken.weaken ⟨width.weaken.weaken.weaken,.bound 1,Forests.weaken.weaken.weaken,.bound 0⟩)
    (branchFormula C.weaken.weaken.weaken T.weaken.weaken.weaken A.weaken.weaken.weaken X.weaken.weaken.weaken
      K.weaken.weaken.weaken level.weaken.weaken.weaken k.weaken.weaken.weaken width.weaken.weaken.weaken
      ⟨width.weaken.weaken.weaken,.bound 1,Forests.weaken.weaken.weaken,.bound 0⟩))

theorem targetFormula_delta0 {n : Nat} (C : ExpressionData (Project.Term n)) (T : MatrixArithmetic (Project.Term n))
    (A : CopyCoordinates.Context (Project.Term n)) (X : Data (Project.Term n)) (K level k width Forests code : Project.Term n) :
    (targetFormula C T A X K level k width Forests code).IsDelta0 :=
  withCodeFormula_delta0 _ (.conj (validFormula_delta0 _ _) (branchFormula_delta0 _ _ _ _ _ _ _ _ _))

theorem targetFormula_freeClosed {n : Nat} {C : ExpressionData (Project.Term n)} (hC : C.Closed)
    {T : MatrixArithmetic (Project.Term n)} (hT : CopyCoordinates.ArithmeticClosed T) {A : CopyCoordinates.Context (Project.Term n)} (hA : A.Closed)
    {X : Data (Project.Term n)} (hX : X.Closed) (K level k width Forests code : Project.Term n)
    (hK : K.freeSupport=[]) (hLevel : level.freeSupport=[]) (hk : k.freeSupport=[]) (hWidth : width.freeSupport=[])
    (hForests : Forests.freeSupport=[]) (hCode : code.freeSupport=[]) : (targetFormula C T A X K level k width Forests code).FreeClosed := by
  have hY : (⟨width.weaken.weaken.weaken,Project.Term.bound (depth := n+3) 1,Forests.weaken.weaken.weaken,.bound 0⟩ : Data (Project.Term (n+3))).Closed :=
    ⟨by simpa using hWidth,rfl,by simpa using hForests,rfl⟩
  apply withCodeFormula_freeClosed _ hCode
  simp only [Definitional.Formula.FreeClosed]
  exact ⟨validFormula_freeClosed hC.weaken.weaken.weaken hY,
    branchFormula_freeClosed hC.weaken.weaken.weaken hT.weaken.weaken.weaken hA.weaken.weaken.weaken hX.weaken.weaken.weaken hY
      K.weaken.weaken.weaken level.weaken.weaken.weaken k.weaken.weaken.weaken width.weaken.weaken.weaken
      (by simpa using hK) (by simpa using hLevel) (by simpa using hk) (by simpa using hWidth)⟩

theorem targetFormula_iff {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory) {n : Nat} (e : Env M n)
    (C : ExpressionData (Project.Term n)) (T : MatrixArithmetic (Project.Term n)) (A : CopyCoordinates.Context (Project.Term n))
    (X : Data (Project.Term n)) (K level k width Forests code : Project.Term n)
    (hC : (C.eval e).Valid M) (hT : (T.eval e).Valid M (C.eval e)) (hA : (A.eval e).Valid M (C.eval e))
    {m : M.Domain} {L : LayerStateSpace M.Domain} {V P H W Q J : M.Domain} (hLayers : LayerRun M (C.eval e) m L V P H)
    (hBad : BadAt M (C.eval e) m L H (K.eval e) (level.eval e) (A.eval e).last (A.eval e).root)
    (hLayer : RowAt M L.states H (k.eval e) W Q) (hRun : RowRun M (C.eval e) m L.rows W Q J)
    (hX : (X.eval e).Valid M (C.eval e)) (hFrom : FromRun M (C.eval e) m L.rows W J (X.eval e))
    (hForests : ∀ F, M.mem F (Forests.eval e) ↔ Forest M (C.eval e).omega (width.eval e) F) :
    Project.Formula.satisfies e (targetFormula C T A X K level k width Forests code) ↔
      TargetAt M (C.eval e) (T.eval e) (A.eval e) (X.eval e) (K.eval e) (level.eval e) (k.eval e) (width.eval e) (Forests.eval e) (code.eval e) := by
  apply withCodeFormula_iff_exists hM.1 e code _ (fun heights parents =>
    (⟨width.eval e,heights,Forests.eval e,parents⟩ : Data M.Domain).Valid M (C.eval e) ∧
      Branch M (C.eval e) (T.eval e) (A.eval e) (X.eval e) (K.eval e) (level.eval e) (k.eval e) (width.eval e)
        ⟨width.eval e,heights,Forests.eval e,parents⟩)
  intro b heights parents
  let Y : Data (Project.Term (n+3)) := ⟨width.weaken.weaken.weaken,.bound 1,Forests.weaken.weaken.weaken,.bound 0⟩
  have hValid := validFormula_iff hM (((e.push b).push heights).push parents) C.weaken.weaken.weaken Y
    (by simpa only [ExpressionData.eval_weaken] using hC)
  have hBranch (hY : (Y.eval (((e.push b).push heights).push parents)).Valid M (C.eval e)) :=
    branchFormula_iff hM (((e.push b).push heights).push parents) C.weaken.weaken.weaken T.weaken.weaken.weaken
      A.weaken.weaken.weaken X.weaken.weaken.weaken K.weaken.weaken.weaken level.weaken.weaken.weaken
      k.weaken.weaken.weaken width.weaken.weaken.weaken Y
      (by simpa only [ExpressionData.eval_weaken] using hC)
      (by simpa only [ExpressionData.eval_weaken,MatrixArithmetic.eval_weaken] using hT)
      (by simpa only [ExpressionData.eval_weaken,CopyCoordinates.Context.eval_weaken] using hA)
      (by simpa only [ExpressionData.eval_weaken] using hLayers)
      (by simpa only [ExpressionData.eval_weaken,CopyCoordinates.Context.eval_weaken,Term.eval_weaken] using hBad)
      (by simpa only [Term.eval_weaken] using hLayer)
      (by simpa only [ExpressionData.eval_weaken] using hRun)
      (by simpa only [ExpressionData.eval_weaken,Data.eval_weaken] using hX)
      (by simpa only [ExpressionData.eval_weaken,Data.eval_weaken] using hFrom)
      (by simpa only [ExpressionData.eval_weaken] using hY) rfl
      (by simpa only [Y,Data.eval,Data.map,Term.eval_weaken,ExpressionData.eval_weaken] using hForests)
  dsimp only [Y] at hValid
  simp only [Project.Formula.satisfies_conj_iff,hValid]
  constructor
  · rintro ⟨hY,hφ⟩
    have hB := (hBranch (by simpa only [ExpressionData.eval_weaken] using hY)).mp hφ
    simpa only [Y,ExpressionData.eval_weaken,MatrixArithmetic.eval_weaken,CopyCoordinates.Context.eval_weaken,Data.eval_weaken,
      Data.eval,Data.map,Data.weaken,Term.eval_weaken,Project.Term.eval_bound_one_push,Project.Term.eval_bound_zero_push] using And.intro hY hB
  · rintro ⟨hY,hB⟩
    have hY' : (Y.eval (((e.push b).push heights).push parents)).Valid M (C.eval e) := by
      simpa only [Y,Data.eval,Data.map,Term.eval_weaken,Project.Term.eval_bound_one_push,Project.Term.eval_bound_zero_push] using hY
    refine ⟨by simpa only [ExpressionData.eval_weaken] using hY',?_⟩
    apply (hBranch hY').mpr
    simpa only [Y,ExpressionData.eval_weaken,MatrixArithmetic.eval_weaken,CopyCoordinates.Context.eval_weaken,Data.eval_weaken,
      Data.eval,Data.map,Data.weaken,Term.eval_weaken,Project.Term.eval_bound_one_push,Project.Term.eval_bound_zero_push] using hB


private theorem withCodeFormula_iff_of_code {M : SetTheory.Structure.{u}} (he : Extensional M) {n : Nat} (e : Env M n)
    (code : Project.Term n) (body : Project.Formula 1 (n+3)) (P : M.Domain → M.Domain → Prop)
    (hBody : ∀ b heights parents, Codes M (code.eval e) heights parents →
      (Project.Formula.satisfies (((e.push b).push heights).push parents) body ↔ P heights parents)) :
    Project.Formula.satisfies e (withCodeFormula code body) ↔ ∃ heights parents, Codes M (code.eval e) heights parents ∧ P heights parents := by
  rw [withCodeFormula_iff he]
  constructor
  · rintro ⟨b,_,heights,_,parents,_,hCode,hφ⟩
    exact ⟨heights,parents,hCode,(hBody b heights parents hCode).mp hφ⟩
  · rintro ⟨heights,parents,hCode,hP⟩
    obtain ⟨b,hb,hh,hp⟩ := code_component_container hCode
    exact ⟨b,hb,heights,hh,parents,hp,hCode,(hBody b heights parents hCode).mpr hP⟩

def copiedFormula {n : Nat} (C : ExpressionData (Project.Term n)) (T : MatrixArithmetic (Project.Term n))
    (A : CopyCoordinates.Context (Project.Term n)) (m SourceForests K level k width Forests Sources SourceMap code : Project.Term n) : Project.Formula 1 n :=
  Project.Formula.existsMem Sources (.conj (memPairFormula SourceMap.weaken k.weaken (.bound 0))
    (withCodeFormula (.bound 0)
      (targetFormula C.weaken.weaken.weaken.weaken T.weaken.weaken.weaken.weaken A.weaken.weaken.weaken.weaken
        ⟨m.weaken.weaken.weaken.weaken,.bound 1,SourceForests.weaken.weaken.weaken.weaken,.bound 0⟩
        K.weaken.weaken.weaken.weaken level.weaken.weaken.weaken.weaken k.weaken.weaken.weaken.weaken
        width.weaken.weaken.weaken.weaken Forests.weaken.weaken.weaken.weaken code.weaken.weaken.weaken.weaken)))

theorem copiedFormula_delta0 {n : Nat} (C : ExpressionData (Project.Term n)) (T : MatrixArithmetic (Project.Term n))
    (A : CopyCoordinates.Context (Project.Term n)) (m SourceForests K level k width Forests Sources SourceMap code : Project.Term n) :
    (copiedFormula C T A m SourceForests K level k width Forests Sources SourceMap code).IsDelta0 :=
  .existsMem _ (.conj (memPairFormula_delta0 _ _ _) (withCodeFormula_delta0 _ (targetFormula_delta0 _ _ _ _ _ _ _ _ _ _)))

theorem copiedFormula_freeClosed {n : Nat} {C : ExpressionData (Project.Term n)} (hC : C.Closed)
    {T : MatrixArithmetic (Project.Term n)} (hT : CopyCoordinates.ArithmeticClosed T) {A : CopyCoordinates.Context (Project.Term n)} (hA : A.Closed)
    (m SourceForests K level k width Forests Sources SourceMap code : Project.Term n)
    (hm : m.freeSupport=[]) (hSourceForests : SourceForests.freeSupport=[]) (hK : K.freeSupport=[]) (hLevel : level.freeSupport=[])
    (hk : k.freeSupport=[]) (hWidth : width.freeSupport=[]) (hForests : Forests.freeSupport=[])
    (hSources : Sources.freeSupport=[]) (hSourceMap : SourceMap.freeSupport=[]) (hCode : code.freeSupport=[]) :
    (copiedFormula C T A m SourceForests K level k width Forests Sources SourceMap code).FreeClosed := by
  have hTarget := targetFormula_freeClosed hC.weaken.weaken.weaken.weaken hT.weaken.weaken.weaken.weaken hA.weaken.weaken.weaken.weaken
    (X := ⟨m.weaken.weaken.weaken.weaken,Project.Term.bound (depth := n+4) 1,SourceForests.weaken.weaken.weaken.weaken,.bound 0⟩)
    ⟨by simpa using hm,rfl,by simpa using hSourceForests,rfl⟩
    K.weaken.weaken.weaken.weaken level.weaken.weaken.weaken.weaken k.weaken.weaken.weaken.weaken width.weaken.weaken.weaken.weaken
    Forests.weaken.weaken.weaken.weaken code.weaken.weaken.weaken.weaken
    (by simpa using hK) (by simpa using hLevel) (by simpa using hk) (by simpa using hWidth) (by simpa using hForests) (by simpa using hCode)
  have hWith := withCodeFormula_freeClosed (Project.Term.bound (depth := n+1) 0) rfl hTarget
  simp [copiedFormula,Project.Formula.existsMem,Definitional.Formula.FreeClosed,memPairFormula,codeFormula,pairFormula,
    Project.Formula.forallMem,hSources,hSourceMap,hk,hWith]

theorem copiedFormula_iff {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory) {n : Nat} (e : Env M n)
    (C : ExpressionData (Project.Term n)) (T : MatrixArithmetic (Project.Term n)) (A : CopyCoordinates.Context (Project.Term n))
    (m SourceForests K level k width Forests Sources SourceMap code : Project.Term n)
    (hC : (C.eval e).Valid M) (hT : (T.eval e).Valid M (C.eval e)) (hA : (A.eval e).Valid M (C.eval e))
    {L : LayerStateSpace M.Domain} {V P H B : M.Domain} (hLayers : LayerRun M (C.eval e) (m.eval e) L V P H)
    (hBad : BadAt M (C.eval e) (m.eval e) L H (K.eval e) (level.eval e) (A.eval e).last (A.eval e).root)
    (hSources : SourceGraph M (C.eval e) (m.eval e) L H B (Sources.eval e) (SourceMap.eval e))
    (hSourceForests : SourceForests.eval e=L.rows.forests)
    (hForests : ∀ F, M.mem F (Forests.eval e) ↔ Forest M (C.eval e).omega (width.eval e) F) :
    Project.Formula.satisfies e (copiedFormula C T A m SourceForests K level k width Forests Sources SourceMap code) ↔
      M.mem (k.eval e) B ∧ ExpandedAt M (C.eval e) (T.eval e) (A.eval e) (m.eval e) L H
        (K.eval e) (level.eval e) (k.eval e) (width.eval e) (Forests.eval e) (code.eval e) := by
  have hPacked (source : M.Domain) (hAt : MemPair M (SourceMap.eval e) (k.eval e) source) :
      Project.Formula.satisfies (e.push source) (withCodeFormula (.bound 0)
        (targetFormula C.weaken.weaken.weaken.weaken T.weaken.weaken.weaken.weaken A.weaken.weaken.weaken.weaken
          ⟨m.weaken.weaken.weaken.weaken,.bound 1,SourceForests.weaken.weaken.weaken.weaken,.bound 0⟩
          K.weaken.weaken.weaken.weaken level.weaken.weaken.weaken.weaken k.weaken.weaken.weaken.weaken
          width.weaken.weaken.weaken.weaken Forests.weaken.weaken.weaken.weaken code.weaken.weaken.weaken.weaken)) ↔
      ∃ sourceHeights sourceParents, Codes M source sourceHeights sourceParents ∧
        TargetAt M (C.eval e) (T.eval e) (A.eval e) ⟨m.eval e,sourceHeights,L.rows.forests,sourceParents⟩
          (K.eval e) (level.eval e) (k.eval e) (width.eval e) (Forests.eval e) (code.eval e) := by
    apply withCodeFormula_iff_of_code hM.1 (e.push source) (.bound 0) _ (fun sh sp =>
      TargetAt M (C.eval e) (T.eval e) (A.eval e) ⟨m.eval e,sh,L.rows.forests,sp⟩
        (K.eval e) (level.eval e) (k.eval e) (width.eval e) (Forests.eval e) (code.eval e))
    intro b sh sp hCode
    have hSource := ((hSources.rows (k.eval e) source).mp hAt).2
    obtain ⟨W,Q,J,hLayer,hRun,hX,hFrom⟩ := hSource.read hM.1 hCode
    have h := targetFormula_iff hM ((((e.push source).push b).push sh).push sp)
      C.weaken.weaken.weaken.weaken T.weaken.weaken.weaken.weaken A.weaken.weaken.weaken.weaken
      ⟨m.weaken.weaken.weaken.weaken,.bound 1,SourceForests.weaken.weaken.weaken.weaken,.bound 0⟩
      K.weaken.weaken.weaken.weaken level.weaken.weaken.weaken.weaken k.weaken.weaken.weaken.weaken
      width.weaken.weaken.weaken.weaken Forests.weaken.weaken.weaken.weaken code.weaken.weaken.weaken.weaken
      (by simpa only [ExpressionData.eval_weaken] using hC)
      (by simpa only [ExpressionData.eval_weaken,MatrixArithmetic.eval_weaken] using hT)
      (by simpa only [ExpressionData.eval_weaken,CopyCoordinates.Context.eval_weaken] using hA)
      (by simpa only [ExpressionData.eval_weaken] using hLayers)
      (by simpa only [ExpressionData.eval_weaken,CopyCoordinates.Context.eval_weaken,Term.eval_weaken] using hBad)
      (by simpa only [Term.eval_weaken] using hLayer)
      (by simpa only [ExpressionData.eval_weaken] using hRun)
      (by simpa only [ExpressionData.eval_weaken,Data.eval,Data.map,Term.eval_weaken,Project.Term.eval_bound_one_push,
        Project.Term.eval_bound_zero_push,hSourceForests] using hX)
      (by simpa only [ExpressionData.eval_weaken,Data.eval,Data.map,Term.eval_weaken,Project.Term.eval_bound_one_push,
        Project.Term.eval_bound_zero_push,hSourceForests] using hFrom)
      (by simpa only [ExpressionData.eval_weaken,Term.eval_weaken] using hForests)
    simpa only [ExpressionData.eval_weaken,MatrixArithmetic.eval_weaken,CopyCoordinates.Context.eval_weaken,Data.eval,Data.map,
      Term.eval_weaken,Project.Term.eval_bound_one_push,Project.Term.eval_bound_zero_push,hSourceForests] using h
  simp only [copiedFormula,Project.Formula.satisfies_existsMem_iff,Project.Formula.satisfies_conj_iff,memPairFormula_iff hM.1,Term.eval_weaken]
  constructor
  · rintro ⟨source,_,hAt,hCode⟩
    obtain ⟨sh,sp,hSourceCode,hTarget⟩ := (hPacked source hAt).mp hCode
    obtain ⟨hk,hSource⟩ := (hSources.rows (k.eval e) source).mp hAt
    exact ⟨hk,source,hSource,sh,sp,hSourceCode,hTarget⟩
  · rintro ⟨hk,source,hSource,sh,sp,hSourceCode,hTarget⟩
    have hAt := (hSources.rows (k.eval e) source).mpr ⟨hk,hSource⟩
    exact ⟨source,(hSources.graph.bounds hM.1 hAt).2,hAt,(hPacked source hAt).mpr ⟨sh,sp,hSourceCode,hTarget⟩⟩


private def copiedSchema : Project.Delta0BinarySchema 23 where
  body := copiedFormula ⟨.bound 24,.bound 23,.bound 22,.bound 21,.bound 20⟩
    ⟨.bound 19,.bound 18,.bound 17,.bound 16,.bound 15,.bound 14⟩ ⟨.bound 13,.bound 12,.bound 11,.bound 10⟩
    (.bound 9) (.bound 8) (.bound 7) (.bound 6) (.bound 1) (.bound 5) (.bound 4) (.bound 3) (.bound 2) (.bound 0)
  freeClosed := copiedFormula_freeClosed ⟨rfl,rfl,rfl,rfl,rfl⟩ ⟨rfl,rfl,rfl,rfl,rfl,rfl⟩ ⟨rfl,rfl,rfl,rfl⟩
    _ _ _ _ _ _ _ _ _ _ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
  delta0 := copiedFormula_delta0 _ _ _ _ _ _ _ _ _ _ _ _ _

private def copiedEnv {M : SetTheory.Structure.{u}} (C : ExpressionData M.Domain) (T : MatrixArithmetic M.Domain)
    (A : CopyCoordinates.Context M.Domain) (m SourceForests K level width Forests Sources SourceMap : M.Domain) : Env M 23 :=
  (((((((((((((((((((((((oneEnv C.omega).push C.zero).push C.one).push C.sequences).push C.expressions).push T.addPairs).push T.plus).push T.mulPairs).push T.times).push T.diffPairs).push T.difference).push A.last).push A.root).push A.length).push A.first).push m).push SourceForests).push K).push level).push width).push Forests).push Sources).push SourceMap)

/-- 三种实际单层复制经Δ₀函数像形成整个有限复制塔；没有 supplied totality 假设。 -/
theorem tower_exists_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {m : M.Domain} {L : LayerStateSpace M.Domain} {V P H K level B n : M.Domain}
    (hLayers : LayerRun M C m L V P H) {A : CopyCoordinates.Context M.Domain} (hA : A.Valid M C)
    (hBad : BadAt M C m L H K level A.last A.root) (hB : M.mem B C.omega) (hn : M.mem n C.omega) :
    ∃ Forests CodeSpace G, Tower M C T A m L H K level B n Forests CodeSpace G := by
  obtain ⟨Forests,hForests⟩ := forest_space_exists_d hM hC hn
  obtain ⟨Sources,SourceMap,hSources⟩ := source_graph_exists_d hM hC hLayers hB
  let e := copiedEnv C T A m L.rows.forests K level n Forests Sources SourceMap
  have hφ (k code : M.Domain) : Project.Formula.satisfies ((e.push k).push code) copiedSchema.body ↔
      M.mem k B ∧ ExpandedAt M C T A m L H K level k n Forests code :=
    copiedFormula_iff hM ((e.push k).push code) ⟨.bound 24,.bound 23,.bound 22,.bound 21,.bound 20⟩
      ⟨.bound 19,.bound 18,.bound 17,.bound 16,.bound 15,.bound 14⟩ ⟨.bound 13,.bound 12,.bound 11,.bound 10⟩
      (.bound 9) (.bound 8) (.bound 7) (.bound 6) (.bound 1) (.bound 5) (.bound 4) (.bound 3) (.bound 2) (.bound 0)
      hC hT hA hLayers hBad hSources rfl hForests
  have hK := (bad_indices_d hM hC hLayers hBad).1
  have hTotal : ∀ k, M.mem k B → ∃ code, Project.Formula.satisfies ((e.push k).push code) copiedSchema.body := by
    intro k hk
    obtain ⟨code,hCode⟩ := expanded_at_exists_d hM hC hT hLayers hA hBad
      ((omega_isOrdinal_d hM hC.omega).transitive B hB k hk) hn hForests
    exact ⟨code,(hφ k code).mpr ⟨hk,hCode⟩⟩
  obtain ⟨CodeSpace,hCodes⟩ := KP1Y.functional_image_d hM copiedSchema e B hTotal
    (fun k _ code code' hCode hCode' => ((hφ k code).mp hCode).2.unique_d hM hC hLayers hK ((hφ k code').mp hCode').2)
  have hRange (code : M.Domain) : M.mem code CodeSpace ↔ ∃ k, M.mem k B ∧ ExpandedAt M C T A m L H K level k n Forests code := by
    have hr := hCodes code
    simp only [hφ] at hr
    exact hr.trans ⟨fun ⟨k,hk,_,h⟩ => ⟨k,hk,h⟩,fun ⟨k,hk,h⟩ => ⟨k,hk,hk,h⟩⟩
  obtain ⟨G,hSupport,hRaw⟩ := relation_comprehension_d hM copiedSchema e B CodeSpace
  have hRows (k code : M.Domain) : MemPair M G k code ↔ M.mem k B ∧ ExpandedAt M C T A m L H K level k n Forests code := by
    have hr := hRaw k code
    rw [hφ] at hr
    exact hr.trans ⟨fun h => h.2.2,fun h => ⟨h.1,(hRange code).mpr ⟨k,h⟩,h⟩⟩
  refine ⟨Forests,CodeSpace,G,hB,hn,hForests,⟨hSupport,?_,?_⟩,hRange,hRows⟩
  · intro k hk
    obtain ⟨code,hCode⟩ := hTotal k hk
    have hExpanded := (hφ k code).mp hCode
    exact ⟨code,(hRange code).mpr ⟨k,hExpanded⟩,(hRows k code).mpr hExpanded⟩
  · intro k code code' hCode hCode'
    exact ((hRows k code).mp hCode).2.unique_d hM hC hLayers hK ((hRows k code').mp hCode').2

theorem Tower.code_valid {M : SetTheory.Structure.{u}} {C : ExpressionData M.Domain} {T : MatrixArithmetic M.Domain}
    {A : CopyCoordinates.Context M.Domain} {m : M.Domain} {L : LayerStateSpace M.Domain}
    {H K level B n Forests CodeSpace G k code : M.Domain}
    (h : Tower M C T A m L H K level B n Forests CodeSpace G) (hAt : MemPair M G k code) : CodeValid M C n Forests code := by
  obtain ⟨_,_,_,_,_,heights,parents,hCode,hValid,_⟩ := ((h.rows k code).mp hAt).2
  exact ⟨heights,parents,hCode,hValid⟩


/-- 原算法的宽度 last+N*(last-root)，仍保留独立且明确的山形horizon B。 -/
theorem tower_width_exists_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {m : M.Domain} {L : LayerStateSpace M.Domain} {V P H K level B N : M.Domain}
    (hLayers : LayerRun M C m L V P H) {A : CopyCoordinates.Context M.Domain} (hA : A.Valid M C)
    (hBad : BadAt M C m L H K level A.last A.root) (hB : M.mem B C.omega) (hN : M.mem N C.omega) :
    ∃ n Forests CodeSpace G, CopyCoordinates.Width M C T A N n ∧ Tower M C T A m L H K level B n Forests CodeSpace G := by
  obtain ⟨n,hn,hWidth⟩ := CopyCoordinates.encode_exists_d hM hC hT hA hA.last hN
  obtain ⟨Forests,CodeSpace,G,hTower⟩ := tower_exists_d hM hC hT hLayers hA hBad hB hn
  exact ⟨n,Forests,CodeSpace,G,hWidth,hTower⟩

theorem width_tower_unique {M : SetTheory.Structure.{u}} (he : Extensional M)
    {C : ExpressionData M.Domain} {T : MatrixArithmetic M.Domain} (hT : T.Valid M C) {A : CopyCoordinates.Context M.Domain}
    {m : M.Domain} {L : LayerStateSpace M.Domain} {H K level B N n n' Forests Forests' CodeSpace CodeSpace' G G' : M.Domain}
    (hWidth : CopyCoordinates.Width M C T A N n) (hWidth' : CopyCoordinates.Width M C T A N n')
    (h : Tower M C T A m L H K level B n Forests CodeSpace G) (h' : Tower M C T A m L H K level B n' Forests' CodeSpace' G') :
    n=n' ∧ Forests=Forests' ∧ CodeSpace=CodeSpace' ∧ G=G' := by
  have hnn := CopyCoordinates.encode_unique he hT hWidth hWidth'
  subst n'
  exact ⟨rfl,h.unique he h'⟩

/-- 连坐标上下文也从真实坏根构造；没有遗留的根/高度或复制总性假设。 -/
theorem tower_from_bad_exists_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {m : M.Domain} {L : LayerStateSpace M.Domain} {V P H K level x y B N : M.Domain}
    (hLayers : LayerRun M C m L V P H) (hBad : BadAt M C m L H K level x y)
    (hB : M.mem B C.omega) (hN : M.mem N C.omega) :
    ∃ A n Forests CodeSpace G, A.last=x ∧ A.root=y ∧ A.Valid M C ∧ CopyCoordinates.Width M C T A N n ∧
      Tower M C T A m L H K level B n Forests CodeSpace G := by
  obtain ⟨_,_,hx,hy⟩ := bad_indices_d hM hC hLayers hBad
  have hw := omega_isOrdinal_d hM hC.omega
  have hxNat := hw.transitive m hLayers.space.rows.width x hx
  have hyNat := hw.transitive m hLayers.space.rows.width y hy
  have hyx : M.mem y x := by
    obtain ⟨_,_,_,_,_,_,hRun,_,_,_,_,hRow,hParent,_⟩ := hBad
    exact (hRun.at_numeric_d hM hC hRow).forest.left x y hParent
  obtain ⟨A,hAx,hAy,hA⟩ := CopyCoordinates.context_exists_d hM hC hxNat hyNat hyx
  have hBadA : BadAt M C m L H K level A.last A.root := by simpa only [hAx,hAy] using hBad
  obtain ⟨n,Forests,CodeSpace,G,hWidth,hTower⟩ := tower_width_exists_d hM hC hT hLayers hA hBadA hB hN
  exact ⟨A,n,Forests,CodeSpace,G,hAx,hAy,hA,hWidth,hTower⟩


theorem coordinates_unique_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {A A' : CopyCoordinates.Context M.Domain}
    (hA : A.Valid M C) (hA' : A'.Valid M C) (hLast : A.last=A'.last) (hRoot : A.root=A'.root) : A=A' := by
  cases A with
  | mk last root length first =>
    cases A' with
    | mk last' root' length' first' =>
      dsimp only at hLast hRoot
      subst last'
      subst root'
      have hLength := truncated_difference_unique_d hM hC hA.difference hA'.difference
      change length=length' at hLength
      subst length'
      have hFirst := Structure.SuccessorOf.eq hM.1 hA.first hA'.first
      change first=first' at hFirst
      subst first'
      rfl

theorem full_tower_unique_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {A A' : CopyCoordinates.Context M.Domain} (hA : A.Valid M C) (hA' : A'.Valid M C)
    (hLast : A.last=A'.last) (hRoot : A.root=A'.root) {m : M.Domain} {L : LayerStateSpace M.Domain}
    {H K level B N n n' Forests Forests' CodeSpace CodeSpace' G G' : M.Domain}
    (hWidth : CopyCoordinates.Width M C T A N n) (hWidth' : CopyCoordinates.Width M C T A' N n')
    (h : Tower M C T A m L H K level B n Forests CodeSpace G) (h' : Tower M C T A' m L H K level B n' Forests' CodeSpace' G') :
    A=A' ∧ n=n' ∧ Forests=Forests' ∧ CodeSpace=CodeSpace' ∧ G=G' := by
  have hAA := coordinates_unique_d hM hC hA hA' hLast hRoot
  subst A'
  exact ⟨rfl,width_tower_unique hM.1 hT hWidth hWidth' h h'⟩

end KP1Y.OneYFinite.CopyTower
