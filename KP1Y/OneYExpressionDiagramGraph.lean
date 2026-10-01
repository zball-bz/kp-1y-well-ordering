import KP1Y.OneYExpressionDiagram
import KP1Y.RankedUnion

/-! 规范根图计算的真实 Σ₁ 证书与全局表达式到图的集合函数。 -/
namespace KP1Y.OneYFinite.ExpressionDiagram
open YesMetaZFC YesMetaZFC.SetTheory YesMetaZFC.SetTheory.Definitional
open KP1Y.Kuratowski KP1Y.Functions KP1Y.Naturals KP1Y.Bounded
universe u v

structure CalculationData (α : Type u) where
  width : α
  linear : α
  initial : α
  rowValues : α
  rowForests : α
  rowStates : α
  layerStates : α
  layers : α
  step : α
  stepBound : α
  bound : α
  slots : α
  size : α
  histories : α
  runs : α
  atoms : α
  length : α
  indices : α

def CalculationData.map {α : Type u} {β : Type v} (W : CalculationData α) (f : α → β) : CalculationData β :=
  ⟨f W.width,f W.linear,f W.initial,f W.rowValues,f W.rowForests,f W.rowStates,f W.layerStates,f W.layers,f W.step,f W.stepBound,f W.bound,f W.slots,f W.size,f W.histories,f W.runs,f W.atoms,f W.length,f W.indices⟩

def CalculationData.eval {M : SetTheory.Structure.{u}} {n : Nat} (W : CalculationData (Project.Term n)) (e : Env M n) : CalculationData M.Domain :=
  W.map (fun t => t.eval e)

def CalculationData.weaken {n : Nat} (W : CalculationData (Project.Term n)) : CalculationData (Project.Term (n+1)) := W.map (fun t => t.weaken)

theorem CalculationData.eval_weaken {M : SetTheory.Structure.{u}} {n : Nat}
    (W : CalculationData (Project.Term n)) (e : Env M n) (x : M.Domain) : W.weaken.eval (e.push x)=W.eval e := by
  cases W
  simp [CalculationData.eval,CalculationData.weaken,CalculationData.map,Term.eval_weaken]

def CalculationData.rows {α : Type u} (W : CalculationData α) : RowStateSpace α := ⟨W.rowValues,W.rowForests,W.rowStates⟩
def CalculationData.space {α : Type u} (W : CalculationData α) : LayerStateSpace α := ⟨W.rows,W.layerStates⟩

structure CalculationData.Closed {n : Nat} (W : CalculationData (Project.Term n)) : Prop where
  width : W.width.freeSupport=[]
  linear : W.linear.freeSupport=[]
  initial : W.initial.freeSupport=[]
  rowValues : W.rowValues.freeSupport=[]
  rowForests : W.rowForests.freeSupport=[]
  rowStates : W.rowStates.freeSupport=[]
  layerStates : W.layerStates.freeSupport=[]
  layers : W.layers.freeSupport=[]
  step : W.step.freeSupport=[]
  stepBound : W.stepBound.freeSupport=[]
  bound : W.bound.freeSupport=[]
  slots : W.slots.freeSupport=[]
  size : W.size.freeSupport=[]
  histories : W.histories.freeSupport=[]
  runs : W.runs.freeSupport=[]
  atoms : W.atoms.freeSupport=[]
  length : W.length.freeSupport=[]
  indices : W.indices.freeSupport=[]

theorem CalculationData.Closed.rows {n : Nat} {W : CalculationData (Project.Term n)} (h : W.Closed) : W.rows.Closed :=
  ⟨h.rowValues,h.rowForests,h.rowStates⟩

def extractionParams {n : Nat} (C : ExpressionData (Project.Term n)) (m : Project.Term n)
    (R : RowStateSpace (Project.Term n)) (Pairs Table : Project.Term n) : Fin 11 → Project.Term n :=
  Fin.cases Table (Fin.cases Pairs (Fin.cases R.states (Fin.cases R.forests (Fin.cases R.values (Fin.cases m (Fin.cases C.expressions (Fin.cases C.sequences (Fin.cases C.one (Fin.cases C.zero (Fin.cases C.omega (fun i => Fin.elim0 i)))))))))))

def stepCertificateFormula {n : Nat} (C : ExpressionData (Project.Term n)) (m : Project.Term n)
    (R : RowStateSpace (Project.Term n)) (Pairs Table Step States Bound : Project.Term n) : Project.Formula 1 n :=
  sigmaGraphCertificateFormula extractionStepMatrix (extractionParams C m R Pairs Table) Step States States Bound

theorem stepCertificateFormula_delta0 {n : Nat} (C : ExpressionData (Project.Term n)) (m : Project.Term n)
    (R : RowStateSpace (Project.Term n)) (Pairs Table Step States Bound : Project.Term n) :
    (stepCertificateFormula C m R Pairs Table Step States Bound).IsDelta0 := sigmaGraphCertificateFormula_delta0 _ _ _ _ _ _

theorem stepCertificateFormula_freeClosed {n : Nat} {C : ExpressionData (Project.Term n)} (hC : C.Closed)
    {R : RowStateSpace (Project.Term n)} (hR : R.Closed) (m Pairs Table Step States Bound : Project.Term n)
    (hm : m.freeSupport=[]) (hPairs : Pairs.freeSupport=[]) (hTable : Table.freeSupport=[])
    (hStep : Step.freeSupport=[]) (hStates : States.freeSupport=[]) (hBound : Bound.freeSupport=[]) :
    (stepCertificateFormula C m R Pairs Table Step States Bound).FreeClosed := by
  apply sigmaGraphCertificateFormula_freeClosed
  · intro i
    exact Fin.cases hTable (Fin.cases hPairs (Fin.cases hR.states (Fin.cases hR.forests (Fin.cases hR.values (Fin.cases hm (Fin.cases hC.expressions (Fin.cases hC.sequences (Fin.cases hC.one (Fin.cases hC.zero (Fin.cases hC.omega (fun i => Fin.elim0 i))))))))))) i
  · exact hStep
  · exact hStates
  · exact hStates
  · exact hBound

theorem stepCertificateFormula_iff {M : SetTheory.Structure.{u}} (he : Extensional M) {n : Nat} (e : Env M n)
    (C : ExpressionData (Project.Term n)) (m : Project.Term n) (R : RowStateSpace (Project.Term n))
    (Pairs Table Step States Bound : Project.Term n) :
    Project.Formula.satisfies e (stepCertificateFormula C m R Pairs Table Step States Bound) ↔
      SigmaGraphCertificate extractionStepMatrix (extractionStepEnv (C.eval e) (m.eval e) (R.eval e) (Pairs.eval e) (Table.eval e))
        (Step.eval e) (States.eval e) (States.eval e) (Bound.eval e) := by
  apply sigmaGraphCertificateFormula_iff_bound he
  intro i
  exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun i => Fin.elim0 i))))))))))) i

structure Calculation (M : SetTheory.Structure.{u}) (C : ExpressionData M.Domain) (T : MatrixArithmetic M.Domain)
    (Forests Pairs Codes V A : M.Domain) (W : CalculationData M.Domain) : Prop where
  legal : LegalAt M C.omega C.zero C.one V W.width
  linear : LinearForest M C.omega W.width W.linear
  selected : Selects true M C W.width W.linear V W.initial
  space : LayerSpaceCertificate M C Forests W.width W.space
  base : RootedRow M C W.width V W.initial
  step : SigmaGraphCertificate extractionStepMatrix (extractionStepEnv C W.width W.rows T.diffPairs T.difference)
    W.step W.layerStates W.layerStates W.stepBound
  run : RunAlong M C.omega C.zero W.layerStates W.step V W.initial W.layers
  bound : SequenceBound M C W.width V W.bound
  slots : MulAt M T.mulPairs T.times W.bound W.width W.slots
  size : MulAt M T.mulPairs T.times W.slots W.bound W.size
  family : RowFamily M C W.width W.space W.layers W.bound W.histories W.runs
  atoms : AtomMap M C T W.width W.bound W.slots W.size W.rows W.histories W.runs Pairs Codes W.atoms
  filtered : Filter.Filtered M C.omega W.atoms W.size Codes W.length A W.indices

theorem Calculation.layer_run_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {Forests Pairs Codes V A : M.Domain} (hForests : AllForests M C.omega Forests) {W : CalculationData M.Domain}
    (h : Calculation M C T Forests Pairs Codes V A W) : LayerRun M C W.width W.space V W.initial W.layers :=
  (run_along_iff_layer_run_d hM hC ((layer_space_certificate_iff hC hForests).mp h.space) hT.diff h.step h.base).mp h.run

theorem Calculation.expression_graph_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {Forests : M.Domain} (hForests : AllForests M C.omega Forests) (D : KP1Y.Reflection.Data M.Domain)
    {V A : M.Domain} {W : CalculationData M.Domain} (h : Calculation M C T Forests D.pairs D.edgeCodes V A W) :
    ExpressionGraph M C T D V W.width A := by
  have hLayers := h.layer_run_d hM hC hT hForests
  have hS := (hT.mul.mul_iff_product hM h.bound.1.1 h.legal.1.1).mp h.slots
  have hSn := natural_product_closed_d hM hC h.bound.1.1 h.legal.1.1 hS
  have hN := (hT.mul.mul_iff_product hM hSn h.bound.1.1).mp h.size
  exact ⟨h.legal,W.linear,W.initial,W.space,W.layers,h.linear,h.selected,hLayers,
    W.bound,W.slots,W.size,W.histories,W.runs,W.atoms,W.length,W.indices,h.bound,hS,hN,h.family,h.atoms,h.filtered⟩

theorem calculation_exists_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {Forests : M.Domain} (hForests : AllForests M C.omega Forests) {D : KP1Y.Reflection.Data M.Domain}
    {V m A : M.Domain} (h : ExpressionGraph M C T D V m A) :
    ∃ W, Calculation M C T Forests D.pairs D.edgeCodes V A W := by
  obtain ⟨hLegal,F,P,L,H,hF,hP,hLayers,B,S,N,Histories,Runs,Map,len,I,hB,hS,hN,hFamily,hMap,hFilter⟩ := h
  obtain ⟨Step,Bound,hStep⟩ := layer_step_certificate_exists_d hM hC hLayers.space hT.diff
  have hSn := natural_product_closed_d hM hC hB.1.1 hLegal.1.1 hS
  refine ⟨⟨m,F,P,L.rows.values,L.rows.forests,L.rows.states,L.states,H,Step,Bound,B,S,N,Histories,Runs,Map,len,I⟩,
    hLegal,hF,hP,(layer_space_certificate_iff hC hForests).mpr hLayers.space,hLayers.base,hStep,
    (run_along_iff_layer_run_d hM hC hLayers.space hT.diff hStep hLayers.base).mpr hLayers,hB,
    (hT.mul.mul_iff_product hM hB.1.1 hLegal.1.1).mpr hS,(hT.mul.mul_iff_product hM hSn hB.1.1).mpr hN,hFamily,hMap,hFilter⟩


def calculationFormula {n : Nat} (C : ExpressionData (Project.Term n)) (T : MatrixArithmetic (Project.Term n))
    (Forests Pairs Codes V A : Project.Term n) (W : CalculationData (Project.Term n)) : Project.Formula 1 n :=
  (.conj (legalAtFormula C.omega C.zero C.one V W.width)
    (.conj (linearForestFormula C.omega W.width W.linear)
    (.conj (selectsFormula true C W.width W.linear V W.initial)
    (.conj (layerSpaceCertificateFormula C Forests W.width W.rows W.layerStates)
    (.conj (rootedRowFormula C W.width V W.initial)
    (.conj (stepCertificateFormula C W.width W.rows T.diffPairs T.difference W.step W.layerStates W.stepBound)
    (.conj (runAlongFormula C.omega C.zero W.layerStates W.step V W.initial W.layers)
    (.conj (sequenceBoundFormula C.omega C.zero W.width V W.bound)
    (.conj (mulAtFormula T.mulPairs T.times W.bound W.width W.slots)
    (.conj (mulAtFormula T.mulPairs T.times W.slots W.bound W.size)
    (.conj (rowFamilyFormula C W.width W.rows W.layerStates W.layers W.bound W.histories W.runs T.diffPairs T.difference)
    (.conj (atomMapFormula C T W.width W.bound W.slots W.size W.rows W.histories W.runs Pairs Codes W.atoms)
    (Filter.filteredFormula C.omega W.atoms W.size Codes W.length A W.indices)))))))))))))

theorem calculationFormula_delta0 {n : Nat} (C : ExpressionData (Project.Term n)) (T : MatrixArithmetic (Project.Term n))
    (Forests Pairs Codes V A : Project.Term n) (W : CalculationData (Project.Term n)) :
    (calculationFormula C T Forests Pairs Codes V A W).IsDelta0 :=
  (.conj (legalAtFormula_delta0 _ _ _ _ _)
    (.conj (linearForestFormula_delta0 _ _ _)
    (.conj (selectsFormula_delta0 _ _ _ _ _ _)
    (.conj (layerSpaceCertificateFormula_delta0 _ _ _ _ _)
    (.conj (rootedRowFormula_delta0 _ _ _ _)
    (.conj (stepCertificateFormula_delta0 _ _ _ _ _ _ _ _)
    (.conj (runAlongFormula_delta0 _ _ _ _ _ _ _)
    (.conj (sequenceBoundFormula_delta0 _ _ _ _ _)
    (.conj (mulAtFormula_delta0 _ _ _ _ _)
    (.conj (mulAtFormula_delta0 _ _ _ _ _)
    (.conj (rowFamilyFormula_delta0 _ _ _ _ _ _ _ _ _ _)
    (.conj (atomMapFormula_delta0 _ _ _ _ _ _ _ _ _ _ _ _)
    (Filter.filteredFormula_delta0 _ _ _ _ _ _ _)))))))))))))

theorem calculationFormula_freeClosed {n : Nat} {C : ExpressionData (Project.Term n)} (hC : C.Closed)
    {T : MatrixArithmetic (Project.Term n)} (hT : CopyCoordinates.ArithmeticClosed T)
    {W : CalculationData (Project.Term n)} (hW : W.Closed) (Forests Pairs Codes V A : Project.Term n)
    (hForests : Forests.freeSupport=[]) (hPairs : Pairs.freeSupport=[]) (hCodes : Codes.freeSupport=[])
    (hV : V.freeSupport=[]) (hA : A.freeSupport=[]) : (calculationFormula C T Forests Pairs Codes V A W).FreeClosed := by
  simp only [calculationFormula,Definitional.Formula.FreeClosed]
  exact ⟨legalAtFormula_freeClosed _ _ _ _ _ hC.omega hC.zero hC.one hV hW.width,
    linearForestFormula_freeClosed _ _ _ hC.omega hW.width hW.linear,
    selectsFormula_freeClosed true hC _ _ _ _ hW.width hW.linear hV hW.initial,
    layerSpaceCertificateFormula_freeClosed hC hW.rows _ _ _ hForests hW.width hW.layerStates,
    rootedRowFormula_freeClosed hC _ _ _ hW.width hV hW.initial,
    stepCertificateFormula_freeClosed hC hW.rows _ _ _ _ _ _ hW.width hT.diffPairs hT.difference hW.step hW.layerStates hW.stepBound,
    runAlongFormula_freeClosed _ _ _ _ _ _ _ hC.omega hC.zero hW.layerStates hW.step hV hW.initial hW.layers,
    sequenceBoundFormula_freeClosed _ _ _ _ _ hC.omega hC.zero hW.width hV hW.bound,
    mulAtFormula_freeClosed _ _ _ _ _ hT.mulPairs hT.times hW.bound hW.width hW.slots,
    mulAtFormula_freeClosed _ _ _ _ _ hT.mulPairs hT.times hW.slots hW.bound hW.size,
    rowFamilyFormula_freeClosed hC hW.rows _ _ _ _ _ _ _ _ hW.width hW.layerStates hW.layers hW.bound hW.histories hW.runs hT.diffPairs hT.difference,
    atomMapFormula_freeClosed hC hT hW.rows _ _ _ _ _ _ _ _ _ hW.width hW.bound hW.slots hW.size hW.histories hW.runs hPairs hCodes hW.atoms,
    Filter.filteredFormula_freeClosed _ _ _ _ _ _ _ hC.omega hW.atoms hW.size hCodes hW.length hA hW.indices⟩

theorem calculationFormula_iff {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory) {n : Nat}
    (e : Env M n) (C : ExpressionData (Project.Term n)) (T : MatrixArithmetic (Project.Term n))
    (Forests Pairs Codes V A : Project.Term n) (W : CalculationData (Project.Term n))
    (hC : (C.eval e).Valid M) (hT : (T.eval e).Valid M (C.eval e)) (hForests : AllForests M (C.omega.eval e) (Forests.eval e)) :
    Project.Formula.satisfies e (calculationFormula C T Forests Pairs Codes V A W) ↔
      Calculation M (C.eval e) (T.eval e) (Forests.eval e) (Pairs.eval e) (Codes.eval e) (V.eval e) (A.eval e) (W.eval e) := by
  have hBound := sequenceBoundFormula_iff hM.1 e C W.width V W.bound
  have hLinear := linearForestFormula_iff hM e C.omega W.width W.linear hC.omega
  simp only [calculationFormula,Project.Formula.satisfies_conj_iff,legalAtFormula_iff hM.1,hLinear,selectsFormula_iff hM.1,
    layerSpaceCertificateFormula_iff hM,rootedRowFormula_iff hM.1,stepCertificateFormula_iff hM.1,runAlongFormula_iff hM.1,
    hBound,mulAtFormula_iff hM.1,atomMapFormula_iff hM.1,Filter.filteredFormula_iff hM.1]
  have hRows (hLayer : LayerRun M (C.eval e) (W.width.eval e) (W.eval e).space (V.eval e) (W.initial.eval e) (W.layers.eval e)) :
      Project.Formula.satisfies e (rowFamilyFormula C W.width W.rows W.layerStates W.layers W.bound W.histories W.runs T.diffPairs T.difference) ↔
      RowFamily M (C.eval e) (W.width.eval e) (W.eval e).space (W.layers.eval e) (W.bound.eval e) (W.histories.eval e) (W.runs.eval e) :=
    rowFamilyFormula_iff hM e C W.width W.rows W.layerStates W.layers W.bound W.histories W.runs T.diffPairs T.difference
      hC hLayer.space.rows hT.diff (fun k U F hAt => hLayer.at_rooted hM.1 hAt)
  constructor
  · rintro ⟨hLegal,hLin,hSel,hSpace,hBase,hStep,hRun,hB,hS,hN,hFamily,hMap,hFilter⟩
    have hL := (layer_space_certificate_iff hC hForests).mp hSpace
    have hLayer := (run_along_iff_layer_run_d hM hC hL hT.diff hStep hBase).mp hRun
    exact ⟨hLegal,hLin,hSel,hSpace,hBase,hStep,hRun,hB,hS,hN,(hRows hLayer).mp hFamily,hMap,hFilter⟩
  · intro h
    exact ⟨h.legal,h.linear,h.selected,h.space,h.base,h.step,h.run,h.bound,h.slots,h.size,
      (hRows (h.layer_run_d hM hC hT hForests)).mpr h.family,h.atoms,h.filtered⟩


private def computationC : ExpressionData (Project.Term 35) := ⟨.bound 34,.bound 33,.bound 32,.bound 31,.bound 30⟩
private def computationT : MatrixArithmetic (Project.Term 35) := ⟨.bound 29,.bound 28,.bound 27,.bound 26,.bound 25,.bound 24⟩
private def computationW : CalculationData (Project.Term 35) := ⟨.bound 17,.bound 16,.bound 15,.bound 14,.bound 13,.bound 12,.bound 11,.bound 10,.bound 9,.bound 8,.bound 7,.bound 6,.bound 5,.bound 4,.bound 3,.bound 2,.bound 1,.bound 0⟩

/-- 唯一无界见证 Box 界住全部辅助集合；域宽、预算、地址和过滤长度始终在内部 ω。 -/
def expressionDiagramMatrix : KP1Y.WitnessMatrix 14 where
  body := (Project.Formula.existsMem (.bound 16)
    (Project.Formula.existsMem (.bound 6)
    (Project.Formula.existsMem (.bound 7)
    (Project.Formula.existsMem (.bound 3)
    (Project.Formula.existsMem (.bound 4)
    (Project.Formula.existsMem (.bound 5)
    (Project.Formula.existsMem (.bound 6)
    (Project.Formula.existsMem (.bound 7)
    (Project.Formula.existsMem (.bound 8)
    (Project.Formula.existsMem (.bound 9)
    (Project.Formula.existsMem (.bound 26)
    (Project.Formula.existsMem (.bound 27)
    (Project.Formula.existsMem (.bound 28)
    (Project.Formula.existsMem (.bound 13)
    (Project.Formula.existsMem (.bound 14)
    (Project.Formula.existsMem (.bound 15)
    (Project.Formula.existsMem (.bound 32)
    (Project.Formula.existsMem (.bound 17)
    (calculationFormula computationC computationT (.bound 23) (.bound 22) (.bound 21) (.bound 20) (.bound 19) computationW)))))))))))))))))))
  freeClosed := by
    have hInner := calculationFormula_freeClosed (C := computationC) ⟨rfl,rfl,rfl,rfl,rfl⟩
      (T := computationT) ⟨rfl,rfl,rfl,rfl,rfl,rfl⟩ (W := computationW) ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩
      (.bound 23) (.bound 22) (.bound 21) (.bound 20) (.bound 19) rfl rfl rfl rfl rfl
    simp [Project.Formula.existsMem,Definitional.Formula.FreeClosed,hInner]
  delta0 := (.existsMem _ (.existsMem _ (.existsMem _ (.existsMem _ (.existsMem _ (.existsMem _ (.existsMem _ (.existsMem _ (.existsMem _ (.existsMem _ (.existsMem _ (.existsMem _ (.existsMem _ (.existsMem _ (.existsMem _ (.existsMem _ (.existsMem _ (.existsMem _ (calculationFormula_delta0 _ _ _ _ _ _ _ _)))))))))))))))))))

def expressionDiagramEnv {M : SetTheory.Structure.{u}} (C : ExpressionData M.Domain) (T : MatrixArithmetic M.Domain)
    (Forests Pairs Codes : M.Domain) : Env M 14 :=
  ((((((((((((((oneEnv C.omega).push C.zero).push C.one).push C.sequences).push C.expressions).push T.addPairs).push T.plus).push T.mulPairs).push T.times).push T.diffPairs).push T.difference).push Forests).push Pairs).push Codes)

theorem expressionDiagramMatrix_iff {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {Forests : M.Domain} (hForests : AllForests M C.omega Forests) (Pairs Codes V A Box : M.Domain) :
    Project.Formula.satisfies ((((expressionDiagramEnv C T Forests Pairs Codes).push V).push A).push Box) expressionDiagramMatrix.body ↔
      ∃ width, M.mem width C.omega ∧ ∃ linear, M.mem linear Forests ∧ ∃ initial, M.mem initial Forests ∧ ∃ rowValues, M.mem rowValues Box ∧ ∃ rowForests, M.mem rowForests Box ∧ ∃ rowStates, M.mem rowStates Box ∧ ∃ layerStates, M.mem layerStates Box ∧ ∃ layers, M.mem layers Box ∧ ∃ step, M.mem step Box ∧ ∃ stepBound, M.mem stepBound Box ∧ ∃ bound, M.mem bound C.omega ∧ ∃ slots, M.mem slots C.omega ∧ ∃ size, M.mem size C.omega ∧ ∃ histories, M.mem histories Box ∧ ∃ runs, M.mem runs Box ∧ ∃ atoms, M.mem atoms Box ∧ ∃ length, M.mem length C.omega ∧ ∃ indices, M.mem indices Box ∧ Calculation M C T Forests Pairs Codes V A ⟨width,linear,initial,rowValues,rowForests,rowStates,layerStates,layers,step,stepBound,bound,slots,size,histories,runs,atoms,length,indices⟩ := by
  simp only [expressionDiagramMatrix,Project.Formula.satisfies_existsMem_iff]
  have hCalc (width linear initial rowValues rowForests rowStates layerStates layers step stepBound bound slots size histories runs atoms length indices : M.Domain) :=
    calculationFormula_iff hM
      ((((((((((((((((((((((expressionDiagramEnv C T Forests Pairs Codes).push V).push A).push Box).push width).push linear).push initial).push rowValues).push rowForests).push rowStates).push layerStates).push layers).push step).push stepBound).push bound).push slots).push size).push histories).push runs).push atoms).push length).push indices)
      computationC computationT (.bound 23) (.bound 22) (.bound 21) (.bound 20) (.bound 19) computationW hC hT hForests
  simp only [hCalc]
  rfl

theorem expression_diagram_certificate_exists_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {Forests : M.Domain} (hForests : AllForests M C.omega Forests) {D : KP1Y.Reflection.Data M.Domain}
    {V m A : M.Domain} (h : ExpressionGraph M C T D V m A) : ∃ Box,
    Project.Formula.satisfies ((((expressionDiagramEnv C T Forests D.pairs D.edgeCodes).push V).push A).push Box) expressionDiagramMatrix.body := by
  obtain ⟨W,hW⟩ := calculation_exists_d hM hC hT hForests h
  obtain ⟨Box,hBox⟩ := KP1Y.Ranking.finite_list_container_d hM [W.rowValues,W.rowForests,W.rowStates,W.layerStates,W.layers,W.step,W.stepBound,W.histories,W.runs,W.atoms,W.indices]
  have hS := (hT.mul.mul_iff_product hM hW.bound.1.1 hW.legal.1.1).mp hW.slots
  have hSn := natural_product_closed_d hM hC hW.bound.1.1 hW.legal.1.1 hS
  have hN := (hT.mul.mul_iff_product hM hSn hW.bound.1.1).mp hW.size
  have hNn := natural_product_closed_d hM hC hSn hW.bound.1.1 hN
  apply Exists.intro Box
  apply (expressionDiagramMatrix_iff hM hC hT hForests D.pairs D.edgeCodes V A Box).mpr
  exact ⟨W.width,
    hW.legal.1.1,
    W.linear,
    (hForests W.linear).mpr ⟨W.width,hW.legal.1.1,hW.linear.1⟩,
    W.initial,
    (hForests W.initial).mpr ⟨W.width,hW.legal.1.1,hW.selected.forest⟩,
    W.rowValues,
    hBox W.rowValues (by simp),
    W.rowForests,
    hBox W.rowForests (by simp),
    W.rowStates,
    hBox W.rowStates (by simp),
    W.layerStates,
    hBox W.layerStates (by simp),
    W.layers,
    hBox W.layers (by simp),
    W.step,
    hBox W.step (by simp),
    W.stepBound,
    hBox W.stepBound (by simp),
    W.bound,
    hW.bound.1.1,
    W.slots,
    hSn,
    W.size,
    hNn,
    W.histories,
    hBox W.histories (by simp),
    W.runs,
    hBox W.runs (by simp),
    W.atoms,
    hBox W.atoms (by simp),
    W.length,
    hW.filtered.length,
    W.indices,
    hBox W.indices (by simp),hW⟩

theorem expression_diagram_certificate_sound_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {Forests : M.Domain} (hForests : AllForests M C.omega Forests) (D : KP1Y.Reflection.Data M.Domain)
    {V A Box : M.Domain} (h : Project.Formula.satisfies
      ((((expressionDiagramEnv C T Forests D.pairs D.edgeCodes).push V).push A).push Box) expressionDiagramMatrix.body) :
    ∃ m, M.mem m C.omega ∧ ExpressionGraph M C T D V m A := by
  obtain ⟨width,hwidth,linear,hlinear,initial,hinitial,rowValues,hrowValues,rowForests,hrowForests,rowStates,hrowStates,layerStates,hlayerStates,layers,hlayers,step,hstep,stepBound,hstepBound,bound,hbound,slots,hslots,size,hsize,histories,hhistories,runs,hruns,atoms,hatoms,length,hlength,indices,hindices,hCalc⟩ :=
    (expressionDiagramMatrix_iff hM hC hT hForests D.pairs D.edgeCodes V A Box).mp h
  exact ⟨width,hwidth,hCalc.expression_graph_d hM hC hT hForests D⟩


/-- 全部合法内部表达式到规范有限边表的真实集合函数；不是逐点宿主选择函数。 -/
theorem expression_diagram_graph_exists_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {D : KP1Y.Reflection.Data M.Domain} (hD : D.Valid M) (hOmega : D.omega=C.omega) :
    ∃ GraphA, Graph M GraphA C.expressions D.edgeLists ∧ ∀ V A, MemPair M GraphA V A ↔
      ∃ m, M.mem m C.omega ∧ ExpressionGraph M C T D V m A := by
  obtain ⟨Forests,hForests⟩ := all_forests_exists_d hM hC
  let e := expressionDiagramEnv C T Forests D.pairs D.edgeCodes
  have hTotal : ∀ V, M.mem V C.expressions → ∃ A Box,
      Project.Formula.satisfies (((e.push V).push A).push Box) expressionDiagramMatrix.body := by
    intro V hV
    obtain ⟨m,_,hLegal⟩ := (hC.expressions V).mp hV
    obtain ⟨A,hA⟩ := expression_graph_exists_d hM hC hT D hLegal
    obtain ⟨Box,hBox⟩ := expression_diagram_certificate_exists_d hM hC hT hForests hA
    exact ⟨A,Box,hBox⟩
  obtain ⟨GraphA,hGraph,hRows⟩ := sigma_function_graph_d hM expressionDiagramMatrix e C.expressions D.edgeLists hTotal
    (fun V _ A Box hCert => by
      obtain ⟨_,_,hA⟩ := expression_diagram_certificate_sound_d hM hC hT hForests D hCert
      exact (hA.diagram_d hM hC hT hD hOmega).2.1)
    (fun V _ A A' Box Box' hCert hCert' => by
      obtain ⟨_,_,hA⟩ := expression_diagram_certificate_sound_d hM hC hT hForests D hCert
      obtain ⟨_,_,hA'⟩ := expression_diagram_certificate_sound_d hM hC hT hForests D hCert'
      exact (hA.unique_d hM hC hA').2)
  refine ⟨GraphA,hGraph,fun V A => ?_⟩
  constructor
  · intro hAt
    obtain ⟨_,_,Box,hCert⟩ := (hRows V A).mp hAt
    exact expression_diagram_certificate_sound_d hM hC hT hForests D hCert
  · rintro ⟨m,hm,hA⟩
    obtain ⟨Box,hBox⟩ := expression_diagram_certificate_exists_d hM hC hT hForests hA
    exact (hRows V A).mpr ⟨(hC.expressions V).mpr ⟨m,hm,hA.1⟩,
      (hA.diagram_d hM hC hT hD hOmega).2.1,Box,hBox⟩

theorem expression_diagram_graph_unique {M : SetTheory.Structure.{u}} (he : Extensional M)
    {C : ExpressionData M.Domain} {T : MatrixArithmetic M.Domain} {D : KP1Y.Reflection.Data M.Domain}
    {F G : M.Domain} (hF : Graph M F C.expressions D.edgeLists) (hG : Graph M G C.expressions D.edgeLists)
    (hFRows : ∀ V A, MemPair M F V A ↔ ∃ m, M.mem m C.omega ∧ ExpressionGraph M C T D V m A)
    (hGRows : ∀ V A, MemPair M G V A ↔ ∃ m, M.mem m C.omega ∧ ExpressionGraph M C T D V m A) : F=G :=
  hF.ext he hG (fun V _ A => (hFRows V A).trans (hGRows V A).symm)

theorem expression_diagram_graph_width_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {D : KP1Y.Reflection.Data M.Domain} (hD : D.Valid M) (hOmega : D.omega=C.omega)
    {F V A m : M.Domain} (hRows : ∀ s a, MemPair M F s a ↔ ∃ n, M.mem n C.omega ∧ ExpressionGraph M C T D s n a)
    (hAt : MemPair M F V A) (hLegal : LegalAt M C.omega C.zero C.one V m) :
    ExpressionGraph M C T D V m A ∧ KP1Y.Reflection.Diagram M D m A := by
  obtain ⟨n,_,hA⟩ := (hRows V A).mp hAt
  have hnm := legal_length_unique hM.1 hA.1 hLegal
  subst n
  exact ⟨hA,hA.diagram_d hM hC hT hD hOmega⟩

theorem expression_diagram_graph_empty_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain}
    {D : KP1Y.Reflection.Data M.Domain} {F V A : M.Domain}
    (hRows : ∀ s a, MemPair M F s a ↔ ∃ n, M.mem n C.omega ∧ ExpressionGraph M C T D s n a)
    (hAt : MemPair M F V A) (hLegal : LegalAt M C.omega C.zero C.one V C.zero) : A=C.zero := by
  obtain ⟨m,_,hLegal',_,_,_,_,_,_,_,hA⟩ := (hRows V A).mp hAt
  have hm := legal_length_unique hM.1 hLegal' hLegal
  subst m
  exact hA.empty_d hM hC

end KP1Y.OneYFinite.ExpressionDiagram
