import KP1Y.OneYFiniteFilter
import KP1Y.OneYExtractionBounds
import KP1Y.OneYCopyCoordinates
import KP1Y.ReflectionShapeEntries

/-! 实际表达式根图。有限原子按层、列、行顺序稳定过滤；全局输出通过有界计算证书收集。 -/
namespace KP1Y.OneYFinite.ExpressionDiagram
open YesMetaZFC YesMetaZFC.SetTheory YesMetaZFC.SetTheory.Definitional
open KP1Y.Kuratowski KP1Y.Functions KP1Y.Naturals KP1Y.Bounded
universe u

/-- 所有内部有限宽度的父森林组成一个实际集合。宽度不是宿主自然数。 -/
def AllForests (M : SetTheory.Structure.{u}) (w Forests : M.Domain) : Prop :=
  ∀ P, M.mem P Forests ↔ ∃ m, M.mem m w ∧ Forest M w m P

private def globalDecodeSchema : Project.Delta0BinarySchema 1 where
  body := Project.Formula.existsMem (.bound 2)
    (.conj (graphFormula (.bound 2) (.bound 0) (.bound 3))
      (forestDecodeFormula (.bound 0) (.bound 2) (.bound 1)))
  freeClosed := by
    simp [graphFormula,forestDecodeFormula,relationSupportFormula,memPairFormula,codeFormula,pairFormula,
      Project.Formula.forallMem,Project.Formula.existsMem,Definitional.Formula.FreeClosed]
  delta0 := .existsMem _ (.conj (graphFormula_delta0 _ _ _) (forestDecodeFormula_delta0 _ _ _))

theorem all_forests_exists_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) : ∃ Forests, AllForests M C.omega Forests := by
  have hφ (E P : M.Domain) : Project.Formula.satisfies (((oneEnv C.omega).push E).push P) globalDecodeSchema.body ↔
      ∃ m, M.mem m C.omega ∧ Graph M E m C.omega ∧ ForestDecode M m E P := by
    simp only [globalDecodeSchema,Project.Formula.satisfies_existsMem_iff,Project.Formula.satisfies_conj_iff,
      graphFormula_iff hM.1,forestDecodeFormula_iff hM.1]
    rfl
  obtain ⟨Forests,hForests⟩ := KP1Y.functional_image_d hM globalDecodeSchema (oneEnv C.omega) C.sequences
    (fun E hE => by
      obtain ⟨m,hm,hGraph⟩ := (hC.sequences E).mp hE
      obtain ⟨P,hDecode⟩ := forest_decode_exists_d hM m E
      exact ⟨P,(hφ E P).mpr ⟨m,hm,hGraph,hDecode⟩⟩)
    (fun E _ P Q hP hQ => by
      obtain ⟨m,_,hE,hD⟩ := (hφ E P).mp hP
      obtain ⟨n,_,hE',hD'⟩ := (hφ E Q).mp hQ
      have hmn := graph_domain_unique hM.1 hE hE'
      subst n
      exact hD.unique hM.1 hD')
  refine ⟨Forests,fun P => ?_⟩
  have hMem := hForests P
  simp only [hφ] at hMem
  refine hMem.trans ⟨?_,?_⟩
  · rintro ⟨E,_,m,hm,hGraph,hDecode⟩
    exact ⟨m,hm,hDecode.forest hM.1 hm hGraph⟩
  · rintro ⟨m,hm,hForest⟩
    obtain ⟨E,hGraph,hDecode,_⟩ := forest_encoding_exists_d hM hC hForest
    exact ⟨E,(hC.sequences E).mpr ⟨m,hm,hGraph⟩,m,hm,hGraph,hDecode⟩

/-- 全宽度固定上界下的集合空间证书；其各量词均可字面有界。 -/
structure RowSpaceCertificate (M : SetTheory.Structure.{u}) (C : ExpressionData M.Domain)
    (Forests m : M.Domain) (R : RowStateSpace M.Domain) : Prop where
  width : M.mem m C.omega
  values_subset : ∀ V, M.mem V R.values → M.mem V C.sequences
  values : ∀ V, M.mem V C.sequences → (M.mem V R.values ↔ Graph M V m C.omega)
  forests_subset : ∀ P, M.mem P R.forests → M.mem P Forests
  forests : ∀ P, M.mem P Forests → (M.mem P R.forests ↔ Forest M C.omega m P)
  states : IsProduct M R.states R.values R.forests

theorem row_space_certificate_iff {M : SetTheory.Structure.{u}} {C : ExpressionData M.Domain}
    (hC : C.Valid M) {Forests m : M.Domain} (hForests : AllForests M C.omega Forests)
    {R : RowStateSpace M.Domain} : RowSpaceCertificate M C Forests m R ↔ R.Valid M C m := by
  constructor
  · intro h
    refine ⟨h.width,fun V => ?_,fun P => ?_,h.states⟩
    · constructor
      · intro hV
        exact (h.values V (h.values_subset V hV)).mp hV
      · intro hV
        exact (h.values V ((hC.sequences V).mpr ⟨m,h.width,hV⟩)).mpr hV
    · constructor
      · intro hP
        exact (h.forests P (h.forests_subset P hP)).mp hP
      · intro hP
        exact (h.forests P ((hForests P).mpr ⟨m,h.width,hP⟩)).mpr hP
  · intro h
    exact ⟨h.width,fun V hV => (hC.sequences V).mpr ⟨m,h.width,(h.values V).mp hV⟩,
      fun V _ => h.values V,fun P hP => (hForests P).mpr ⟨m,h.width,(h.forests P).mp hP⟩,
      fun P _ => h.forests P,h.states⟩

def rowSpaceCertificateFormula {n : Nat} (C : ExpressionData (Project.Term n))
    (Forests m : Project.Term n) (R : RowStateSpace (Project.Term n)) : Project.Formula 1 n :=
  .conj (.mem m C.omega)
    (.conj (Project.Formula.forallMem R.values (.mem (.bound 0) C.sequences.weaken))
    (.conj (Project.Formula.forallMem C.sequences
      (.iff (.mem (.bound 0) R.values.weaken) (graphFormula (.bound 0) m.weaken C.omega.weaken)))
    (.conj (Project.Formula.forallMem R.forests (.mem (.bound 0) Forests.weaken))
    (.conj (Project.Formula.forallMem Forests
      (.iff (.mem (.bound 0) R.forests.weaken) (forestFormula C.omega.weaken m.weaken (.bound 0))))
      (productBoundedFormula R.states R.values R.forests)))))

theorem rowSpaceCertificateFormula_delta0 {n : Nat} (C : ExpressionData (Project.Term n))
    (Forests m : Project.Term n) (R : RowStateSpace (Project.Term n)) :
    (rowSpaceCertificateFormula C Forests m R).IsDelta0 :=
  .conj (.mem _ _) (.conj (.forallMem _ (.mem _ _))
    (.conj (.forallMem _ (.iff (.mem _ _) (graphFormula_delta0 _ _ _)))
    (.conj (.forallMem _ (.mem _ _))
    (.conj (.forallMem _ (.iff (.mem _ _) (forestFormula_delta0 _ _ _)))
      (productBoundedFormula_delta0 _ _ _)))))

theorem rowSpaceCertificateFormula_freeClosed {n : Nat} {C : ExpressionData (Project.Term n)} (hC : C.Closed)
    {R : RowStateSpace (Project.Term n)} (hR : R.Closed) (Forests m : Project.Term n)
    (hF : Forests.freeSupport=[]) (hm : m.freeSupport=[]) :
    (rowSpaceCertificateFormula C Forests m R).FreeClosed := by
  simp [rowSpaceCertificateFormula,productBoundedFormula,relationSupportFormula,graphFormula,
    forestFormula,memPairFormula,codeFormula,pairFormula,Project.Formula.forallMem,Project.Formula.existsMem,
    Definitional.Formula.FreeClosed,hC.omega,hC.sequences,hR.values,hR.forests,hR.states,hF,hm]

theorem rowSpaceCertificateFormula_iff {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {n : Nat} (e : Env M n) (C : ExpressionData (Project.Term n)) (Forests m : Project.Term n)
    (R : RowStateSpace (Project.Term n)) :
    Project.Formula.satisfies e (rowSpaceCertificateFormula C Forests m R) ↔
      RowSpaceCertificate M (C.eval e) (Forests.eval e) (m.eval e) (R.eval e) := by
  simp only [rowSpaceCertificateFormula,Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_mem_iff,
    Project.Formula.satisfies_forallMem_iff,Project.Formula.satisfies_iff_iff,graphFormula_iff hM.1,
    forestFormula_iff hM.1,productBoundedFormula_iff hM,Term.eval_weaken]
  exact ⟨fun h => ⟨h.1,h.2.1,h.2.2.1,h.2.2.2.1,h.2.2.2.2.1,h.2.2.2.2.2⟩,
    fun h => ⟨h.width,h.values_subset,h.values,h.forests_subset,h.forests,h.states⟩⟩


structure LayerSpaceCertificate (M : SetTheory.Structure.{u}) (C : ExpressionData M.Domain)
    (Forests m : M.Domain) (L : LayerStateSpace M.Domain) : Prop where
  rows : RowSpaceCertificate M C Forests m L.rows
  subset : ∀ state, M.mem state L.states → M.mem state L.rows.states
  states : ∀ state, M.mem state L.rows.states → (M.mem state L.states ↔
    ∃ V, M.mem V L.rows.values ∧ ∃ P, M.mem P L.rows.forests ∧ Codes M state V P ∧ RootedRow M C m V P)

theorem layer_space_certificate_iff {M : SetTheory.Structure.{u}} {C : ExpressionData M.Domain}
    (hC : C.Valid M) {Forests m : M.Domain} (hForests : AllForests M C.omega Forests)
    {L : LayerStateSpace M.Domain} : LayerSpaceCertificate M C Forests m L ↔ L.Valid M C m := by
  constructor
  · intro h
    have hR := (row_space_certificate_iff hC hForests).mp h.rows
    refine ⟨hR,fun state => ?_⟩
    constructor
    · intro hs
      obtain ⟨V,_,P,_,hCode,hRooted⟩ := (h.states state (h.subset state hs)).mp hs
      exact ⟨V,P,hCode,hRooted⟩
    · rintro ⟨V,P,hCode,hRooted⟩
      have hV := (hR.values V).mpr hRooted.row.values
      have hP := (hR.forests P).mpr hRooted.row.forest
      exact (h.states state ((hR.states state).mpr ⟨V,hV,P,hP,hCode⟩)).mpr ⟨V,hV,P,hP,hCode,hRooted⟩
  · intro h
    refine ⟨(row_space_certificate_iff hC hForests).mpr h.rows,?_,?_⟩
    · intro state hs
      obtain ⟨V,P,hCode,hRooted⟩ := (h.states state).mp hs
      exact (h.rows.states state).mpr ⟨V,(h.rows.values V).mpr hRooted.row.values,
        P,(h.rows.forests P).mpr hRooted.row.forest,hCode⟩
    · intro state _
      constructor
      · intro hs
        obtain ⟨V,P,hCode,hRooted⟩ := (h.states state).mp hs
        exact ⟨V,(h.rows.values V).mpr hRooted.row.values,P,(h.rows.forests P).mpr hRooted.row.forest,hCode,hRooted⟩
      · rintro ⟨V,_,P,_,hCode,hRooted⟩
        exact (h.states state).mpr ⟨V,P,hCode,hRooted⟩

def layerSpaceCertificateFormula {n : Nat} (C : ExpressionData (Project.Term n))
    (Forests m : Project.Term n) (R : RowStateSpace (Project.Term n)) (States : Project.Term n) : Project.Formula 1 n :=
  .conj (rowSpaceCertificateFormula C Forests m R)
    (.conj (Project.Formula.forallMem States (.mem (.bound 0) R.states.weaken))
      (Project.Formula.forallMem R.states (.iff (.mem (.bound 0) States.weaken)
        (Project.Formula.existsMem R.values.weaken (Project.Formula.existsMem R.forests.weaken.weaken
          (.conj (codeFormula (.bound 2) (.bound 1) (.bound 0))
            (rootedRowFormula C.weaken.weaken.weaken m.weaken.weaken.weaken (.bound 1) (.bound 0))))))))

theorem layerSpaceCertificateFormula_delta0 {n : Nat} (C : ExpressionData (Project.Term n))
    (Forests m : Project.Term n) (R : RowStateSpace (Project.Term n)) (States : Project.Term n) :
    (layerSpaceCertificateFormula C Forests m R States).IsDelta0 :=
  .conj (rowSpaceCertificateFormula_delta0 _ _ _ _)
    (.conj (.forallMem _ (.mem _ _)) (.forallMem _ (.iff (.mem _ _)
      (.existsMem _ (.existsMem _ (.conj (codeFormula_delta0 _ _ _) (rootedRowFormula_delta0 _ _ _ _)))))))

theorem layerSpaceCertificateFormula_freeClosed {n : Nat} {C : ExpressionData (Project.Term n)} (hC : C.Closed)
    {R : RowStateSpace (Project.Term n)} (hR : R.Closed) (Forests m States : Project.Term n)
    (hF : Forests.freeSupport=[]) (hm : m.freeSupport=[]) (hS : States.freeSupport=[]) :
    (layerSpaceCertificateFormula C Forests m R States).FreeClosed := by
  have hRow := rowSpaceCertificateFormula_freeClosed hC hR Forests m hF hm
  have hRooted := rootedRowFormula_freeClosed hC.weaken.weaken.weaken m.weaken.weaken.weaken
    (Project.Term.bound (depth := n+3) 1) (.bound 0) (by simpa using hm) rfl rfl
  simp [layerSpaceCertificateFormula,Project.Formula.forallMem,Project.Formula.existsMem,
    Definitional.Formula.FreeClosed,codeFormula,pairFormula,hRow,hRooted,hR.states,hR.values,hR.forests,hS]

theorem layerSpaceCertificateFormula_iff {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {n : Nat} (e : Env M n) (C : ExpressionData (Project.Term n)) (Forests m : Project.Term n)
    (R : RowStateSpace (Project.Term n)) (States : Project.Term n) :
    Project.Formula.satisfies e (layerSpaceCertificateFormula C Forests m R States) ↔
      LayerSpaceCertificate M (C.eval e) (Forests.eval e) (m.eval e) ⟨R.eval e,States.eval e⟩ := by
  simp only [layerSpaceCertificateFormula,Project.Formula.satisfies_conj_iff,rowSpaceCertificateFormula_iff hM,
    Project.Formula.satisfies_forallMem_iff,Project.Formula.satisfies_mem_iff,Project.Formula.satisfies_iff_iff,
    Project.Formula.satisfies_existsMem_iff,codeFormula_iff hM.1,rootedRowFormula_iff hM.1,
    ExpressionData.eval_weaken,Term.eval_weaken]
  exact ⟨fun h => ⟨h.1,h.2.1,h.2.2⟩,fun h => ⟨h.rows,h.subset,h.states⟩⟩


/-- 已给定实际一步图时，层历史的纯有界验证。 -/
structure RunAlong (M : SetTheory.Structure.{u}) (w z States Step V P H : M.Domain) : Prop where
  graph : Graph M H w States
  initial : ∀ state, M.mem state States → Codes M state V P → MemPair M H z state
  transition : ∀ i j source target, M.SuccessorOf j i → MemPair M H i source →
    MemPair M H j target → MemPair M Step source target

def runAlongFormula {n : Nat} (w z States Step V P H : Project.Term n) : Project.Formula 1 n :=
  .conj (graphFormula H w States)
    (.conj (Project.Formula.forallMem States (.imp (codeFormula (.bound 0) V.weaken P.weaken)
      (memPairFormula H.weaken z.weaken (.bound 0))))
      (Project.Formula.forallMem w (Project.Formula.forallMem w.weaken
        (Project.Formula.forallMem States.weaken.weaken (Project.Formula.forallMem States.weaken.weaken.weaken
          (.imp (.conj (successorFormula (.bound 2) (.bound 3))
            (.conj (memPairFormula H.weaken.weaken.weaken.weaken (.bound 3) (.bound 1))
              (memPairFormula H.weaken.weaken.weaken.weaken (.bound 2) (.bound 0))))
            (memPairFormula Step.weaken.weaken.weaken.weaken (.bound 1) (.bound 0))))))))

theorem runAlongFormula_delta0 {n : Nat} (w z States Step V P H : Project.Term n) :
    (runAlongFormula w z States Step V P H).IsDelta0 :=
  .conj (graphFormula_delta0 _ _ _) (.conj (.forallMem _ (.imp (codeFormula_delta0 _ _ _) (memPairFormula_delta0 _ _ _)))
    (.forallMem _ (.forallMem _ (.forallMem _ (.forallMem _ (.imp
      (.conj (successorFormula_delta0 _ _) (.conj (memPairFormula_delta0 _ _ _) (memPairFormula_delta0 _ _ _)))
      (memPairFormula_delta0 _ _ _)))))))

theorem runAlongFormula_freeClosed {n : Nat} (w z States Step V P H : Project.Term n)
    (hw : w.freeSupport=[]) (hz : z.freeSupport=[]) (hStates : States.freeSupport=[])
    (hStep : Step.freeSupport=[]) (hV : V.freeSupport=[]) (hP : P.freeSupport=[]) (hH : H.freeSupport=[]) :
    (runAlongFormula w z States Step V P H).FreeClosed := by
  simp [runAlongFormula,graphFormula,memPairFormula,codeFormula,pairFormula,successorFormula,
    Project.Formula.forallMem,Project.Formula.existsMem,Definitional.Formula.FreeClosed,hw,hz,hStates,hStep,hV,hP,hH]

theorem runAlongFormula_iff {M : SetTheory.Structure.{u}} (he : Extensional M) {n : Nat} (e : Env M n)
    (w z States Step V P H : Project.Term n) :
    Project.Formula.satisfies e (runAlongFormula w z States Step V P H) ↔
      RunAlong M (w.eval e) (z.eval e) (States.eval e) (Step.eval e) (V.eval e) (P.eval e) (H.eval e) := by
  simp only [runAlongFormula,Project.Formula.satisfies_conj_iff,graphFormula_iff he,
    Project.Formula.satisfies_forallMem_iff,Project.Formula.satisfies_imp_iff,codeFormula_iff he,
    memPairFormula_iff he,successorFormula_iff he,Term.eval_weaken]
  constructor
  · rintro ⟨hGraph,hInitial,hStep⟩
    refine ⟨hGraph,hInitial,?_⟩
    intro i j source target hs hIn hOut
    obtain ⟨hi,hSource⟩ := hGraph.bounds he hIn
    obtain ⟨hj,hTarget⟩ := hGraph.bounds he hOut
    exact hStep i hi j hj source hSource target hTarget ⟨hs,hIn,hOut⟩
  · intro h
    exact ⟨h.graph,h.initial,fun i _ j _ source _ target _ hAnte =>
      h.transition i j source target hAnte.1 hAnte.2.1 hAnte.2.2⟩

/-- 一步提取的共同证书集合由 KPω 收集构造，不能作为未证明的总性假设。 -/
theorem layer_step_certificate_exists_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {m : M.Domain} {L : LayerStateSpace M.Domain}
    (hL : L.Valid M C m) {Pairs Table : M.Domain} (hTable : DifferenceTable M C Pairs Table) :
    ∃ Step Bound, SigmaGraphCertificate extractionStepMatrix (extractionStepEnv C m L.rows Pairs Table)
      Step L.states L.states Bound := by
  exact sigma_graph_certificate_exists_d hM extractionStepMatrix (extractionStepEnv C m L.rows Pairs Table) L.states L.states
    (fun source hSource => by
      obtain ⟨V,P,hCode,hRooted⟩ := (hL.states source).mp hSource
      exact extraction_step_exists_d hM hC hL.rows hTable hRooted hCode)
    (fun source hSource target Box hCert => hL.transition_mem_d hM hC hSource (extraction_step_sound_d hM hC hL.rows hTable hCert))
    (fun source _ target target' Box Box' hCert hCert' => layer_transition_unique_d hM hC
      (extraction_step_sound_d hM hC hL.rows hTable hCert) (extraction_step_sound_d hM hC hL.rows hTable hCert'))

theorem layer_step_certificate_rows_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {m : M.Domain} {L : LayerStateSpace M.Domain}
    (hL : L.Valid M C m) {Pairs Table Step Bound : M.Domain} (hTable : DifferenceTable M C Pairs Table)
    (hCert : SigmaGraphCertificate extractionStepMatrix (extractionStepEnv C m L.rows Pairs Table) Step L.states L.states Bound)
    (source target : M.Domain) : MemPair M Step source target ↔ M.mem source L.states ∧ LayerTransition M C m source target := by
  constructor
  · intro hAt
    obtain ⟨hSource,hTarget⟩ := hCert.graph.bounds hM.1 hAt
    obtain ⟨Box,_,hBox⟩ := hCert.rows source hSource target hTarget hAt
    exact ⟨hSource,extraction_step_sound_d hM hC hL.rows hTable hBox⟩
  · rintro ⟨hSource,hNext⟩
    obtain ⟨target',hTarget',hAt⟩ := hCert.graph.total source hSource
    obtain ⟨Box,_,hBox⟩ := hCert.rows source hSource target' hTarget' hAt
    have he := layer_transition_unique_d hM hC hNext (extraction_step_sound_d hM hC hL.rows hTable hBox)
    exact he.symm ▸ hAt

theorem run_along_iff_layer_run_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {m : M.Domain} {L : LayerStateSpace M.Domain}
    (hL : L.Valid M C m) {Pairs Table Step Bound V P H : M.Domain} (hTable : DifferenceTable M C Pairs Table)
    (hCert : SigmaGraphCertificate extractionStepMatrix (extractionStepEnv C m L.rows Pairs Table) Step L.states L.states Bound)
    (hBase : RootedRow M C m V P) :
    RunAlong M C.omega C.zero L.states Step V P H ↔ LayerRun M C m L V P H := by
  have hRows := layer_step_certificate_rows_d hM hC hL hTable hCert
  constructor
  · intro h
    refine ⟨hL,hBase,h.graph,?_,?_⟩
    · intro state hCode
      exact h.initial state ((hL.states state).mpr ⟨V,P,hCode,hBase⟩) hCode
    · intro i j source target hs hIn hOut
      exact ((hRows source target).mp (h.transition i j source target hs hIn hOut)).2
  · intro h
    refine ⟨h.graph,fun state _ hCode => h.initial state hCode,?_⟩
    intro i j source target hs hIn hOut
    exact (hRows source target).mpr ⟨(h.graph.bounds hM.1 hIn).2,h.transition i j source target hs hIn hOut⟩


def rowForLayerFormula {n : Nat} (C : ExpressionData (Project.Term n)) (m : Project.Term n)
    (R : RowStateSpace (Project.Term n)) (States H Pairs Table k J : Project.Term n) : Project.Formula 1 n :=
  Project.Formula.existsMem R.values (Project.Formula.existsMem R.forests.weaken
    (.conj (rowAtFormula States.weaken.weaken H.weaken.weaken k.weaken.weaken (.bound 1) (.bound 0))
      (rowRunFormula C.weaken.weaken m.weaken.weaken R.weaken.weaken Pairs.weaken.weaken Table.weaken.weaken
        (.bound 1) (.bound 0) J.weaken.weaken)))

theorem rowForLayerFormula_delta0 {n : Nat} (C : ExpressionData (Project.Term n)) (m : Project.Term n)
    (R : RowStateSpace (Project.Term n)) (States H Pairs Table k J : Project.Term n) :
    (rowForLayerFormula C m R States H Pairs Table k J).IsDelta0 :=
  .existsMem _ (.existsMem _ (.conj (rowAtFormula_delta0 _ _ _ _ _) (rowRunFormula_delta0 _ _ _ _ _ _ _ _)))

theorem rowForLayerFormula_freeClosed {n : Nat} {C : ExpressionData (Project.Term n)} (hC : C.Closed)
    {R : RowStateSpace (Project.Term n)} (hR : R.Closed) (m States H Pairs Table k J : Project.Term n)
    (hm : m.freeSupport=[]) (hStates : States.freeSupport=[]) (hH : H.freeSupport=[])
    (hPairs : Pairs.freeSupport=[]) (hTable : Table.freeSupport=[]) (hk : k.freeSupport=[]) (hJ : J.freeSupport=[]) :
    (rowForLayerFormula C m R States H Pairs Table k J).FreeClosed := by
  have hRun := rowRunFormula_freeClosed hC.weaken.weaken hR.weaken.weaken
    m.weaken.weaken Pairs.weaken.weaken Table.weaken.weaken (.bound 1) (.bound 0) J.weaken.weaken
    (by simpa using hm) (by simpa using hPairs) (by simpa using hTable) rfl rfl (by simpa using hJ)
  simp [rowForLayerFormula,rowAtFormula,memPairFormula,codeFormula,pairFormula,Project.Formula.forallMem,
    Project.Formula.existsMem,Definitional.Formula.FreeClosed,hR.values,hR.forests,hStates,hH,hk,hRun]

private theorem rowForLayerFormula_iff {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {n : Nat} (e : Env M n) (C : ExpressionData (Project.Term n)) (m : Project.Term n)
    (R : RowStateSpace (Project.Term n)) (States H Pairs Table k J : Project.Term n)
    (hC : (C.eval e).Valid M) (hR : (R.eval e).Valid M (C.eval e) (m.eval e))
    (hTable : DifferenceTable M (C.eval e) (Pairs.eval e) (Table.eval e))
    (hRooted : ∀ W Q, RowAt M (States.eval e) (H.eval e) (k.eval e) W Q →
      RootedRow M (C.eval e) (m.eval e) W Q) :
    Project.Formula.satisfies e (rowForLayerFormula C m R States H Pairs Table k J) ↔
      ∃ W Q, RowAt M (States.eval e) (H.eval e) (k.eval e) W Q ∧
        RowRun M (C.eval e) (m.eval e) (R.eval e) W Q (J.eval e) := by
  have hRun (W Q : M.Domain) (hAt : RowAt M (States.eval e) (H.eval e) (k.eval e) W Q) :
      Project.Formula.satisfies ((e.push W).push Q)
        (rowRunFormula C.weaken.weaken m.weaken.weaken R.weaken.weaken Pairs.weaken.weaken Table.weaken.weaken
          (.bound 1) (.bound 0) J.weaken.weaken) ↔ RowRun M (C.eval e) (m.eval e) (R.eval e) W Q (J.eval e) := by
    have h := rowRunFormula_iff hM ((e.push W).push Q) C.weaken.weaken m.weaken.weaken R.weaken.weaken
      Pairs.weaken.weaken Table.weaken.weaken (.bound 1) (.bound 0) J.weaken.weaken
      (by simpa only [ExpressionData.eval_weaken] using hC)
      (by simpa only [ExpressionData.eval_weaken,RowStateSpace.eval_weaken,Term.eval_weaken] using hR)
      (by simpa only [ExpressionData.eval_weaken,Term.eval_weaken] using hTable)
      (by simpa only [ExpressionData.eval_weaken,Term.eval_weaken,Project.Term.eval_bound_one_push,Project.Term.eval_bound_zero_push]
        using (hRooted W Q hAt).row)
    simpa only [ExpressionData.eval_weaken,RowStateSpace.eval_weaken,Term.eval_weaken,
      Project.Term.eval_bound_one_push,Project.Term.eval_bound_zero_push] using h
  simp only [rowForLayerFormula,Project.Formula.satisfies_existsMem_iff,Project.Formula.satisfies_conj_iff,
    rowAtFormula_iff hM.1,Term.eval_weaken]
  constructor
  · rintro ⟨W,_,Q,_,hAt,hCert⟩
    exact ⟨W,Q,hAt,(hRun W Q hAt).mp hCert⟩
  · rintro ⟨W,Q,hAt,hRows⟩
    exact ⟨W,(hR.values W).mpr hRows.base.values,Q,(hR.forests Q).mpr hRows.base.forest,hAt,(hRun W Q hAt).mpr hRows⟩

private def rowForLayerSchema : Project.Delta0BinarySchema 13 where
  body := rowForLayerFormula ⟨.bound 14,.bound 13,.bound 12,.bound 11,.bound 10⟩ (.bound 9)
    ⟨.bound 8,.bound 7,.bound 6⟩ (.bound 5) (.bound 4) (.bound 3) (.bound 2) (.bound 1) (.bound 0)
  freeClosed := rowForLayerFormula_freeClosed ⟨rfl,rfl,rfl,rfl,rfl⟩ ⟨rfl,rfl,rfl⟩ _ _ _ _ _ _ _ rfl rfl rfl rfl rfl rfl rfl
  delta0 := rowForLayerFormula_delta0 _ _ _ _ _ _ _ _ _

structure RowFamily (M : SetTheory.Structure.{u}) (C : ExpressionData M.Domain) (m : M.Domain)
    (L : LayerStateSpace M.Domain) (H B Histories Runs : M.Domain) : Prop where
  graph : Graph M Runs B Histories
  rows : ∀ k J, MemPair M Runs k J → ∃ W Q, RowAt M L.states H k W Q ∧ RowRun M C m L.rows W Q J

theorem row_family_exists_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {m : M.Domain} {L : LayerStateSpace M.Domain}
    {V P H B : M.Domain} (hLayers : LayerRun M C m L V P H) (hB : M.mem B C.omega) :
    ∃ Histories Runs, RowFamily M C m L H B Histories Runs := by
  obtain ⟨Pairs,Table,hTable⟩ := difference_table_exists_d hM hC
  let e := ((((((((((((oneEnv C.omega).push C.zero).push C.one).push C.sequences).push C.expressions).push m).push L.rows.values).push L.rows.forests).push L.rows.states).push L.states).push H).push Pairs).push Table
  have hφ (k J : M.Domain) : Project.Formula.satisfies ((e.push k).push J) rowForLayerSchema.body ↔
      ∃ W Q, RowAt M L.states H k W Q ∧ RowRun M C m L.rows W Q J :=
    rowForLayerFormula_iff hM _ _ _ _ _ _ _ _ _ _ hC hLayers.space.rows hTable
      (fun W Q hAt => hLayers.at_rooted hM.1 hAt)
  have hTotal : ∀ k, M.mem k B → ∃ J, Project.Formula.satisfies ((e.push k).push J) rowForLayerSchema.body := by
    intro k hk
    obtain ⟨W,Q,hAt⟩ := hLayers.at_exists_d ((omega_isOrdinal_d hM hC.omega).transitive B hB k hk)
    obtain ⟨J,hJ⟩ := row_run_exists_d hM hC hLayers.space.rows (hLayers.at_rooted hM.1 hAt).row
    exact ⟨J,(hφ k J).mpr ⟨W,Q,hAt,hJ⟩⟩
  obtain ⟨Histories,hHistories⟩ := SetTheory.KP.collection_exists_d (KP1Y.models_weakKP hM) rowForLayerSchema e B hTotal
  obtain ⟨Runs,hSupport,hRaw⟩ := relation_comprehension_d hM rowForLayerSchema e B Histories
  have hRows (k J : M.Domain) : MemPair M Runs k J ↔ M.mem k B ∧ M.mem J Histories ∧
      ∃ W Q, RowAt M L.states H k W Q ∧ RowRun M C m L.rows W Q J := by
    simpa only [hφ] using hRaw k J
  refine ⟨Histories,Runs,⟨hSupport,?_,?_⟩,fun k J hAt => ((hRows k J).mp hAt).2.2⟩
  · intro k hk
    obtain ⟨J,hJ,hCert⟩ := hHistories k hk
    exact ⟨J,hJ,(hRows k J).mpr ⟨hk,hJ,(hφ k J).mp hCert⟩⟩
  · intro k J J' hAt hAt'
    obtain ⟨_,_,W,Q,hLayer,hRun⟩ := (hRows k J).mp hAt
    obtain ⟨_,_,W',Q',hLayer',hRun'⟩ := (hRows k J').mp hAt'
    obtain ⟨hWW,hQQ⟩ := hLayers.at_unique hM.1 hLayer hLayer'
    subst W'
    subst Q'
    exact hRun.unique_d hM hC hRun'

theorem RowFamily.at_d {M : SetTheory.Structure.{u}} {C : ExpressionData M.Domain}
    {m : M.Domain} {L : LayerStateSpace M.Domain} {H B Histories Runs k : M.Domain}
    (h : RowFamily M C m L H B Histories Runs) (hk : M.mem k B) :
    ∃ J W Q, M.mem J Histories ∧ MemPair M Runs k J ∧ RowAt M L.states H k W Q ∧ RowRun M C m L.rows W Q J := by
  obtain ⟨J,hJ,hAt⟩ := h.graph.total k hk
  obtain ⟨W,Q,hLayer,hRun⟩ := h.rows k J hAt
  exact ⟨J,W,Q,hJ,hAt,hLayer,hRun⟩


/-- 地址 ((k*m)+c)*B+r：层号最外、列号次之、行号最内。 -/
def Position (M : SetTheory.Structure.{u}) (C : ExpressionData M.Domain) (T : MatrixArithmetic M.Domain)
    (m B S i k c r : M.Domain) : Prop :=
  M.mem k B ∧ M.mem c m ∧ M.mem r B ∧ ∃ s, M.mem s S ∧
    CopyPosition M C.omega T.addPairs T.plus T.mulPairs T.times C.zero m k c s ∧
    CopyPosition M C.omega T.addPairs T.plus T.mulPairs T.times C.zero B s r i

def positionFormula {n : Nat} (C : ExpressionData (Project.Term n)) (T : MatrixArithmetic (Project.Term n))
    (m B S i k c r : Project.Term n) : Project.Formula 1 n :=
  .conj (.mem k B) (.conj (.mem c m) (.conj (.mem r B) (Project.Formula.existsMem S
    (.conj (copyPositionFormula C.omega.weaken T.addPairs.weaken T.plus.weaken T.mulPairs.weaken T.times.weaken
      C.zero.weaken m.weaken k.weaken c.weaken (.bound 0))
      (copyPositionFormula C.omega.weaken T.addPairs.weaken T.plus.weaken T.mulPairs.weaken T.times.weaken
        C.zero.weaken B.weaken (.bound 0) r.weaken i.weaken)))))

theorem positionFormula_delta0 {n : Nat} (C : ExpressionData (Project.Term n)) (T : MatrixArithmetic (Project.Term n))
    (m B S i k c r : Project.Term n) : (positionFormula C T m B S i k c r).IsDelta0 :=
  .conj (.mem _ _) (.conj (.mem _ _) (.conj (.mem _ _) (.existsMem _
    (.conj (copyPositionFormula_delta0 _ _ _ _ _ _ _ _ _ _) (copyPositionFormula_delta0 _ _ _ _ _ _ _ _ _ _)))))

theorem positionFormula_freeClosed {n : Nat} {C : ExpressionData (Project.Term n)} (hC : C.Closed)
    {T : MatrixArithmetic (Project.Term n)} (hT : CopyCoordinates.ArithmeticClosed T) (m B S i k c r : Project.Term n)
    (hm : m.freeSupport=[]) (hB : B.freeSupport=[]) (hS : S.freeSupport=[]) (hi : i.freeSupport=[])
    (hk : k.freeSupport=[]) (hc : c.freeSupport=[]) (hr : r.freeSupport=[]) :
    (positionFormula C T m B S i k c r).FreeClosed := by
  simp [positionFormula,copyPositionFormula,mulAtFormula,addAtFormula,memPairFormula,codeFormula,pairFormula,
    Project.Formula.forallMem,Project.Formula.existsMem,Definitional.Formula.FreeClosed,hC.omega,hC.zero,
    hT.addPairs,hT.plus,hT.mulPairs,hT.times,hm,hB,hS,hi,hk,hc,hr]

theorem positionFormula_iff {M : SetTheory.Structure.{u}} (he : Extensional M) {n : Nat} (e : Env M n)
    (C : ExpressionData (Project.Term n)) (T : MatrixArithmetic (Project.Term n)) (m B S i k c r : Project.Term n) :
    Project.Formula.satisfies e (positionFormula C T m B S i k c r) ↔
      Position M (C.eval e) (T.eval e) (m.eval e) (B.eval e) (S.eval e) (i.eval e) (k.eval e) (c.eval e) (r.eval e) := by
  simp only [positionFormula,Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_mem_iff,
    Project.Formula.satisfies_existsMem_iff,copyPositionFormula_iff he,Term.eval_weaken]
  rfl

private theorem zero_sum_self_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {a : M.Domain} (ha : M.mem a C.omega) :
    KP1Y.Arithmetic.Sum M C.zero a a :=
  natural_sum_comm_d hM hC ha hC.zero_nat (KP1Y.Arithmetic.sum_zero_d hM a hC.zero_empty)

private theorem zero_le_nat_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {a : M.Domain} (ha : M.mem a C.omega) : C.zero=a ∨ M.mem C.zero a := by
  classical
  by_cases he : a=C.zero
  · exact Or.inl he.symm
  · exact Or.inr ((hC.zero_mem_iff hM ha).mpr he)

theorem position_coverage_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {m B S N i : M.Domain} (hm : M.mem m C.omega) (hB : M.mem B C.omega)
    (hS : KP1Y.Arithmetic.Product M B m S) (hN : KP1Y.Arithmetic.Product M S B N) (hi : M.mem i N) :
    ∃ k c r, Position M C T m B S i k c r := by
  have hw := omega_isOrdinal_d hM hC.omega
  have hSn := natural_product_closed_d hM hC hB hm hS
  have hNn := natural_product_closed_d hM hC hSn hB hN
  obtain ⟨s,hs,r,hr,hOuter⟩ := copy_interval_coverage_d hM hC hT.add hT.mul hC.zero_nat hB hSn hN
    (zero_sum_self_d hM hC hNn) hi (zero_le_nat_d hM hC (hw.transitive N hNn i hi))
  obtain ⟨k,hk,c,hc,hInner⟩ := copy_interval_coverage_d hM hC hT.add hT.mul hC.zero_nat hm hB hS
    (zero_sum_self_d hM hC hSn) hs (zero_le_nat_d hM hC (hw.transitive S hSn s hs))
  exact ⟨k,c,r,hk,hc,hr,s,hs,hInner,hOuter⟩

theorem position_exists_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {m B S N k c r : M.Domain} (hm : M.mem m C.omega) (hB : M.mem B C.omega)
    (hS : KP1Y.Arithmetic.Product M B m S) (hN : KP1Y.Arithmetic.Product M S B N)
    (hk : M.mem k B) (hc : M.mem c m) (hr : M.mem r B) :
    ∃ i, M.mem i N ∧ Position M C T m B S i k c r := by
  have hw := omega_isOrdinal_d hM hC.omega
  have hSn := natural_product_closed_d hM hC hB hm hS
  have hNn := natural_product_closed_d hM hC hSn hB hN
  obtain ⟨s,hsn,hInner⟩ := copy_position_exists_d hM hC hT.add hT.mul hC.zero_nat hm
    (hw.transitive B hB k hk) (hw.transitive m hm c hc)
  have hs := copy_position_bounded_d hM hC hT.add hT.mul hC.zero_nat hm hB hS (zero_sum_self_d hM hC hSn) hk hc hInner
  obtain ⟨i,_,hOuter⟩ := copy_position_exists_d hM hC hT.add hT.mul hC.zero_nat hB hsn (hw.transitive B hB r hr)
  have hi := copy_position_bounded_d hM hC hT.add hT.mul hC.zero_nat hB hSn hN (zero_sum_self_d hM hC hNn) hs hr hOuter
  exact ⟨i,hi,hk,hc,hr,s,hs,hInner,hOuter⟩

theorem Position.injective_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {m B S i k c r k' c' r' : M.Domain} (hm : M.mem m C.omega) (hB : M.mem B C.omega) (hS : M.mem S C.omega)
    (h : Position M C T m B S i k c r) (h' : Position M C T m B S i k' c' r') : k=k' ∧ c=c' ∧ r=r' := by
  obtain ⟨hk,hc,hr,s,hs,hInner,hOuter⟩ := h
  obtain ⟨hk',hc',hr',s',hs',hInner',hOuter'⟩ := h'
  have hw := omega_isOrdinal_d hM hC.omega
  obtain ⟨hss,hrr⟩ := copy_position_injective_d hM hC hT.add hT.mul hC.zero_nat hB
    (hw.transitive S hS s hs) (hw.transitive S hS s' hs') hr hr' hOuter hOuter'
  subst s'
  obtain ⟨hkk,hcc⟩ := copy_position_injective_d hM hC hT.add hT.mul hC.zero_nat hm
    (hw.transitive B hB k hk) (hw.transitive B hB k' hk') hc hc' hInner hInner'
  exact ⟨hkk,hcc,hrr⟩

theorem Position.unique {M : SetTheory.Structure.{u}} (he : Extensional M)
    {C : ExpressionData M.Domain} {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {m B S i j k c r : M.Domain} (h : Position M C T m B S i k c r) (h' : Position M C T m B S j k c r) : i=j := by
  obtain ⟨_,_,_,s,_,hInner,hOuter⟩ := h
  obtain ⟨_,_,_,s',_,hInner',hOuter'⟩ := h'
  have hss := copy_position_unique he hT.add hT.mul hInner hInner'
  subst s'
  exact copy_position_unique he hT.add hT.mul hOuter hOuter'


/-- 完整山形的语义原子，行号仅作见证，不进入根图原子。 -/
def ActualAtom (M : SetTheory.Structure.{u}) (C : ExpressionData M.Domain) (m : M.Domain)
    (L : LayerStateSpace M.Domain) (H k q p c : M.Domain) : Prop :=
  ∃ W Q, RowAt M L.states H k W Q ∧ ∃ R : RowStateSpace M.Domain, ∃ J r U F,
    RowRun M C m R W Q J ∧ RowAt M R.states J r U F ∧ MemPair M F c p ∧ Root M C m F c q

/-- 读取实际有限行历史家族中的单个父/root事实。 -/
def RowAtom (M : SetTheory.Structure.{u}) (C : ExpressionData M.Domain) (m : M.Domain)
    (R : RowStateSpace M.Domain) (Histories Runs k r q p c : M.Domain) : Prop :=
  ∃ J, M.mem J Histories ∧ MemPair M Runs k J ∧ ∃ U, M.mem U R.values ∧ ∃ F, M.mem F R.forests ∧
    RowAt M R.states J r U F ∧ MemPair M F c p ∧ Root M C m F c q

def rowAtomFormula {n : Nat} (C : ExpressionData (Project.Term n)) (m : Project.Term n)
    (R : RowStateSpace (Project.Term n)) (Histories Runs k r q p c : Project.Term n) : Project.Formula 1 n :=
  Project.Formula.existsMem Histories (.conj (memPairFormula Runs.weaken k.weaken (.bound 0))
    (Project.Formula.existsMem R.values.weaken (Project.Formula.existsMem R.forests.weaken.weaken
      (.conj (rowAtFormula R.states.weaken.weaken.weaken (.bound 2) r.weaken.weaken.weaken (.bound 1) (.bound 0))
        (.conj (memPairFormula (.bound 0) c.weaken.weaken.weaken p.weaken.weaken.weaken)
          (rootFormula C.weaken.weaken.weaken m.weaken.weaken.weaken (.bound 0) c.weaken.weaken.weaken q.weaken.weaken.weaken))))))

theorem rowAtomFormula_delta0 {n : Nat} (C : ExpressionData (Project.Term n)) (m : Project.Term n)
    (R : RowStateSpace (Project.Term n)) (Histories Runs k r q p c : Project.Term n) :
    (rowAtomFormula C m R Histories Runs k r q p c).IsDelta0 :=
  .existsMem _ (.conj (memPairFormula_delta0 _ _ _) (.existsMem _ (.existsMem _
    (.conj (rowAtFormula_delta0 _ _ _ _ _) (.conj (memPairFormula_delta0 _ _ _) (rootFormula_delta0 _ _ _ _ _))))))

theorem rowAtomFormula_freeClosed {n : Nat} {C : ExpressionData (Project.Term n)} (hC : C.Closed)
    {R : RowStateSpace (Project.Term n)} (hR : R.Closed) (m Histories Runs k r q p c : Project.Term n)
    (hm : m.freeSupport=[]) (hHistories : Histories.freeSupport=[]) (hRuns : Runs.freeSupport=[])
    (hk : k.freeSupport=[]) (hr : r.freeSupport=[]) (hq : q.freeSupport=[]) (hp : p.freeSupport=[]) (hc : c.freeSupport=[]) :
    (rowAtomFormula C m R Histories Runs k r q p c).FreeClosed := by
  have hRoot := rootFormula_freeClosed hC.weaken.weaken.weaken m.weaken.weaken.weaken (.bound 0)
    c.weaken.weaken.weaken q.weaken.weaken.weaken (by simpa using hm) rfl (by simpa using hc) (by simpa using hq)
  simp [rowAtomFormula,rowAtFormula,memPairFormula,codeFormula,pairFormula,Project.Formula.forallMem,
    Project.Formula.existsMem,Definitional.Formula.FreeClosed,hR.values,hR.forests,hR.states,hHistories,hRuns,hk,hr,hp,hc,hRoot]

theorem rowAtomFormula_iff {M : SetTheory.Structure.{u}} (he : Extensional M) {n : Nat} (e : Env M n)
    (C : ExpressionData (Project.Term n)) (m : Project.Term n) (R : RowStateSpace (Project.Term n))
    (Histories Runs k r q p c : Project.Term n) :
    Project.Formula.satisfies e (rowAtomFormula C m R Histories Runs k r q p c) ↔
      RowAtom M (C.eval e) (m.eval e) (R.eval e) (Histories.eval e) (Runs.eval e)
        (k.eval e) (r.eval e) (q.eval e) (p.eval e) (c.eval e) := by
  simp only [rowAtomFormula,Project.Formula.satisfies_existsMem_iff,Project.Formula.satisfies_conj_iff,
    memPairFormula_iff he,rowAtFormula_iff he,rootFormula_iff he,ExpressionData.eval_weaken,Term.eval_weaken]
  rfl

theorem RowAtom.actual {M : SetTheory.Structure.{u}} {C : ExpressionData M.Domain} {m : M.Domain}
    {L : LayerStateSpace M.Domain} {H B Histories Runs k r q p c : M.Domain}
    (hFamily : RowFamily M C m L H B Histories Runs) (h : RowAtom M C m L.rows Histories Runs k r q p c) :
    ActualAtom M C m L H k q p c := by
  obtain ⟨J,_,hJ,U,_,F,_,hAt,hParent,hRoot⟩ := h
  obtain ⟨W,Q,hLayer,hRows⟩ := hFamily.rows k J hJ
  exact ⟨W,Q,hLayer,L.rows,J,r,U,F,hRows,hAt,hParent,hRoot⟩

theorem actualAtom_iff_bounded_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {m : M.Domain} {L : LayerStateSpace M.Domain}
    {V P H B Histories Runs k q p c : M.Domain} (hLayers : LayerRun M C m L V P H)
    (hB : SequenceBound M C m V B) (hFamily : RowFamily M C m L H B Histories Runs) :
    ActualAtom M C m L H k q p c ↔ M.mem k B ∧ ∃ r, M.mem r B ∧ RowAtom M C m L.rows Histories Runs k r q p c := by
  constructor
  · rintro ⟨W,Q,hLayer,R,J,r,U,F,hRows,hRow,hParent,hRoot⟩
    obtain ⟨hk,hr⟩ := hLayers.parent_indices_below_d hM hC hB hLayer hRows hRow hParent
    obtain ⟨J',W',Q',hJ',hRunAt,hLayer',hRows'⟩ := hFamily.at_d hk
    obtain ⟨hWW,hQQ⟩ := hLayers.at_unique hM.1 hLayer hLayer'
    subst W'
    subst Q'
    have hJJ := hRows.unique_d hM hC hRows'
    subst J'
    have hNumeric := hRows.at_numeric_d hM hC hRow
    obtain ⟨state,_,hState,hCode⟩ := hRow
    have hRow' : RowAt M L.rows.states J r U F := ⟨state,(hRows'.graph.bounds hM.1 hState).2,hState,hCode⟩
    exact ⟨hk,r,hr,J,hJ',hRunAt,U,(hLayers.space.rows.values U).mpr hNumeric.values,
      F,(hLayers.space.rows.forests F).mpr hNumeric.forest,hRow',hParent,hRoot⟩
  · rintro ⟨_,r,_,hAtom⟩
    exact hAtom.actual hFamily

theorem ActualAtom.valid_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {m : M.Domain} {L : LayerStateSpace M.Domain}
    {H k q p c : M.Domain} (h : ActualAtom M C m L H k q p c) :
    (q=p ∨ M.mem q p) ∧ M.mem p c ∧ M.mem c m := by
  obtain ⟨W,Q,_,R,J,r,U,F,hRows,hAt,hParent,hRoot⟩ := h
  have hF := (hRows.at_numeric_d hM hC hAt).forest
  have hRootP := (root_parent_iff_d hM hC hF hParent).mp hRoot
  exact ⟨hRootP.2.2.imp_right And.left,hF.left c p hParent,(hF.bounds hM.1 hParent).1⟩

theorem RowAtom.unique_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {m : M.Domain} {L : LayerStateSpace M.Domain}
    {H B Histories Runs k r q p q' p' c : M.Domain} (hFamily : RowFamily M C m L H B Histories Runs)
    (h : RowAtom M C m L.rows Histories Runs k r q p c) (h' : RowAtom M C m L.rows Histories Runs k r q' p' c) : q=q' ∧ p=p' := by
  obtain ⟨J,_,hJ,U,_,F,_,hAt,hParent,hRoot⟩ := h
  obtain ⟨J',_,hJ',U',_,F',_,hAt',hParent',hRoot'⟩ := h'
  have hJJ := hFamily.graph.unique k J J' hJ hJ'
  subst J'
  obtain ⟨W,Q,_,hRows⟩ := hFamily.rows k J hJ
  obtain ⟨hUU,hFF⟩ := hRows.at_unique hM.1 hAt hAt'
  subst U'
  subst F'
  have hForest := (hRows.at_numeric_d hM hC hAt).forest
  exact ⟨root_unique_d hM hC hForest hRoot hRoot',hForest.unique c p p' hParent hParent'⟩


def IndexedAtom (M : SetTheory.Structure.{u}) (C : ExpressionData M.Domain) (T : MatrixArithmetic M.Domain)
    (m B S : M.Domain) (R : RowStateSpace M.Domain) (Histories Runs Pairs i e : M.Domain) : Prop :=
  ∃ k, M.mem k B ∧ ∃ c, M.mem c m ∧ ∃ r, M.mem r B ∧ ∃ q, M.mem q m ∧ ∃ p, M.mem p m ∧
    Position M C T m B S i k c r ∧ RowAtom M C m R Histories Runs k r q p c ∧ KP1Y.Reflection.Quad M Pairs e k q p c

def indexedAtomFormula {n : Nat} (C : ExpressionData (Project.Term n)) (T : MatrixArithmetic (Project.Term n))
    (m B S : Project.Term n) (R : RowStateSpace (Project.Term n)) (Histories Runs Pairs i e : Project.Term n) : Project.Formula 1 n :=
  Project.Formula.existsMem B (Project.Formula.existsMem m.weaken (Project.Formula.existsMem B.weaken.weaken
    (Project.Formula.existsMem m.weaken.weaken.weaken (Project.Formula.existsMem m.weaken.weaken.weaken.weaken
      (.conj (positionFormula C.weaken.weaken.weaken.weaken.weaken T.weaken.weaken.weaken.weaken.weaken
        m.weaken.weaken.weaken.weaken.weaken B.weaken.weaken.weaken.weaken.weaken S.weaken.weaken.weaken.weaken.weaken
        i.weaken.weaken.weaken.weaken.weaken (.bound 4) (.bound 3) (.bound 2))
        (.conj (rowAtomFormula C.weaken.weaken.weaken.weaken.weaken m.weaken.weaken.weaken.weaken.weaken
          R.weaken.weaken.weaken.weaken.weaken Histories.weaken.weaken.weaken.weaken.weaken Runs.weaken.weaken.weaken.weaken.weaken
          (.bound 4) (.bound 2) (.bound 1) (.bound 0) (.bound 3))
          (KP1Y.Reflection.quadFormula Pairs.weaken.weaken.weaken.weaken.weaken e.weaken.weaken.weaken.weaken.weaken
            (.bound 4) (.bound 1) (.bound 0) (.bound 3))))))))

theorem indexedAtomFormula_delta0 {n : Nat} (C : ExpressionData (Project.Term n)) (T : MatrixArithmetic (Project.Term n))
    (m B S : Project.Term n) (R : RowStateSpace (Project.Term n)) (Histories Runs Pairs i e : Project.Term n) :
    (indexedAtomFormula C T m B S R Histories Runs Pairs i e).IsDelta0 :=
  .existsMem _ (.existsMem _ (.existsMem _ (.existsMem _ (.existsMem _
    (.conj (positionFormula_delta0 _ _ _ _ _ _ _ _ _) (.conj (rowAtomFormula_delta0 _ _ _ _ _ _ _ _ _ _)
      (KP1Y.Reflection.quadFormula_delta0 _ _ _ _ _ _)))))))

theorem indexedAtomFormula_freeClosed {n : Nat} {C : ExpressionData (Project.Term n)} (hC : C.Closed)
    {T : MatrixArithmetic (Project.Term n)} (hT : CopyCoordinates.ArithmeticClosed T)
    {R : RowStateSpace (Project.Term n)} (hR : R.Closed) (m B S Histories Runs Pairs i e : Project.Term n)
    (hm : m.freeSupport=[]) (hB : B.freeSupport=[]) (hS : S.freeSupport=[]) (hHistories : Histories.freeSupport=[])
    (hRuns : Runs.freeSupport=[]) (hPairs : Pairs.freeSupport=[]) (hi : i.freeSupport=[]) (he : e.freeSupport=[]) :
    (indexedAtomFormula C T m B S R Histories Runs Pairs i e).FreeClosed := by
  have hPos := positionFormula_freeClosed hC.weaken.weaken.weaken.weaken.weaken hT.weaken.weaken.weaken.weaken.weaken
    m.weaken.weaken.weaken.weaken.weaken B.weaken.weaken.weaken.weaken.weaken S.weaken.weaken.weaken.weaken.weaken
    i.weaken.weaken.weaken.weaken.weaken (.bound 4) (.bound 3) (.bound 2)
    (by simpa using hm) (by simpa using hB) (by simpa using hS) (by simpa using hi) rfl rfl rfl
  have hAtom := rowAtomFormula_freeClosed hC.weaken.weaken.weaken.weaken.weaken hR.weaken.weaken.weaken.weaken.weaken
    m.weaken.weaken.weaken.weaken.weaken Histories.weaken.weaken.weaken.weaken.weaken Runs.weaken.weaken.weaken.weaken.weaken
    (.bound 4) (.bound 2) (.bound 1) (.bound 0) (.bound 3)
    (by simpa using hm) (by simpa using hHistories) (by simpa using hRuns) rfl rfl rfl rfl rfl
  have hQuad := KP1Y.Reflection.quadFormula_freeClosed Pairs.weaken.weaken.weaken.weaken.weaken
    e.weaken.weaken.weaken.weaken.weaken (Project.Term.bound (depth := n+5) 4) (.bound 1) (.bound 0) (.bound 3)
    (by simpa using hPairs) (by simpa using he) rfl rfl rfl rfl
  simp [indexedAtomFormula,Project.Formula.existsMem,Definitional.Formula.FreeClosed,hm,hB,hPos,hAtom,hQuad]

theorem indexedAtomFormula_iff {M : SetTheory.Structure.{u}} (he : Extensional M) {n : Nat} (env : Env M n)
    (C : ExpressionData (Project.Term n)) (T : MatrixArithmetic (Project.Term n)) (m B S : Project.Term n)
    (R : RowStateSpace (Project.Term n)) (Histories Runs Pairs i e : Project.Term n) :
    Project.Formula.satisfies env (indexedAtomFormula C T m B S R Histories Runs Pairs i e) ↔
      IndexedAtom M (C.eval env) (T.eval env) (m.eval env) (B.eval env) (S.eval env) (R.eval env)
        (Histories.eval env) (Runs.eval env) (Pairs.eval env) (i.eval env) (e.eval env) := by
  simp only [indexedAtomFormula,Project.Formula.satisfies_existsMem_iff,Project.Formula.satisfies_conj_iff,
    positionFormula_iff he,rowAtomFormula_iff he,KP1Y.Reflection.quadFormula_iff he,
    ExpressionData.eval_weaken,MatrixArithmetic.eval_weaken,RowStateSpace.eval_weaken,Term.eval_weaken]
  rfl

private theorem quad_unique {M : SetTheory.Structure.{u}} (he : Extensional M) {Pairs e e' k q p c : M.Domain}
    (h : KP1Y.Reflection.Quad M Pairs e k q p c) (h' : KP1Y.Reflection.Quad M Pairs e' k q p c) : e=e' := by
  obtain ⟨u,_,v,_,hE,hU,hV⟩ := h
  obtain ⟨u',_,v',_,hE',hU',hV'⟩ := h'
  have huu := codes_unique he hU hU'
  have hvv := codes_unique he hV hV'
  subst u'
  subst v'
  exact codes_unique he hE hE'

theorem IndexedAtom.unique_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {m B S : M.Domain} {L : LayerStateSpace M.Domain} {H Histories Runs Pairs i e e' : M.Domain}
    (hm : M.mem m C.omega) (hB : M.mem B C.omega) (hS : M.mem S C.omega)
    (hFamily : RowFamily M C m L H B Histories Runs)
    (h : IndexedAtom M C T m B S L.rows Histories Runs Pairs i e)
    (h' : IndexedAtom M C T m B S L.rows Histories Runs Pairs i e') : e=e' := by
  obtain ⟨k,_,c,_,r,_,q,_,p,_,hPos,hAtom,hQuad⟩ := h
  obtain ⟨k',_,c',_,r',_,q',_,p',_,hPos',hAtom',hQuad'⟩ := h'
  obtain ⟨hkk,hcc,hrr⟩ := hPos.injective_d hM hC hT hm hB hS hPos'
  subst k'
  subst c'
  subst r'
  obtain ⟨hqq,hpp⟩ := hAtom.unique_d hM hC hFamily hAtom'
  subst q'
  subst p'
  exact quad_unique hM.1 hQuad hQuad'

private def indexedAtomSchema : Project.Delta0BinarySchema 20 where
  body := indexedAtomFormula ⟨.bound 21,.bound 20,.bound 19,.bound 18,.bound 17⟩
    ⟨.bound 16,.bound 15,.bound 14,.bound 13,.bound 12,.bound 11⟩ (.bound 10) (.bound 9) (.bound 8)
    ⟨.bound 7,.bound 6,.bound 5⟩ (.bound 4) (.bound 3) (.bound 2) (.bound 1) (.bound 0)
  freeClosed := indexedAtomFormula_freeClosed ⟨rfl,rfl,rfl,rfl,rfl⟩ ⟨rfl,rfl,rfl,rfl,rfl,rfl⟩ ⟨rfl,rfl,rfl⟩
    _ _ _ _ _ _ _ _ rfl rfl rfl rfl rfl rfl rfl rfl
  delta0 := indexedAtomFormula_delta0 _ _ _ _ _ _ _ _ _ _ _

structure AtomMap (M : SetTheory.Structure.{u}) (C : ExpressionData M.Domain) (T : MatrixArithmetic M.Domain)
    (m B S N : M.Domain) (R : RowStateSpace M.Domain) (Histories Runs Pairs Codes P : M.Domain) : Prop where
  graph : Filter.PartialGraph M P N Codes
  rows : ∀ i e, MemPair M P i e ↔ M.mem i N ∧ M.mem e Codes ∧ IndexedAtom M C T m B S R Histories Runs Pairs i e

theorem atom_map_exists_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {m B S N : M.Domain} {L : LayerStateSpace M.Domain} {H Histories Runs Pairs Codes : M.Domain}
    (hm : M.mem m C.omega) (hB : M.mem B C.omega) (hS : M.mem S C.omega)
    (hFamily : RowFamily M C m L H B Histories Runs) :
    ∃ P, AtomMap M C T m B S N L.rows Histories Runs Pairs Codes P := by
  let env := ((((((((((((((((((((oneEnv C.omega).push C.zero).push C.one).push C.sequences).push C.expressions).push T.addPairs).push T.plus).push T.mulPairs).push T.times).push T.diffPairs).push T.difference).push m).push B).push S).push L.rows.values).push L.rows.forests).push L.rows.states).push Histories).push Runs).push Pairs)
  have hφ (i e : M.Domain) : Project.Formula.satisfies ((env.push i).push e) indexedAtomSchema.body ↔
      IndexedAtom M C T m B S L.rows Histories Runs Pairs i e := indexedAtomFormula_iff hM.1 _ _ _ _ _ _ _ _ _ _ _ _
  obtain ⟨P,hSupport,hRaw⟩ := relation_comprehension_d hM indexedAtomSchema env N Codes
  have hRows (i e : M.Domain) : MemPair M P i e ↔ M.mem i N ∧ M.mem e Codes ∧
      IndexedAtom M C T m B S L.rows Histories Runs Pairs i e := by
    simpa only [hφ] using hRaw i e
  refine ⟨P,⟨hSupport,?_⟩,hRows⟩
  intro i e e' hAt hAt'
  exact ((hRows i e).mp hAt).2.2.unique_d hM hC hT hm hB hS hFamily ((hRows i e').mp hAt').2.2


theorem filtered_edges_iff_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {D : KP1Y.Reflection.Data M.Domain} (hD : D.Valid M) (hOmega : D.omega=C.omega)
    {m B S N : M.Domain} {L : LayerStateSpace M.Domain} {V P H Histories Runs Map len A I k q p c : M.Domain}
    (hLayers : LayerRun M C m L V P H) (hB : SequenceBound M C m V B)
    (hS : KP1Y.Arithmetic.Product M B m S) (hN : KP1Y.Arithmetic.Product M S B N)
    (hFamily : RowFamily M C m L H B Histories Runs)
    (hMap : AtomMap M C T m B S N L.rows Histories Runs D.pairs D.edgeCodes Map)
    (hFilter : Filter.Filtered M C.omega Map N D.edgeCodes len A I) :
    KP1Y.Reflection.EdgeAt M D A k q p c ↔ ActualAtom M C m L H k q p c := by
  have hm := hLayers.space.rows.width
  have hw := omega_isOrdinal_d hM hC.omega
  constructor
  · rintro ⟨j,_,e,_,hEntry,hQuad⟩
    obtain ⟨i,_,hAt⟩ := (hFilter.range_iff hM.1 hMap.graph).mp ⟨j,(hFilter.output.bounds hM.1 hEntry).1,hEntry⟩
    obtain ⟨_,_,k',_,c',_,r,_,q',_,p',_,_,hAtom,hQuad'⟩ := (hMap.rows i e).mp hAt
    obtain ⟨hkk,hqq,hpp,hcc⟩ := hQuad.injective hM.1 hQuad'
    subst k'
    subst q'
    subst p'
    subst c'
    exact hAtom.actual hFamily
  · intro hActual
    obtain ⟨hk,r,hr,hAtom⟩ := (actualAtom_iff_bounded_d hM hC hLayers hB hFamily).mp hActual
    have hValid := hActual.valid_d hM hC
    have hc := hValid.2.2
    have hp := (hw.mem hm).transitive c hc p hValid.2.1
    have hq : M.mem q m := by
      rcases hValid.1 with he | hlt
      · exact he.symm ▸ hp
      · exact (hw.mem hm).transitive p hp q hlt
    obtain ⟨i,hi,hPos⟩ := position_exists_d hM hC hT hm hB.1.1 hS hN hk hc hr
    obtain ⟨e,he,hQuad⟩ := KP1Y.Reflection.quad_code_exists_d hM hD
      (hOmega.symm ▸ hw.transitive B hB.1.1 k hk) (hOmega.symm ▸ hw.transitive m hm q hq)
      (hOmega.symm ▸ hw.transitive m hm p hp) (hOmega.symm ▸ hw.transitive m hm c hc)
    have hAt := (hMap.rows i e).mpr ⟨hi,he,k,hk,c,hc,r,hr,q,hq,p,hp,hPos,hAtom,hQuad⟩
    obtain ⟨j,hj,hEntry⟩ := (hFilter.range_iff hM.1 hMap.graph).mpr ⟨i,hi,hAt⟩
    exact ⟨j,hOmega.symm ▸ hw.transitive len hFilter.length j hj,e,he,hEntry,hQuad⟩

theorem filtered_diagram_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {D : KP1Y.Reflection.Data M.Domain} (hD : D.Valid M) (hOmega : D.omega=C.omega)
    {m B S N : M.Domain} {L : LayerStateSpace M.Domain} {V P H Histories Runs Map len A I : M.Domain}
    (hLayers : LayerRun M C m L V P H) (hB : SequenceBound M C m V B)
    (hS : KP1Y.Arithmetic.Product M B m S) (hN : KP1Y.Arithmetic.Product M S B N)
    (hFamily : RowFamily M C m L H B Histories Runs)
    (hMap : AtomMap M C T m B S N L.rows Histories Runs D.pairs D.edgeCodes Map)
    (hFilter : Filter.Filtered M C.omega Map N D.edgeCodes len A I) : KP1Y.Reflection.Diagram M D m A := by
  refine ⟨hOmega.symm ▸ hLayers.space.rows.width,(hD.edgeLists A).mpr ⟨len,hOmega.symm ▸ hFilter.length,hFilter.output⟩,?_⟩
  intro k _ q _ p _ c _ hEdge
  exact ((filtered_edges_iff_d hM hC hT hD hOmega hLayers hB hS hN hFamily hMap hFilter).mp hEdge).valid_d hM hC

/-- 完整对象计算证据，不把原子集、行运行或有限预算当作外部 oracle。 -/
def Enumerated (M : SetTheory.Structure.{u}) (C : ExpressionData M.Domain) (T : MatrixArithmetic M.Domain)
    (D : KP1Y.Reflection.Data M.Domain) (m : M.Domain) (L : LayerStateSpace M.Domain) (V H A : M.Domain) : Prop :=
  ∃ B S N Histories Runs Map len I, SequenceBound M C m V B ∧ KP1Y.Arithmetic.Product M B m S ∧
    KP1Y.Arithmetic.Product M S B N ∧ RowFamily M C m L H B Histories Runs ∧
    AtomMap M C T m B S N L.rows Histories Runs D.pairs D.edgeCodes Map ∧
    Filter.Filtered M C.omega Map N D.edgeCodes len A I

theorem enumerated_exists_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    (D : KP1Y.Reflection.Data M.Domain) {m : M.Domain} {L : LayerStateSpace M.Domain} {V P H : M.Domain}
    (hLayers : LayerRun M C m L V P H) : ∃ A, Enumerated M C T D m L V H A := by
  have hm := hLayers.space.rows.width
  obtain ⟨B,hB⟩ := sequence_bound_exists_d hM hC hm hLayers.base.row.values
  obtain ⟨S,hSn,hSMul⟩ := hT.mul.mul_exists_d hM hC hB.1.1 hm
  have hS := (hT.mul.mul_iff_product hM hB.1.1 hm).mp hSMul
  obtain ⟨N,hNn,hNMul⟩ := hT.mul.mul_exists_d hM hC hSn hB.1.1
  have hN := (hT.mul.mul_iff_product hM hSn hB.1.1).mp hNMul
  obtain ⟨Histories,Runs,hFamily⟩ := row_family_exists_d hM hC hLayers hB.1.1
  obtain ⟨Map,hMap⟩ := atom_map_exists_d (Pairs := D.pairs) (Codes := D.edgeCodes) (N := N) hM hC hT hm hB.1.1 hSn hFamily
  obtain ⟨len,A,I,hFilter⟩ := Filter.filtered_exists_d hM hC hNn hMap.graph
  exact ⟨A,B,S,N,Histories,Runs,Map,len,I,hB,hS,hN,hFamily,hMap,hFilter⟩

theorem Enumerated.diagram_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {D : KP1Y.Reflection.Data M.Domain} (hD : D.Valid M) (hOmega : D.omega=C.omega)
    {m : M.Domain} {L : LayerStateSpace M.Domain} {V P H A : M.Domain}
    (hLayers : LayerRun M C m L V P H) (h : Enumerated M C T D m L V H A) : KP1Y.Reflection.Diagram M D m A := by
  obtain ⟨B,S,N,Histories,Runs,Map,len,I,hB,hS,hN,hFamily,hMap,hFilter⟩ := h
  exact filtered_diagram_d hM hC hT hD hOmega hLayers hB hS hN hFamily hMap hFilter

theorem Enumerated.edges_iff_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {D : KP1Y.Reflection.Data M.Domain} (hD : D.Valid M) (hOmega : D.omega=C.omega)
    {m : M.Domain} {L : LayerStateSpace M.Domain} {V P H A k q p c : M.Domain}
    (hLayers : LayerRun M C m L V P H) (h : Enumerated M C T D m L V H A) :
    KP1Y.Reflection.EdgeAt M D A k q p c ↔ ActualAtom M C m L H k q p c := by
  obtain ⟨B,S,N,Histories,Runs,Map,len,I,hB,hS,hN,hFamily,hMap,hFilter⟩ := h
  exact filtered_edges_iff_d hM hC hT hD hOmega hLayers hB hS hN hFamily hMap hFilter


theorem RowFamily.atom_iff_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {m : M.Domain} {L : LayerStateSpace M.Domain}
    {V P H B Histories Runs Histories' Runs' k r q p c : M.Domain} (hLayers : LayerRun M C m L V P H)
    (h : RowFamily M C m L H B Histories Runs) (h' : RowFamily M C m L H B Histories' Runs') :
    RowAtom M C m L.rows Histories Runs k r q p c ↔ RowAtom M C m L.rows Histories' Runs' k r q p c := by
  have transfer {X F Y G : M.Domain} (hF : RowFamily M C m L H B X F) (hG : RowFamily M C m L H B Y G)
      (hAtom : RowAtom M C m L.rows X F k r q p c) : RowAtom M C m L.rows Y G k r q p c := by
    obtain ⟨J,_,hJ,U,hU,Q,hQ,hAt,hParent,hRoot⟩ := hAtom
    obtain ⟨W,Q0,hLayer,hRows⟩ := hF.rows k J hJ
    obtain ⟨J',W',Q0',hJ',hPair',hLayer',hRows'⟩ := hG.at_d (hF.graph.bounds hM.1 hJ).1
    obtain ⟨hWW,hQQ⟩ := hLayers.at_unique hM.1 hLayer hLayer'
    subst W'
    subst Q0'
    have hJJ := hRows.unique_d hM hC hRows'
    subst J'
    exact ⟨J,hJ',hPair',U,hU,Q,hQ,hAt,hParent,hRoot⟩
  exact ⟨transfer h h',transfer h' h⟩

theorem AtomMap.unique_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain}
    {m B S N : M.Domain} {L : LayerStateSpace M.Domain} {V P H Histories Runs Histories' Runs' Pairs Codes Map Map' : M.Domain}
    (hLayers : LayerRun M C m L V P H) (hFamily : RowFamily M C m L H B Histories Runs)
    (hFamily' : RowFamily M C m L H B Histories' Runs')
    (h : AtomMap M C T m B S N L.rows Histories Runs Pairs Codes Map)
    (h' : AtomMap M C T m B S N L.rows Histories' Runs' Pairs Codes Map') : Map=Map' := by
  apply relation_ext hM.1 h.graph.support h'.graph.support
  intro i e
  rw [h.rows i e,h'.rows i e]
  apply and_congr Iff.rfl
  apply and_congr Iff.rfl
  have hAtom (k r q p c : M.Domain) := hFamily.atom_iff_d (k := k) (r := r) (q := q) (p := p) (c := c) hM hC hLayers hFamily'
  simp only [IndexedAtom,hAtom]

theorem Enumerated.unique_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain}
    {D : KP1Y.Reflection.Data M.Domain} {m : M.Domain} {L : LayerStateSpace M.Domain} {V P H A A' : M.Domain}
    (hLayers : LayerRun M C m L V P H) (h : Enumerated M C T D m L V H A)
    (h' : Enumerated M C T D m L V H A') : A=A' := by
  obtain ⟨B,S,N,Histories,Runs,Map,len,I,hB,hS,hN,hFamily,hMap,hFilter⟩ := h
  obtain ⟨B',S',N',Histories',Runs',Map',len',I',hB',hS',hN',hFamily',hMap',hFilter'⟩ := h'
  have hBB := hB.unique_d hM hC hB'
  subst B'
  have hSS := KP1Y.Arithmetic.product_unique_d hM hS hS'
  subst S'
  have hNN := KP1Y.Arithmetic.product_unique_d hM hN hN'
  subst N'
  have hMaps := hMap.unique_d hM hC hLayers hFamily hFamily' hMap'
  subst Map'
  have hSn := natural_product_closed_d hM hC hB.1.1 hLayers.space.rows.width hS
  have hNn := natural_product_closed_d hM hC hSn hB.1.1 hN
  exact (hFilter.unique_d hM hC hNn hMap.graph hFilter').2.1

theorem Enumerated.empty_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain}
    {D : KP1Y.Reflection.Data M.Domain} {L : LayerStateSpace M.Domain} {V H A : M.Domain}
    (h : Enumerated M C T D C.zero L V H A) : A=C.zero := by
  obtain ⟨B,S,N,Histories,Runs,Map,len,I,_,_,_,_,hMap,hFilter⟩ := h
  exact (hFilter.empty_d hM hC (fun i e hAt => by
    obtain ⟨_,_,_,_,c,hc,_⟩ := (hMap.rows i e).mp hAt
    exact hC.zero_empty c hc)).2.1

private theorem row_space_unique {M : SetTheory.Structure.{u}} (he : Extensional M)
    {C : ExpressionData M.Domain} {m : M.Domain} {R R' : RowStateSpace M.Domain}
    (hR : R.Valid M C m) (hR' : R'.Valid M C m) : R=R' := by
  have hv : R.values=R'.values := he.eq_of_same_members _ _ (fun V => (hR.values V).trans (hR'.values V).symm)
  have hf : R.forests=R'.forests := he.eq_of_same_members _ _ (fun P => (hR.forests P).trans (hR'.forests P).symm)
  have hs : R.states=R'.states := he.eq_of_same_members _ _ (fun state => by
    rw [hR.states state,hR'.states state,hv,hf])
  cases R
  cases R'
  simp_all

private theorem layer_space_unique {M : SetTheory.Structure.{u}} (he : Extensional M)
    {C : ExpressionData M.Domain} {m : M.Domain} {L L' : LayerStateSpace M.Domain}
    (hL : L.Valid M C m) (hL' : L'.Valid M C m) : L=L' := by
  have hr := row_space_unique he hL.rows hL'.rows
  have hs : L.states=L'.states := he.eq_of_same_members _ _ (fun state => (hL.states state).trans (hL'.states state).symm)
  cases L
  cases L'
  simp_all

/-- 合法表达式的规范有限根图；所有山形、父图和有限过滤均由真实对象计算见证。 -/
def ExpressionGraph (M : SetTheory.Structure.{u}) (C : ExpressionData M.Domain) (T : MatrixArithmetic M.Domain)
    (D : KP1Y.Reflection.Data M.Domain) (V m A : M.Domain) : Prop :=
  LegalAt M C.omega C.zero C.one V m ∧ ∃ F P L H, LinearForest M C.omega m F ∧
    Selects true M C m F V P ∧ LayerRun M C m L V P H ∧ Enumerated M C T D m L V H A

theorem expression_graph_exists_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    (D : KP1Y.Reflection.Data M.Domain) {V m : M.Domain} (hLegal : LegalAt M C.omega C.zero C.one V m) :
    ∃ A, ExpressionGraph M C T D V m A := by
  obtain ⟨F,P,L,H,hF,hP,hH⟩ := legal_layers_exists_d hM hC hLegal
  obtain ⟨A,hA⟩ := enumerated_exists_d hM hC hT D hH
  exact ⟨A,hLegal,F,P,L,H,hF,hP,hH,hA⟩

theorem ExpressionGraph.unique_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain}
    {D : KP1Y.Reflection.Data M.Domain} {V m m' A A' : M.Domain}
    (h : ExpressionGraph M C T D V m A) (h' : ExpressionGraph M C T D V m' A') : m=m' ∧ A=A' := by
  obtain ⟨hLegal,F,P,L,H,hF,hP,hH,hA⟩ := h
  obtain ⟨hLegal',F',P',L',H',hF',hP',hH',hA'⟩ := h'
  have hmm := legal_length_unique hM.1 hLegal hLegal'
  subst m'
  have hFF := linear_forest_unique hM.1 hF hF'
  subst F'
  have hPP := hP.unique hM.1 hP'
  subst P'
  have hLL := layer_space_unique hM.1 hH.space hH'.space
  subst L'
  have hHH := hH.unique_d hM hC hH'
  subst H'
  exact ⟨rfl,hA.unique_d hM hC hH hA'⟩

theorem ExpressionGraph.diagram_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {D : KP1Y.Reflection.Data M.Domain} (hD : D.Valid M) (hOmega : D.omega=C.omega) {V m A : M.Domain}
    (h : ExpressionGraph M C T D V m A) : KP1Y.Reflection.Diagram M D m A := by
  obtain ⟨_,_,_,_,_,_,_,hH,hA⟩ := h
  exact hA.diagram_d hM hC hT hD hOmega hH


def linearForestFormula {n : Nat} (w m P : Project.Term n) : Project.Formula 1 n :=
  .conj (forestFormula w m P) (Project.Formula.forallMem m (Project.Formula.forallMem m.weaken
    (.iff (memPairFormula P.weaken.weaken (.bound 1) (.bound 0)) (successorFormula (.bound 1) (.bound 0)))))

theorem linearForestFormula_delta0 {n : Nat} (w m P : Project.Term n) : (linearForestFormula w m P).IsDelta0 :=
  .conj (forestFormula_delta0 _ _ _) (.forallMem _ (.forallMem _ (.iff (memPairFormula_delta0 _ _ _) (successorFormula_delta0 _ _))))

theorem linearForestFormula_freeClosed {n : Nat} (w m P : Project.Term n)
    (hw : w.freeSupport=[]) (hm : m.freeSupport=[]) (hP : P.freeSupport=[]) : (linearForestFormula w m P).FreeClosed := by
  simp [linearForestFormula,forestFormula,memPairFormula,codeFormula,pairFormula,successorFormula,
    Project.Formula.forallMem,Project.Formula.existsMem,Definitional.Formula.FreeClosed,hw,hm,hP]

theorem linearForestFormula_iff {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory) {n : Nat}
    (e : Env M n) (w m P : Project.Term n) (hω : M.IsOmega (w.eval e)) :
    Project.Formula.satisfies e (linearForestFormula w m P) ↔ LinearForest M (w.eval e) (m.eval e) (P.eval e) := by
  simp only [linearForestFormula,Project.Formula.satisfies_conj_iff,forestFormula_iff hM.1,
    Project.Formula.satisfies_forallMem_iff,Project.Formula.satisfies_iff_iff,memPairFormula_iff hM.1,
    successorFormula_iff hM.1,Term.eval_weaken]
  constructor
  · rintro ⟨hForest,hRows⟩
    refine ⟨hForest,fun c p => ?_⟩
    constructor
    · intro hAt
      obtain ⟨hc,hp⟩ := hForest.bounds hM.1 hAt
      exact ⟨hc,(hRows c hc p hp).mp hAt⟩
    · rintro ⟨hc,hs⟩
      have hp := ((omega_isOrdinal_d hM hω).mem hForest.width).transitive c hc p hs.predecessor_mem
      exact (hRows c hc p hp).mpr hs
  · intro h
    exact ⟨h.1,fun c hc p _ => (h.2 c p).trans ⟨And.right,fun hs => ⟨hc,hs⟩⟩⟩

def rowFamilyFormula {n : Nat} (C : ExpressionData (Project.Term n)) (m : Project.Term n) (R : RowStateSpace (Project.Term n))
    (States H B Histories Runs Pairs Table : Project.Term n) : Project.Formula 1 n :=
  .conj (graphFormula Runs B Histories) (Project.Formula.forallMem B (Project.Formula.forallMem Histories.weaken
    (.imp (memPairFormula Runs.weaken.weaken (.bound 1) (.bound 0))
      (rowForLayerFormula C.weaken.weaken m.weaken.weaken R.weaken.weaken States.weaken.weaken H.weaken.weaken
        Pairs.weaken.weaken Table.weaken.weaken (.bound 1) (.bound 0)))))

theorem rowFamilyFormula_delta0 {n : Nat} (C : ExpressionData (Project.Term n)) (m : Project.Term n) (R : RowStateSpace (Project.Term n))
    (States H B Histories Runs Pairs Table : Project.Term n) : (rowFamilyFormula C m R States H B Histories Runs Pairs Table).IsDelta0 :=
  .conj (graphFormula_delta0 _ _ _) (.forallMem _ (.forallMem _ (.imp (memPairFormula_delta0 _ _ _)
    (rowForLayerFormula_delta0 _ _ _ _ _ _ _ _ _))))

theorem rowFamilyFormula_freeClosed {n : Nat} {C : ExpressionData (Project.Term n)} (hC : C.Closed)
    {R : RowStateSpace (Project.Term n)} (hR : R.Closed) (m States H B Histories Runs Pairs Table : Project.Term n)
    (hm : m.freeSupport=[]) (hStates : States.freeSupport=[]) (hH : H.freeSupport=[]) (hB : B.freeSupport=[])
    (hHistories : Histories.freeSupport=[]) (hRuns : Runs.freeSupport=[]) (hPairs : Pairs.freeSupport=[]) (hTable : Table.freeSupport=[]) :
    (rowFamilyFormula C m R States H B Histories Runs Pairs Table).FreeClosed := by
  have hRow := rowForLayerFormula_freeClosed hC.weaken.weaken hR.weaken.weaken m.weaken.weaken States.weaken.weaken H.weaken.weaken
    Pairs.weaken.weaken Table.weaken.weaken (.bound 1) (.bound 0)
    (by simpa using hm) (by simpa using hStates) (by simpa using hH) (by simpa using hPairs) (by simpa using hTable) rfl rfl
  simp [rowFamilyFormula,graphFormula,memPairFormula,codeFormula,pairFormula,Project.Formula.forallMem,
    Project.Formula.existsMem,Definitional.Formula.FreeClosed,hB,hHistories,hRuns,hRow]

theorem rowFamilyFormula_iff {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory) {n : Nat} (e : Env M n)
    (C : ExpressionData (Project.Term n)) (m : Project.Term n) (R : RowStateSpace (Project.Term n))
    (States H B Histories Runs Pairs Table : Project.Term n)
    (hC : (C.eval e).Valid M) (hR : (R.eval e).Valid M (C.eval e) (m.eval e))
    (hTable : DifferenceTable M (C.eval e) (Pairs.eval e) (Table.eval e))
    (hRooted : ∀ k W Q, RowAt M (States.eval e) (H.eval e) k W Q → RootedRow M (C.eval e) (m.eval e) W Q) :
    Project.Formula.satisfies e (rowFamilyFormula C m R States H B Histories Runs Pairs Table) ↔
      RowFamily M (C.eval e) (m.eval e) ⟨R.eval e,States.eval e⟩ (H.eval e) (B.eval e) (Histories.eval e) (Runs.eval e) := by
  have hRow (k J : M.Domain) : Project.Formula.satisfies ((e.push k).push J)
      (rowForLayerFormula C.weaken.weaken m.weaken.weaken R.weaken.weaken States.weaken.weaken H.weaken.weaken
        Pairs.weaken.weaken Table.weaken.weaken (.bound 1) (.bound 0)) ↔
      ∃ W Q, RowAt M (States.eval e) (H.eval e) k W Q ∧ RowRun M (C.eval e) (m.eval e) (R.eval e) W Q J := by
    have h := rowForLayerFormula_iff hM ((e.push k).push J) C.weaken.weaken m.weaken.weaken R.weaken.weaken
      States.weaken.weaken H.weaken.weaken Pairs.weaken.weaken Table.weaken.weaken (.bound 1) (.bound 0)
      (by simpa only [ExpressionData.eval_weaken] using hC)
      (by simpa only [ExpressionData.eval_weaken,RowStateSpace.eval_weaken,Term.eval_weaken] using hR)
      (by simpa only [ExpressionData.eval_weaken,Term.eval_weaken] using hTable)
      (by simpa only [ExpressionData.eval_weaken,Term.eval_weaken,Project.Term.eval_bound_one_push,Project.Term.eval_bound_zero_push] using hRooted k)
    simpa only [ExpressionData.eval_weaken,RowStateSpace.eval_weaken,Term.eval_weaken,
      Project.Term.eval_bound_one_push,Project.Term.eval_bound_zero_push] using h
  simp only [rowFamilyFormula,Project.Formula.satisfies_conj_iff,graphFormula_iff hM.1,
    Project.Formula.satisfies_forallMem_iff,Project.Formula.satisfies_imp_iff,memPairFormula_iff hM.1,Term.eval_weaken,hRow]
  constructor
  · rintro ⟨hGraph,hRows⟩
    exact ⟨hGraph,fun k J hAt => hRows k (hGraph.bounds hM.1 hAt).1 J (hGraph.bounds hM.1 hAt).2 hAt⟩
  · intro h
    exact ⟨h.graph,fun k _ J _ hAt => h.rows k J hAt⟩

def atomMapFormula {n : Nat} (C : ExpressionData (Project.Term n)) (T : MatrixArithmetic (Project.Term n))
    (m B S N : Project.Term n) (R : RowStateSpace (Project.Term n)) (Histories Runs Pairs Codes P : Project.Term n) : Project.Formula 1 n :=
  .conj (Filter.partialGraphFormula P N Codes) (Project.Formula.forallMem N (Project.Formula.forallMem Codes.weaken
    (.iff (memPairFormula P.weaken.weaken (.bound 1) (.bound 0))
      (indexedAtomFormula C.weaken.weaken T.weaken.weaken m.weaken.weaken B.weaken.weaken S.weaken.weaken R.weaken.weaken
        Histories.weaken.weaken Runs.weaken.weaken Pairs.weaken.weaken (.bound 1) (.bound 0)))))

theorem atomMapFormula_delta0 {n : Nat} (C : ExpressionData (Project.Term n)) (T : MatrixArithmetic (Project.Term n))
    (m B S N : Project.Term n) (R : RowStateSpace (Project.Term n)) (Histories Runs Pairs Codes P : Project.Term n) :
    (atomMapFormula C T m B S N R Histories Runs Pairs Codes P).IsDelta0 :=
  .conj (Filter.partialGraphFormula_delta0 _ _ _) (.forallMem _ (.forallMem _ (.iff (memPairFormula_delta0 _ _ _)
    (indexedAtomFormula_delta0 _ _ _ _ _ _ _ _ _ _ _))))

theorem atomMapFormula_freeClosed {n : Nat} {C : ExpressionData (Project.Term n)} (hC : C.Closed)
    {T : MatrixArithmetic (Project.Term n)} (hT : CopyCoordinates.ArithmeticClosed T) {R : RowStateSpace (Project.Term n)} (hR : R.Closed)
    (m B S N Histories Runs Pairs Codes P : Project.Term n) (hm : m.freeSupport=[]) (hB : B.freeSupport=[])
    (hS : S.freeSupport=[]) (hN : N.freeSupport=[]) (hHistories : Histories.freeSupport=[]) (hRuns : Runs.freeSupport=[])
    (hPairs : Pairs.freeSupport=[]) (hCodes : Codes.freeSupport=[]) (hP : P.freeSupport=[]) :
    (atomMapFormula C T m B S N R Histories Runs Pairs Codes P).FreeClosed := by
  have hIndexed := indexedAtomFormula_freeClosed hC.weaken.weaken hT.weaken.weaken hR.weaken.weaken
    m.weaken.weaken B.weaken.weaken S.weaken.weaken Histories.weaken.weaken Runs.weaken.weaken Pairs.weaken.weaken (.bound 1) (.bound 0)
    (by simpa using hm) (by simpa using hB) (by simpa using hS) (by simpa using hHistories)
    (by simpa using hRuns) (by simpa using hPairs) rfl rfl
  have hPartial := Filter.partialGraphFormula_freeClosed P N Codes hP hN hCodes
  simp [atomMapFormula,Project.Formula.forallMem,Definitional.Formula.FreeClosed,memPairFormula,codeFormula,pairFormula,
    Project.Formula.existsMem,hIndexed,hPartial,hP,hN,hCodes]

theorem atomMapFormula_iff {M : SetTheory.Structure.{u}} (he : Extensional M) {n : Nat} (env : Env M n)
    (C : ExpressionData (Project.Term n)) (T : MatrixArithmetic (Project.Term n)) (m B S N : Project.Term n)
    (R : RowStateSpace (Project.Term n)) (Histories Runs Pairs Codes P : Project.Term n) :
    Project.Formula.satisfies env (atomMapFormula C T m B S N R Histories Runs Pairs Codes P) ↔
      AtomMap M (C.eval env) (T.eval env) (m.eval env) (B.eval env) (S.eval env) (N.eval env) (R.eval env)
        (Histories.eval env) (Runs.eval env) (Pairs.eval env) (Codes.eval env) (P.eval env) := by
  simp only [atomMapFormula,Project.Formula.satisfies_conj_iff,Filter.partialGraphFormula_iff he,
    Project.Formula.satisfies_forallMem_iff,Project.Formula.satisfies_iff_iff,memPairFormula_iff he,indexedAtomFormula_iff he,
    ExpressionData.eval_weaken,MatrixArithmetic.eval_weaken,RowStateSpace.eval_weaken,Term.eval_weaken]
  constructor
  · rintro ⟨hGraph,hRows⟩
    refine ⟨hGraph,fun i e => ?_⟩
    constructor
    · intro hAt
      obtain ⟨hi,he⟩ := hGraph.bounds he hAt
      exact ⟨hi,he,(hRows i hi e he).mp hAt⟩
    · rintro ⟨hi,he,hIndexed⟩
      exact (hRows i hi e he).mpr hIndexed
  · intro h
    exact ⟨h.graph,fun i hi e he => (h.rows i e).trans ⟨fun h => h.2.2,fun h => ⟨hi,he,h⟩⟩⟩

end KP1Y.OneYFinite.ExpressionDiagram
