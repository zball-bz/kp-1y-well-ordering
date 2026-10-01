import KP1Y.OneYMountainLayerSyntax

/-! 全部内部 ω 层的实际提取运行：每步证书经 Σ₁ 收集形成函数图，再进行对象迭代。 -/
namespace KP1Y.OneYFinite
open YesMetaZFC YesMetaZFC.SetTheory YesMetaZFC.SetTheory.Definitional
open KP1Y.Kuratowski KP1Y.Functions KP1Y.Naturals
universe u

def LayerTransition (M : SetTheory.Structure.{u}) (C : ExpressionData M.Domain) (m source target : M.Domain) : Prop :=
  ∃ V P W Q, Codes M source V P ∧ Codes M target W Q ∧ Extraction M C m V P W Q

theorem layer_transition_unique_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory) {C : ExpressionData M.Domain} (hC : C.Valid M)
    {m source target target' : M.Domain} (h : LayerTransition M C m source target) (h' : LayerTransition M C m source target') : target=target' := by
  obtain ⟨V,P,W,Q,hIn,hOut,hNext⟩ := h
  obtain ⟨V',P',W',Q',hIn',hOut',hNext'⟩ := h'
  obtain ⟨hVV,hPP⟩ := codes_injective hM.1 hIn hIn'
  subst V'
  subst P'
  obtain ⟨hWW,hQQ⟩ := hNext.unique_d hM hC hNext'
  subst W'
  subst Q'
  exact codes_unique hM.1 hOut hOut'

theorem extraction_step_sound_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {m : M.Domain} {R : RowStateSpace M.Domain} (hR : R.Valid M C m)
    {Pairs Table : M.Domain} (hTable : DifferenceTable M C Pairs Table) {source target Box : M.Domain}
    (h : Project.Formula.satisfies ((((extractionStepEnv C m R Pairs Table).push source).push target).push Box) extractionStepMatrix.body) :
    LayerTransition M C m source target := by
  obtain ⟨V,_,P,_,W,_,Q,_,H,_,Heights,_,F,_,hIn,hOut,_,hRun,hHeights,hTop,hPseudo,hSelected⟩ :=
    (extractionStepMatrix_iff hM hC hR hTable source target Box).mp h
  exact ⟨V,P,W,Q,hIn,hOut,R,H,Heights,F,hRun,hHeights,hTop,hPseudo,hSelected⟩

theorem LayerStateSpace.Valid.transition_mem_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {m : M.Domain} {L : LayerStateSpace M.Domain} (hL : L.Valid M C m)
    {source target : M.Domain} (hSource : M.mem source L.states) (hNext : LayerTransition M C m source target) : M.mem target L.states := by
  obtain ⟨V,P,hIn,hRooted⟩ := (hL.states source).mp hSource
  obtain ⟨V',P',W,Q,hIn',hOut,hExtraction⟩ := hNext
  obtain ⟨hVV,hPP⟩ := codes_injective hM.1 hIn hIn'
  subst V'
  subst P'
  exact (hL.states target).mpr ⟨W,Q,hOut,hExtraction.rooted_d hM hC hRooted⟩

theorem layer_step_graph_exists_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory) {C : ExpressionData M.Domain} (hC : C.Valid M)
    {m : M.Domain} {L : LayerStateSpace M.Domain} (hL : L.Valid M C m) : ∃ Step, Graph M Step L.states L.states ∧
      ∀ source target, MemPair M Step source target ↔ M.mem source L.states ∧ LayerTransition M C m source target := by
  obtain ⟨Pairs,Table,hTable⟩ := difference_table_exists_d hM hC
  let e := extractionStepEnv C m L.rows Pairs Table
  obtain ⟨Step,hGraph,hRows⟩ := sigma_function_graph_d hM extractionStepMatrix e L.states L.states
    (fun source hSource => by
      obtain ⟨V,P,hCode,hRooted⟩ := (hL.states source).mp hSource
      exact extraction_step_exists_d hM hC hL.rows hTable hRooted hCode)
    (fun source hSource target Box hCert => hL.transition_mem_d hM hC hSource (extraction_step_sound_d hM hC hL.rows hTable hCert))
    (fun source _ target target' Box Box' hCert hCert' => layer_transition_unique_d hM hC
      (extraction_step_sound_d hM hC hL.rows hTable hCert) (extraction_step_sound_d hM hC hL.rows hTable hCert'))
  refine ⟨Step,hGraph,?_⟩
  intro source target
  constructor
  · intro hAt
    obtain ⟨hSource,_,Box,hCert⟩ := (hRows source target).mp hAt
    exact ⟨hSource,extraction_step_sound_d hM hC hL.rows hTable hCert⟩
  · rintro ⟨hSource,hNext⟩
    obtain ⟨target',_,hAt'⟩ := hGraph.total source hSource
    obtain ⟨_,_,Box,hCert⟩ := (hRows source target').mp hAt'
    have he := layer_transition_unique_d hM hC hNext (extraction_step_sound_d hM hC hL.rows hTable hCert)
    exact he.symm ▸ hAt'

structure LayerRun (M : SetTheory.Structure.{u}) (C : ExpressionData M.Domain) (m : M.Domain)
    (L : LayerStateSpace M.Domain) (V P H : M.Domain) : Prop where
  space : L.Valid M C m
  base : RootedRow M C m V P
  graph : Graph M H C.omega L.states
  initial : ∀ state, Codes M state V P → MemPair M H C.zero state
  transition : ∀ i j source target, M.SuccessorOf j i → MemPair M H i source → MemPair M H j target → LayerTransition M C m source target

theorem layer_run_exists_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory) {C : ExpressionData M.Domain} (hC : C.Valid M)
    {m : M.Domain} {L : LayerStateSpace M.Domain} (hL : L.Valid M C m) {V P : M.Domain} (hBase : RootedRow M C m V P) :
    ∃ H, LayerRun M C m L V P H := by
  obtain ⟨Step,hStep,hRows⟩ := layer_step_graph_exists_d hM hC hL
  obtain ⟨base,hBaseMem,hBaseCode⟩ := hL.encode_d hM hBase
  have hNext (x y : M.Domain) : KP1Y.Iteration.nextDenote KP1Y.Recursion.memberSchema (oneEnv Step) x y ↔ MemPair M Step x y :=
    KP1Y.Recursion.memberSchema_iff hM.1 Step x y
  obtain ⟨H,hH⟩ := KP1Y.Iteration.iterator_exists_d hM KP1Y.Recursion.memberSchema (oneEnv Step) hC.omega hBaseMem
    (fun x hx => by
      obtain ⟨y,hy,hxy⟩ := hStep.total x hx
      exact ⟨y,hy,(hNext x y).mpr hxy⟩)
    (fun x _ y _ y' _ hxy hxy' => hStep.unique x y y' ((hNext x y).mp hxy) ((hNext x y').mp hxy'))
  refine ⟨H,hL,hBase,hH.graph,?_,?_⟩
  · intro state hCode
    exact (codes_unique hM.1 hCode hBaseCode).symm ▸ hH.initial C.zero hC.zero_nat hC.zero_empty
  · intro i j source target hs hIn hOut
    exact ((hRows source target).mp ((hNext source target).mp (hH.transition i j source target hs hIn hOut))).2

theorem LayerRun.initial_at_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory) {C : ExpressionData M.Domain}
    {m : M.Domain} {L : LayerStateSpace M.Domain} {V P H : M.Domain} (h : LayerRun M C m L V P H) : RowAt M L.states H C.zero V P := by
  obtain ⟨state,hs,hCode⟩ := h.space.encode_d hM h.base
  exact ⟨state,hs,h.initial state hCode,hCode⟩

theorem LayerRun.at_exists_d {M : SetTheory.Structure.{u}} {C : ExpressionData M.Domain}
    {m : M.Domain} {L : LayerStateSpace M.Domain} {V P H k : M.Domain} (h : LayerRun M C m L V P H)
    (hk : M.mem k C.omega) : ∃ W Q, RowAt M L.states H k W Q := by
  obtain ⟨state,hs,hAt⟩ := h.graph.total k hk
  obtain ⟨W,Q,hCode,_⟩ := (h.space.states state).mp hs
  exact ⟨W,Q,state,hs,hAt,hCode⟩

theorem LayerRun.at_unique {M : SetTheory.Structure.{u}} (he : Extensional M) {C : ExpressionData M.Domain}
    {m : M.Domain} {L : LayerStateSpace M.Domain} {V P H k W Q W' Q' : M.Domain} (h : LayerRun M C m L V P H)
    (hAt : RowAt M L.states H k W Q) (hAt' : RowAt M L.states H k W' Q') : W=W' ∧ Q=Q' := by
  obtain ⟨state,_,hState,hCode⟩ := hAt
  obtain ⟨state',_,hState',hCode'⟩ := hAt'
  have hss := h.graph.unique k state state' hState hState'
  subst state'
  exact codes_injective he hCode hCode'

theorem LayerRun.at_rooted {M : SetTheory.Structure.{u}} (he : Extensional M) {C : ExpressionData M.Domain}
    {m : M.Domain} {L : LayerStateSpace M.Domain} {V P H k W Q : M.Domain} (h : LayerRun M C m L V P H)
    (hAt : RowAt M L.states H k W Q) : RootedRow M C m W Q := by
  obtain ⟨state,hs,_,hCode⟩ := hAt
  obtain ⟨W',Q',hCode',hRooted⟩ := (h.space.states state).mp hs
  obtain ⟨hWW,hQQ⟩ := codes_injective he hCode hCode'
  subst W'
  subst Q'
  exact hRooted

theorem LayerRun.at_next {M : SetTheory.Structure.{u}} (he : Extensional M) {C : ExpressionData M.Domain}
    {m : M.Domain} {L : LayerStateSpace M.Domain} {V P H k k' W Q W' Q' : M.Domain} (h : LayerRun M C m L V P H)
    (hs : M.SuccessorOf k' k) (hAt : RowAt M L.states H k W Q) (hAt' : RowAt M L.states H k' W' Q') : Extraction M C m W Q W' Q' := by
  obtain ⟨source,_,hSource,hCode⟩ := hAt
  obtain ⟨target,_,hTarget,hCode'⟩ := hAt'
  obtain ⟨X,Y,X',Y',hIn,hOut,hNext⟩ := h.transition k k' source target hs hSource hTarget
  obtain ⟨hWX,hQY⟩ := codes_injective he hCode hIn
  obtain ⟨hWX',hQY'⟩ := codes_injective he hCode' hOut
  subst X
  subst Y
  subst X'
  subst Y'
  exact hNext

private def layerRunAgreementSchema : Project.UnarySchema 2 where
  body := .forallE (.forallE (.imp (.conj (memPairFormula (.bound 4) (.bound 2) (.bound 1))
    (memPairFormula (.bound 3) (.bound 2) (.bound 0))) (Project.Formula.extensionalEq (.bound 1) (.bound 0))))
  freeClosed := by
    simp [memPairFormula,codeFormula,pairFormula,Project.Formula.forallMem,Project.Formula.existsMem,Definitional.Formula.FreeClosed]

private theorem layerRunAgreementSchema_iff {M : SetTheory.Structure.{u}} (he : Extensional M) (H J k : M.Domain) :
    Project.Formula.satisfies (((oneEnv H).push J).push k) layerRunAgreementSchema.body ↔
      ∀ x y, MemPair M H k x → MemPair M J k y → x=y := by
  simp only [layerRunAgreementSchema,Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_imp_iff,
    Project.Formula.satisfies_conj_iff,memPairFormula_iff he,Project.Formula.satisfies_extensionalEq_iff_eq he]
  exact ⟨fun h x y hx hy => h x y ⟨hx,hy⟩,fun h x y hs => h x y hs.1 hs.2⟩

theorem LayerRun.unique_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory) {C : ExpressionData M.Domain} (hC : C.Valid M)
    {m : M.Domain} {L L' : LayerStateSpace M.Domain} {V P H J : M.Domain}
    (hH : LayerRun M C m L V P H) (hJ : LayerRun M C m L' V P J) : H=J := by
  have hAll := natural_induction_d hM layerRunAgreementSchema ((oneEnv H).push J) hC.omega
    (fun z hz => (layerRunAgreementSchema_iff hM.1 H J z).mpr (by
      have hzz := hM.1.eq_of_same_members z C.zero (fun x => iff_of_false (hz x) (hC.zero_empty x))
      subst z
      obtain ⟨base,hCode⟩ := codes_total hM V P
      intro x y hx hy
      exact (hH.graph.unique C.zero x base hx (hH.initial base hCode)).trans
        (hJ.graph.unique C.zero y base hy (hJ.initial base hCode)).symm))
    (fun k hk ih k' hs => (layerRunAgreementSchema_iff hM.1 H J k').mpr (by
      obtain ⟨x,_,hX⟩ := hH.graph.total k hk
      obtain ⟨y,_,hY⟩ := hJ.graph.total k hk
      have hxy := (layerRunAgreementSchema_iff hM.1 H J k).mp ih x y hX hY
      subst y
      intro p q hp hq
      exact layer_transition_unique_d hM hC (hH.transition k k' x p hs hX hp) (hJ.transition k k' x q hs hY hq)))
  apply hH.graph.ext hM.1 hJ.graph
  intro k hk x
  have hAgree := (layerRunAgreementSchema_iff hM.1 H J k).mp (hAll k hk)
  constructor
  · intro hx
    obtain ⟨y,_,hy⟩ := hJ.graph.total k hk
    exact (hAgree x y hx hy).symm ▸ hy
  · intro hx
    obtain ⟨y,_,hy⟩ := hH.graph.total k hk
    exact hAgree y x hy hx ▸ hy

theorem LayerRun.finite_trace_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory) {C : ExpressionData M.Domain} (hC : C.Valid M)
    {m : M.Domain} {L : LayerStateSpace M.Domain} {V P H n : M.Domain} (h : LayerRun M C m L V P H) (hn : M.mem n C.omega) :
    ∃ trace, Graph M trace n L.states ∧ ∀ k state, MemPair M trace k state ↔ M.mem k n ∧ MemPair M H k state :=
  restrict_graph_d hM h.graph ((omega_isOrdinal_d hM hC.omega).transitive n hn)

theorem mountain_layers_exists_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory) {C : ExpressionData M.Domain} (hC : C.Valid M)
    {m V P : M.Domain} (hBase : RootedRow M C m V P) : ∃ L H, LayerRun M C m L V P H := by
  obtain ⟨L,hL⟩ := layer_state_space_exists_d hM hC hBase.row.forest.width
  obtain ⟨H,hH⟩ := layer_run_exists_d hM hC hL hBase
  exact ⟨L,H,hH⟩

theorem legal_layers_exists_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory) {C : ExpressionData M.Domain} (hC : C.Valid M)
    {m V : M.Domain} (hLegal : LegalAt M C.omega C.zero C.one V m) :
    ∃ F P L H, LinearForest M C.omega m F ∧ Selects true M C m F V P ∧ LayerRun M C m L V P H := by
  obtain ⟨F,P,hF,hP,hRooted⟩ := rooted_sequence_row_exists_d hM hC hLegal
  obtain ⟨L,H,hH⟩ := mountain_layers_exists_d hM hC hRooted
  exact ⟨F,P,L,H,hF,hP,hH⟩

end KP1Y.OneYFinite
