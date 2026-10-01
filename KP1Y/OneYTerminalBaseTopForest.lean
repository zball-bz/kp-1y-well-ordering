import KP1Y.OneYTerminalTowerUpper
import KP1Y.OneYTerminalCopyHighRoots

/-! Terminal层的相邻选择 SelectNext(K)。实际数值行的伪父选择等于在严格高度帧
(伪父森林按高度的最近更小选择)上的选择；严格高度帧只由高度与各行连通根决定，
而 Terminal 复制的高度与连通根都是源层的普通复制，于是目标选择是源下一层父图的普通复制。 -/
namespace KP1Y.OneYFinite.TowerCanon
open YesMetaZFC YesMetaZFC.SetTheory YesMetaZFC.SetTheory.Definitional
open KP1Y.Kuratowski KP1Y.Functions KP1Y.Naturals KP1Y.Bounded
open KP1Y.OneYFinite.CopiedMountain
universe u

/-- 收缩候选森林：若细帧祖先都是粗帧祖先，且粗帧选择的边都是细帧祖先，则两者选择相同。 -/
theorem select_of_refinements_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {m Fc Ff V S : M.Domain}
    (hFine : Forest M C.omega m Ff) (hRefine : ∀ a c, Ancestor M C m Ff a c → Ancestor M C m Fc a c)
    (hSel : Selects true M C m Fc V S) (hSelRefines : ForestRefines M C m S Ff) : Selects true M C m Ff V S := by
  have hForward (c p : M.Domain) (hcp : MemPair M S c p) : RestrictedParent true M C m Ff V c p := by
    obtain ⟨⟨_,hValues⟩,hMax⟩ := (hSel.parents c p).mp hcp
    exact ⟨⟨hSelRefines c p hcp,hValues⟩,fun q hq hQ => hMax q hq ⟨hRefine q c hQ.1,hQ.2⟩⟩
  refine ⟨hFine,hSel.values,hSel.forest,fun c p => ⟨hForward c p,fun hRP => ?_⟩⟩
  obtain ⟨p',hRP'⟩ := restricted_parent_exists_d hM true hC hSel.inherited ⟨p,⟨hRefine p c hRP.1.1,hRP.1.2⟩⟩
  have hS := (hSel.parents c p').mpr hRP'
  have he := restricted_parent_unique_d hM true hC hFine hRP (hForward c p' hS)
  exact he ▸ hS

/-- 实际行运行：提取的伪父选择等于严格高度帧上的选择。 -/
theorem actual_top_forest_select_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {m : M.Domain} {R : RowStateSpace M.Domain}
    {V P H Heights Top F T S : M.Domain} (hRun : RowRun M C m R V P H)
    (hHeights : HeightGraph M C m R V H Heights) (hTop : TopValueGraph M C m R H Heights Top)
    (hF : PseudoForest M C m R H Heights F) (hT : Selects false M C m F Heights T)
    (hPositive : ∀ i v, MemPair M V i v → M.mem C.zero v) (hS : Selects true M C m F Top S) :
    Selects true M C m T Top S :=
  select_of_refinements_d hM hC hT.forest (fun _ _ h => hT.ancestor_inherited_d hM hC h) hS
    (selected_top_values_refine_height_forest_d hM hC hRun hHeights hTop hF hS hT hPositive)

/-- 实际行运行的严格高度帧父项：恰为该列在第 h(c)-1 行的连通根。 -/
theorem actual_top_parent_iff_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {m : M.Domain} {R : RowStateSpace M.Domain}
    {V P H F T : M.Domain} {X : Data M.Domain} (hRun : RowRun M C m R V P H) (hX : X.Valid M C)
    (hFrom : FromRun M C m R V H X) (hF : PseudoForest M C m R H X.heights F) (hT : Selects false M C m F X.heights T)
    (hPositive : ∀ i v, MemPair M V i v → M.mem C.zero v) {c p hc : M.Domain} (hHC : MemPair M X.heights c hc) :
    MemPair M T c p ↔ ∃ r, M.SuccessorOf hc r ∧ Lower.RootAt M C X r c p := by
  have hw := omega_isOrdinal_d hM hC.omega
  have hRootAt (r q : M.Domain) (hr : M.mem r C.omega) :
      Lower.RootAt M C X r c q ↔ ∃ U Q, RowAt M R.states H r U Q ∧ Root M C m Q c q := by
    constructor
    · rintro ⟨Q,_,hRow,hRoot⟩
      obtain ⟨U,hAt⟩ := (hFrom.parents r Q).mp hRow
      exact ⟨U,Q,hAt,hFrom.width ▸ hRoot⟩
    · rintro ⟨U,Q,hAt,hRoot⟩
      have hRow := (hFrom.parents r Q).mpr ⟨U,hAt⟩
      exact ⟨Q,(hX.parents.bounds hM.1 hRow).2,hRow,hFrom.width.symm ▸ hRoot⟩
  have hForward (p : M.Domain) (hcp : MemPair M T c p) : ∃ r, M.SuccessorOf hc r ∧ Lower.RootAt M C X r c p := by
    obtain ⟨hp,hpNat,hHP⟩ := hFrom.heights.graph.total p (hT.forest.bounds hM.1 hcp).2
    obtain ⟨U,Q,hAt⟩ := hRun.at_exists_d hpNat
    obtain ⟨hSucc,hRoot⟩ := top_forest_parent_root_d hM hC hRun hFrom.heights hF hT hPositive hcp hHC hHP hAt
    exact ⟨hp,hSucc,(hRootAt hp p hpNat).mpr ⟨U,Q,hAt,hRoot⟩⟩
  refine ⟨hForward p,?_⟩
  rintro ⟨r,hSucc,hRA⟩
  have hhc := (hFrom.heights.graph.bounds hM.1 hHC).2
  have hPos : M.mem C.zero hc := (hC.zero_mem_iff hM hhc).mpr (fun he => hC.zero_empty r (he ▸ hSucc.predecessor_mem))
  obtain ⟨p',hcp'⟩ := top_forest_parent_exists_d hM hC hRun hFrom.heights hF hT hPositive hHC hPos
  obtain ⟨r',hSucc',hRA'⟩ := hForward p' hcp'
  have hrr := Structure.SuccessorOf.predecessor_eq hM.1 ((hw.mem hhc).mem hSucc'.predecessor_mem) hSucc' hSucc
  subst r'
  have he := hRA'.unique_d hM hC hX hRA
  exact he ▸ hcp'

variable {M : SetTheory.Structure.{u}} {C : ExpressionData M.Domain} {T : MatrixArithmetic M.Domain}
  {A : CopyCoordinates.Context M.Domain} {m : M.Domain} {L : LayerStateSpace M.Domain}
  {V P H K level B strict N n Forests CodeSpace G Nr Top Hr : M.Domain}

/-- Terminal层(k=K)：伪父森林在Hr(K+1)上恰选出塔第K+1层(普通复制)底父图。 -/
theorem Setting.terminal_select_d (hM : M.Models KP1Y.theory) (hC : C.Valid M) (hT : T.Valid M C)
    (h : Setting M C T A m L V P H K level B strict N n Forests CodeSpace G Nr Top Hr) :
    SelectNext M C n Forests G Hr B K := by
  intro k' code heights parents code' heights' parents' Un P' Pseudo hs hk' hAt hCode hAt' hCode' hUn hP' hPseudo
  have hw := omega_isOrdinal_d hM hC.omega
  have hKB := h.active_lt_d hM hC
  have hK := (h.indices_d hM hC).1
  obtain ⟨code0,heights0,parents0,sH,sP,W,Q,J,hAt0,hCode0,hY,hLayer,hRun,hX,hFrom,hBranch⟩ := h.layer_read_d hM hKB
  have hcc := h.tower.graph.unique K code0 code hAt0 hAt
  subst code0
  obtain ⟨hhh,hpp⟩ := codes_injective hM.1 hCode0 hCode
  subst heights0
  subst parents0
  have hCopy := hBranch.terminal_d hM
  have hActive := Terminal.active_from_bad_d hM hC h.layers h.bad hLayer hRun hX hFrom
  obtain ⟨W',Q',hLayer',hNextSource⟩ := h.source_next_d hM hC hK hs hLayer
  have hTopRun := h.source_top_d hM hC hLayer hRun hFrom hs hLayer'
  have hNewTop := h.terminal_new_top_d hM hC hT hs hUn hLayer hRun hFrom hTopRun
  have hKk' : M.mem K k' := (hs K).mpr (Or.inr fun _ => Iff.rfl)
  have hValues := h.ordinary_values_d hM hC hT k' (Or.inr hk') hKk' Un W' Q' hUn hLayer'
  have hPositive := (h.layers.at_rooted hM.1 hLayer).positive
  -- 目标：重建行的实际运行
  have hKN : M.mem K Nr := (h.run.length K).mpr (Or.inl hKB)
  obtain ⟨U,_,hU⟩ := h.run.graph.total K hKN
  obtain ⟨code'',_,hAt'',heights'',parents'',hCode'',hRebuild⟩ := h.run.transition K hKB k' hs Un U hUn hU
  have hcc' := h.tower.graph.unique K code'' code hAt'' hAt
  subst code''
  obtain ⟨hhh',hpp'⟩ := codes_injective hM.1 hCode'' hCode
  subst heights''
  subst parents''
  obtain ⟨R',PY,RunY,hRunY,hFromY,hTopY,hPositiveY⟩ := ExpansionCanonical.terminal_rebuild_rows_d hM hC hT hRun
    (h.layers.at_rooted hM.1 hLayer) hX hFrom hTopRun h.coordinates h.last (h.bad.in_run_d hM hC h.layers hLayer hRun)
    h.index h.width hY hCopy hNewTop hRebuild
  have hPseudoY := (ReconstructionExtraction.pseudo_forest_iff_d hM hC hRunY hY hFromY).mp hPseudo
  obtain ⟨SY,hSY⟩ := select_forest_exists_d hM true hC hPseudoY.forest hTopY.graph
  obtain ⟨TY,hTY⟩ := top_forest_exists_d hM hC hFromY.heights hPseudoY
  have hSYT := actual_top_forest_select_d hM hC hRunY hFromY.heights hTopY hPseudoY hTY hPositiveY hSY
  -- 源：第K层提取
  obtain ⟨FX,QX,hFX,hSelX,hExtractionX⟩ := ReconstructionExtraction.extraction_graph_exists_d hM hC hRun hX hFrom hTopRun
  have hQX := (hExtractionX.unique_d hM hC hNextSource).2
  subst QX
  have hPseudoX := (ReconstructionExtraction.pseudo_forest_iff_d hM hC hRun hX hFrom).mp hFX
  obtain ⟨TX,hTX⟩ := top_forest_exists_d hM hC hFrom.heights hPseudoX
  have hSXT := actual_top_forest_select_d hM hC hRun hFrom.heights hTopRun hPseudoX hTX hPositive hSelX
  -- 严格高度帧的普通复制
  have hFrame : Ordinary.ForestCopies M C T A n TX TY := by
    intro s b c hs' hc hMap a
    obtain ⟨hcHeight,_,hHC⟩ := hY.heights.total c hc
    have hHS := (Terminal.height_parent_copy_iff_d hM hC hT h.coordinates hs' hMap).mp ((hCopy.heights c hcHeight).mp hHC).2
    rw [actual_top_parent_iff_d hM hC hRunY hY hFromY hPseudoY hTY hPositiveY hHC]
    constructor
    · rintro ⟨r,hSucc,hRA⟩
      obtain ⟨q,hRAX,hMapQ⟩ := (Terminal.Copies.root_parent_copy_iff_d hM hC hT h.coordinates hX hY hRun hFrom hActive
        hCopy hs' hc hMap).mp hRA
      exact ⟨q,(actual_top_parent_iff_d hM hC hRun hX hFrom hPseudoX hTX hPositive hHS).mpr ⟨r,hSucc,hRAX⟩,hMapQ⟩
    · rintro ⟨q,hTq,hMapQ⟩
      obtain ⟨r,hSucc,hRAX⟩ := (actual_top_parent_iff_d hM hC hRun hX hFrom hPseudoX hTX hPositive hHS).mp hTq
      exact ⟨r,hSucc,(Terminal.Copies.root_parent_copy_iff_d hM hC hT h.coordinates hX hY hRun hFrom hActive
        hCopy hs' hc hMap).mpr ⟨q,hRAX,hMapQ⟩⟩
  have hSelected := hFrame.selected_d hM true hC hT h.coordinates hValues hSXT hSYT
  -- 塔第K+1层是普通复制，其底父图也是源K+1层父图的普通复制
  obtain ⟨code1,heights1,parents1,sH1,sP1,W1,Q1,J1,hAt1,hCode1,hY1,hLayer1,hRun1,hX1,hFrom1,hBranch1⟩ := h.layer_read_d hM hk'
  have hc1 := h.tower.graph.unique k' code1 code' hAt1 hAt'
  subst code1
  obtain ⟨hhh1,hpp1⟩ := codes_injective hM.1 hCode1 hCode'
  subst heights1
  subst parents1
  obtain ⟨hWW,hQQ⟩ := h.layers.at_unique hM.1 hLayer1 hLayer'
  subst W1
  subst Q1
  have hCopy1 := hBranch1.ordinary_d hM hC hK hKk'
  have hQ'0 : MemPair M sP1 C.zero Q' := (hFrom1.parents C.zero Q').mpr ⟨W',hRun1.initial_row_at_d hM⟩
  have hTarget := ordinary_forest_copies_d hM hC hT h.coordinates hX1 hY1 hCopy1 hQ'0 hP'
  have hEq := forest_copies_unique_d hM hC hT h.coordinates hSY.forest (hY1.forest C.zero P' hP') hSelected hTarget
  subst SY
  exact hSY

end KP1Y.OneYFinite.TowerCanon
