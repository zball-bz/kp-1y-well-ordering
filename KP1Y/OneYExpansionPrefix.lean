import KP1Y.OneYExpansionCore

/-! 原提取塔的实际重建恢复、复制塔保留列与N=0删末项；不使用规范重提取假设。 -/
namespace KP1Y.OneYFinite.Expansion
open YesMetaZFC YesMetaZFC.SetTheory YesMetaZFC.SetTheory.Definitional
open KP1Y.Kuratowski KP1Y.Functions KP1Y.Naturals KP1Y.Bounded
open KP1Y.OneYFinite
universe u

private def layerValueSchema : Project.Delta0BinarySchema 3 where
  body := Project.Formula.existsMem (.bound 3) (rowAtFormula (.bound 5) (.bound 3) (.bound 2) (.bound 1) (.bound 0))
  freeClosed := by simp [rowAtFormula,memPairFormula,codeFormula,pairFormula,Project.Formula.forallMem,Project.Formula.existsMem,Definitional.Formula.FreeClosed]
  delta0 := .existsMem _ (rowAtFormula_delta0 _ _ _ _ _)

theorem layer_values_history_exists_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {m : M.Domain} {L : LayerStateSpace M.Domain} {V P H N : M.Domain}
    (hLayers : LayerRun M C m L V P H) (hN : M.mem N C.omega) :
    ∃J, Graph M J N C.sequences ∧ ∀k W, MemPair M J k W ↔ M.mem k N ∧ ∃Q, RowAt M L.states H k W Q := by
  let e := ((oneEnv L.states).push L.rows.forests).push H
  have hφ (k W : M.Domain) : Project.Formula.satisfies ((e.push k).push W) layerValueSchema.body ↔
      ∃Q, M.mem Q L.rows.forests ∧ RowAt M L.states H k W Q := by
    simp only [layerValueSchema,Project.Formula.satisfies_existsMem_iff,rowAtFormula_iff hM.1]
    rfl
  obtain ⟨J,hSupport,hRaw⟩ := relation_comprehension_d hM layerValueSchema e N C.sequences
  have hRows (k W : M.Domain) : MemPair M J k W ↔ M.mem k N ∧ ∃Q, RowAt M L.states H k W Q := by
    rw [hRaw k W,hφ]
    constructor
    · rintro ⟨hk,_,Q,_,hAt⟩
      exact ⟨hk,Q,hAt⟩
    · rintro ⟨hk,Q,hAt⟩
      have hRooted := hLayers.at_rooted hM.1 hAt
      exact ⟨hk,(hC.sequences W).mpr ⟨m,hLayers.space.rows.width,hRooted.row.values⟩,
        Q,(hLayers.space.rows.forests Q).mpr hRooted.row.forest,hAt⟩
  refine ⟨J,⟨hSupport,?_,?_⟩,hRows⟩
  · intro k hk
    obtain ⟨W,Q,hAt⟩ := hLayers.at_exists_d ((omega_isOrdinal_d hM hC.omega).transitive N hN k hk)
    exact ⟨W,(hC.sequences W).mpr ⟨m,hLayers.space.rows.width,(hLayers.at_rooted hM.1 hAt).row.values⟩,(hRows k W).mpr ⟨hk,Q,hAt⟩⟩
  · intro k W W' hW hW'
    obtain ⟨_,Q,hAt⟩ := (hRows k W).mp hW
    obtain ⟨_,Q',hAt'⟩ := (hRows k W').mp hW'
    exact (hLayers.at_unique hM.1 hAt hAt').1

theorem source_graph_code_valid {M : SetTheory.Structure.{u}} {C : ExpressionData M.Domain} {m : M.Domain}
    {L : LayerStateSpace M.Domain} {H B Sources G k code : M.Domain} (h : CopyTower.SourceGraph M C m L H B Sources G)
    (hAt : MemPair M G k code) : CopiedMountain.CodeValid M C m L.rows.forests code := by
  obtain ⟨_,_,_,_,_,heights,parents,hCode,hX,_⟩ := ((h.rows k code).mp hAt).2
  exact ⟨heights,parents,hCode,hX⟩

theorem extraction_top_for_source_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {m V P Top Q J : M.Domain} {R : RowStateSpace M.Domain}
    (hRun : RowRun M C m R V P J) {X : CopiedMountain.Data M.Domain} (hFrom : CopiedMountain.FromRun M C m R V J X)
    (hExtraction : Extraction M C m V P Top Q) : TopValueGraph M C m R J X.heights Top := by
  obtain ⟨R',J',Heights,F,hRun',hHeights,hTop,_,_⟩ := hExtraction
  have hRR := row_state_space_unique hM.1 hRun'.space hRun.space
  subst R'
  have hJJ := hRun'.unique_d hM hC hRun
  subst J'
  have hh := hHeights.unique hM.1 hFrom.heights
  rw [hh] at hTop
  exact hTop

theorem original_code_step_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {Pairs Plus : M.Domain} (hPlus : AdditionTable M C Pairs Plus)
    {m : M.Domain} {L : LayerStateSpace M.Domain} {V P H B Sources G k j lower lp upper up : M.Domain}
    (hLayers : LayerRun M C m L V P H) (hSources : CopyTower.SourceGraph M C m L H B Sources G)
    (hk : M.mem k B) (hs : M.SuccessorOf j k) (hLower : RowAt M L.states H k lower lp) (hUpper : RowAt M L.states H j upper up) :
    TowerReconstruction.CodeStep M C Pairs Plus m L.rows.forests Sources G k upper lower := by
  obtain ⟨code,hCode,hAt⟩ := hSources.graph.total k hk
  have hSource := ((hSources.rows k code).mp hAt).2
  obtain ⟨heights,parents,hDecode⟩ := hSource.contents
  obtain ⟨W,Q,J,hLayer,hRun,hX,hFrom⟩ := hSource.read hM.1 hDecode
  obtain ⟨hWW,hQQ⟩ := hLayers.at_unique hM.1 hLayer hLower
  subst W
  subst Q
  have hTop := extraction_top_for_source_d hM hC hRun hFrom (hLayers.at_next hM.1 hs hLower hUpper)
  exact ⟨code,hCode,hAt,heights,parents,hDecode,MountainReconstruction.rebuild_original_d hM hC hPlus hRun
    (hLayers.at_rooted hM.1 hLower).positive hX hFrom hTop⟩

theorem original_tower_assembles_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {Pairs Plus : M.Domain} (hPlus : AdditionTable M C Pairs Plus)
    {m : M.Domain} {L : LayerStateSpace M.Domain} {V P H B Sources G Top Q : M.Domain}
    (hLayers : LayerRun M C m L V P H) (hB : M.mem B C.omega) (hSources : CopyTower.SourceGraph M C m L H B Sources G)
    (hTop : RowAt M L.states H B Top Q) : TowerReconstruction.Assembles M C Pairs Plus m L.rows.forests Sources G B Top V := by
  obtain ⟨N,hN,hNω⟩ := hC.omega.1.2 B hB
  obtain ⟨J,hJ,hRows⟩ := layer_values_history_exists_d hM hC hLayers hNω
  have hRun : TowerReconstruction.Run M C Pairs Plus m L.rows.forests Sources G B N Top J := by
    refine ⟨hN,hJ,?_,(hRows B Top).mpr ⟨hN.predecessor_mem,Q,hTop⟩,?_⟩
    · intro k W hAt
      obtain ⟨_,Q,hLayer⟩ := (hRows k W).mp hAt
      exact (hLayers.at_rooted hM.1 hLayer).row.values
    · intro k hk j hs upper lower hU hL
      obtain ⟨_,up,hUpper⟩ := (hRows j upper).mp hU
      obtain ⟨_,lp,hLower⟩ := (hRows k lower).mp hL
      exact original_code_step_d hM hC hPlus hLayers hSources hk hs hLower hUpper
  have hZero : M.mem C.zero N := (hC.zero_mem_iff hM hNω).mpr (fun he => hC.zero_empty B (he ▸ hN.predecessor_mem))
  exact ⟨N,J,hRun,(hRows C.zero V).mpr ⟨hZero,P,hLayers.initial_at_d hM⟩⟩

theorem horizon_layer_all_one_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {m : M.Domain} {L : LayerStateSpace M.Domain} {V P H B Top Q : M.Domain}
    (hLayers : LayerRun M C m L V P H) (hB : Horizon M C V m B) (hTop : RowAt M L.states H B Top Q) :
    TowerReconstruction.AllOne M C m Top := by
  have hBN := hB.natural_d hM hC
  obtain ⟨strict,_,hStrict,hSucc⟩ := hB
  have hRooted := hLayers.at_rooted hM.1 hTop
  have hOne (c v : M.Domain) (hAt : MemPair M Top c v) : v=C.one :=
    hLayers.all_one_from_bound_predecessor_d hM hC hStrict hSucc hBN (.inl rfl)
      ⟨Top,(hLayers.space.rows.values Top).mpr hRooted.row.values,Q,(hLayers.space.rows.forests Q).mpr hRooted.row.forest,hTop,hAt⟩
  refine ⟨hRooted.row.values,fun c v => ?_⟩
  constructor
  · exact fun hAt => ⟨(hRooted.row.values.bounds hM.1 hAt).1,hOne c v hAt⟩
  · rintro ⟨hc,rfl⟩
    obtain ⟨v,_,hAt⟩ := hRooted.row.values.total c hc
    exact hOne c v hAt ▸ hAt

theorem width_keeps_prefix_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {A : CopyCoordinates.Context M.Domain} {N n : M.Domain} (h : CopyCoordinates.Width M C T A N n) : M.MemberSubset A.last n := by
  obtain ⟨hl,_,offset,ho,_,hAdd⟩ := h
  exact KP1Y.Arithmetic.sum_base_subset_d hM ((omega_isOrdinal_d hM hC.omega).mem hl) ((hT.add.add_iff_sum hM hl ho).mp hAdd)

theorem branch_original_rows_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {A : CopyCoordinates.Context M.Domain} (hA : A.Valid M C) {X Y : CopiedMountain.Data M.Domain} (hX : X.Valid M C)
    {K level k n c : M.Domain} (h : CopyTower.Branch M C T A X K level k n Y) (hc : M.mem c n) (hOld : M.mem c A.last) :
    (∀height, MemPair M Y.heights c height ↔ MemPair M X.heights c height) ∧
      ∀r p, CopiedMountain.ParentAt M Y r c p ↔ CopiedMountain.ParentAt M X r c p := by
  rcases h with ⟨_,D,hDA,hDX,hD,hCopies⟩ | ⟨_,hCopies⟩ | ⟨_,hCopies⟩
  · have hBefore : c=D.coordinates.last ∨ M.mem c D.coordinates.last := .inr (by simpa only [hDA] using hOld)
    exact ⟨fun height => by simpa only [hDX] using hCopies.original_heights_d hM hC hD (height := height) hc hBefore,
      fun r p => by simpa only [hDX] using hCopies.original_parents_d hM hC hD (r := r) (p := p) hc hBefore⟩
  · exact ⟨fun _ => hCopies.original_heights_d hM hC hT hA hc hOld,fun _ _ => hCopies.original_parents_d hM hC hA hc hOld⟩
  · exact ⟨fun _ => hCopies.original_heights_d hM hC hT hA hc hOld,fun _ _ => hCopies.original_parents_d hM hC hT hA hX hc hOld⟩

theorem copy_source_family_prefix_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {A : CopyCoordinates.Context M.Domain} (hA : A.Valid M C) {m : M.Domain} {L : LayerStateSpace M.Domain}
    {V P H K level B n Forests Codes G Sources SourceG : M.Domain} (hLayers : LayerRun M C m L V P H)
    (hTower : CopyTower.Tower M C T A m L H K level B n Forests Codes G)
    (hSources : CopyTower.SourceGraph M C m L H B Sources SourceG)
    (hLeft : M.MemberSubset A.last n) (hRight : M.MemberSubset A.last m) :
    TowerReconstruction.FamilyPrefix M C n Forests G m L.rows.forests SourceG B A.last := by
  refine ⟨hA.last,hLeft,hRight,?_⟩
  intro k _ code sourceCode heights parents sourceHeights sourceParents hAt hSourceAt hDecode hSourceDecode
  have hExpanded := ((hTower.rows k code).mp hAt).2
  obtain ⟨_,source,sH,sP,hSource,hSC,hBranch⟩ := hExpanded.read hM.1 hDecode
  have hOriginal := ((hSources.rows k sourceCode).mp hSourceAt).2
  have hSourceEq := hSource.unique_d hM hC hLayers hOriginal
  have hSC' : KP1Y.Kuratowski.Codes M sourceCode sH sP := hSourceEq ▸ hSC
  obtain ⟨hHH,hPP⟩ := codes_injective hM.1 hSC' hSourceDecode
  subst sH
  subst sP
  obtain ⟨_,_,_,_,_,hX,_⟩ := hOriginal.read hM.1 hSourceDecode
  refine ⟨fun c hc height => (branch_original_rows_d hM hC hT hA hX hBranch (hLeft c hc) hc).1 height,
    fun c hc r _ p => (branch_original_rows_d hM hC hT hA hX hBranch (hLeft c hc) hc).2 r p⟩

theorem Successful.prefix_old_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {s m last N t : M.Domain} {W : SuccessData M.Domain} (h : Successful M C T s m last N t W)
    (hLast : M.SuccessorOf m last) : RowsAgreeOn M t s last := by
  have hBN := h.horizon.natural_d hM hC
  obtain ⟨Sources,G,hSources⟩ := CopyTower.source_graph_exists_d hM hC h.run hBN
  obtain ⟨Top,Q,hLayerTop⟩ := h.run.at_exists_d hBN
  have hTop := horizon_layer_all_one_d hM hC h.run h.horizon hLayerTop
  have hOriginal := original_tower_assembles_d hM hC hT.add h.run hBN hSources hLayerTop
  have hLeft := width_keeps_prefix_d hM hC hT h.width
  have hRight : M.MemberSubset W.coordinates.last m := fun c hc => (hLast c).mpr (.inl (h.last ▸ hc))
  have hPrefix := copy_source_family_prefix_d hM hC hT h.coordinates h.run h.tower hSources hLeft hRight
  have hTops : RowsAgreeOn M W.top Top W.coordinates.last := by
    intro c hc v
    rw [h.top.2 c v,hTop.2 c v]
    exact ⟨fun h => ⟨hRight c hc,h.2⟩,fun h => ⟨hLeft c hc,h.2⟩⟩
  have hAgree := h.reconstruction.prefix_d hM hC hT.add h.tower.width h.run.space.rows.width hBN h.tower.graph hSources.graph
    (fun _ _ => h.tower.code_valid) (fun _ _ => source_graph_code_valid hSources) hPrefix hTops hOriginal
  exact h.last ▸ hAgree

theorem Successful.zero_prefix_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {s m last t : M.Domain} {W : SuccessData M.Domain} (h : Successful M C T s m last C.zero t W)
    (hLast : M.SuccessorOf m last) : Prefix M t s last C.omega := by
  have hn : W.width=last := (CopyCoordinates.width_zero_d hM hC hT h.coordinates h.width).trans h.last
  have hGraph : Graph M t last C.omega := hn ▸ h.reconstruction.graph
  exact ⟨hGraph,fun c hc v _ => h.prefix_old_d hM hC hT hLast c hc v⟩

theorem Expands.zero_drop_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {s m t : M.Domain} (hLegal : LegalAt M C.omega C.zero C.one s m) (h : Expands M C T s C.zero t) : DropLast M C s m t := by
  obtain ⟨_,m',_,hLegal',hCases⟩ := h
  have hmm := legal_length_unique hM.1 hLegal' hLegal
  subst m'
  rcases hCases with ⟨hm,ht⟩ | ⟨last,hl,hSucc,hDrop | ⟨W,hSuccess⟩⟩
  · subst m
    subst t
    exact ⟨C.zero,⟨hC.zero_nat,.inl ⟨rfl,rfl⟩⟩,⟨hLegal.1.2,fun _ _ _ _ => Iff.rfl⟩⟩
  · exact ⟨last,⟨hl,.inr hSucc⟩,hDrop.2⟩
  · exact ⟨last,⟨hl,.inr hSucc⟩,hSuccess.zero_prefix_d hM hC hT hSucc⟩

theorem expands_zero_iff_drop_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {s m t : M.Domain} (hLegal : LegalAt M C.omega C.zero C.one s m) : Expands M C T s C.zero t ↔ DropLast M C s m t := by
  constructor
  · exact Expands.zero_drop_d hM hC hT hLegal
  · intro hDrop
    obtain ⟨u,hExpand⟩ := expands_exists_d hM hC hT ((hC.expressions s).mpr ⟨m,hLegal.1.1,hLegal⟩) hC.zero_nat
    obtain ⟨canonical,_,_,hUnique⟩ := legal_drop_last_d hM hC hLegal
    have hut := (hUnique u (hExpand.zero_drop_d hM hC hT hLegal)).trans (hUnique t hDrop).symm
    exact hut ▸ hExpand

end KP1Y.OneYFinite.Expansion
