import KP1Y.OneYTowerCanonLowerSchema

/-! Lower 输入的对象反向归纳：顶层 K-1 的输入由 Terminal 底行出口 H1–H4 给出，
其余各层由上一 lower 层的 `LowerLayerStep` 字段(bottom/nonroot/down)与通用前缀保持推出。
归纳对层号间隔作对象自然数归纳（`backward_induction_d` + 字面模式 `inputsSchema`）。 -/
namespace KP1Y.OneYFinite.TowerCanon
open YesMetaZFC YesMetaZFC.SetTheory YesMetaZFC.SetTheory.Definitional
open KP1Y.Kuratowski KP1Y.Functions KP1Y.Naturals KP1Y.Bounded
open KP1Y.OneYFinite.CopiedMountain
universe u

variable {M : SetTheory.Structure.{u}} {C : ExpressionData M.Domain} {T : MatrixArithmetic M.Domain}
  {A : CopyCoordinates.Context M.Domain} {m : M.Domain} {L : LayerStateSpace M.Domain}
  {V P H K level B strict N n Forests CodeSpace G Nr Top Hr : M.Domain}

/-- lower 层 k 的全部实际读数（源码、源行、下一源层、Lower 上下文与目标复制）。 -/
theorem Setting.lower_read_d (hM : M.Models KP1Y.theory) (hC : C.Valid M)
    (h : Setting M C T A m L V P H K level B strict N n Forests CodeSpace G Nr Top Hr)
    {Sources Gs : M.Domain} (hGs : CopyTower.SourceGraph M C m L H B Sources Gs) {k k' : M.Domain}
    (hk : M.mem k K) (hs : M.SuccessorOf k' k) :
    ∃ code heights parents sCode sH sP W Q J W' Q', ∃ D : Lower.Context M.Domain,
      MemPair M G k code ∧ Codes M code heights parents ∧ MemPair M Gs k sCode ∧ Codes M sCode sH sP ∧
      D.mountain=⟨m,sH,L.rows.forests,sP⟩ ∧ RowAt M L.states H k' W' Q' ∧
      LowerLayerData M C T A m L H K k n W Q J W' Q' D ⟨n,heights,Forests,parents⟩ := by
  have hw := omega_isOrdinal_d hM hC.omega
  have hKB := h.active_lt_d hM hC
  have hK := (h.indices_d hM hC).1
  have hkB : M.mem k B := (hw.mem h.tower.bound).transitive K hKB k hk
  have hkω := hw.transitive B h.tower.bound k hkB
  obtain ⟨code,heights,parents,_,hAt,hCode,hY,source,sH,sP,hSource,hSC,hBranch⟩ := h.tower.mountain_at_d hkB
  obtain ⟨W,Q,J,hLayer,hRun,hX,hFrom⟩ := hSource.read hM.1 hSC
  obtain ⟨D,hDA,hDX,hD,hCopy⟩ := hBranch.lower_d hM hC hK hk
  obtain ⟨W',Q',hLayer',hNext⟩ := h.source_next_d hM hC hkω hs hLayer
  exact ⟨code,heights,parents,source,sH,sP,W,Q,J,W',Q',D,hAt,hCode,(hGs.rows k source).mpr ⟨hkB,hSource⟩,hSC,hDX,hLayer',
    ⟨hk,hLayer,hRun,hDX ▸ hFrom,hNext,hDA,hD,hY,hCopy⟩⟩

private theorem successor_le_K_d (hM : M.Models KP1Y.theory) (hC : C.Valid M) {r s q : M.Domain} (hr : M.mem r C.omega)
    (hq : M.mem q C.omega) (hSucc : M.SuccessorOf s r) (hrq : M.mem r q) : s=q ∨ M.mem s q := by
  have hw := omega_isOrdinal_d hM hC.omega
  apply ordinal_subset_cases_d hM (hw.mem (natural_successor_mem_d hM hC hr hSucc)) (hw.mem hq)
  intro a ha
  rcases (hSucc a).mp ha with har | he
  · exact (hw.mem hq).transitive r hrq a har
  · exact (hM.1.eq_of_same_members a r he).symm ▸ hrq

/-- Hr 在 k'≤B 处有值。 -/
theorem Setting.hr_total_d (hM : M.Models KP1Y.theory) (hC : C.Valid M)
    (h : Setting M C T A m L V P H K level B strict N n Forests CodeSpace G Nr Top Hr) {k k' : M.Domain}
    (hk : M.mem k B) (hs : M.SuccessorOf k' k) : ∃ U, MemPair M Hr k' U := by
  have hw := omega_isOrdinal_d hM hC.omega
  have hkω := hw.transitive B h.tower.bound k hk
  have hk'N : M.mem k' Nr := by
    rcases successor_le_K_d hM hC hkω h.tower.bound hs hk with he | hlt
    · exact (h.run.length k').mpr (Or.inr (by rw [he]; exact fun _ => Iff.rfl))
    · exact (h.run.length k').mpr (Or.inl hlt)
  obtain ⟨U,_,hU⟩ := h.run.graph.total k' hk'N
  exact ⟨U,hU⟩

/-- 顶层 K0（K=K0+1）的输入：来自 Terminal 底行出口 H1–H4。 -/
theorem Setting.top_inputs_d (hM : M.Models KP1Y.theory) (hC : C.Valid M) (hT : T.Valid M C)
    (h : Setting M C T A m L V P H K level B strict N n Forests CodeSpace G Nr Top Hr) (hExits : TerminalExits M)
    {Sources Gs : M.Domain} (hGs : CopyTower.SourceGraph M C m L H B Sources Gs) {K0 : M.Domain} (hK : M.SuccessorOf K K0) :
    InputsAt M C T A m n L.rows.forests Gs H Hr G K0 := by
  intro k1 sCode sH sP state1 V1 Q1 newTop code1 h1 p1 P1 hs hGsAt hSCode hState hCodeState hNewTop hG1 hCode1 hP1
  have hk1 := Structure.SuccessorOf.eq hM.1 hs hK
  subst k1
  have hw := omega_isOrdinal_d hM hC.omega
  have hKB := h.active_lt_d hM hC
  have hKω := (h.indices_d hM hC).1
  obtain ⟨_,_,_,sCode0,sH0,sP0,W0,Q0,J0,W',Q',D,_,_,hGs0,hSC0,hDX,hLayer',hData⟩ :=
    h.lower_read_d hM hC hGs hK.predecessor_mem hK
  have hsc := hGs.graph.unique K0 sCode sCode0 hGsAt hGs0
  subst sCode0
  obtain ⟨hsh,hsp⟩ := codes_injective hM.1 hSC0 hSCode
  subst sH0
  subst sP0
  have hLayerK : RowAt M L.states H K V1 Q1 := ⟨state1,(h.layers.graph.bounds hM.1 hState).2,hState,hCodeState⟩
  obtain ⟨hWV,hQQ⟩ := h.layers.at_unique hM.1 hLayer' hLayerK
  subst W'
  subst Q'
  obtain ⟨codeK,heightsK,parentsK,sHK,sPK,WK,QK,JK,hAtK,hCodeK,hYK,hLayerK',hRunK,hXK,hFromK,hBranchK⟩ := h.layer_read_d hM hKB
  have hcc := h.tower.graph.unique K codeK code1 hAtK hG1
  subst codeK
  obtain ⟨hhh,hpp⟩ := codes_injective hM.1 hCodeK hCode1
  subst heightsK
  subst parentsK
  obtain ⟨hWW,hQQ'⟩ := h.layers.at_unique hM.1 hLayerK' hLayerK
  subst WK
  subst QK
  have hCopyK := hBranchK.terminal_d hM
  obtain ⟨K',hK',_⟩ := hC.omega.1.2 K hKω
  obtain ⟨W'',Q'',hLayer'',_⟩ := h.source_next_d hM hC hKω hK' hLayerK
  have hTopK := h.source_top_d hM hC hLayerK hRunK hFromK hK' hLayer''
  obtain ⟨Un,hUn⟩ := h.hr_total_d hM hC hKB hK'
  have hCopiedTop := h.terminal_new_top_d hM hC hT hK' hUn hLayerK hRunK hFromK hTopK
  obtain ⟨code',_,hAt',heights',parents',hCode',hRebuild⟩ := h.run.transition K hKB K' hK' Un newTop hUn hNewTop
  have hcc' := h.tower.graph.unique K code' code1 hAt' hG1
  subst code'
  obtain ⟨hhh',hpp'⟩ := codes_injective hM.1 hCode' hCode1
  subst heights'
  subst parents'
  have hRootedK := h.layers.at_rooted hM.1 hLayerK
  have hCtx : TerminalBaseContext M C T m V1 Q1 JK level N n W'' Un newTop L.rows
      ⟨m,sHK,L.rows.forests,sPK⟩ ⟨n,h1,Forests,p1⟩ A :=
    ⟨hC,hT,hRunK,hRootedK,hXK,hFromK,hTopK,h.coordinates,h.last,h.bad.in_run_d hM hC h.layers hLayerK hRunK,
      h.index,h.width,hYK,hCopyK,hCopiedTop,hRebuild⟩
  have hLastX : M.mem A.last (⟨m,sHK,L.rows.forests,sPK⟩ : Data M.Domain).width := (h.indices_d hM hC).2.2.1
  have hPrefix := terminal_rebuild_prefix_d hM hC hT h.coordinates hRunK hRootedK.positive hXK hYK hFromK hTopK hCopyK
    hCopiedTop hRebuild hLastX (h.last_subset_d hM hC hT)
  -- 源 K0 层的伪父森林在 V1 上选出 Q1
  have hX0 : D.mountain.Valid M C := hData.context.mountain
  have hTop0 := h.source_top_d hM hC hData.layer hData.run (hDX ▸ hData.from_run) hK hLayerK
  apply inputs_body_of_d hM hC hT h.coordinates hData.coordinates hDX hX0 h.width hPrefix
    (hExits.fixed hCtx hData.coordinates)
  · intro Pseudo hPseudo
    have hPseudo' : GraphPseudoForest M C ⟨m,sH,L.rows.forests,sP⟩ Pseudo := hDX ▸ hPseudo
    obtain ⟨F,Qs,hF,hSel,hExtraction⟩ := ReconstructionExtraction.extraction_graph_exists_d hM hC hData.run
      (hDX ▸ hX0) (hDX ▸ hData.from_run) hTop0
    have hQs := (hExtraction.unique_d hM hC hData.extraction).2
    subst Qs
    have hFF := hF.unique hM.1 hPseudo'
    subst F
    exact hExits.order hCtx hData.coordinates hSel
  · intro F F' hSel hCopy
    exact hExits.select hCtx hSel hCopy hP1
  · intro s b c hs hsx hMap hc p
    exact hExits.nonroot hCtx hP1 hs hsx hMap hc

/-- 由 q=p+1 层的输入推出 p 层输入（q 是 lower 层）。 -/
theorem Setting.step_inputs_d (hM : M.Models KP1Y.theory) (hC : C.Valid M) (hT : T.Valid M C)
    (h : Setting M C T A m L V P H K level B strict N n Forests CodeSpace G Nr Top Hr)
    (hLower : ∀ k, M.mem k K → LowerLayerStep M C T A m L H K k N n)
    {Sources Gs : M.Domain} (hGs : CopyTower.SourceGraph M C m L H B Sources Gs) {p q : M.Domain}
    (hq : M.mem q K) (hpq : M.SuccessorOf q p) (ih : InputsAt M C T A m n L.rows.forests Gs H Hr G q) :
    InputsAt M C T A m n L.rows.forests Gs H Hr G p := by
  intro k1 sCode sH sP state1 V1 Q1 newTop code1 h1 p1 P1 hs hGsAt hSCode hState hCodeState hNewTop hG1 hCode1 hP1
  have hk1 := Structure.SuccessorOf.eq hM.1 hs hpq
  subst k1
  have hw := omega_isOrdinal_d hM hC.omega
  have hKB := h.active_lt_d hM hC
  have hK := (h.indices_d hM hC).1
  have hKω := (h.indices_d hM hC).1
  have hp : M.mem p K := ((hw.mem hKω).transitive q hq p hpq.predecessor_mem)
  obtain ⟨_,_,_,sCode0,sH0,sP0,Wp,Qp,Jp,W',Q',Dp,_,_,hGs0,hSC0,hDXp,hLayer',hDataP⟩ := h.lower_read_d hM hC hGs hp hpq
  have hsc := hGs.graph.unique p sCode sCode0 hGsAt hGs0
  subst sCode0
  obtain ⟨hsh,hsp⟩ := codes_injective hM.1 hSC0 hSCode
  subst sH0
  subst sP0
  have hLayerQ : RowAt M L.states H q V1 Q1 := ⟨state1,(h.layers.graph.bounds hM.1 hState).2,hState,hCodeState⟩
  obtain ⟨hWV,hQQ⟩ := h.layers.at_unique hM.1 hLayer' hLayerQ
  subst W'
  subst Q'
  have hqω := hw.transitive K hKω q hq
  obtain ⟨q',hq',_⟩ := hC.omega.1.2 q hqω
  obtain ⟨codeQ,heightsQ,parentsQ,sCodeQ,sHQ,sPQ,Wq,Qq,Jq,W'',Q'',Dq,hAtQ,hCodeQ,hGsQ,hSCQ,hDXq,hLayer'',hDataQ⟩ :=
    h.lower_read_d hM hC hGs hq hq'
  have hcc := h.tower.graph.unique q codeQ code1 hAtQ hG1
  subst codeQ
  obtain ⟨hhh,hpp⟩ := codes_injective hM.1 hCodeQ hCode1
  subst heightsQ
  subst parentsQ
  obtain ⟨hWq,hQq⟩ := h.layers.at_unique hM.1 hDataQ.layer hLayerQ
  subst Wq
  subst Qq
  have hqB : M.mem q B := (hw.mem h.tower.bound).transitive K hKB q hq
  have hq'B : M.mem q' B := by
    rcases successor_le_K_d hM hC hqω hKω hq' hq with he | hlt
    · exact he ▸ hKB
    · exact (hw.mem h.tower.bound).transitive K hKB q' hlt
  obtain ⟨Un,hUn⟩ := h.hr_total_d hM hC hqB hq'
  obtain ⟨code',heights',parents',P',hAt',hCode',_,hP'⟩ := tower_code_bottom_d hC h.tower.graph h.valid_codes hq'B
  obtain ⟨state'',hState''Mem,hState'',hCode''⟩ := hLayer''
  have hBody := ih q' sCodeQ sHQ sPQ state'' W'' Q'' Un code' heights' parents' P' hq' hGsQ hSCQ hState'' hCode'' hUn hAt' hCode' hP'
  have hInputs := hBody.lower_inputs_d hM hC hT h.coordinates hDataQ.coordinates hDXq h.width
  have hUnGraph : Graph M Un n C.omega := h.run.values q' Un hUn
  have hUnPos := h.row_positive_d hM hC hT hUn
  obtain ⟨code'',_,hAt'',heights'',parents'',hCode''',hRebuild⟩ := h.run.transition q hqB q' hq' Un newTop hUn hNewTop
  have hc3 := h.tower.graph.unique q code'' code1 hAt'' hG1
  subst code''
  obtain ⟨hh3,hp3⟩ := codes_injective hM.1 hCode''' hCode1
  subst heights''
  subst parents''
  have hStep := hLower q hq
  have hTopQ := h.source_top_d hM hC hDataQ.layer hDataQ.run (hDXq ▸ hDataQ.from_run) hq' ⟨state'',hState''Mem,hState'',hCode''⟩
  have hPrefix : RowsAgreeOn M newTop V1 A.last := by
    have hTopQ' : TopValueGraph M C m L.rows Jq Dq.mountain.heights W'' := by rw [hDXq]; exact hTopQ
    have hKept : M.MemberSubset Dq.coordinates.last (⟨n,h1,Forests,p1⟩ : Data M.Domain).width := by
      rw [hDataQ.coordinates]; exact h.last_subset_d hM hC hT
    have hRP := Lower.Copies.rebuild_prefix_d hM hC hT.add hDataQ.context hDataQ.target hDataQ.run
      (h.layers.at_rooted hM.1 hDataQ.layer).positive hDataQ.from_run hTopQ' hDataQ.copies hUnGraph
      hKept hInputs.prefixTop hRebuild
    rw [hDataQ.coordinates] at hRP
    exact hRP
  obtain ⟨hFixed,hOrder⟩ := hStep.down hpq hDataP hDataQ hUnGraph hUnPos hInputs hRebuild
  apply inputs_body_of_d hM hC hT h.coordinates hDataP.coordinates hDXp hDataP.context.mountain h.width hPrefix hFixed hOrder
  · intro F F' hSel hCopy
    exact hStep.bottom hDataQ hUnGraph hUnPos hInputs hRebuild hSel hCopy hP1
  · intro s b c hs hsx hMap hc p
    exact hStep.nonroot hDataQ hP1 hs hsx hMap hc

/-- 全部 lower 层的输入。 -/
theorem Setting.lower_inputs_d (hM : M.Models KP1Y.theory) (hC : C.Valid M) (hT : T.Valid M C)
    (h : Setting M C T A m L V P H K level B strict N n Forests CodeSpace G Nr Top Hr) (hExits : TerminalExits M)
    (hLower : ∀ k, M.mem k K → LowerLayerStep M C T A m L H K k N n)
    {Sources Gs : M.Domain} (hGs : CopyTower.SourceGraph M C m L H B Sources Gs) :
    ∀ k, M.mem k K → InputsAt M C T A m n L.rows.forests Gs H Hr G k := by
  have hw := omega_isOrdinal_d hM hC.omega
  have hKω := (h.indices_d hM hC).1
  rcases natural_cases hM hC.omega hKω with hEmpty | ⟨K0,hK0,hK⟩
  · intro k hk
    exact False.elim (hEmpty k hk)
  · let e := inputsEnv C T A m n L.rows.forests Gs H Hr G
    have hAll := backward_induction_d hM hC hT.add inputsSchema e hK0
      ((inputsSchema_iff hM.1 C T A m n L.rows.forests Gs H Hr G K0).mpr (h.top_inputs_d hM hC hT hExits hGs hK))
      (fun p hp q hpq ihq => by
        have hqK : M.mem q K := by
          rcases successor_le_K_d hM hC (hw.transitive K0 hK0 p hp) hK0 hpq hp with he | hlt
          · exact he ▸ hK.predecessor_mem
          · exact (hK q).mpr (Or.inl hlt)
        exact (inputsSchema_iff hM.1 C T A m n L.rows.forests Gs H Hr G p).mpr
          (h.step_inputs_d hM hC hT hLower hGs hqK hpq ((inputsSchema_iff hM.1 C T A m n L.rows.forests Gs H Hr G q).mp ihq)))
    intro k hk
    have hkLe : k=K0 ∨ M.mem k K0 := by
      rcases (hK k).mp hk with hlt | he
      · exact Or.inr hlt
      · exact Or.inl (hM.1.eq_of_same_members k K0 he)
    exact (inputsSchema_iff hM.1 C T A m n L.rows.forests Gs H Hr G k).mp (hAll k hkLe)

end KP1Y.OneYFinite.TowerCanon
