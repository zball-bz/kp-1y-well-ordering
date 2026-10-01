import KP1Y.OneYTowerCanonLowerInduction

/-! lower 层(k<K)的 LayerCanon/SelectNext，初始线性帧的 BaseSelect，以及全塔逐层汇总：
对塔内每一层 k<B，三分支(k<K, k=K, K<k)全部给出实际规范运行与相邻选择。 -/
namespace KP1Y.OneYFinite.TowerCanon
open YesMetaZFC YesMetaZFC.SetTheory YesMetaZFC.SetTheory.Definitional
open KP1Y.Kuratowski KP1Y.Functions KP1Y.Naturals KP1Y.Bounded
open KP1Y.OneYFinite.CopiedMountain
universe u

variable {M : SetTheory.Structure.{u}} {C : ExpressionData M.Domain} {T : MatrixArithmetic M.Domain}
  {A : CopyCoordinates.Context M.Domain} {m : M.Domain} {L : LayerStateSpace M.Domain}
  {V P H K level B strict N n Forests CodeSpace G Nr Top Hr : M.Domain}

private theorem successor_le_B_d (hM : M.Models KP1Y.theory) (hC : C.Valid M) {r s q : M.Domain} (hr : M.mem r C.omega)
    (hq : M.mem q C.omega) (hSucc : M.SuccessorOf s r) (hrq : M.mem r q) : s=q ∨ M.mem s q := by
  have hw := omega_isOrdinal_d hM hC.omega
  apply ordinal_subset_cases_d hM (hw.mem (natural_successor_mem_d hM hC hr hSucc)) (hw.mem hq)
  intro a ha
  rcases (hSucc a).mp ha with har | he
  · exact (hw.mem hq).transitive r hrq a har
  · exact (hM.1.eq_of_same_members a r he).symm ▸ hrq

/-- lower 层 k 的实际输入（读出 k+1 层的全部对象后）。 -/
private theorem Setting.lower_layer_inputs_d (hM : M.Models KP1Y.theory) (hC : C.Valid M) (hT : T.Valid M C)
    (h : Setting M C T A m L V P H K level B strict N n Forests CodeSpace G Nr Top Hr)
    {Sources Gs : M.Domain} (hGs : CopyTower.SourceGraph M C m L H B Sources Gs)
    {k k' : M.Domain} (hk : M.mem k K) (hs : M.SuccessorOf k' k) (hInputs : InputsAt M C T A m n L.rows.forests Gs H Hr G k)
    {Un code' heights' parents' P' : M.Domain} (hUn : MemPair M Hr k' Un) (hAt' : MemPair M G k' code')
    (hCode' : Codes M code' heights' parents') (hP' : MemPair M parents' C.zero P') :
    ∃ code heights parents W Q J W' Q', ∃ D : Lower.Context M.Domain, MemPair M G k code ∧ Codes M code heights parents ∧
      LowerLayerData M C T A m L H K k n W Q J W' Q' D ⟨n,heights,Forests,parents⟩ ∧
      LowerInputs M C T D m N n W' Q' Un P' := by
  obtain ⟨code,heights,parents,sCode,sH,sP,W,Q,J,W',Q',D,hAt,hCode,hGsAt,hSC,hDX,hLayer',hData⟩ := h.lower_read_d hM hC hGs hk hs
  obtain ⟨state',_,hState',hCodeState'⟩ := hLayer'
  have hBody := hInputs k' sCode sH sP state' W' Q' Un code' heights' parents' P' hs hGsAt hSC hState' hCodeState' hUn hAt' hCode' hP'
  exact ⟨code,heights,parents,W,Q,J,W',Q',D,hAt,hCode,hData,hBody.lower_inputs_d hM hC hT h.coordinates hData.coordinates hDX h.width⟩

/-- lower 层(k<K)的规范运行。 -/
theorem Setting.lower_canon_d (hM : M.Models KP1Y.theory) (hC : C.Valid M) (hT : T.Valid M C)
    (h : Setting M C T A m L V P H K level B strict N n Forests CodeSpace G Nr Top Hr)
    (hLower : ∀ k, M.mem k K → LowerLayerStep M C T A m L H K k N n)
    {Sources Gs : M.Domain} (hGs : CopyTower.SourceGraph M C m L H B Sources Gs)
    {k : M.Domain} (hk : M.mem k K) (hInputs : InputsAt M C T A m n L.rows.forests Gs H Hr G k) :
    LayerCanon M C n Forests G Hr k := by
  intro code heights parents U k' Un hAt hCode hU hs hUn
  have hw := omega_isOrdinal_d hM hC.omega
  have hKB := h.active_lt_d hM hC
  have hKω := (h.indices_d hM hC).1
  have hkB : M.mem k B := (hw.mem h.tower.bound).transitive K hKB k hk
  have hk'B : M.mem k' B := by
    rcases successor_le_B_d hM hC (hw.transitive K hKω k hk) hKω hs hk with he | hlt
    · exact he ▸ hKB
    · exact (hw.mem h.tower.bound).transitive K hKB k' hlt
  obtain ⟨code',heights',parents',P',hAt',hCode',_,hP'⟩ := tower_code_bottom_d hC h.tower.graph h.valid_codes hk'B
  obtain ⟨code0,heights0,parents0,W,Q,J,W',Q',D,hAt0,hCode0,hData,hInputsK⟩ :=
    h.lower_layer_inputs_d hM hC hT hGs hk hs hInputs hUn hAt' hCode' hP'
  have hcc := h.tower.graph.unique k code0 code hAt0 hAt
  subst code0
  obtain ⟨hhh,hpp⟩ := codes_injective hM.1 hCode0 hCode
  subst heights0
  subst parents0
  obtain ⟨code'',_,hAt'',heights'',parents'',hCode'',hRebuild⟩ := h.run.transition k hkB k' hs Un U hUn hU
  have hc2 := h.tower.graph.unique k code'' code hAt'' hAt
  subst code''
  obtain ⟨hh2,hp2⟩ := codes_injective hM.1 hCode'' hCode
  subst heights''
  subst parents''
  exact (hLower k hk).rows hData (h.run.values k' Un hUn) (h.row_positive_d hM hC hT hUn) hInputsK hRebuild

/-- lower 层(k<K)的相邻选择。 -/
theorem Setting.lower_select_d (hM : M.Models KP1Y.theory) (hC : C.Valid M) (hT : T.Valid M C)
    (h : Setting M C T A m L V P H K level B strict N n Forests CodeSpace G Nr Top Hr)
    (hLower : ∀ k, M.mem k K → LowerLayerStep M C T A m L H K k N n)
    {Sources Gs : M.Domain} (hGs : CopyTower.SourceGraph M C m L H B Sources Gs)
    {k : M.Domain} (hk : M.mem k K) (hInputs : InputsAt M C T A m n L.rows.forests Gs H Hr G k) :
    SelectNext M C n Forests G Hr B k := by
  intro k' code heights parents code' heights' parents' Un P' Pseudo hs _ hAt hCode hAt' hCode' hUn hP' hPseudo
  obtain ⟨code0,heights0,parents0,W,Q,J,W',Q',D,hAt0,hCode0,hData,hInputsK⟩ :=
    h.lower_layer_inputs_d hM hC hT hGs hk hs hInputs hUn hAt' hCode' hP'
  have hcc := h.tower.graph.unique k code0 code hAt0 hAt
  subst code0
  obtain ⟨hhh,hpp⟩ := codes_injective hM.1 hCode0 hCode
  subst heights0
  subst parents0
  obtain ⟨F,F',hSel,hCopy,hSame⟩ := (hLower k hk).extract hData (h.run.values k' Un hUn) (h.row_positive_d hM hC hT hUn)
    hInputsK hPseudo
  exact (hSame P').mpr (hInputsK.select.1 F F' hSel (hData.coordinates.symm ▸ hCopy))

/-- Terminal 层(k=K)的完整前提包（读出塔码与源层）。 -/
theorem Setting.terminal_context_d (hM : M.Models KP1Y.theory) (hC : C.Valid M) (hT : T.Valid M C)
    (h : Setting M C T A m L V P H K level B strict N n Forests CodeSpace G Nr Top Hr)
    {code heights parents U : M.Domain} (hAt : MemPair M G K code) (hCode : Codes M code heights parents)
    (hU : MemPair M Hr K U) :
    ∃ W Q J sH sP OldTop Un, RowAt M L.states H K W Q ∧
      TerminalBaseContext M C T m W Q J level N n OldTop Un U L.rows ⟨m,sH,L.rows.forests,sP⟩ ⟨n,heights,Forests,parents⟩ A := by
  have hKB := h.active_lt_d hM hC
  have hKω := (h.indices_d hM hC).1
  obtain ⟨code0,heights0,parents0,sH,sP,W,Q,J,hAt0,hCode0,hY,hLayer,hRun,hX,hFrom,hBranch⟩ := h.layer_read_d hM hKB
  have hcc := h.tower.graph.unique K code0 code hAt0 hAt
  subst code0
  obtain ⟨hhh,hpp⟩ := codes_injective hM.1 hCode0 hCode
  subst heights0
  subst parents0
  obtain ⟨K',hK',_⟩ := hC.omega.1.2 K hKω
  obtain ⟨W',Q',hLayer',_⟩ := h.source_next_d hM hC hKω hK' hLayer
  have hTopRun := h.source_top_d hM hC hLayer hRun hFrom hK' hLayer'
  obtain ⟨Un,hUn⟩ := h.hr_total_d hM hC hKB hK'
  have hCopied := h.terminal_new_top_d hM hC hT hK' hUn hLayer hRun hFrom hTopRun
  obtain ⟨code',_,hAt',heights',parents',hCode',hRebuild⟩ := h.run.transition K hKB K' hK' Un U hUn hU
  have hc2 := h.tower.graph.unique K code' code hAt' hAt
  subst code'
  obtain ⟨hh2,hp2⟩ := codes_injective hM.1 hCode' hCode
  subst heights'
  subst parents'
  exact ⟨W,Q,J,sH,sP,W',Un,hLayer,hC,hT,hRun,h.layers.at_rooted hM.1 hLayer,hX,hFrom,hTopRun,h.coordinates,h.last,
    h.bad.in_run_d hM hC h.layers hLayer hRun,h.index,h.width,hY,hBranch.terminal_d hM,hCopied,hRebuild⟩

/-- 初始线性帧：塔第0层底父图由线性森林在 Hr(0) 上选出。 -/
theorem Setting.base_select_d (hM : M.Models KP1Y.theory) (hC : C.Valid M) (hT : T.Valid M C)
    (h : Setting M C T A m L V P H K level B strict N n Forests CodeSpace G Nr Top Hr) (hExits : TerminalExits M)
    (hLower : ∀ k, M.mem k K → LowerLayerStep M C T A m L H K k N n)
    {Sources Gs : M.Domain} (hGs : CopyTower.SourceGraph M C m L H B Sources Gs)
    {F0 : M.Domain} (hLinear0 : LinearForest M C.omega m F0) (hSel0 : Selects true M C m F0 V P) :
    BaseSelect M C n G Hr := by
  intro F code heights parents U0 P0 hLinear hAt hCode hU0 hP0
  have hw := omega_isOrdinal_d hM hC.omega
  have hKB := h.active_lt_d hM hC
  have hKω := (h.indices_d hM hC).1
  have hLastM := (h.indices_d hM hC).2.2.1
  obtain ⟨F'',hF''⟩ := FrameCopy.copies_exists_d hM hC hT h.coordinates hLinear0.1 h.width
  have hLin'' := hF''.linear_d hM hC hT h.coordinates hLinear0 hLastM
  have hFF := linear_forest_unique hM.1 hLin'' hLinear
  subst F''
  have hInitial := h.layers.initial_at_d hM
  by_cases hK0 : K=C.zero
  · subst K
    obtain ⟨W,Q,J,sH,sP,OldTop,Un,hLayer,hCtx⟩ := h.terminal_context_d hM hC hT hAt hCode hU0
    obtain ⟨hWV,hQP⟩ := h.layers.at_unique hM.1 hLayer hInitial
    subst W
    subst Q
    exact hExits.select hCtx hSel0 hF'' hP0
  · have h0K : M.mem C.zero K := (hC.zero_mem_iff hM hKω).mpr hK0
    have hInputs := h.lower_inputs_d hM hC hT hExits hLower hGs C.zero h0K
    obtain ⟨one,hOne,_⟩ := hC.omega.1.2 C.zero hC.zero_nat
    have h1B : M.mem one B := by
      rcases successor_le_B_d hM hC hC.zero_nat hKω hOne h0K with he | hlt
      · exact he ▸ hKB
      · exact (hw.mem h.tower.bound).transitive K hKB one hlt
    obtain ⟨Un,hUn⟩ := h.hr_total_d hM hC ((hw.mem h.tower.bound).transitive K hKB C.zero h0K) hOne
    obtain ⟨code',heights',parents',P',hAt',hCode',_,hP'⟩ := tower_code_bottom_d hC h.tower.graph h.valid_codes h1B
    obtain ⟨code0,heights0,parents0,W,Q,J,W',Q',D,hAt0,hCode0,hData,hInputs0⟩ :=
      h.lower_layer_inputs_d hM hC hT hGs h0K hOne hInputs hUn hAt' hCode' hP'
    have hcc := h.tower.graph.unique C.zero code0 code hAt0 hAt
    subst code0
    obtain ⟨hhh,hpp⟩ := codes_injective hM.1 hCode0 hCode
    subst heights0
    subst parents0
    obtain ⟨hWV,hQP⟩ := h.layers.at_unique hM.1 hData.layer hInitial
    subst W
    subst Q
    obtain ⟨code'',_,hAt'',heights'',parents'',hCode'',hRebuild⟩ :=
      h.run.transition C.zero ((hw.mem h.tower.bound).transitive K hKB C.zero h0K) one hOne Un U0 hUn hU0
    have hc2 := h.tower.graph.unique C.zero code'' code hAt'' hAt
    subst code''
    obtain ⟨hh2,hp2⟩ := codes_injective hM.1 hCode'' hCode
    subst heights''
    subst parents''
    exact (hLower C.zero h0K).bottom hData (h.run.values one Un hUn) (h.row_positive_d hM hC hT hUn) hInputs0 hRebuild
      hSel0 hF'' hP0

/-- 全塔逐层：每一层 k<B 的 LayerCanon 与 SelectNext。 -/
theorem Setting.tower_canon_d (hM : M.Models KP1Y.theory) (hC : C.Valid M) (hT : T.Valid M C)
    (h : Setting M C T A m L V P H K level B strict N n Forests CodeSpace G Nr Top Hr) (hExits : TerminalExits M)
    (hLower : ∀ k, M.mem k K → LowerLayerStep M C T A m L H K k N n) :
    (∀ k, M.mem k B → LayerCanon M C n Forests G Hr k) ∧ (∀ k, M.mem k B → SelectNext M C n Forests G Hr B k) := by
  have hw := omega_isOrdinal_d hM hC.omega
  have hKω := (h.indices_d hM hC).1
  obtain ⟨Sources,Gs,hGs⟩ := CopyTower.source_graph_exists_d hM hC h.layers h.tower.bound
  have hInputs := h.lower_inputs_d hM hC hT hExits hLower hGs
  have hCases (k : M.Domain) (hk : M.mem k B) : M.mem k K ∨ k=K ∨ M.mem K k := by
    rcases hw.wellOrder.linear.compare k (hw.transitive B h.tower.bound k hk) K hKω with he | hlt | hgt
    · exact Or.inr (Or.inl (hM.1.eq_of_same_members k K he))
    · exact Or.inl hlt
    · exact Or.inr (Or.inr hgt)
  constructor
  · intro k hk
    rcases hCases k hk with hlt | he | hgt
    · exact h.lower_canon_d hM hC hT hLower hGs hlt (hInputs k hlt)
    · subst k
      exact h.terminal_canon_d hM hC hT
    · exact h.ordinary_canon_d hM hC hT hk hgt
  · intro k hk
    rcases hCases k hk with hlt | he | hgt
    · exact h.lower_select_d hM hC hT hLower hGs hlt (hInputs k hlt)
    · subst k
      exact h.terminal_select_d hM hC hT
    · exact h.ordinary_select_d hM hC hT hk hgt

end KP1Y.OneYFinite.TowerCanon
