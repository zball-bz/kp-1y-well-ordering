import KP1Y.OneYTerminalTowerOrdinary
import KP1Y.OneYExpansionCanonical

/-! 活动层及其以上(k≥K)的逐层规范性：普通层(k>K)的完整运行与相邻选择，
Terminal层(k=K)的完整运行（新Top为实际 CopiedTop，由普通层反向归纳识别）。 -/
namespace KP1Y.OneYFinite.TowerCanon
open YesMetaZFC YesMetaZFC.SetTheory YesMetaZFC.SetTheory.Definitional
open KP1Y.Kuratowski KP1Y.Functions KP1Y.Naturals KP1Y.Bounded
open KP1Y.OneYFinite.CopiedMountain
universe u

/-- 普通复制同一行的父图互为 ForestCopies。 -/
theorem ordinary_forest_copies_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {A : CopyCoordinates.Context M.Domain} (hA : A.Valid M C) {X Y : Data M.Domain} (hX : X.Valid M C) (hY : Y.Valid M C)
    {n r F G : M.Domain} (hCopy : Ordinary.Copies M C T A X n Y) (hF : MemPair M X.parents r F) (hG : MemPair M Y.parents r G) :
    Ordinary.ForestCopies M C T A n F G := by
  intro s b c hs hc hMap a
  have hParent : MemPair M G c a ↔ ParentAt M Y r c a := by
    constructor
    · exact fun h => ⟨G,(hY.parents.bounds hM.1 hG).2,hG,h⟩
    · rintro ⟨G',_,hG',h⟩
      exact hY.parents.unique r G' G hG' hG ▸ h
  rw [hParent,hCopy.parents r c a,Ordinary.parent_parent_copy_iff_d hM hC hT hA hX hs hMap]
  constructor
  · rintro ⟨_,p,_,⟨F',_,hF',hEdge⟩,hMapP⟩
    exact ⟨p,hX.parents.unique r F' F hF' hF ▸ hEdge,hMapP⟩
  · rintro ⟨p,hEdge,hMapP⟩
    exact ⟨hc,p,hMapP.1,⟨F,(hX.parents.bounds hM.1 hF).2,hF,hEdge⟩,hMapP⟩

/-- 两个宽n森林若都是同一源森林的普通复制则相等。 -/
theorem forest_copies_unique_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {A : CopyCoordinates.Context M.Domain} (hA : A.Valid M C) {n F G G' : M.Domain}
    (hG : Forest M C.omega n G) (hG' : Forest M C.omega n G')
    (h : Ordinary.ForestCopies M C T A n F G) (h' : Ordinary.ForestCopies M C T A n F G') : G=G' := by
  apply hG.ext hM.1 hG'
  intro c p
  have hw := omega_isOrdinal_d hM hC.omega
  constructor
  · intro hAt
    have hc := (hG.bounds hM.1 hAt).1
    obtain ⟨s,b,hDec⟩ := OrdinaryCoordinates.decoded_exists_d hM hC hT hA (hw.transitive n hG.width c hc)
    have hs := hDec.source_lt_last_d hM hC hT hA
    have hMap := hDec.parent_copy_reconstruct_d hM hC hT hA
    exact (h' s b c hs hc hMap p).mpr ((h s b c hs hc hMap p).mp hAt)
  · intro hAt
    have hc := (hG'.bounds hM.1 hAt).1
    obtain ⟨s,b,hDec⟩ := OrdinaryCoordinates.decoded_exists_d hM hC hT hA (hw.transitive n hG'.width c hc)
    have hs := hDec.source_lt_last_d hM hC hT hA
    have hMap := hDec.parent_copy_reconstruct_d hM hC hT hA
    exact (h s b c hs hc hMap p).mpr ((h' s b c hs hc hMap p).mp hAt)

variable {M : SetTheory.Structure.{u}} {C : ExpressionData M.Domain} {T : MatrixArithmetic M.Domain}
  {A : CopyCoordinates.Context M.Domain} {m : M.Domain} {L : LayerStateSpace M.Domain}
  {V P H K level B strict N n Forests CodeSpace G Nr Top Hr : M.Domain}

private theorem successor_le_d (hM : M.Models KP1Y.theory) (hC : C.Valid M) {r s q : M.Domain} (hr : M.mem r C.omega)
    (hq : M.mem q C.omega) (hSucc : M.SuccessorOf s r) (hrq : M.mem r q) : s=q ∨ M.mem s q := by
  have hw := omega_isOrdinal_d hM hC.omega
  apply ordinal_subset_cases_d hM (hw.mem (natural_successor_mem_d hM hC hr hSucc)) (hw.mem hq)
  intro a ha
  rcases (hSucc a).mp ha with har | he
  · exact (hw.mem hq).transitive r hrq a har
  · exact (hM.1.eq_of_same_members a r he).symm ▸ hrq

/-- 普通层(K<k<B)：塔重建行的实际运行读出普通复制山形，Top为Hr(k+1)。 -/
theorem Setting.ordinary_canon_d (hM : M.Models KP1Y.theory) (hC : C.Valid M) (hT : T.Valid M C)
    (h : Setting M C T A m L V P H K level B strict N n Forests CodeSpace G Nr Top Hr)
    {k : M.Domain} (hk : M.mem k B) (hKk : M.mem K k) : LayerCanon M C n Forests G Hr k := by
  intro code heights parents U k' Un hAt hCode hU hs hUn
  have hw := omega_isOrdinal_d hM hC.omega
  have hkω := hw.transitive B h.tower.bound k hk
  obtain ⟨code0,heights0,parents0,sH,sP,W,Q,J,hAt0,hCode0,hY,hLayer,hRun,hX,hFrom,hBranch⟩ := h.layer_read_d hM hk
  have hcc := h.tower.graph.unique k code0 code hAt0 hAt
  subst code0
  obtain ⟨hhh,hpp⟩ := codes_injective hM.1 hCode0 hCode
  subst heights0
  subst parents0
  have hCopy := hBranch.ordinary_d hM hC (h.indices_d hM hC).1 hKk
  obtain ⟨W',Q',hLayer',_⟩ := h.source_next_d hM hC hkω hs hLayer
  have hTopRun := h.source_top_d hM hC hLayer hRun hFrom hs hLayer'
  have hk'B := successor_le_d hM hC hkω h.tower.bound hs hk
  have hTopCopy := h.ordinary_values_d hM hC hT k' hk'B ((hs K).mpr (Or.inl hKk)) Un W' Q' hUn hLayer'
  obtain ⟨code',_,hAt',heights',parents',hCode',hRebuild⟩ := h.run.transition k hk k' hs Un U hUn hU
  have hcc' := h.tower.graph.unique k code' code hAt' hAt
  subst code'
  obtain ⟨hhh',hpp'⟩ := codes_injective hM.1 hCode' hCode
  subst heights'
  subst parents'
  obtain ⟨R',P',Run',hRun',hFrom',hTop',_,_⟩ := Ordinary.Copies.canonical_run_exists_d hM hC hT h.coordinates hT.add hRun
    (h.layers.at_rooted hM.1 hLayer).positive hX hY hFrom hCopy hTopRun hTopCopy hRebuild
  exact ⟨R',P',Run',hRun',hFrom',hTop'⟩

/-- 普通层(K<k，k+1<B)：伪父森林在Hr(k+1)上恰选出塔第k+1层底父图。 -/
theorem Setting.ordinary_select_d (hM : M.Models KP1Y.theory) (hC : C.Valid M) (hT : T.Valid M C)
    (h : Setting M C T A m L V P H K level B strict N n Forests CodeSpace G Nr Top Hr)
    {k : M.Domain} (hk : M.mem k B) (hKk : M.mem K k) : SelectNext M C n Forests G Hr B k := by
  intro k' code heights parents code' heights' parents' Un P' Pseudo hs hk' hAt hCode hAt' hCode' hUn hP' hPseudo
  have hw := omega_isOrdinal_d hM hC.omega
  have hkω := hw.transitive B h.tower.bound k hk
  have hK := (h.indices_d hM hC).1
  obtain ⟨code0,heights0,parents0,sH,sP,W,Q,J,hAt0,hCode0,hY,hLayer,hRun,hX,hFrom,hBranch⟩ := h.layer_read_d hM hk
  have hcc := h.tower.graph.unique k code0 code hAt0 hAt
  subst code0
  obtain ⟨hhh,hpp⟩ := codes_injective hM.1 hCode0 hCode
  subst heights0
  subst parents0
  have hCopy := hBranch.ordinary_d hM hC hK hKk
  obtain ⟨W',Q',hLayer',hNextSource⟩ := h.source_next_d hM hC hkω hs hLayer
  have hTopRun := h.source_top_d hM hC hLayer hRun hFrom hs hLayer'
  have hKk' : M.mem K k' := (hs K).mpr (Or.inl hKk)
  have hTopCopy := h.ordinary_values_d hM hC hT k' (Or.inr hk') hKk' Un W' Q' hUn hLayer'
  obtain ⟨F,Qs,hF,hSel,hExtraction⟩ := ReconstructionExtraction.extraction_graph_exists_d hM hC hRun hX hFrom hTopRun
  have hQs := (hExtraction.unique_d hM hC hNextSource).2
  subst Qs
  obtain ⟨Q2,hQ2,hCopies⟩ := hCopy.pseudo_selection_exists_d hM hC hT h.coordinates hX hY hF hPseudo hTopCopy hSel
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
  have hEq := forest_copies_unique_d hM hC hT h.coordinates hQ2.forest (hY1.forest C.zero P' hP') hCopies hTarget
  subst Q2
  exact hQ2

/-- Terminal层的新Top：塔在K+1处的实际重建行恰是源K层Top的普通 CopiedTop。 -/
theorem Setting.terminal_new_top_d (hM : M.Models KP1Y.theory) (hC : C.Valid M) (hT : T.Valid M C)
    (h : Setting M C T A m L V P H K level B strict N n Forests CodeSpace G Nr Top Hr)
    {K' Un W Q J sH sP OldTop : M.Domain} (hs : M.SuccessorOf K' K) (hUn : MemPair M Hr K' Un)
    (hLayer : RowAt M L.states H K W Q) (hRun : RowRun M C m L.rows W Q J)
    (hFrom : FromRun M C m L.rows W J ⟨m,sH,L.rows.forests,sP⟩) (hOldTop : TopValueGraph M C m L.rows J sH OldTop) :
    CopiedTop M C T A OldTop n Un := by
  have hw := omega_isOrdinal_d hM hC.omega
  have hK := (h.indices_d hM hC).1
  obtain ⟨W',Q',hLayer',_⟩ := h.source_next_d hM hC hK hs hLayer
  have hTopRun := h.source_top_d hM hC hLayer hRun hFrom hs hLayer'
  have hTT := hTopRun.unique hM.1 hOldTop
  subst OldTop
  have hK'B := successor_le_d hM hC hK h.tower.bound hs (h.active_lt_d hM hC)
  have hCopies := h.ordinary_values_d hM hC hT K' hK'B ((hs K).mpr (Or.inr fun _ => Iff.rfl)) Un W' Q' hUn hLayer'
  refine ⟨hCopies.graph,?_⟩
  intro c v
  constructor
  · intro hAt
    have hc := (hCopies.graph.bounds hM.1 hAt).1
    obtain ⟨s,b,hDec⟩ := OrdinaryCoordinates.decoded_exists_d hM hC hT h.coordinates (hw.transitive n h.tower.width c hc)
    exact ⟨hc,s,hDec.2.1,b,hDec.2.2.1,hDec,((hCopies.rows c s b hDec v).mp hAt).2⟩
  · rintro ⟨hc,s,_,b,_,hDec,hV⟩
    exact (hCopies.rows c s b hDec v).mpr ⟨hc,hV⟩

/-- Terminal层(k=K)：塔重建行的实际运行读出Terminal复制山形，Top为Hr(K+1)。 -/
theorem Setting.terminal_canon_d (hM : M.Models KP1Y.theory) (hC : C.Valid M) (hT : T.Valid M C)
    (h : Setting M C T A m L V P H K level B strict N n Forests CodeSpace G Nr Top Hr) :
    LayerCanon M C n Forests G Hr K := by
  intro code heights parents U K' Un hAt hCode hU hs hUn
  have hKB := h.active_lt_d hM hC
  obtain ⟨code0,heights0,parents0,sH,sP,W,Q,J,hAt0,hCode0,hY,hLayer,hRun,hX,hFrom,hBranch⟩ := h.layer_read_d hM hKB
  have hcc := h.tower.graph.unique K code0 code hAt0 hAt
  subst code0
  obtain ⟨hhh,hpp⟩ := codes_injective hM.1 hCode0 hCode
  subst heights0
  subst parents0
  have hCopy := hBranch.terminal_d hM
  obtain ⟨W',Q',hLayer',_⟩ := h.source_next_d hM hC (h.indices_d hM hC).1 hs hLayer
  have hTopRun := h.source_top_d hM hC hLayer hRun hFrom hs hLayer'
  have hNewTop := h.terminal_new_top_d hM hC hT hs hUn hLayer hRun hFrom hTopRun
  obtain ⟨code',_,hAt',heights',parents',hCode',hRebuild⟩ := h.run.transition K hKB K' hs Un U hUn hU
  have hcc' := h.tower.graph.unique K code' code hAt' hAt
  subst code'
  obtain ⟨hhh',hpp'⟩ := codes_injective hM.1 hCode' hCode
  subst heights'
  subst parents'
  obtain ⟨R',P',Run',hRun',hFrom',hTop',_⟩ := ExpansionCanonical.terminal_rebuild_rows_d hM hC hT hRun
    (h.layers.at_rooted hM.1 hLayer) hX hFrom hTopRun h.coordinates h.last (h.bad.in_run_d hM hC h.layers hLayer hRun)
    h.index h.width hY hCopy hNewTop hRebuild
  exact ⟨R',P',Run',hRun',hFrom',hTop'⟩

end KP1Y.OneYFinite.TowerCanon
