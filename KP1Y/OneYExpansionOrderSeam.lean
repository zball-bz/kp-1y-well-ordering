import KP1Y.OneYExpansionOrderLayer
import KP1Y.OneYExpansion

/-! 实际展开的第一接缝：N≥1 时 E_N(s)[x]+1=s[x]，x=|s|-1。
对实际复制塔从 horizon 向下作对象有界反向归纳：普通层 Y(x)=X(root)，活动层与下层 Y(x)+1=X(x)。 -/
namespace KP1Y.OneYFinite.ExpansionOrder
open YesMetaZFC YesMetaZFC.SetTheory YesMetaZFC.SetTheory.Definitional
open KP1Y.Kuratowski KP1Y.Functions KP1Y.Naturals KP1Y.Bounded KP1Y.Arithmetic
open KP1Y.OneYFinite KP1Y.OneYFinite.Expansion
universe u

/-- 塔的第k层：实际复制山形Y与同层原山形X构成LayerPair，并给出原层的行运行读数。 -/
theorem layer_pair_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {A : CopyCoordinates.Context M.Domain} (hA : A.Valid M C) {m : M.Domain} {L : LayerStateSpace M.Domain}
    {V P H K level B n Forests Codes G Sources G0 Nn Nn' Top Top0 J J0 k j U Lw U0 Lw0 : M.Domain}
    (hLayers : LayerRun M C m L V P H) (hTower : CopyTower.Tower M C T A m L H K level B n Forests Codes G)
    (hSources : CopyTower.SourceGraph M C m L H B Sources G0)
    (hNew : TowerReconstruction.Run M C T.addPairs T.plus n Forests Codes G B Nn Top J)
    (hOrig : TowerReconstruction.Run M C T.addPairs T.plus m L.rows.forests Sources G0 B Nn' Top0 J0)
    (hxm : M.mem A.last m) (hxn : M.mem A.last n)
    (hAgree : ∀i, M.mem i Nn → ∀R R0, MemPair M J i R → MemPair M J0 i R0 → RowsAgreeOn M R R0 A.last)
    (hk : M.mem k B) (hs : M.SuccessorOf j k) (hU : MemPair M J j U) (hL : MemPair M J k Lw)
    (hU0 : MemPair M J0 j U0) (hL0 : MemPair M J0 k Lw0) :
    ∃X Y, LayerPair M C T A X Y U0 U Lw0 Lw ∧ CopyTower.Branch M C T A X K level k n Y ∧
      ∃W Q R, RowAt M L.states H k W Q ∧ RowRun M C m L.rows W Q R ∧ CopiedMountain.FromRun M C m L.rows W R X := by
  have hw := omega_isOrdinal_d hM hC.omega
  obtain ⟨code,_,hAt,heights,parents,hCode,hRebuild⟩ := hNew.transition k hk j hs U Lw hU hL
  obtain ⟨code0,_,hAt0,h0,p0,hCode0,hRebuild0⟩ := hOrig.transition k hk j hs U0 Lw0 hU0 hL0
  obtain ⟨hY,source,sH,sP,hSource,hSC,hBranch⟩ := ((hTower.rows k code).mp hAt).2.read hM.1 hCode
  have hSrc0 := ((hSources.rows k code0).mp hAt0).2
  have hss := hSource.unique_d hM hC hLayers hSrc0
  subst source
  obtain ⟨hHH,hPP⟩ := codes_injective hM.1 hSC hCode0
  subst sH
  subst sP
  obtain ⟨W,Q,R,hRowAt,hRun,hX,hFrom⟩ := hSrc0.read hM.1 hCode0
  have hn := hTower.width
  have hInN (c : M.Domain) (hc : M.mem c A.last) : M.mem c n := (hw.mem hn).transitive A.last hxn c hc
  have hRows (c : M.Domain) (hc : M.mem c A.last) := branch_original_rows_d hM hC hT hA hX hBranch (hInN c hc) hc
  have hj : M.mem j Nn := (hNew.graph.bounds hM.1 hU).1
  refine ⟨_,_,⟨hX,hY,hxm,hxn,fun c hc v => (hRows c hc).1 v,fun c hc r p => (hRows c hc).2 r p,
    hOrig.values j U0 hU0,hNew.values j U hU,fun c hc v => (hAgree j hj U U0 hU hU0 c hc v).symm,hRebuild0,hRebuild⟩,
    hBranch,W,Q,R,hRowAt,hRun,hFrom⟩

private def seamEnv {M : SetTheory.Structure.{u}} (w S J J0 K x y : M.Domain) : Env M 7 :=
  ((((((oneEnv w).push S).push J).push J0).push K).push x).push y

private def seamSchema : Project.Delta0UnarySchema 7 where
  body := .conj
    (.imp (.mem (.bound 3) (.bound 0))
      (Project.Formula.forallMem (.bound 6) (Project.Formula.forallMem (.bound 7)
        (.imp (memPairFormula (.bound 7) (.bound 2) (.bound 1)) (.imp (memPairFormula (.bound 6) (.bound 2) (.bound 0))
          (Project.Formula.forallMem (.bound 9) (Project.Formula.forallMem (.bound 10)
            (.imp (memPairFormula (.bound 3) (.bound 6) (.bound 1)) (.imp (memPairFormula (.bound 2) (.bound 5) (.bound 0))
              (Project.Formula.extensionalEq (.bound 1) (.bound 0)))))))))))
    (.imp (Project.Formula.subset (.bound 0) (.bound 3))
      (Project.Formula.forallMem (.bound 6) (Project.Formula.forallMem (.bound 7)
        (.imp (memPairFormula (.bound 7) (.bound 2) (.bound 1)) (.imp (memPairFormula (.bound 6) (.bound 2) (.bound 0))
          (Project.Formula.forallMem (.bound 9) (Project.Formula.forallMem (.bound 10)
            (.imp (memPairFormula (.bound 3) (.bound 6) (.bound 1)) (.imp (memPairFormula (.bound 2) (.bound 6) (.bound 0))
              (successorFormula (.bound 0) (.bound 1)))))))))))
  freeClosed := by
    simp [memPairFormula,codeFormula,pairFormula,successorFormula,Project.Formula.forallMem,Project.Formula.existsMem,
      Project.Formula.subset,Project.Formula.extensionalEq,Definitional.Formula.FreeClosed]
  delta0 := .conj
    (.imp (.mem _ _) (.forallMem _ (.forallMem _ (.imp (memPairFormula_delta0 _ _ _) (.imp (memPairFormula_delta0 _ _ _)
      (.forallMem _ (.forallMem _ (.imp (memPairFormula_delta0 _ _ _) (.imp (memPairFormula_delta0 _ _ _) (.atom _ _ _))))))))))
    (.imp (.atom _ _ _) (.forallMem _ (.forallMem _ (.imp (memPairFormula_delta0 _ _ _) (.imp (memPairFormula_delta0 _ _ _)
      (.forallMem _ (.forallMem _ (.imp (memPairFormula_delta0 _ _ _) (.imp (memPairFormula_delta0 _ _ _)
        (successorFormula_delta0 _ _))))))))))

private theorem seamSchema_iff {M : SetTheory.Structure.{u}} (he : Extensional M) (w S J J0 K x y k : M.Domain) :
    Project.Formula.satisfies ((seamEnv w S J J0 K x y).push k) seamSchema.body ↔
      (M.mem K k → ∀R, M.mem R S → ∀R0, M.mem R0 S → MemPair M J k R → MemPair M J0 k R0 →
        ∀a, M.mem a w → ∀b, M.mem b w → MemPair M R x a → MemPair M R0 y b → a=b) ∧
      (M.MemberSubset k K → ∀R, M.mem R S → ∀R0, M.mem R0 S → MemPair M J k R → MemPair M J0 k R0 →
        ∀a, M.mem a w → ∀b, M.mem b w → MemPair M R x a → MemPair M R0 x b → M.SuccessorOf b a) := by
  simp only [seamSchema,seamEnv,Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_imp_iff,
    Project.Formula.satisfies_mem_iff,Project.Formula.satisfies_subset_iff,Project.Formula.satisfies_forallMem_iff,
    memPairFormula_iff he,Project.Formula.satisfies_extensionalEq_iff_eq he,successorFormula_iff he]
  rfl

/-- 原展开塔的实际逐层运行：第k项恰为第k层数值行。 -/
theorem original_run_exists_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {m : M.Domain} {L : LayerStateSpace M.Domain} {V P H B Sources G0 : M.Domain}
    (hLayers : LayerRun M C m L V P H) (hB : M.mem B C.omega) (hSources : CopyTower.SourceGraph M C m L H B Sources G0) :
    ∃N0 J0 Top0, TowerReconstruction.Run M C T.addPairs T.plus m L.rows.forests Sources G0 B N0 Top0 J0 ∧
      (∀k W, MemPair M J0 k W ↔ M.mem k N0 ∧ ∃Q, RowAt M L.states H k W Q) ∧
      MemPair M J0 C.zero V ∧ ∃Q0, RowAt M L.states H B Top0 Q0 := by
  obtain ⟨N0,hN0,hN0ω⟩ := hC.omega.1.2 B hB
  obtain ⟨J0,hJ0,hRows⟩ := layer_values_history_exists_d hM hC hLayers hN0ω
  obtain ⟨Top0,Q0,hTopLayer⟩ := hLayers.at_exists_d hB
  refine ⟨N0,J0,Top0,⟨hN0,hJ0,?_,(hRows B Top0).mpr ⟨hN0.predecessor_mem,Q0,hTopLayer⟩,?_⟩,hRows,?_,Q0,hTopLayer⟩
  · intro k W hAt
    obtain ⟨_,Q,hLayer⟩ := (hRows k W).mp hAt
    exact (hLayers.at_rooted hM.1 hLayer).row.values
  · intro k hk j hs upper lower hU hL
    obtain ⟨_,up,hUpper⟩ := (hRows j upper).mp hU
    obtain ⟨_,lp,hLower⟩ := (hRows k lower).mp hL
    exact original_code_step_d hM hC hT.add hLayers hSources hk hs hLower hUpper
  · have hZero : M.mem C.zero N0 := (hC.zero_mem_iff hM hN0ω).mpr (fun he => hC.zero_empty B (he ▸ hN0.predecessor_mem))
    exact (hRows C.zero V).mpr ⟨hZero,P,hLayers.initial_at_d hM⟩

/-- 第一接缝：N≠0 时 x=last 在输出宽度内，且 E_N(s)[x]+1=s[x]。 -/
theorem Successful.first_seam_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {s m last N t : M.Domain} {W : SuccessData M.Domain} (h : Successful M C T s m last N t W)
    (hLast : M.SuccessorOf m last) (hN : N≠C.zero) :
    M.mem last W.width ∧ ∀a b, MemPair M t last a → MemPair M s last b → M.SuccessorOf b a := by
  have hw := omega_isOrdinal_d hM hC.omega
  rcases W with ⟨F,P,L,H,K,level,root,B,A,n,Forests,Codes,G,Top⟩
  rcases h with ⟨_,_,hLayers,hBad,hB,hAx,hAy,hA,hWidth,hTower,hTop,hRebuild⟩
  dsimp only at *
  subst hAx
  subst hAy
  have hBN := hB.natural_d hM hC
  have hxm : M.mem A.last m := hLast.predecessor_mem
  have hNω : M.mem N C.omega := hWidth.2.1
  have hxn : M.mem A.last n := (CopyCoordinates.seam_lt_width_iff_d hM hC hT hA
    (CopyCoordinates.encode_zero_d hM hC hT hA hA.last) hWidth).mpr ((hC.zero_mem_iff hM hNω).mpr hN)
  refine ⟨hxn,?_⟩
  have hKB := bad_in_horizon_d hM hC hLayers hBad hB
  have hKω := hw.transitive B hBN K hKB
  obtain ⟨Nn,J,hNew,hJt⟩ := hRebuild
  obtain ⟨Sources,G0,hSources⟩ := CopyTower.source_graph_exists_d hM hC hLayers hBN
  obtain ⟨N0,J0,Top0,hOrig,hRows0,hJs,Q0,hTopLayer⟩ := original_run_exists_d hM hC hT hLayers hBN hSources
  have hNN := Structure.SuccessorOf.eq hM.1 hNew.length hOrig.length
  subst N0
  have hTop0 := horizon_layer_all_one_d hM hC hLayers hB hTopLayer
  have hPrefix := copy_source_family_prefix_d hM hC hT hA hLayers hTower hSources (width_keeps_prefix_d hM hC hT hWidth)
    (fun c hc => (hLast c).mpr (.inl hc))
  have hTops : RowsAgreeOn M Top Top0 A.last := by
    intro c hc v
    rw [hTop.2 c v,hTop0.2 c v]
    exact ⟨fun h => ⟨(hLast c).mpr (.inl hc),h.2⟩,fun h => ⟨(hw.mem hTower.width).transitive A.last hxn c hc,h.2⟩⟩
  have hAgree := TowerReconstruction.Run.prefix_d hM hC hT.add hTower.width hLayers.space.rows.width hBN hTower.graph
    hSources.graph (fun _ _ => hTower.code_valid) (fun _ _ => source_graph_code_valid hSources) hPrefix hTops hNew hOrig
  have hNnω := natural_successor_mem_d hM hC hBN hNew.length
  have hInNn (q : M.Domain) (hq : M.mem q C.omega) (hqB : M.MemberSubset q B) : M.mem q Nn := by
    rcases ordinal_subset_cases_d hM (hw.mem hq) (hw.mem hBN) hqB with he | hlt
    · exact he ▸ hNew.length.predecessor_mem
    · exact (hNew.length q).mpr (.inl hlt)
  let env := seamEnv C.omega C.sequences J J0 K A.last A.root
  have hAll := bounded_backward_induction_d hM seamSchema env hC.omega hBN
    ((seamSchema_iff hM.1 C.omega C.sequences J J0 K A.last A.root B).mpr ⟨by
      intro _ R _ R0 _ hR hR0 a _ b _ ha hb
      have hRT := hNew.graph.unique B R Top hR hNew.top
      have hR0T := hOrig.graph.unique B R0 Top0 hR0 hOrig.top
      subst R
      subst R0
      exact ((hTop.2 A.last a).mp ha).2.trans ((hTop0.2 A.root b).mp hb).2.symm,
      fun hBK => False.elim (SetTheory.KP.mem_irrefl_d (KP1Y.models_weakKP hM) K (hBK K hKB))⟩)
    (by
      intro p hp q hq hs hqB ih
      obtain ⟨IH1,IH2⟩ := (seamSchema_iff hM.1 C.omega C.sequences J J0 K A.last A.root q).mp ih
      have hpω := hw.transitive B hBN p hp
      have hpNn := hInNn p hpω (fun x hx => (hw.mem hBN).transitive p hp x hx)
      have hqNn := hInNn q hq hqB
      obtain ⟨U,hUS,hU⟩ := hNew.graph.total q hqNn
      obtain ⟨Lw,_,hL⟩ := hNew.graph.total p hpNn
      obtain ⟨U0,hU0S,hU0⟩ := hOrig.graph.total q hqNn
      obtain ⟨Lw0,_,hL0⟩ := hOrig.graph.total p hpNn
      obtain ⟨X,Y,hPair,hBranch,Wk,Qk,Rk,hRowAt,hRowRun,hFrom⟩ := layer_pair_d hM hC hT hA hLayers hTower hSources
        hNew hOrig hxm hxn hAgree hp hs hU hL hU0 hL0
      have hReadL (R : M.Domain) (hR : MemPair M J p R) : R=Lw := hNew.graph.unique p R Lw hR hL
      have hReadL0 (R0 : M.Domain) (hR0 : MemPair M J0 p R0) : R0=Lw0 := hOrig.graph.unique p R0 Lw0 hR0 hL0
      refine (seamSchema_iff hM.1 C.omega C.sequences J J0 K A.last A.root p).mpr ⟨?_,?_⟩
      · intro hKp R _ R0 _ hR hR0 a _ b _ ha hb
        have hKq : M.mem K q := (hs K).mpr (.inl hKp)
        have hCopy := hBranch.ordinary_d hM hC hKω hKp
        have hSeam := hPair.ordinary_seam_d hM hC hT hA hCopy (fun a b ha hb =>
          IH1 hKq U hUS U0 hU0S hU hU0 a (hPair.top_copy.bounds hM.1 ha).2 b (hPair.top_orig.bounds hM.1 hb).2 ha hb)
        rw [hReadL R hR] at ha
        rw [hReadL0 R0 hR0] at hb
        exact hSeam a b ha hb
      · intro hpK R _ R0 _ hR hR0 a _ b _ ha hb
        rw [hReadL R hR] at ha
        rw [hReadL0 R0 hR0] at hb
        rcases ordinal_subset_cases_d hM (hw.mem hpω) (hw.mem hKω) hpK with he | hlt
        · subst p
          have hKq : M.mem K q := hs.predecessor_mem
          have hCopy := hBranch.terminal_d hM
          have hActive := CopiedMountain.Terminal.active_from_bad_d hM hC hLayers hBad hRowAt hRowRun hPair.orig hFrom
          obtain ⟨Wq,_,Qq,_,hRowQ,hOne⟩ := hBad.next_layer_one_d hM hC hLayers hs
          obtain ⟨_,Q',hRowU0⟩ := (hRows0 q U0).mp hU0
          have hWU := (hLayers.at_unique hM.1 hRowQ hRowU0).1
          subst Wq
          exact hPair.terminal_seam_d hM hC hT hA hCopy hActive hOne (fun a b ha hb =>
            IH1 hKq U hUS U0 hU0S hU hU0 a (hPair.top_copy.bounds hM.1 ha).2 b (hPair.top_orig.bounds hM.1 hb).2 ha hb) a b ha hb
        · have hqK : M.MemberSubset q K := by
            intro x hx
            rcases (hs x).mp hx with hxp | hSame
            · exact (hw.mem hKω).transitive p hlt x hxp
            · exact (hM.1.eq_of_same_members x p hSame) ▸ hlt
          obtain ⟨D,hDA,hDX,hD,hCopy⟩ := hBranch.lower_d hM hC hKω hlt
          have hOld : A.last=D.coordinates.last ∨ M.mem A.last D.coordinates.last := .inl (by rw [hDA])
          exact hPair.kept_seam_d hM hC hT hA
            (fun v => by simpa only [hDX] using hCopy.original_heights_d hM hC hD (height := v) hxn hOld)
            (fun r q' => by simpa only [hDX] using hCopy.original_parents_d hM hC hD (r := r) (p := q') hxn hOld)
            (fun a b ha hb => IH2 hqK U hUS U0 hU0S hU hU0 a (hPair.top_copy.bounds hM.1 ha).2 b
              (hPair.top_orig.bounds hM.1 hb).2 ha hb) a b ha hb)
  have hZeroB : C.zero=B ∨ M.mem C.zero B := by
    by_cases he : B=C.zero
    · exact .inl he.symm
    · exact .inr ((hC.zero_mem_iff hM hBN).mpr he)
  obtain ⟨_,IH2⟩ := (seamSchema_iff hM.1 C.omega C.sequences J J0 K A.last A.root C.zero).mp (hAll C.zero hZeroB)
  intro a b ha hb
  exact IH2 (fun x hx => False.elim (hC.zero_empty x hx)) t (hNew.graph.bounds hM.1 hJt).2 s (hOrig.graph.bounds hM.1 hJs).2
    hJt hJs a (hNew.values C.zero t hJt |>.bounds hM.1 ha).2 b (hLayers.base.row.values.bounds hM.1 hb).2 ha hb

end KP1Y.OneYFinite.ExpansionOrder
