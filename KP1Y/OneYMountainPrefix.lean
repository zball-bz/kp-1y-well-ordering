import KP1Y.OneYExpressionDiagram
import KP1Y.ReflectionRepresentation

/-! 实际数值山形和提取塔的宽度前缀局部性；不把原子枚举误认作列表前缀。 -/
namespace KP1Y.OneYFinite
open YesMetaZFC YesMetaZFC.SetTheory YesMetaZFC.SetTheory.Definitional
open KP1Y.Kuratowski KP1Y.Functions KP1Y.Naturals KP1Y.Bounded
universe u

theorem difference_at_prefix_iff_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {m n V P W Q c d : M.Domain}
    (hP : Forest M C.omega m P) (hn : M.mem n C.omega) (hSub : M.MemberSubset n m)
    (hValues : RowsAgreeOn M V W n) (hParents : RowsAgreeOn M P Q n) (hc : M.mem c n) :
    DifferenceAt M C m V P c d ↔ DifferenceAt M C n W Q c d := by
  have hNone := no_parent_prefix_iff_d hM hC hP hn hc hParents
  have hpn (p : M.Domain) (hp : MemPair M P c p) : M.mem p n :=
    ((omega_isOrdinal_d hM hC.omega).mem hn).transitive c hc p (hP.left c p hp)
  constructor
  · rintro (⟨hNo,hd⟩ | ⟨p,_,x,hx,y,hy,hPc,hCx,hPy,hDiff⟩)
    · exact .inl ⟨hNone.mp hNo,hd⟩
    · exact .inr ⟨p,hpn p hPc,x,hx,y,hy,(hParents c hc p).mp hPc,
        (hValues c hc x).mp hCx,(hValues p (hpn p hPc) y).mp hPy,hDiff⟩
  · rintro (⟨hNo,hd⟩ | ⟨p,hp,x,hx,y,hy,hPc,hCx,hPy,hDiff⟩)
    · exact .inl ⟨hNone.mpr hNo,hd⟩
    · exact .inr ⟨p,hSub p hp,x,hx,y,hy,(hParents c hc p).mpr hPc,
        (hValues c hc x).mpr hCx,(hValues p hp y).mpr hPy,hDiff⟩

theorem DifferenceGraph.prefix_rows_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {m n V P W Q D E : M.Domain}
    (hP : Forest M C.omega m P) (hn : M.mem n C.omega) (hSub : M.MemberSubset n m)
    (hD : DifferenceGraph M C m V P D) (hE : DifferenceGraph M C n W Q E)
    (hValues : RowsAgreeOn M V W n) (hParents : RowsAgreeOn M P Q n) : RowsAgreeOn M D E n := by
  intro c hc d
  rw [hD.rows c d,hE.rows c d,difference_at_prefix_iff_d hM hC hP hn hSub hValues hParents hc]
  exact ⟨fun h => ⟨hc,h.2⟩,fun h => ⟨hSub c hc,h.2⟩⟩

theorem RowNext.prefix_rows_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {m n V P W Q V' P' W' Q' : M.Domain}
    (hOld : RowNext M C m V P V' P') (hNew : RowNext M C n W Q W' Q')
    (hSub : M.MemberSubset n m) (hValues : RowsAgreeOn M V W n) (hParents : RowsAgreeOn M P Q n) :
    RowsAgreeOn M V' W' n ∧ RowsAgreeOn M P' Q' n := by
  have hValues' := hOld.difference.prefix_rows_d hM hC hOld.selection.inherited hNew.selection.inherited.width hSub hNew.difference hValues hParents
  exact ⟨hValues',hOld.selection.prefix_rows_d hM hC hNew.selection hSub hParents hValues'⟩

def RowHistoriesAgree (M : SetTheory.Structure.{u}) (S H S' H' n r : M.Domain) : Prop :=
  ∀ V P W Q, RowAt M S H r V P → RowAt M S' H' r W Q → RowsAgreeOn M V W n ∧ RowsAgreeOn M P Q n

private def rowsAgreeFormula {n : Nat} (V W cut : Project.Term n) : Project.Formula 1 n :=
  Project.Formula.forallMem cut (.forallE (.iff (memPairFormula V.weaken.weaken (.bound 1) (.bound 0))
    (memPairFormula W.weaken.weaken (.bound 1) (.bound 0))))

private theorem rowsAgreeFormula_iff {M : SetTheory.Structure.{u}} (he : Extensional M) {n : Nat}
    (e : Env M n) (V W cut : Project.Term n) : Project.Formula.satisfies e (rowsAgreeFormula V W cut) ↔
    RowsAgreeOn M (V.eval e) (W.eval e) (cut.eval e) := by
  simp only [rowsAgreeFormula,Project.Formula.satisfies_forallMem_iff,Project.Formula.satisfies_forall_iff,
    Project.Formula.satisfies_iff_iff,memPairFormula_iff he,Term.eval_weaken]
  rfl

private def rowHistoriesSchema : Project.UnarySchema 5 where
  body := .forallE (.forallE (.forallE (.forallE (.imp
    (.conj (rowAtFormula (.bound 9) (.bound 8) (.bound 4) (.bound 3) (.bound 2))
      (rowAtFormula (.bound 7) (.bound 6) (.bound 4) (.bound 1) (.bound 0)))
    (.conj (rowsAgreeFormula (.bound 3) (.bound 1) (.bound 5)) (rowsAgreeFormula (.bound 2) (.bound 0) (.bound 5)))))))
  freeClosed := by
    simp [rowsAgreeFormula,rowAtFormula,memPairFormula,codeFormula,pairFormula,Project.Formula.forallMem,Project.Formula.existsMem,Definitional.Formula.FreeClosed]

private theorem rowHistoriesSchema_iff {M : SetTheory.Structure.{u}} (he : Extensional M) (S H S' H' n r : M.Domain) :
    Project.Formula.satisfies ((((((oneEnv S).push H).push S').push H').push n).push r) rowHistoriesSchema.body ↔
      RowHistoriesAgree M S H S' H' n r := by
  simp only [rowHistoriesSchema,Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_imp_iff,
    Project.Formula.satisfies_conj_iff,rowAtFormula_iff he,rowsAgreeFormula_iff he]
  exact ⟨fun h V P W Q hA hB => h V P W Q ⟨hA,hB⟩,fun h V P W Q hs => h V P W Q hs.1 hs.2⟩

theorem row_histories_agree_induction_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {S H S' H' n : M.Domain}
    (hZero : RowHistoriesAgree M S H S' H' n C.zero)
    (hStep : ∀r, M.mem r C.omega → RowHistoriesAgree M S H S' H' n r → ∀r', M.SuccessorOf r' r → RowHistoriesAgree M S H S' H' n r') :
    ∀r, M.mem r C.omega → RowHistoriesAgree M S H S' H' n r := by
  have hAll := natural_induction_d hM rowHistoriesSchema (((((oneEnv S).push H).push S').push H').push n) hC.omega
    (fun z hz => (rowHistoriesSchema_iff hM.1 S H S' H' n z).mpr (by
      have he := hM.1.eq_of_same_members z C.zero (fun x => iff_of_false (hz x) (hC.zero_empty x))
      exact he.symm ▸ hZero))
    (fun r hr ih r' hs => (rowHistoriesSchema_iff hM.1 S H S' H' n r').mpr
      (hStep r hr ((rowHistoriesSchema_iff hM.1 S H S' H' n r).mp ih) r' hs))
  exact fun r hr => (rowHistoriesSchema_iff hM.1 S H S' H' n r).mp (hAll r hr)

theorem RowRun.prefix_rows_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {m n : M.Domain} {R R' : RowStateSpace M.Domain}
    {V P W Q H J : M.Domain} (hRun : RowRun M C m R V P H) (hOther : RowRun M C n R' W Q J)
    (hSub : M.MemberSubset n m) (hValues : RowsAgreeOn M V W n) (hParents : RowsAgreeOn M P Q n) :
    ∀r, M.mem r C.omega → RowHistoriesAgree M R.states H R'.states J n r := by
  apply row_histories_agree_induction_d hM hC
  · intro U F U' F' hAt hAt'
    obtain ⟨heV,heP⟩ := hRun.at_unique hM.1 hAt (hRun.initial_row_at_d hM)
    obtain ⟨heW,heQ⟩ := hOther.at_unique hM.1 hAt' (hOther.initial_row_at_d hM)
    subst U
    subst F
    subst U'
    subst F'
    exact ⟨hValues,hParents⟩
  · intro r hr ih r' hs U F U' F' hAt hAt'
    obtain ⟨X,G,hX⟩ := hRun.at_exists_d hr
    obtain ⟨Y,G',hY⟩ := hOther.at_exists_d hr
    have hAgree := ih X G Y G' hX hY
    exact (hRun.at_next hM.1 hs hX hAt).prefix_rows_d hM hC (hOther.at_next hM.1 hs hY hAt') hSub hAgree.1 hAgree.2

theorem row_value_prefix_iff_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {m n : M.Domain} {R R' : RowStateSpace M.Domain}
    {V P W Q H J r c v : M.Domain} (hRun : RowRun M C m R V P H) (hOther : RowRun M C n R' W Q J)
    (hAgree : ∀r, M.mem r C.omega → RowHistoriesAgree M R.states H R'.states J n r) (hc : M.mem c n) :
    RowValue M R.states R.values R.forests H r c v ↔ RowValue M R'.states R'.values R'.forests J r c v := by
  constructor
  · rintro ⟨U,_,F,_,hAt,hValue⟩
    have hAtCopy := hAt
    obtain ⟨state,_,hState,_⟩ := hAtCopy
    have hr := (hRun.graph.bounds hM.1 hState).1
    obtain ⟨U',F',hAt'⟩ := hOther.at_exists_d hr
    have hN := hOther.at_numeric_d hM hC hAt'
    exact ⟨U',(hOther.space.values U').mpr hN.values,F',(hOther.space.forests F').mpr hN.forest,hAt',
      ((hAgree r hr U F U' F' hAt hAt').1 c hc v).mp hValue⟩
  · rintro ⟨U',_,F',_,hAt',hValue⟩
    have hAtCopy := hAt'
    obtain ⟨state,_,hState,_⟩ := hAtCopy
    have hr := (hOther.graph.bounds hM.1 hState).1
    obtain ⟨U,F,hAt⟩ := hRun.at_exists_d hr
    have hN := hRun.at_numeric_d hM hC hAt
    exact ⟨U,(hRun.space.values U).mpr hN.values,F,(hRun.space.forests F).mpr hN.forest,hAt,
      ((hAgree r hr U F U' F' hAt hAt').1 c hc v).mpr hValue⟩

theorem live_row_prefix_iff_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {m n : M.Domain} {R R' : RowStateSpace M.Domain}
    {V P W Q H J r c : M.Domain} (hRun : RowRun M C m R V P H) (hOther : RowRun M C n R' W Q J)
    (hAgree : ∀r, M.mem r C.omega → RowHistoriesAgree M R.states H R'.states J n r) (hc : M.mem c n) :
    LiveRow M C.omega C.zero R.states R.values R.forests H c r ↔ LiveRow M C.omega C.zero R'.states R'.values R'.forests J c r := by
  simp only [LiveRow,row_value_prefix_iff_d hM hC hRun hOther hAgree hc]

theorem height_at_prefix_iff_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {m n : M.Domain} {R R' : RowStateSpace M.Domain}
    {V P W Q H J c height : M.Domain} (hRun : RowRun M C m R V P H) (hOther : RowRun M C n R' W Q J)
    (hValues : RowsAgreeOn M V W n) (hAgree : ∀r, M.mem r C.omega → RowHistoriesAgree M R.states H R'.states J n r)
    (hc : M.mem c n) : HeightAt M C R V H c height ↔ HeightAt M C R' W J c height := by
  simp only [HeightAt,hValues c hc,live_row_prefix_iff_d hM hC hRun hOther hAgree hc]

theorem HeightGraph.prefix_rows_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {m n : M.Domain} {R R' : RowStateSpace M.Domain}
    {V P W Q H J Heights Heights' : M.Domain} (hRun : RowRun M C m R V P H) (hOther : RowRun M C n R' W Q J)
    (hSub : M.MemberSubset n m) (hValues : RowsAgreeOn M V W n)
    (hAgree : ∀r, M.mem r C.omega → RowHistoriesAgree M R.states H R'.states J n r)
    (hHeights : HeightGraph M C m R V H Heights) (hHeights' : HeightGraph M C n R' W J Heights') :
    RowsAgreeOn M Heights Heights' n := by
  intro c hc height
  rw [hHeights.rows c height,hHeights'.rows c height,height_at_prefix_iff_d hM hC hRun hOther hValues hAgree hc]
  exact ⟨fun h => ⟨hc,h.2⟩,fun h => ⟨hSub c hc,h.2⟩⟩

theorem TopValueGraph.prefix_rows_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {m n : M.Domain} {R R' : RowStateSpace M.Domain}
    {V P W Q H J Heights Heights' Top Top' : M.Domain} (hRun : RowRun M C m R V P H) (hOther : RowRun M C n R' W Q J)
    (hAgree : ∀r, M.mem r C.omega → RowHistoriesAgree M R.states H R'.states J n r)
    (hHeights : RowsAgreeOn M Heights Heights' n)
    (hTop : TopValueGraph M C m R H Heights Top) (hTop' : TopValueGraph M C n R' J Heights' Top') : RowsAgreeOn M Top Top' n := by
  intro c hc v
  simp only [hTop.rows c v,hTop'.rows c v,hHeights c hc,row_value_prefix_iff_d hM hC hRun hOther hAgree hc]

theorem pseudo_candidate_prefix_iff_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {m n : M.Domain} {R R' : RowStateSpace M.Domain}
    {V P W Q H J Heights Heights' c p : M.Domain} (hRun : RowRun M C m R V P H) (hOther : RowRun M C n R' W Q J)
    (hSub : M.MemberSubset n m)
    (hAgree : ∀r, M.mem r C.omega → RowHistoriesAgree M R.states H R'.states J n r)
    (hHeights : RowsAgreeOn M Heights Heights' n) (hc : M.mem c n) :
    PseudoCandidate M C m R H Heights c p ↔ PseudoCandidate M C n R' J Heights' c p := by
  have hn := hOther.space.width
  constructor
  · rintro ⟨height,hh,ph,hph,r,hr,hHC,hHP,hPrev,U,_,F,_,hAt,hAnc,hShape⟩
    obtain ⟨U',F',hAt'⟩ := hOther.at_exists_d hr
    have hN := hOther.at_numeric_d hM hC hAt'
    have hp := ((omega_isOrdinal_d hM hC.omega).mem hn).transitive c hc p hAnc.1
    have hParents := (hAgree r hr U F U' F' hAt hAt').2
    exact ⟨height,hh,ph,hph,r,hr,(hHeights c hc height).mp hHC,(hHeights p hp ph).mp hHP,hPrev,
      U',(hOther.space.values U').mpr hN.values,F',(hOther.space.forests F').mpr hN.forest,hAt',
      (ancestor_prefix_iff_d hM hC (hRun.at_numeric_d hM hC hAt).forest hn hSub hc hParents).mp hAnc,hShape⟩
  · rintro ⟨height,hh,ph,hph,r,hr,hHC,hHP,hPrev,U',_,F',_,hAt',hAnc,hShape⟩
    obtain ⟨U,F,hAt⟩ := hRun.at_exists_d hr
    have hN := hRun.at_numeric_d hM hC hAt
    have hp := ((omega_isOrdinal_d hM hC.omega).mem hn).transitive c hc p hAnc.1
    have hParents := (hAgree r hr U F U' F' hAt hAt').2
    exact ⟨height,hh,ph,hph,r,hr,(hHeights c hc height).mpr hHC,(hHeights p hp ph).mpr hHP,hPrev,
      U,(hRun.space.values U).mpr hN.values,F,(hRun.space.forests F).mpr hN.forest,hAt,
      (ancestor_prefix_iff_d hM hC hN.forest hn hSub hc hParents).mpr hAnc,hShape⟩

theorem pseudo_parent_prefix_iff_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {m n : M.Domain} {R R' : RowStateSpace M.Domain}
    {V P W Q H J Heights Heights' c p : M.Domain} (hRun : RowRun M C m R V P H) (hOther : RowRun M C n R' W Q J)
    (hSub : M.MemberSubset n m)
    (hAgree : ∀r, M.mem r C.omega → RowHistoriesAgree M R.states H R'.states J n r)
    (hHeights : RowsAgreeOn M Heights Heights' n) (hc : M.mem c n) :
    PseudoParent M C m R H Heights c p ↔ PseudoParent M C n R' J Heights' c p := by
  simp only [PseudoParent,hHeights c hc,pseudo_candidate_prefix_iff_d hM hC hRun hOther hSub hAgree hHeights hc]

theorem PseudoForest.prefix_rows_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {m n : M.Domain} {R R' : RowStateSpace M.Domain}
    {V P W Q H J Heights Heights' F F' : M.Domain} (hRun : RowRun M C m R V P H) (hOther : RowRun M C n R' W Q J)
    (hSub : M.MemberSubset n m)
    (hAgree : ∀r, M.mem r C.omega → RowHistoriesAgree M R.states H R'.states J n r)
    (hHeights : RowsAgreeOn M Heights Heights' n)
    (hF : PseudoForest M C m R H Heights F) (hF' : PseudoForest M C n R' J Heights' F') : RowsAgreeOn M F F' n := by
  intro c hc p
  exact (hF.parents c p).trans ((pseudo_parent_prefix_iff_d hM hC hRun hOther hSub hAgree hHeights hc).trans (hF'.parents c p).symm)

theorem Extraction.prefix_rows_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {m n V P W Q V' P' W' Q' : M.Domain}
    (hOld : Extraction M C m V P V' P') (hNew : Extraction M C n W Q W' Q')
    (hSub : M.MemberSubset n m) (hValues : RowsAgreeOn M V W n) (hParents : RowsAgreeOn M P Q n) :
    RowsAgreeOn M V' W' n ∧ RowsAgreeOn M P' Q' n := by
  obtain ⟨R,H,Heights,F,hRun,hHeights,hTop,hF,hSelected⟩ := hOld
  obtain ⟨R',J,Heights',F',hOther,hHeights',hTop',hF',hSelected'⟩ := hNew
  have hAgree := hRun.prefix_rows_d hM hC hOther hSub hValues hParents
  have hHeightRows := hHeights.prefix_rows_d hM hC hRun hOther hSub hValues hAgree hHeights'
  have hTopRows := hTop.prefix_rows_d hM hC hRun hOther hAgree hHeightRows hTop'
  have hForestRows := hF.prefix_rows_d hM hC hRun hOther hSub hAgree hHeightRows hF'
  exact ⟨hTopRows,hSelected.prefix_rows_d hM hC hSelected' hSub hForestRows hTopRows⟩

theorem LayerRun.prefix_rows_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {m n : M.Domain} {L L' : LayerStateSpace M.Domain}
    {V P W Q H J : M.Domain} (hRun : LayerRun M C m L V P H) (hOther : LayerRun M C n L' W Q J)
    (hSub : M.MemberSubset n m) (hValues : RowsAgreeOn M V W n) (hParents : RowsAgreeOn M P Q n) :
    ∀k, M.mem k C.omega → RowHistoriesAgree M L.states H L'.states J n k := by
  apply row_histories_agree_induction_d hM hC
  · intro U F U' F' hAt hAt'
    obtain ⟨heV,heP⟩ := hRun.at_unique hM.1 hAt (hRun.initial_at_d hM)
    obtain ⟨heW,heQ⟩ := hOther.at_unique hM.1 hAt' (hOther.initial_at_d hM)
    subst U
    subst F
    subst U'
    subst F'
    exact ⟨hValues,hParents⟩
  · intro k hk ih k' hs U F U' F' hAt hAt'
    obtain ⟨X,G,hX⟩ := hRun.at_exists_d hk
    obtain ⟨Y,G',hY⟩ := hOther.at_exists_d hk
    have hAgree := ih X G Y G' hX hY
    exact (hRun.at_next hM.1 hs hX hAt).prefix_rows_d hM hC (hOther.at_next hM.1 hs hY hAt') hSub hAgree.1 hAgree.2

theorem LinearForest.prefix_rows {M : SetTheory.Structure.{u}} {w m n F G : M.Domain}
    (hF : LinearForest M w m F) (hG : LinearForest M w n G) (hSub : M.MemberSubset n m) : RowsAgreeOn M F G n := by
  intro c hc p
  rw [hF.2 c p,hG.2 c p]
  exact ⟨fun h => ⟨hc,h.2⟩,fun h => ⟨hSub c hc,h.2⟩⟩

theorem selected_sequence_prefix_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {m n F G V W P Q : M.Domain}
    (hF : LinearForest M C.omega m F) (hG : LinearForest M C.omega n G)
    (hP : Selects true M C m F V P) (hQ : Selects true M C n G W Q)
    (hSub : M.MemberSubset n m) (hValues : RowsAgreeOn M V W n) : RowsAgreeOn M P Q n :=
  hP.prefix_rows_d hM hC hQ hSub (hF.prefix_rows hG hSub) hValues

/-- 高度与顶部值的直接运行接口；逐行一致性由算法证明提供。 -/
theorem RowRun.height_top_prefix_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {m n : M.Domain} {R R' : RowStateSpace M.Domain}
    {V P W Q H J Heights Heights' Top Top' : M.Domain}
    (hRun : RowRun M C m R V P H) (hOther : RowRun M C n R' W Q J)
    (hSub : M.MemberSubset n m) (hValues : RowsAgreeOn M V W n) (hParents : RowsAgreeOn M P Q n)
    (hHeights : HeightGraph M C m R V H Heights) (hHeights' : HeightGraph M C n R' W J Heights')
    (hTop : TopValueGraph M C m R H Heights Top) (hTop' : TopValueGraph M C n R' J Heights' Top') :
    RowsAgreeOn M Heights Heights' n ∧ RowsAgreeOn M Top Top' n := by
  have hAgree := hRun.prefix_rows_d hM hC hOther hSub hValues hParents
  have hHH := hHeights.prefix_rows_d hM hC hRun hOther hSub hValues hAgree hHeights'
  exact ⟨hHH,hTop.prefix_rows_d hM hC hRun hOther hAgree hHH hTop'⟩

/-- 从合法序列和内部截断宽度实际构造两条相容的层塔。 -/
theorem legal_prefix_layers_exists_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {V m n : M.Domain}
    (hLegal : LegalAt M C.omega C.zero C.one V m) (hn : M.mem n C.omega) (hSub : M.MemberSubset n m) :
    ∃ W F P L H G Q L' J, Prefix M W V n C.omega ∧
      LinearForest M C.omega m F ∧ Selects true M C m F V P ∧ LayerRun M C m L V P H ∧
      LinearForest M C.omega n G ∧ Selects true M C n G W Q ∧ LayerRun M C n L' W Q J ∧
      ∀k, M.mem k C.omega → RowHistoriesAgree M L.states H L'.states J n k := by
  obtain ⟨W,hPrefix,hLegal',_⟩ := legal_prefix_d hM hC hLegal hn hSub
  obtain ⟨F,P,L,H,hF,hP,hLayers⟩ := legal_layers_exists_d hM hC hLegal
  obtain ⟨G,Q,L',J,hG,hQ,hOther⟩ := legal_layers_exists_d hM hC hLegal'
  have hValues : RowsAgreeOn M V W n := fun c hc v => (hPrefix.all_rows hM.1 hLegal.1.2 c hc v).symm
  have hParents := selected_sequence_prefix_d hM hC hF hG hP hQ hSub hValues
  exact ⟨W,F,P,L,H,G,Q,L',J,hPrefix,hF,hP,hLayers,hG,hQ,hOther,hLayers.prefix_rows_d hM hC hOther hSub hValues hParents⟩

namespace ExpressionDiagram

/-- 保留层、列和行三个真实枚举坐标；行号仍不进入根图原子。 -/
def LayerRowAtom (M : SetTheory.Structure.{u}) (C : ExpressionData M.Domain) (m : M.Domain)
    (L : LayerStateSpace M.Domain) (H k r q p c : M.Domain) : Prop :=
  ∃ W Q, RowAt M L.states H k W Q ∧ ∃ R : RowStateSpace M.Domain, ∃ J U F,
    RowRun M C m R W Q J ∧ RowAt M R.states J r U F ∧ MemPair M F c p ∧ Root M C m F c q

theorem actual_atom_iff_row {M : SetTheory.Structure.{u}} {C : ExpressionData M.Domain} {m : M.Domain}
    {L : LayerStateSpace M.Domain} {H k q p c : M.Domain} :
    ActualAtom M C m L H k q p c ↔ ∃r, LayerRowAtom M C m L H k r q p c := by
  exact ⟨fun ⟨W,Q,hL,R,J,r,U,F,hR,hA,hP,hRoot⟩ => ⟨r,W,Q,hL,R,J,U,F,hR,hA,hP,hRoot⟩,
    fun ⟨r,W,Q,hL,R,J,U,F,hR,hA,hP,hRoot⟩ => ⟨W,Q,hL,R,J,r,U,F,hR,hA,hP,hRoot⟩⟩

private theorem row_at_index_mem {M : SetTheory.Structure.{u}} (he : Extensional M)
    {S H w r V P : M.Domain} (hGraph : Graph M H w S) (hAt : RowAt M S H r V P) : M.mem r w := by
  obtain ⟨state,_,hState,_⟩ := hAt
  exact (hGraph.bounds he hState).1

theorem layer_row_atom_prefix_iff_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {m n : M.Domain} {L L' : LayerStateSpace M.Domain}
    {V P W Q H J k r q p c : M.Domain} (hLayers : LayerRun M C m L V P H) (hOther : LayerRun M C n L' W Q J)
    (hSub : M.MemberSubset n m)
    (hAgree : ∀k, M.mem k C.omega → RowHistoriesAgree M L.states H L'.states J n k) (hc : M.mem c n) :
    LayerRowAtom M C m L H k r q p c ↔ LayerRowAtom M C n L' J k r q p c := by
  constructor
  · rintro ⟨X,F,hLayer,R,HRows,U,G,hRows,hRow,hParent,hRoot⟩
    have hk := row_at_index_mem hM.1 hLayers.graph hLayer
    have hr := row_at_index_mem hM.1 hRows.graph hRow
    obtain ⟨Y,F',hLayer'⟩ := hOther.at_exists_d hk
    obtain ⟨JRows,hRows'⟩ := row_run_exists_d hM hC hOther.space.rows (hOther.at_rooted hM.1 hLayer').row
    obtain ⟨U',G',hRow'⟩ := hRows'.at_exists_d hr
    have hBase := hAgree k hk X F Y F' hLayer hLayer'
    have hAt := hRows.prefix_rows_d hM hC hRows' hSub hBase.1 hBase.2 r hr U G U' G' hRow hRow'
    exact ⟨Y,F',hLayer',L'.rows,JRows,U',G',hRows',hRow',(hAt.2 c hc p).mp hParent,
      (root_prefix_iff_d hM hC (hRows.at_numeric_d hM hC hRow).forest hOther.space.rows.width hSub hc hAt.2).mp hRoot⟩
  · rintro ⟨Y,F',hLayer',R',JRows,U',G',hRows',hRow',hParent,hRoot⟩
    have hk := row_at_index_mem hM.1 hOther.graph hLayer'
    have hr := row_at_index_mem hM.1 hRows'.graph hRow'
    obtain ⟨X,F,hLayer⟩ := hLayers.at_exists_d hk
    obtain ⟨HRows,hRows⟩ := row_run_exists_d hM hC hLayers.space.rows (hLayers.at_rooted hM.1 hLayer).row
    obtain ⟨U,G,hRow⟩ := hRows.at_exists_d hr
    have hBase := hAgree k hk X F Y F' hLayer hLayer'
    have hAt := hRows.prefix_rows_d hM hC hRows' hSub hBase.1 hBase.2 r hr U G U' G' hRow hRow'
    exact ⟨X,F,hLayer,L.rows,HRows,U,G,hRows,hRow,(hAt.2 c hc p).mpr hParent,
      (root_prefix_iff_d hM hC (hRows.at_numeric_d hM hC hRow).forest hOther.space.rows.width hSub hc hAt.2).mpr hRoot⟩

theorem actual_atom_prefix_iff_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {m n : M.Domain} {L L' : LayerStateSpace M.Domain}
    {V P W Q H J k q p c : M.Domain} (hLayers : LayerRun M C m L V P H) (hOther : LayerRun M C n L' W Q J)
    (hSub : M.MemberSubset n m)
    (hAgree : ∀k, M.mem k C.omega → RowHistoriesAgree M L.states H L'.states J n k) (hc : M.mem c n) :
    ActualAtom M C m L H k q p c ↔ ActualAtom M C n L' J k q p c := by
  simp only [actual_atom_iff_row,layer_row_atom_prefix_iff_d hM hC hLayers hOther hSub hAgree hc]

/-- 规范根图的宽度限制。此定义不要求底层边列表有字面前缀关系。 -/
structure DiagramRestriction (M : SetTheory.Structure.{u}) (D : KP1Y.Reflection.Data M.Domain)
    (m A n B : M.Domain) : Prop where
  width : M.MemberSubset n m
  edges : ∀ k q p c, KP1Y.Reflection.EdgeAt M D B k q p c ↔ M.mem c n ∧ KP1Y.Reflection.EdgeAt M D A k q p c

theorem Enumerated.prefix_restriction_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {D : KP1Y.Reflection.Data M.Domain} (hD : D.Valid M) (hOmega : D.omega=C.omega)
    {m n : M.Domain} {L L' : LayerStateSpace M.Domain} {V P W Q H J A B : M.Domain}
    (hLayers : LayerRun M C m L V P H) (hOther : LayerRun M C n L' W Q J)
    (hSub : M.MemberSubset n m)
    (hAgree : ∀k, M.mem k C.omega → RowHistoriesAgree M L.states H L'.states J n k)
    (hA : Enumerated M C T D m L V H A) (hB : Enumerated M C T D n L' W J B) : DiagramRestriction M D m A n B := by
  refine ⟨hSub,fun k q p c => ?_⟩
  rw [hA.edges_iff_d hM hC hT hD hOmega hLayers,hB.edges_iff_d hM hC hT hD hOmega hOther]
  constructor
  · intro hAtom
    have hc := (hAtom.valid_d hM hC).2.2
    exact ⟨hc,(actual_atom_prefix_iff_d hM hC hLayers hOther hSub hAgree hc).mpr hAtom⟩
  · rintro ⟨hc,hAtom⟩
    exact (actual_atom_prefix_iff_d hM hC hLayers hOther hSub hAgree hc).mp hAtom

theorem ExpressionGraph.prefix_restriction_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {D : KP1Y.Reflection.Data M.Domain} (hD : D.Valid M) (hOmega : D.omega=C.omega)
    {V W m n A B : M.Domain} (hA : ExpressionGraph M C T D V m A) (hB : ExpressionGraph M C T D W n B)
    (hSub : M.MemberSubset n m) (hValues : RowsAgreeOn M V W n) : DiagramRestriction M D m A n B := by
  obtain ⟨_,F,P,L,H,hF,hP,hLayers,hEnum⟩ := hA
  obtain ⟨_,G,Q,L',J,hG,hQ,hOther,hEnum'⟩ := hB
  have hParents := selected_sequence_prefix_d hM hC hF hG hP hQ hSub hValues
  exact hEnum.prefix_restriction_d hM hC hT hD hOmega hLayers hOther hSub
    (hLayers.prefix_rows_d hM hC hOther hSub hValues hParents) hEnum'

theorem ExpressionGraph.prefix_exists_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {D : KP1Y.Reflection.Data M.Domain} (hD : D.Valid M) (hOmega : D.omega=C.omega)
    {V m n A : M.Domain} (hA : ExpressionGraph M C T D V m A) (hn : M.mem n C.omega) (hSub : M.MemberSubset n m) :
    ∃W B, Prefix M W V n C.omega ∧ ExpressionGraph M C T D W n B ∧ DiagramRestriction M D m A n B := by
  obtain ⟨W,hW,hLegal,_⟩ := legal_prefix_d hM hC hA.1 hn hSub
  obtain ⟨B,hB⟩ := expression_graph_exists_d hM hC hT D hLegal
  exact ⟨W,B,hW,hB,hA.prefix_restriction_d hM hC hT hD hOmega hB hSub
    (fun c hc v => (hW.all_rows hM.1 hA.1.1.2 c hc v).symm)⟩

theorem RowFamily.layer_row_atom_iff_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {m : M.Domain} {L : LayerStateSpace M.Domain}
    {V P H B Histories Runs k r q p c : M.Domain} (hLayers : LayerRun M C m L V P H)
    (hFamily : RowFamily M C m L H B Histories Runs) (hk : M.mem k B) :
    RowAtom M C m L.rows Histories Runs k r q p c ↔ LayerRowAtom M C m L H k r q p c := by
  constructor
  · rintro ⟨J,_,hJ,U,_,F,_,hAt,hParent,hRoot⟩
    obtain ⟨W,Q,hLayer,hRun⟩ := hFamily.rows k J hJ
    exact ⟨W,Q,hLayer,L.rows,J,U,F,hRun,hAt,hParent,hRoot⟩
  · rintro ⟨W,Q,hLayer,R,J,U,F,hRows,hRow,hParent,hRoot⟩
    obtain ⟨J',W',Q',hJ',hRunAt,hLayer',hRows'⟩ := hFamily.at_d hk
    obtain ⟨hWW,hQQ⟩ := hLayers.at_unique hM.1 hLayer hLayer'
    subst W'
    subst Q'
    have hJJ := hRows.unique_d hM hC hRows'
    subst J'
    have hNumeric := hRows.at_numeric_d hM hC hRow
    obtain ⟨state,_,hState,hCode⟩ := hRow
    have hRow' : RowAt M L.rows.states J r U F := ⟨state,(hRows'.graph.bounds hM.1 hState).2,hState,hCode⟩
    exact ⟨J,hJ',hRunAt,U,(hLayers.space.rows.values U).mpr hNumeric.values,
      F,(hLayers.space.rows.forests F).mpr hNumeric.forest,hRow',hParent,hRoot⟩

/-- 实际稳定过滤中某个(k,c,r)位置的出现；保存过滤前后索引，重复原子不合并。 -/
def FilteredRowOccurrence (M : SetTheory.Structure.{u}) (C : ExpressionData M.Domain) (T : MatrixArithmetic M.Domain)
    (D : KP1Y.Reflection.Data M.Domain) (m B S len A I k r q p c : M.Domain) : Prop :=
  ∃ i j e, Position M C T m B S i k c r ∧ M.mem j len ∧ MemPair M I j i ∧ MemPair M A j e ∧ KP1Y.Reflection.Quad M D.pairs e k q p c

theorem filtered_row_occurrence_iff_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {D : KP1Y.Reflection.Data M.Domain} (hD : D.Valid M) (hOmega : D.omega=C.omega)
    {m B S N : M.Domain} {L : LayerStateSpace M.Domain} {V P H Histories Runs Map len A I k r q p c : M.Domain}
    (hLayers : LayerRun M C m L V P H) (hB : SequenceBound M C m V B)
    (hS : KP1Y.Arithmetic.Product M B m S) (hN : KP1Y.Arithmetic.Product M S B N)
    (hFamily : RowFamily M C m L H B Histories Runs)
    (hMap : AtomMap M C T m B S N L.rows Histories Runs D.pairs D.edgeCodes Map)
    (hFilter : Filter.Filtered M C.omega Map N D.edgeCodes len A I) :
    FilteredRowOccurrence M C T D m B S len A I k r q p c ↔ LayerRowAtom M C m L H k r q p c := by
  have hm := hLayers.space.rows.width
  have hw := omega_isOrdinal_d hM hC.omega
  have hSn := natural_product_closed_d hM hC hB.1.1 hm hS
  constructor
  · rintro ⟨i,j,e,hPos,hj,hIndex,hEntry,hQuad⟩
    have hMapAt := (hFilter.entry_iff hM.1 hMap.graph).mpr ⟨j,hj,hIndex,hEntry⟩
    obtain ⟨_,_,k',hk,c',_,r',_,q',_,p',_,hPos',hAtom,hQuad'⟩ := (hMap.rows i e).mp hMapAt
    obtain ⟨hkk,hcc,hrr⟩ := hPos.injective_d hM hC hT hm hB.1.1 hSn hPos'
    subst k'
    subst c'
    subst r'
    obtain ⟨_,hqq,hpp,_⟩ := hQuad.injective hM.1 hQuad'
    subst q'
    subst p'
    exact (hFamily.layer_row_atom_iff_d hM hC hLayers hk).mp hAtom
  · intro hAtom
    have hAtomCopy := hAtom
    obtain ⟨W,Q,hLayer,R,J,U,F,hRows,hRow,hParent,_⟩ := hAtomCopy
    obtain ⟨hk,hr⟩ := hLayers.parent_indices_below_d hM hC hB hLayer hRows hRow hParent
    have hRowAtom := (hFamily.layer_row_atom_iff_d hM hC hLayers hk).mpr hAtom
    have hValid := ((actual_atom_iff_row).mpr ⟨r,hAtom⟩).valid_d hM hC
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
    have hAt := (hMap.rows i e).mpr ⟨hi,he,k,hk,c,hc,r,hr,q,hq,p,hp,hPos,hRowAtom,hQuad⟩
    obtain ⟨j,hj,hIndex,hEntry⟩ := (hFilter.entry_iff hM.1 hMap.graph).mp hAt
    exact ⟨i,j,e,hPos,hj,hIndex,hEntry,hQuad⟩

theorem filtered_occurrences_prefix_iff_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {D : KP1Y.Reflection.Data M.Domain} (hD : D.Valid M) (hOmega : D.omega=C.omega)
    {m n B B' S S' N N' : M.Domain} {L L' : LayerStateSpace M.Domain}
    {V P W Q H J Histories Runs Histories' Runs' Map Map' len len' A A' I I' k r q p c : M.Domain}
    (hLayers : LayerRun M C m L V P H) (hOther : LayerRun M C n L' W Q J)
    (hSub : M.MemberSubset n m) (hValues : RowsAgreeOn M V W n) (hParents : RowsAgreeOn M P Q n)
    (hB : SequenceBound M C m V B) (hB' : SequenceBound M C n W B')
    (hS : KP1Y.Arithmetic.Product M B m S) (hN : KP1Y.Arithmetic.Product M S B N)
    (hS' : KP1Y.Arithmetic.Product M B' n S') (hN' : KP1Y.Arithmetic.Product M S' B' N')
    (hFamily : RowFamily M C m L H B Histories Runs) (hFamily' : RowFamily M C n L' J B' Histories' Runs')
    (hMap : AtomMap M C T m B S N L.rows Histories Runs D.pairs D.edgeCodes Map)
    (hMap' : AtomMap M C T n B' S' N' L'.rows Histories' Runs' D.pairs D.edgeCodes Map')
    (hFilter : Filter.Filtered M C.omega Map N D.edgeCodes len A I)
    (hFilter' : Filter.Filtered M C.omega Map' N' D.edgeCodes len' A' I') (hc : M.mem c n) :
    FilteredRowOccurrence M C T D m B S len A I k r q p c ↔ FilteredRowOccurrence M C T D n B' S' len' A' I' k r q p c :=
  (filtered_row_occurrence_iff_d hM hC hT hD hOmega hLayers hB hS hN hFamily hMap hFilter).trans
    ((layer_row_atom_prefix_iff_d hM hC hLayers hOther hSub (hLayers.prefix_rows_d hM hC hOther hSub hValues hParents) hc).trans
      (filtered_row_occurrence_iff_d hM hC hT hD hOmega hOther hB' hS' hN' hFamily' hMap' hFilter').symm)

/-- 同一真实坐标在稳定过滤中有唯一输出位置。 -/
theorem filtered_occurrence_index_unique_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {m B S Map N Codes len A I i i' j j' k c r : M.Domain}
    (hFilter : Filter.Filtered M C.omega Map N Codes len A I)
    (hPos : Position M C T m B S i k c r) (hPos' : Position M C T m B S i' k c r)
    (hIndex : MemPair M I j i) (hIndex' : MemPair M I j' i') : j=j' := by
  have he := hPos.unique hM.1 hT hPos'
  subst i'
  exact hFilter.index_injective_d hM hC hIndex hIndex'

/-- 不同行产生相同原子时，仍占据不同输出位置。 -/
theorem filtered_occurrence_distinct_rows_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {m B S Map N Codes len A I i i' j j' k c r r' : M.Domain}
    (hm : M.mem m C.omega) (hB : M.mem B C.omega) (hS : M.mem S C.omega)
    (hFilter : Filter.Filtered M C.omega Map N Codes len A I)
    (hPos : Position M C T m B S i k c r) (hPos' : Position M C T m B S i' k c r')
    (hIndex : MemPair M I j i) (hIndex' : MemPair M I j' i') (hDifferent : r≠r') : j≠j' := by
  intro he
  subst j'
  have hii := hFilter.indices.unique j i i' hIndex hIndex'
  subst i'
  exact hDifferent (hPos.injective_d hM hC hT hm hB hS hPos').2.2

/-- 原文 IsPrefix 的语义：宽度包含与原子包含，而非列表前缀。 -/
def DiagramIsPrefix (M : SetTheory.Structure.{u}) (D : KP1Y.Reflection.Data M.Domain) (n B m A : M.Domain) : Prop :=
  M.MemberSubset n m ∧ ∀k q p c, KP1Y.Reflection.EdgeAt M D B k q p c → KP1Y.Reflection.EdgeAt M D A k q p c

theorem DiagramRestriction.isPrefix {M : SetTheory.Structure.{u}} {D : KP1Y.Reflection.Data M.Domain}
    {m A n B : M.Domain} (h : DiagramRestriction M D m A n B) : DiagramIsPrefix M D n B m A :=
  ⟨h.width,fun k q p c hEdge => ((h.edges k q p c).mp hEdge).2⟩

theorem DiagramRestriction.representation_prefix_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {D : KP1Y.Reflection.Data M.Domain} (hD : D.Valid M) {m A n B H f g : M.Domain}
    (h : DiagramRestriction M D m A n B) (hB : KP1Y.Reflection.Diagram M D n B)
    (hRep : KP1Y.Reflection.Representation M D H m A f) (hPrefix : Prefix M g f n D.cap) :
    KP1Y.Reflection.Representation M D H n B g := by
  refine ⟨hB,⟨hB.1,hPrefix.graph,?_,?_⟩,?_⟩
  · intro i hi x hx hAt
    exact hRep.labeling.above i (h.width i hi) x hx ((hPrefix.rows i hi x hx).mp hAt)
  · intro i hi j hj hij x hx y hy hAt hAt'
    exact hRep.labeling.increasing i (h.width i hi) j (h.width j hj) hij x hx y hy
      ((hPrefix.rows i hi x hx).mp hAt) ((hPrefix.rows j hj y hy).mp hAt')
  · intro k hk q hq p hp c hc hEdge eta heta a ha b hb hfq hfp hfc
    obtain ⟨hqp,hpc,hcn⟩ := hB.2.2 k hk q hq p hp c hc hEdge
    have hnOrd := (omega_isOrdinal_d hM hD.omega).mem hB.1
    have hpn := hnOrd.transitive c hcn p hpc
    have hqn : M.mem q n := hqp.elim (fun he => he.symm ▸ hpn) (fun hlt => hnOrd.transitive p hpn q hlt)
    exact hRep.edges k hk q hq p hp c hc ((h.edges k q p c).mp hEdge).2 eta heta a ha b hb
      ((hPrefix.rows q hqn eta heta).mp hfq) ((hPrefix.rows p hpn a ha).mp hfp) ((hPrefix.rows c hcn b hb).mp hfc)

theorem DiagramRestriction.representation_exists_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {D : KP1Y.Reflection.Data M.Domain} (hD : D.Valid M) {m A n B H f : M.Domain}
    (h : DiagramRestriction M D m A n B) (hB : KP1Y.Reflection.Diagram M D n B)
    (hRep : KP1Y.Reflection.Representation M D H m A f) :
    ∃g, Prefix M g f n D.cap ∧ KP1Y.Reflection.Representation M D H n B g := by
  obtain ⟨g,hg⟩ := restrict_prefix_d hM hRep.labeling.graph h.width
  exact ⟨g,hg,h.representation_prefix_d hM hD hB hRep hg⟩

end ExpressionDiagram
end KP1Y.OneYFinite
