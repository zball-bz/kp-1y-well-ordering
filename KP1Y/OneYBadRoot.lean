import KP1Y.OneYExtractionBounds
import KP1Y.OneYNaturalDifferenceAddition
import KP1Y.RankedPacketTerms

/-! 实际差一坏根：存在条件、唯一性、有限界和集合搜索图。 -/
namespace KP1Y.OneYFinite
open YesMetaZFC YesMetaZFC.SetTheory YesMetaZFC.SetTheory.Definitional
open KP1Y.Kuratowski KP1Y.Functions KP1Y.Naturals KP1Y.Bounded KP1Y.Arithmetic KP1Y.Ranking
universe u

theorem difference_one_iff_successor_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {a b : M.Domain} (_ha : M.mem a C.omega) (hb : M.mem b C.omega) (hba : M.mem b a) :
    TruncatedDifference M C.omega C.zero a b C.one ↔ M.SuccessorOf a b := by
  have hZero := sum_zero_d hM b hC.zero_empty
  constructor
  · intro hDiff
    exact sum_successor_d hM hC.one_succ hZero (truncated_difference_add_inverse_d hM hC hDiff (Or.inr hba))
  · intro hSucc
    obtain ⟨sum,_,hSum⟩ := natural_sum_exists_d hM hC.omega hb hC.one_nat
    have hs := sum_successor_d hM hC.one_succ hZero hSum
    have he := Structure.SuccessorOf.eq hM.1 hs hSucc
    subst sum
    exact truncated_difference_of_sum_d hM hC hb hC.one_nat hSum

def RowBadAt (M : SetTheory.Structure.{u}) (C : ExpressionData M.Domain) (R : RowStateSpace M.Domain)
    (J r c p : M.Domain) : Prop :=
  ∃ U, M.mem U R.values ∧ ∃ F, M.mem F R.forests ∧ RowAt M R.states J r U F ∧ MemPair M F c p ∧
    ∃ x, M.mem x C.omega ∧ ∃ y, M.mem y C.omega ∧ MemPair M U p x ∧ MemPair M U c y ∧ M.SuccessorOf y x

def rowBadAtFormula {n : Nat} (C : ExpressionData (Project.Term n)) (R : RowStateSpace (Project.Term n))
    (J r c p : Project.Term n) : Project.Formula 1 n :=
  Project.Formula.existsMem R.values (Project.Formula.existsMem R.forests.weaken
    (.conj (rowAtFormula R.states.weaken.weaken J.weaken.weaken r.weaken.weaken (.bound 1) (.bound 0))
      (.conj (memPairFormula (.bound 0) c.weaken.weaken p.weaken.weaken)
        (Project.Formula.existsMem C.omega.weaken.weaken (Project.Formula.existsMem C.omega.weaken.weaken.weaken
          (.conj (memPairFormula (.bound 3) p.weaken.weaken.weaken.weaken (.bound 1))
            (.conj (memPairFormula (.bound 3) c.weaken.weaken.weaken.weaken (.bound 0)) (successorFormula (.bound 0) (.bound 1)))))))))

theorem rowBadAtFormula_delta0 {n : Nat} (C : ExpressionData (Project.Term n)) (R : RowStateSpace (Project.Term n))
    (J r c p : Project.Term n) : (rowBadAtFormula C R J r c p).IsDelta0 :=
  .existsMem _ (.existsMem _ (.conj (rowAtFormula_delta0 _ _ _ _ _) (.conj (memPairFormula_delta0 _ _ _)
    (.existsMem _ (.existsMem _ (.conj (memPairFormula_delta0 _ _ _) (.conj (memPairFormula_delta0 _ _ _) (successorFormula_delta0 _ _))))))))

theorem rowBadAtFormula_freeClosed {n : Nat} {C : ExpressionData (Project.Term n)} (hC : C.Closed)
    {R : RowStateSpace (Project.Term n)} (hR : R.Closed) (J r c p : Project.Term n)
    (hJ : J.freeSupport=[]) (hr : r.freeSupport=[]) (hc : c.freeSupport=[]) (hp : p.freeSupport=[]) :
    (rowBadAtFormula C R J r c p).FreeClosed := by
  simp [rowBadAtFormula,rowAtFormula,memPairFormula,codeFormula,pairFormula,successorFormula,Project.Formula.forallMem,
    Project.Formula.existsMem,Definitional.Formula.FreeClosed,hC.omega,hR.values,hR.forests,hR.states,hJ,hr,hc,hp]

theorem rowBadAtFormula_iff {M : SetTheory.Structure.{u}} (he : Extensional M) {n : Nat} (e : Env M n)
    (C : ExpressionData (Project.Term n)) (R : RowStateSpace (Project.Term n)) (J r c p : Project.Term n) :
    Project.Formula.satisfies e (rowBadAtFormula C R J r c p) ↔ RowBadAt M (C.eval e) (R.eval e) (J.eval e) (r.eval e) (c.eval e) (p.eval e) := by
  simp only [rowBadAtFormula,Project.Formula.satisfies_existsMem_iff,Project.Formula.satisfies_conj_iff,rowAtFormula_iff he,
    memPairFormula_iff he,successorFormula_iff he,Term.eval_weaken]
  rfl

def BadAt (M : SetTheory.Structure.{u}) (C : ExpressionData M.Domain) (m : M.Domain) (L : LayerStateSpace M.Domain)
    (H k r c p : M.Domain) : Prop :=
  ∃ W, M.mem W L.rows.values ∧ ∃ Q, M.mem Q L.rows.forests ∧ RowAt M L.states H k W Q ∧
    ∃ J, RowRun M C m L.rows W Q J ∧ RowBadAt M C L.rows J r c p

theorem RowRun.parent_initial_above_one_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {m : M.Domain} {R : RowStateSpace M.Domain}
    {V P J r U F c p a : M.Domain} (hRun : RowRun M C m R V P J) (hAt : RowAt M R.states J r U F)
    (hParent : MemPair M F c p) (hOriginal : MemPair M V c a) : M.mem C.one a := by
  have hRow := hRun.at_numeric_d hM hC hAt
  obtain ⟨y,hy,hY⟩ := hRow.values.total c (hRow.forest.bounds hM.1 hParent).1
  have hAbove := hRow.parent_value_above_one_d hM hC hParent hY
  have hr : M.mem r C.omega := by
    obtain ⟨_,_,hr,_⟩ := hAt
    exact (hRun.graph.bounds hM.1 hr).1
  have h0r : C.zero=r ∨ M.mem C.zero r := by
    classical
    by_cases he : r=C.zero
    · exact Or.inl he.symm
    · exact Or.inr ((hC.zero_mem_iff hM hr).mpr he)
  have hValue : RowValue M R.states R.values R.forests J r c y :=
    ⟨U,(hRun.space.values U).mpr hRow.values,F,(hRun.space.forests F).mpr hRow.forest,hAt,hY⟩
  rcases hRun.value_antitone_d hM hC hC.zero_nat hr h0r ((hRun.value_initial_iff_d hM).mpr hOriginal) hValue with he | hLess
  · exact he ▸ hAbove
  · exact ((omega_isOrdinal_d hM hC.omega).mem (hRun.base.values.bounds hM.1 hOriginal).2).transitive y hLess C.one hAbove

theorem row_bad_of_top_one_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory) {C : ExpressionData M.Domain} (hC : C.Valid M)
    {m : M.Domain} {R : RowStateSpace M.Domain} {V P J Heights Top c a : M.Domain}
    (hRun : RowRun M C m R V P J) (hBase : RootedRow M C m V P) (hHeights : HeightGraph M C m R V J Heights)
    (hTop : TopValueGraph M C m R J Heights Top) (hOriginal : MemPair M V c a) (hAbove : M.mem C.one a)
    (hOne : MemPair M Top c C.one) : ∃ r p, RowBadAt M C R J r c p := by
  have hc := (hRun.base.values.bounds hM.1 hOriginal).1
  obtain ⟨height,hh,hHeight⟩ := hHeights.graph.total c hc
  have hSome : ∃ p, MemPair M P c p := by
    classical
    apply Classical.byContradiction
    intro hNot
    have he := hBase.rootsOne c a hOriginal (fun p _ hp => hNot ⟨p,hp⟩)
    exact SetTheory.KP.mem_irrefl_d (KP1Y.models_weakKP hM) C.one (he ▸ hAbove)
  have hHeightPos := (hRun.parent_iff_lt_height_d hM hC (hRun.initial_row_at_d hM) hOriginal (hBase.positive c a hOriginal)
    ((hHeights.rows c height).mp hHeight).2).mp hSome
  rcases natural_cases hM hC.omega hh with hEmpty | ⟨r,hr,hs⟩
  · exact False.elim (hEmpty C.zero hHeightPos)
  · obtain ⟨U,F,hAt⟩ := hRun.at_exists_d hr
    obtain ⟨U',F',hAt'⟩ := hRun.at_exists_d hh
    have hNext := hRun.at_next hM.1 hs hAt hAt'
    have hRow := hRun.at_numeric_d hM hC hAt
    obtain ⟨p,hParent⟩ := (hRun.parent_iff_lt_height_d hM hC hAt hOriginal (hBase.positive c a hOriginal)
      ((hHeights.rows c height).mp hHeight).2).mpr hs.predecessor_mem
    obtain ⟨height',_,hHeight',hTopOne⟩ := (hTop.rows c C.one).mp hOne
    have hhe := hHeights.graph.unique c height' height hHeight' hHeight
    subst height'
    obtain ⟨W,_,Q,_,hAtOne,hOneValue⟩ := hTopOne
    obtain ⟨hWU,_⟩ := hRun.at_unique hM.1 hAtOne hAt'
    subst W
    obtain ⟨x,hx,hX⟩ := hRow.values.total p (hRow.forest.bounds hM.1 hParent).2
    obtain ⟨y,hy,hY⟩ := hRow.values.total c hc
    have hDiff := hNext.difference.at_parent_d hM hRow.values hRow.forest hParent hY hX hOneValue
    have hSucc := (difference_one_iff_successor_d hM hC hy hx (hRow.parentValues c p x y hParent hX hY).2).mp hDiff
    exact ⟨r,p,U,(hRun.space.values U).mpr hRow.values,F,(hRun.space.forests F).mpr hRow.forest,hAt,hParent,x,hx,y,hy,hX,hY,hSucc⟩

theorem row_bad_height_top_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory) {C : ExpressionData M.Domain} (hC : C.Valid M)
    {m : M.Domain} {R : RowStateSpace M.Domain} {V P J Heights Top r c p height : M.Domain}
    (hRun : RowRun M C m R V P J) (hBase : RootedRow M C m V P) (hHeights : HeightGraph M C m R V J Heights)
    (hTop : TopValueGraph M C m R J Heights Top) (hBad : RowBadAt M C R J r c p) (hHeight : MemPair M Heights c height) :
    M.SuccessorOf height r ∧ MemPair M Top c C.one := by
  obtain ⟨U,_,F,_,hAt,hParent,x,hx,y,hy,hX,hY,hValueSucc⟩ := hBad
  have hr : M.mem r C.omega := by
    obtain ⟨_,_,hAt,_⟩ := hAt
    exact (hRun.graph.bounds hM.1 hAt).1
  obtain ⟨r',hs,hr'⟩ := hC.omega.1.2 r hr
  obtain ⟨U',F',hAt'⟩ := hRun.at_exists_d hr'
  have hRow := hRun.at_numeric_d hM hC hAt
  have hRow' := hRun.at_numeric_d hM hC hAt'
  have hNext := hRun.at_next hM.1 hs hAt hAt'
  have hc := (hRow.forest.bounds hM.1 hParent).1
  obtain ⟨d,_,hD⟩ := hRow'.values.total c hc
  have hDiff := hNext.difference.at_parent_d hM hRow.values hRow.forest hParent hY hX hD
  have hDiffOne := (difference_one_iff_successor_d hM hC hy hx (hRow.parentValues c p x y hParent hX hY).2).mpr hValueSucc
  have hd := truncated_difference_unique_d hM hC hDiff hDiffOne
  have hOne : MemPair M U' c C.one := hd ▸ hD
  have hValue : RowValue M R.states R.values R.forests J r' c C.one :=
    ⟨U',(hRun.space.values U').mpr hRow'.values,F',(hRun.space.forests F').mpr hRow'.forest,hAt',hOne⟩
  obtain ⟨a,_,hA⟩ := hRun.base.values.total c hc
  have hLe := (hRun.live_iff_le_height_d hM hC hA (hBase.positive c a hA) ((hHeights.rows c height).mp hHeight).2 hr').mp
    ⟨C.one,hC.one_nat,hValue,hC.one_succ.predecessor_mem⟩
  have hNot : ¬M.mem r' height := by
    intro hlt
    obtain ⟨q,hP⟩ := (hRun.parent_iff_lt_height_d hM hC hAt' hA (hBase.positive c a hA) ((hHeights.rows c height).mp hHeight).2).mpr hlt
    exact SetTheory.KP.mem_irrefl_d (KP1Y.models_weakKP hM) C.one (hRow'.parent_value_above_one_d hM hC hP hOne)
  have hrh := hLe.resolve_right hNot
  have hTopOne : MemPair M Top c C.one := (hTop.rows c C.one).mpr
    ⟨height,(hHeights.graph.bounds hM.1 hHeight).2,hHeight,hrh ▸ hValue⟩
  exact ⟨hrh ▸ hs,hTopOne⟩

theorem BadAt.layer_value_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory) {C : ExpressionData M.Domain} (hC : C.Valid M)
    {m : M.Domain} {L : LayerStateSpace M.Domain} {H k r c p : M.Domain} (hBad : BadAt M C m L H k r c p) :
    ∃ a, M.mem a C.omega ∧ LayerValue M L H k c a ∧ M.mem C.one a := by
  obtain ⟨W,hW,Q,hQ,hLayer,J,hRun,hBad⟩ := hBad
  obtain ⟨U,_,F,_,hRow,hParent,_⟩ := hBad
  have hc := ((hRun.at_numeric_d hM hC hRow).forest.bounds hM.1 hParent).1
  obtain ⟨a,ha,hA⟩ := hRun.base.values.total c hc
  exact ⟨a,ha,⟨W,hW,Q,hQ,hLayer,hA⟩,hRun.parent_initial_above_one_d hM hC hRow hParent hA⟩

theorem BadAt.bounds_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory) {C : ExpressionData M.Domain} (hC : C.Valid M)
    {m : M.Domain} {L : LayerStateSpace M.Domain} {V P H B k r c p : M.Domain} (hLayers : LayerRun M C m L V P H)
    (hB : SequenceBound M C m V B) (hBad : BadAt M C m L H k r c p) : M.mem k B ∧ M.mem r B ∧ M.mem p c ∧ M.mem c m := by
  obtain ⟨W,_,Q,_,hLayer,J,hRun,U,_,F,_,hRow,hParent,_⟩ := hBad
  obtain ⟨hk,hr⟩ := hLayers.parent_indices_below_d hM hC hB hLayer hRun hRow hParent
  have hF := (hRun.at_numeric_d hM hC hRow).forest
  exact ⟨hk,hr,hF.left c p hParent,(hF.bounds hM.1 hParent).1⟩

theorem BadAt.in_run_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory) {C : ExpressionData M.Domain} (hC : C.Valid M)
    {m : M.Domain} {L : LayerStateSpace M.Domain} {V P H k r c p W Q J : M.Domain} (hLayers : LayerRun M C m L V P H)
    (hBad : BadAt M C m L H k r c p) (hLayer : RowAt M L.states H k W Q) (hRun : RowRun M C m L.rows W Q J) :
    RowBadAt M C L.rows J r c p := by
  obtain ⟨W',_,Q',_,hLayer',J',hRun',hRowBad⟩ := hBad
  obtain ⟨hWW,hQQ⟩ := hLayers.at_unique hM.1 hLayer' hLayer
  subst W'
  subst Q'
  have hJJ := hRun'.unique_d hM hC hRun
  subst J'
  exact hRowBad

theorem BadAt.next_layer_one_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory) {C : ExpressionData M.Domain} (hC : C.Valid M)
    {m : M.Domain} {L : LayerStateSpace M.Domain} {V P H k k' r c p : M.Domain} (hLayers : LayerRun M C m L V P H)
    (hBad : BadAt M C m L H k r c p) (hSucc : M.SuccessorOf k' k) : LayerValue M L H k' c C.one := by
  obtain ⟨W,hW,Q,hQ,hLayer,J,hRun,hRowBad⟩ := hBad
  have hk : M.mem k C.omega := by
    obtain ⟨_,_,hAt,_⟩ := hLayer
    exact (hLayers.graph.bounds hM.1 hAt).1
  obtain ⟨Top,Q',hLayer'⟩ := hLayers.at_exists_d (natural_successor_mem_d hM hC hk hSucc)
  have hExtract := hLayers.at_next hM.1 hSucc hLayer hLayer'
  obtain ⟨R,J',Heights,F,hRun',hHeights,hTop,hF,hSelected⟩ := hExtract
  have hRR := row_state_space_unique hM.1 hRun'.space hLayers.space.rows
  subst R
  have hJJ := hRun'.unique_d hM hC hRun
  subst J'
  have hc : M.mem c m := by
    obtain ⟨U,_,F',_,hRow,hParent,_⟩ := hRowBad
    exact ((hRun.at_numeric_d hM hC hRow).forest.bounds hM.1 hParent).1
  obtain ⟨height,_,hHeight⟩ := hHeights.graph.total c hc
  have hOne := (row_bad_height_top_d hM hC hRun (hLayers.at_rooted hM.1 hLayer) hHeights hTop hRowBad hHeight).2
  exact ⟨Top,(hLayers.space.rows.values Top).mpr hTop.graph,Q',(hLayers.space.rows.forests Q').mpr hSelected.forest,hLayer',hOne⟩

private theorem one_le_of_positive {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {v : M.Domain} (hv : M.mem v C.omega) (hPos : M.mem C.zero v) : C.one=v ∨ M.mem C.one v := by
  have hω := omega_isOrdinal_d hM hC.omega
  apply ordinal_subset_cases_d hM (hω.mem hC.one_nat) (hω.mem hv)
  intro x hx
  rcases (hC.one_succ x).mp hx with hEmpty | he
  · exact False.elim (hC.zero_empty x hEmpty)
  · exact (hM.1.eq_of_same_members x C.zero he).symm ▸ hPos

private def aboveOneLayerSchema : Project.Delta0UnarySchema 7 where
  body := liveRowFormula (.bound 7) (.bound 6) (.bound 5) (.bound 4) (.bound 3) (.bound 2) (.bound 1) (.bound 0)
  freeClosed := liveRowFormula_freeClosed _ _ _ _ _ _ _ _ rfl rfl rfl rfl rfl rfl rfl rfl
  delta0 := liveRowFormula_delta0 _ _ _ _ _ _ _ _

theorem bad_at_exists_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory) {C : ExpressionData M.Domain} (hC : C.Valid M)
    {m : M.Domain} {L : LayerStateSpace M.Domain} {V P H c a : M.Domain} (hLayers : LayerRun M C m L V P H)
    (hOriginal : MemPair M V c a) (hAbove : M.mem C.one a) : ∃ k r p, BadAt M C m L H k r c p := by
  obtain ⟨B,hB⟩ := sequence_bound_exists_d hM hC hLayers.space.rows.width hLayers.base.row.values
  let e := ((((((oneEnv C.omega).push C.one).push L.states).push L.rows.values).push L.rows.forests).push H).push c
  obtain ⟨Candidates,hCandidates⟩ := SetTheory.KP.separation_exists_d (KP1Y.models_weakKP hM) aboveOneLayerSchema e B
  have hφ (k : M.Domain) : Project.Formula.satisfies (e.push k) aboveOneLayerSchema.body ↔
      ∃ v, M.mem v C.omega ∧ LayerValue M L H k c v ∧ M.mem C.one v := liveRowFormula_iff hM.1 _ _ _ _ _ _ _ _ _
  have hRows (k : M.Domain) : M.mem k Candidates ↔ M.mem k B ∧ ∃ v, M.mem v C.omega ∧ LayerValue M L H k c v ∧ M.mem C.one v := by
    simpa only [hφ] using hCandidates k
  have hZeroCandidate := (hRows C.zero).mpr ⟨hB.1.2.1,a,(hLayers.base.row.values.bounds hM.1 hOriginal).2,
    (hLayers.value_initial_iff_d hM).mpr hOriginal,hAbove⟩
  obtain ⟨k,hMax⟩ := greatest_below_exists_d (A := Candidates) hM hC.omega hB.1.1 ⟨C.zero,hB.1.2.1,hZeroCandidate⟩
  have hk := (omega_isOrdinal_d hM hC.omega).transitive B hB.1.1 k hMax.1
  obtain ⟨_,v,hv,hValue,hAboveV⟩ := (hRows k).mp hMax.2.1
  obtain ⟨k',hSucc,hk'⟩ := hC.omega.1.2 k hk
  obtain ⟨next,hNextNat,hNextValue⟩ := hLayers.value_exists_d hM.1 hk' (hLayers.base.row.values.bounds hM.1 hOriginal).1
  have hNextOne : next=C.one := by
    rcases one_le_of_positive hM hC hNextNat (hLayers.value_positive hM.1 hNextValue) with he | hNextAbove
    · exact he.symm
    · have hk'a := hLayers.above_one_layer_lt_initial_d hM hC hk' hNextValue hOriginal hNextAbove
      have hk'B := ((omega_isOrdinal_d hM hC.omega).mem hB.1.1).transitive a (hB.value_lt hM.1 hLayers.base.row.values hOriginal) k' hk'a
      have hCand := (hRows k').mpr ⟨hk'B,next,hNextNat,hNextValue,hNextAbove⟩
      rcases hMax.2.2 k' hk'B hCand with he | hLess
      · exact False.elim (SetTheory.KP.mem_irrefl_d (KP1Y.models_weakKP hM) k (he ▸ hSucc.predecessor_mem))
      · exact False.elim (SetTheory.KP.mem_irrefl_d (KP1Y.models_weakKP hM) k'
          (((omega_isOrdinal_d hM hC.omega).mem hk').transitive k hSucc.predecessor_mem k' hLess))
  obtain ⟨W,hW,Q,hQ,hLayer,hWv⟩ := hValue
  obtain ⟨Top,_,Q',_,hLayer',hTopValue⟩ := hNextValue
  have hExtraction := hLayers.at_next hM.1 hSucc hLayer hLayer'
  obtain ⟨R,J,Heights,F,hRun,hHeights,hTop,hF,hSelected⟩ := hExtraction
  have hRR := row_state_space_unique hM.1 hRun.space hLayers.space.rows
  subst R
  obtain ⟨r,p,hBad⟩ := row_bad_of_top_one_d hM hC hRun (hLayers.at_rooted hM.1 hLayer) hHeights hTop hWv hAboveV (hNextOne ▸ hTopValue)
  exact ⟨k,r,p,W,hW,Q,hQ,hLayer,J,hRun,hBad⟩

theorem BadAt.layer_natural {M : SetTheory.Structure.{u}} (he : Extensional M) {C : ExpressionData M.Domain}
    {m : M.Domain} {L : LayerStateSpace M.Domain} {V P H k r c p : M.Domain} (hLayers : LayerRun M C m L V P H)
    (hBad : BadAt M C m L H k r c p) : M.mem k C.omega := by
  obtain ⟨_,_,_,_,hLayer,_,_⟩ := hBad
  obtain ⟨_,_,hAt,_⟩ := hLayer
  exact (hLayers.graph.bounds he hAt).1

theorem BadAt.row_natural {M : SetTheory.Structure.{u}} (he : Extensional M) {C : ExpressionData M.Domain}
    {m : M.Domain} {L : LayerStateSpace M.Domain} {H k r c p : M.Domain} (hBad : BadAt M C m L H k r c p) : M.mem r C.omega := by
  obtain ⟨_,_,_,_,_,_,hRun,hRowBad⟩ := hBad
  obtain ⟨_,_,_,_,hRow,_⟩ := hRowBad
  obtain ⟨_,_,hAt,_⟩ := hRow
  exact (hRun.graph.bounds he hAt).1

private theorem bad_layers_not_lt_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory) {C : ExpressionData M.Domain} (hC : C.Valid M)
    {m : M.Domain} {L : LayerStateSpace M.Domain} {V P H k r p ell s q c : M.Domain} (hLayers : LayerRun M C m L V P H)
    (hBad : BadAt M C m L H k r c p) (hBad' : BadAt M C m L H ell s c q) (hlt : M.mem k ell) : False := by
  have hk := hBad.layer_natural hM.1 hLayers
  have hEll := hBad'.layer_natural hM.1 hLayers
  obtain ⟨k',hSucc,hk'⟩ := hC.omega.1.2 k hk
  have hOne := hBad.next_layer_one_d hM hC hLayers hSucc
  obtain ⟨a,ha,hValue,hAbove⟩ := hBad'.layer_value_d hM hC
  have hLe : k'=ell ∨ M.mem k' ell := by
    have hEllOrd := (omega_isOrdinal_d hM hC.omega).mem hEll
    apply ordinal_subset_cases_d hM ((omega_isOrdinal_d hM hC.omega).mem hk') hEllOrd
    intro x hx
    rcases (hSucc x).mp hx with hxk | he
    · exact hEllOrd.transitive k hlt x hxk
    · exact (hM.1.eq_of_same_members x k he).symm ▸ hlt
  rcases hLayers.value_antitone_d hM hC hk' hEll hLe hOne hValue with he | hLess
  · exact SetTheory.KP.mem_irrefl_d (KP1Y.models_weakKP hM) C.one (he ▸ hAbove)
  · exact SetTheory.KP.mem_irrefl_d (KP1Y.models_weakKP hM) a
      (((omega_isOrdinal_d hM hC.omega).mem ha).transitive C.one hAbove a hLess)

theorem BadAt.unique_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory) {C : ExpressionData M.Domain} (hC : C.Valid M)
    {m : M.Domain} {L : LayerStateSpace M.Domain} {V P H k r p ell s q c : M.Domain} (hLayers : LayerRun M C m L V P H)
    (hBad : BadAt M C m L H k r c p) (hBad' : BadAt M C m L H ell s c q) : k=ell ∧ r=s ∧ p=q := by
  have hkEll : k=ell := by
    rcases (omega_isOrdinal_d hM hC.omega).wellOrder.linear.compare k (hBad.layer_natural hM.1 hLayers) ell (hBad'.layer_natural hM.1 hLayers) with he | hlt | hgt
    · exact hM.1.eq_of_same_members k ell he
    · exact False.elim (bad_layers_not_lt_d hM hC hLayers hBad hBad' hlt)
    · exact False.elim (bad_layers_not_lt_d hM hC hLayers hBad' hBad hgt)
  subst ell
  have hr := hBad.row_natural hM.1
  obtain ⟨W,_,Q,_,hLayer,J,hRun,hRowBad⟩ := hBad
  obtain ⟨W',_,Q',_,hLayer',J',hRun',hRowBad'⟩ := hBad'
  obtain ⟨hWW,hQQ⟩ := hLayers.at_unique hM.1 hLayer hLayer'
  subst W'
  subst Q'
  have hJJ := hRun.unique_d hM hC hRun'
  subst J'
  obtain ⟨Heights,Top,hHeights,hTop⟩ := mountain_height_top_exists_d hM hC hRun
  have hc : M.mem c m := by
    obtain ⟨U,_,F,_,hAt,hParent,_⟩ := hRowBad
    exact ((hRun.at_numeric_d hM hC hAt).forest.bounds hM.1 hParent).1
  obtain ⟨height,_,hHeight⟩ := hHeights.graph.total c hc
  have hSucc := (row_bad_height_top_d hM hC hRun (hLayers.at_rooted hM.1 hLayer) hHeights hTop hRowBad hHeight).1
  have hSucc' := (row_bad_height_top_d hM hC hRun (hLayers.at_rooted hM.1 hLayer) hHeights hTop hRowBad' hHeight).1
  have hrs := Structure.SuccessorOf.predecessor_eq hM.1 ((omega_isOrdinal_d hM hC.omega).mem hr) hSucc hSucc'
  subst s
  obtain ⟨U,_,F,_,hAt,hParent,_⟩ := hRowBad
  obtain ⟨U',_,F',_,hAt',hParent',_⟩ := hRowBad'
  obtain ⟨hUU,hFF⟩ := hRun.at_unique hM.1 hAt hAt'
  subst U'
  subst F'
  exact ⟨rfl,rfl,(hRun.at_numeric_d hM hC hAt).forest.unique c p q hParent hParent'⟩

theorem bad_at_exists_iff_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory) {C : ExpressionData M.Domain} (hC : C.Valid M)
    {m : M.Domain} {L : LayerStateSpace M.Domain} {V P H c a : M.Domain} (hLayers : LayerRun M C m L V P H)
    (hOriginal : MemPair M V c a) : (∃ k r p, BadAt M C m L H k r c p) ↔ M.mem C.one a := by
  constructor
  · rintro ⟨k,r,p,hBad⟩
    obtain ⟨b,_,hValue,hAbove⟩ := hBad.layer_value_d hM hC
    rcases hLayers.value_le_initial_d hM hC (hBad.layer_natural hM.1 hLayers) hOriginal hValue with he | hLess
    · exact he ▸ hAbove
    · exact ((omega_isOrdinal_d hM hC.omega).mem (hLayers.base.row.values.bounds hM.1 hOriginal).2).transitive b hLess C.one hAbove
  · exact bad_at_exists_d hM hC hLayers hOriginal

theorem BadAt.successor_layer_lt_initial_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory) {C : ExpressionData M.Domain} (hC : C.Valid M)
    {m : M.Domain} {L : LayerStateSpace M.Domain} {V P H k k' r c p a : M.Domain} (hLayers : LayerRun M C m L V P H)
    (hBad : BadAt M C m L H k r c p) (hOriginal : MemPair M V c a) (hSucc : M.SuccessorOf k' k) : M.mem k' a := by
  have hk := hBad.layer_natural hM.1 hLayers
  have hk' := natural_successor_mem_d hM hC hk hSucc
  have ha := (hLayers.base.row.values.bounds hM.1 hOriginal).2
  obtain ⟨v,_,hValue,hAbove⟩ := hBad.layer_value_d hM hC
  obtain ⟨d,hd,hD⟩ := truncated_difference_exists_d hM hC ha hk
  obtain ⟨d',hd',hD'⟩ := truncated_difference_exists_d hM hC ha hk'
  have hLe := hLayers.above_one_fuel_bound_d hM hC hk hValue hOriginal hD hAbove
  have hAboveD : M.mem C.one d := by
    rcases hLe with he | hLess
    · exact he ▸ hAbove
    · exact ((omega_isOrdinal_d hM hC.omega).mem hd).transitive v hLess C.one hAbove
  have hka := hLayers.above_one_layer_lt_initial_d hM hC hk hValue hOriginal hAbove
  have hSuccD := truncated_difference_successor_of_lt_d hM hC hSucc hka hD hD'
  have hPositive := (natural_successor_lt_iff hM hC hd' hC.zero_nat hSuccD hC.one_succ).mp hAboveD
  exact (truncated_difference_positive_iff_d hM hC hD').mp hPositive

private def badRootTerms : ExpressionData (Project.Term 22) := ⟨.bound 21,.bound 20,.bound 19,.bound 18,.bound 17⟩
private def badRootSpaceTerms : RowStateSpace (Project.Term 22) := ⟨.bound 15,.bound 14,.bound 13⟩

/-- 坏根搜索的唯一无界见证是实际行运行 J；全部索引和其余字段有界。 -/
def badRootMatrix : KP1Y.WitnessMatrix 14 where
  body := Project.Formula.existsMem (.bound 5) (Project.Formula.existsMem (.bound 6)
    (Project.Formula.existsMem (.bound 13) (Project.Formula.existsMem (.bound 13) (Project.Formula.existsMem (.bound 13)
      (.conj (packetFormula (.bound 6) (.bound 4) (.bound 3) (.bound 2))
        (.conj (rowAtFormula (.bound 12) (.bound 11) (.bound 4) (.bound 1) (.bound 0))
          (.conj (rootedRowFormula badRootTerms (.bound 16) (.bound 1) (.bound 0))
            (.conj (rowRunFormula badRootTerms (.bound 16) badRootSpaceTerms (.bound 9) (.bound 8) (.bound 1) (.bound 0) (.bound 5))
              (rowBadAtFormula badRootTerms badRootSpaceTerms (.bound 5) (.bound 3) (.bound 7) (.bound 2))))))))))
  freeClosed := by
    have hC : badRootTerms.Closed := ⟨rfl,rfl,rfl,rfl,rfl⟩
    have hR : badRootSpaceTerms.Closed := ⟨rfl,rfl,rfl⟩
    have hRooted := rootedRowFormula_freeClosed hC (.bound 16) (.bound 1) (.bound 0) rfl rfl rfl
    have hRun := rowRunFormula_freeClosed hC hR (.bound 16) (.bound 9) (.bound 8) (.bound 1) (.bound 0) (.bound 5)
      rfl rfl rfl rfl rfl rfl
    have hBad := rowBadAtFormula_freeClosed hC hR (.bound 5) (.bound 3) (.bound 7) (.bound 2) rfl rfl rfl rfl
    simp [Project.Formula.existsMem,Definitional.Formula.FreeClosed,packetFormula,rowAtFormula,memPairFormula,codeFormula,pairFormula,
      Project.Formula.forallMem,hRooted,hRun,hBad]
  delta0 := .existsMem _ (.existsMem _ (.existsMem _ (.existsMem _ (.existsMem _
    (.conj (packetFormula_delta0 _ _ _ _) (.conj (rowAtFormula_delta0 _ _ _ _ _) (.conj (rootedRowFormula_delta0 _ _ _ _)
      (.conj (rowRunFormula_delta0 _ _ _ _ _ _ _ _) (rowBadAtFormula_delta0 _ _ _ _ _ _)))))))))

def badRootEnv {M : SetTheory.Structure.{u}} (C : ExpressionData M.Domain) (m : M.Domain) (L : LayerStateSpace M.Domain)
    (H B Pairs Table : M.Domain) : Env M 14 :=
  (((((((((((((oneEnv C.omega).push C.zero).push C.one).push C.sequences).push C.expressions).push m).push L.rows.values).push L.rows.forests).push L.rows.states).push L.states).push H).push B).push Pairs).push Table

theorem badRootMatrix_iff {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory) {C : ExpressionData M.Domain} (hC : C.Valid M)
    {m : M.Domain} {L : LayerStateSpace M.Domain} (hL : L.Valid M C m) {H B Pairs Table : M.Domain}
    (hTable : DifferenceTable M C Pairs Table) (c packet J : M.Domain) :
    Project.Formula.satisfies ((((badRootEnv C m L H B Pairs Table).push c).push packet).push J) badRootMatrix.body ↔
      ∃ k, M.mem k B ∧ ∃ r, M.mem r B ∧ ∃ p, M.mem p m ∧ ∃ W, M.mem W L.rows.values ∧ ∃ Q, M.mem Q L.rows.forests ∧
        Packet M packet k r p ∧ RowAt M L.states H k W Q ∧ RootedRow M C m W Q ∧
          RowRun M C m L.rows W Q J ∧ RowBadAt M C L.rows J r c p := by
  let e := (((badRootEnv C m L H B Pairs Table).push c).push packet).push J
  have hRun (k r p W Q : M.Domain) (hBase : RootedRow M C m W Q) := rowRunFormula_iff hM
    (((((e.push k).push r).push p).push W).push Q) badRootTerms (.bound 16) badRootSpaceTerms (.bound 9) (.bound 8)
    (.bound 1) (.bound 0) (.bound 5) hC hL.rows hTable hBase.row
  simp only [badRootMatrix,Project.Formula.satisfies_existsMem_iff,Project.Formula.satisfies_conj_iff,
    packetFormula_iff hM.1,rowAtFormula_iff hM.1,rootedRowFormula_iff hM.1,rowBadAtFormula_iff hM.1]
  constructor
  · rintro ⟨k,hk,r,hr,p,hp,W,hW,Q,hQ,hPacket,hLayer,hBase,hRunSat,hBad⟩
    exact ⟨k,hk,r,hr,p,hp,W,hW,Q,hQ,hPacket,hLayer,hBase,(hRun k r p W Q hBase).mp hRunSat,hBad⟩
  · rintro ⟨k,hk,r,hr,p,hp,W,hW,Q,hQ,hPacket,hLayer,hBase,hRunProof,hBad⟩
    exact ⟨k,hk,r,hr,p,hp,W,hW,Q,hQ,hPacket,hLayer,hBase,(hRun k r p W Q hBase).mpr hRunProof,hBad⟩

theorem badRootMatrix_exists_iff_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory) {C : ExpressionData M.Domain} (hC : C.Valid M)
    {m : M.Domain} {L : LayerStateSpace M.Domain} {V P H B Pairs Table : M.Domain} (hLayers : LayerRun M C m L V P H)
    (hB : SequenceBound M C m V B) (hTable : DifferenceTable M C Pairs Table) (c packet : M.Domain) :
    (∃ J, Project.Formula.satisfies ((((badRootEnv C m L H B Pairs Table).push c).push packet).push J) badRootMatrix.body) ↔
      ∃ k r p, Packet M packet k r p ∧ BadAt M C m L H k r c p := by
  constructor
  · rintro ⟨J,hCert⟩
    obtain ⟨k,_,r,_,p,_,W,hW,Q,hQ,hPacket,hLayer,_,hRun,hBad⟩ := (badRootMatrix_iff hM hC hLayers.space hTable c packet J).mp hCert
    exact ⟨k,r,p,hPacket,W,hW,Q,hQ,hLayer,J,hRun,hBad⟩
  · rintro ⟨k,r,p,hPacket,hBad⟩
    obtain ⟨hk,hr,hpc,hc⟩ := hBad.bounds_d hM hC hLayers hB
    have hp := ((omega_isOrdinal_d hM hC.omega).mem hLayers.space.rows.width).transitive c hc p hpc
    obtain ⟨W,hW,Q,hQ,hLayer,J,hRun,hRowBad⟩ := hBad
    exact ⟨J,(badRootMatrix_iff hM hC hLayers.space hTable c packet J).mpr
      ⟨k,hk,r,hr,p,hp,W,hW,Q,hQ,hPacket,hLayer,hLayers.at_rooted hM.1 hLayer,hRun,hRowBad⟩⟩

private def badColumnsSchema : Project.Delta0UnarySchema 3 where
  body := Project.Formula.existsMem (.bound 3) (.conj (memPairFormula (.bound 2) (.bound 1) (.bound 0)) (.mem (.bound 3) (.bound 0)))
  freeClosed := by
    simp [memPairFormula,codeFormula,pairFormula,Project.Formula.forallMem,Project.Formula.existsMem,Definitional.Formula.FreeClosed]
  delta0 := .existsMem _ (.conj (memPairFormula_delta0 _ _ _) (.mem _ _))

theorem bad_root_search_exists_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory) {C : ExpressionData M.Domain} (hC : C.Valid M)
    {m : M.Domain} {L : LayerStateSpace M.Domain} {V P H B : M.Domain} (hLayers : LayerRun M C m L V P H) (hB : SequenceBound M C m V B) :
    ∃ Columns RowParentPairs Packets Search,
      (∀ c, M.mem c Columns ↔ M.mem c m ∧ ∃ a, M.mem a C.omega ∧ MemPair M V c a ∧ M.mem C.one a) ∧
      IsProduct M RowParentPairs B m ∧ IsProduct M Packets B RowParentPairs ∧ Graph M Search Columns Packets ∧
      ∀ c packet, MemPair M Search c packet ↔ ∃ k r p, Packet M packet k r p ∧ BadAt M C m L H k r c p := by
  obtain ⟨Columns,hColumns⟩ := SetTheory.KP.separation_exists_d (KP1Y.models_weakKP hM) badColumnsSchema
    (((oneEnv C.omega).push C.one).push V) m
  have hColFormula (c : M.Domain) : Project.Formula.satisfies ((((oneEnv C.omega).push C.one).push V).push c) badColumnsSchema.body ↔
      ∃ a, M.mem a C.omega ∧ MemPair M V c a ∧ M.mem C.one a := by
    simp only [badColumnsSchema,Project.Formula.satisfies_existsMem_iff,Project.Formula.satisfies_conj_iff,
      memPairFormula_iff hM.1,Project.Formula.satisfies_mem_iff]
    rfl
  have hCols (c : M.Domain) : M.mem c Columns ↔ M.mem c m ∧ ∃ a, M.mem a C.omega ∧ MemPair M V c a ∧ M.mem C.one a := by
    simpa only [hColFormula] using hColumns c
  obtain ⟨RowParentPairs,hRP⟩ := product_exists hM B m
  obtain ⟨Packets,hPackets⟩ := product_exists hM B RowParentPairs
  obtain ⟨Pairs,Table,hTable⟩ := difference_table_exists_d hM hC
  let e := badRootEnv C m L H B Pairs Table
  have hPacketMem {packet k r p c : M.Domain} (hCode : Packet M packet k r p) (hBad : BadAt M C m L H k r c p) : M.mem packet Packets := by
    obtain ⟨hk,hr,hpc,hc⟩ := hBad.bounds_d hM hC hLayers hB
    have hp := ((omega_isOrdinal_d hM hC.omega).mem hLayers.space.rows.width).transitive c hc p hpc
    obtain ⟨rp,hOuter,hInner⟩ := hCode
    exact (hPackets packet).mpr ⟨k,hk,rp,(hRP rp).mpr ⟨r,hr,p,hp,hInner⟩,hOuter⟩
  obtain ⟨Search,hGraph,hRows⟩ := sigma_function_graph_d hM badRootMatrix e Columns Packets
    (fun c hc => by
      obtain ⟨_,a,_,hA,hAbove⟩ := (hCols c).mp hc
      obtain ⟨k,r,p,hBad⟩ := bad_at_exists_d hM hC hLayers hA hAbove
      obtain ⟨packet,hPacket⟩ := packet_exists_d hM k r p
      obtain ⟨J,hJ⟩ := (badRootMatrix_exists_iff_d hM hC hLayers hB hTable c packet).mpr ⟨k,r,p,hPacket,hBad⟩
      exact ⟨packet,J,hJ⟩)
    (fun c _ packet J hJ => by
      obtain ⟨k,r,p,hPacket,hBad⟩ := (badRootMatrix_exists_iff_d hM hC hLayers hB hTable c packet).mp ⟨J,hJ⟩
      exact hPacketMem hPacket hBad)
    (fun c _ packet packet' J J' hJ hJ' => by
      obtain ⟨k,r,p,hPacket,hBad⟩ := (badRootMatrix_exists_iff_d hM hC hLayers hB hTable c packet).mp ⟨J,hJ⟩
      obtain ⟨k',r',p',hPacket',hBad'⟩ := (badRootMatrix_exists_iff_d hM hC hLayers hB hTable c packet').mp ⟨J',hJ'⟩
      obtain ⟨hkk,hrr,hpp⟩ := hBad.unique_d hM hC hLayers hBad'
      subst k'
      subst r'
      subst p'
      exact hPacket.unique hM.1 hPacket')
  refine ⟨Columns,RowParentPairs,Packets,Search,hCols,hRP,hPackets,hGraph,?_⟩
  intro c packet
  have hr := hRows c packet
  rw [badRootMatrix_exists_iff_d hM hC hLayers hB hTable] at hr
  refine hr.trans ⟨fun h => h.2.2,?_⟩
  rintro ⟨k,r,p,hPacket,hBad⟩
  have hc := (hBad.bounds_d hM hC hLayers hB).2.2.2
  obtain ⟨a,ha,hA⟩ := hLayers.base.row.values.total c hc
  have hAbove := (bad_at_exists_iff_d hM hC hLayers hA).mp ⟨k,r,p,hBad⟩
  exact ⟨(hCols c).mpr ⟨hc,a,ha,hA,hAbove⟩,hPacketMem hPacket hBad,k,r,p,hPacket,hBad⟩

theorem BadAt.height_step_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory) {C : ExpressionData M.Domain} (hC : C.Valid M)
    {m : M.Domain} {L : LayerStateSpace M.Domain} {V P H k r c p W Q J Heights height : M.Domain}
    (hLayers : LayerRun M C m L V P H) (hBad : BadAt M C m L H k r c p) (hLayer : RowAt M L.states H k W Q)
    (hRun : RowRun M C m L.rows W Q J) (hHeights : HeightGraph M C m L.rows W J Heights)
    (hHeight : MemPair M Heights c height) : M.SuccessorOf height r := by
  obtain ⟨Top,hTop⟩ := top_value_graph_exists_d hM hC hRun hHeights
  exact (row_bad_height_top_d hM hC hRun (hLayers.at_rooted hM.1 hLayer) hHeights hTop
    (hBad.in_run_d hM hC hLayers hLayer hRun) hHeight).1

end KP1Y.OneYFinite
