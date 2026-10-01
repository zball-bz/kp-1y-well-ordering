import KP1Y.OneYMountainLayers
import KP1Y.FiniteNaturalRange

/-! 内部提取层的有限预算与规范统一界；坏根搜索在独立模块中处理。 -/
namespace KP1Y.OneYFinite
open YesMetaZFC YesMetaZFC.SetTheory YesMetaZFC.SetTheory.Definitional
open KP1Y.Kuratowski KP1Y.Functions KP1Y.Naturals KP1Y.Bounded
universe u

def LayerValue (M : SetTheory.Structure.{u}) (L : LayerStateSpace M.Domain) (H k c v : M.Domain) : Prop :=
  RowValue M L.states L.rows.values L.rows.forests H k c v

theorem LayerValue.bounds {M : SetTheory.Structure.{u}} (he : Extensional M) {C : ExpressionData M.Domain}
    {m : M.Domain} {L : LayerStateSpace M.Domain} (hL : L.Valid M C m) {H k c v : M.Domain}
    (h : LayerValue M L H k c v) : M.mem c m ∧ M.mem v C.omega := by
  obtain ⟨W,hW,_,_,_,hAt⟩ := h
  exact ((hL.rows.values W).mp hW).bounds he hAt

theorem LayerRun.value_exists_d {M : SetTheory.Structure.{u}} (he : Extensional M) {C : ExpressionData M.Domain}
    {m : M.Domain} {L : LayerStateSpace M.Domain} {V P H k c : M.Domain} (h : LayerRun M C m L V P H)
    (hk : M.mem k C.omega) (hc : M.mem c m) : ∃ v, M.mem v C.omega ∧ LayerValue M L H k c v := by
  obtain ⟨W,Q,hAt⟩ := h.at_exists_d hk
  have hRow := h.at_rooted he hAt
  obtain ⟨v,hv,hValue⟩ := hRow.row.values.total c hc
  exact ⟨v,hv,W,(h.space.rows.values W).mpr hRow.row.values,Q,(h.space.rows.forests Q).mpr hRow.row.forest,hAt,hValue⟩

theorem LayerRun.value_unique {M : SetTheory.Structure.{u}} (he : Extensional M) {C : ExpressionData M.Domain}
    {m : M.Domain} {L : LayerStateSpace M.Domain} {V P H k c x y : M.Domain} (h : LayerRun M C m L V P H)
    (hx : LayerValue M L H k c x) (hy : LayerValue M L H k c y) : x=y := by
  obtain ⟨W,hW,Q,_,hAt,hX⟩ := hx
  obtain ⟨W',_,Q',_,hAt',hY⟩ := hy
  have hWW := (h.at_unique he hAt hAt').1
  subst W'
  exact ((h.space.rows.values W).mp hW).unique c x y hX hY

theorem LayerRun.value_positive {M : SetTheory.Structure.{u}} (he : Extensional M) {C : ExpressionData M.Domain}
    {m : M.Domain} {L : LayerStateSpace M.Domain} {V P H k c v : M.Domain} (h : LayerRun M C m L V P H)
    (hValue : LayerValue M L H k c v) : M.mem C.zero v := by
  obtain ⟨W,_,Q,_,hAt,hV⟩ := hValue
  exact (h.at_rooted he hAt).positive c v hV

theorem LayerRun.value_initial_iff_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory) {C : ExpressionData M.Domain}
    {m : M.Domain} {L : LayerStateSpace M.Domain} {V P H c v : M.Domain} (h : LayerRun M C m L V P H) :
    LayerValue M L H C.zero c v ↔ MemPair M V c v := by
  constructor
  · rintro ⟨W,_,Q,_,hAt,hV⟩
    have hWV := (h.at_unique hM.1 hAt (h.initial_at_d hM)).1
    subst W
    exact hV
  · intro hV
    exact ⟨V,(h.space.rows.values V).mpr h.base.row.values,P,(h.space.rows.forests P).mpr h.base.row.forest,h.initial_at_d hM,hV⟩

theorem LayerRun.value_successor_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory) {C : ExpressionData M.Domain} (hC : C.Valid M)
    {m : M.Domain} {L : LayerStateSpace M.Domain} {V P H k k' c x y : M.Domain} (h : LayerRun M C m L V P H)
    (hs : M.SuccessorOf k' k) (hx : LayerValue M L H k c x) (hy : LayerValue M L H k' c y) :
    (y=x ∨ M.mem y x) ∧ (M.mem C.one x → M.mem y x) := by
  obtain ⟨W,_,Q,_,hAt,hX⟩ := hx
  obtain ⟨W',_,Q',_,hAt',hY⟩ := hy
  have hNext := h.at_next hM.1 hs hAt hAt'
  exact ⟨hNext.value_le_d hM hC hX hY,fun hAbove => hNext.value_lt_above_one_d hM hC (h.at_rooted hM.1 hAt) hX hAbove hY⟩

private def layerBoundEnv {M : SetTheory.Structure.{u}} (C : ExpressionData M.Domain) (m : M.Domain)
    (L : LayerStateSpace M.Domain) (V H : M.Domain) : Env M 9 :=
  ((((((((oneEnv C.omega).push C.zero).push C.one).push L.states).push L.rows.values).push L.rows.forests).push m).push V).push H

private def layerFuelSchema : Project.UnarySchema 9 where
  body := Project.Formula.forallMem (.bound 3) (Project.Formula.forallMem (.bound 10)
    (Project.Formula.forallMem (.bound 11) (Project.Formula.forallMem (.bound 12)
      (.imp (.conj (rowValueFormula (.bound 10) (.bound 9) (.bound 8) (.bound 5) (.bound 4) (.bound 3) (.bound 2))
        (.conj (memPairFormula (.bound 6) (.bound 3) (.bound 1))
          (.conj (differenceFormula (.bound 13) (.bound 12) (.bound 1) (.bound 4) (.bound 0)) (.mem (.bound 11) (.bound 2)))))
        (.disj (Project.Formula.extensionalEq (.bound 2) (.bound 0)) (.mem (.bound 2) (.bound 0)))))))
  freeClosed := by
    have hValue := rowValueFormula_freeClosed (n := 14) (.bound 10) (.bound 9) (.bound 8) (.bound 5) (.bound 4) (.bound 3) (.bound 2)
      rfl rfl rfl rfl rfl rfl rfl
    have hDiff := differenceFormula_freeClosed (n := 14) (.bound 13) (.bound 12) (.bound 1) (.bound 4) (.bound 0) rfl rfl rfl rfl rfl
    simp [Project.Formula.forallMem,Definitional.Formula.FreeClosed,memPairFormula,codeFormula,pairFormula,Project.Formula.existsMem,hValue,hDiff]

private theorem layerFuelSchema_iff {M : SetTheory.Structure.{u}} (he : Extensional M)
    (C : ExpressionData M.Domain) (m : M.Domain) (L : LayerStateSpace M.Domain) (V H k : M.Domain) :
    Project.Formula.satisfies ((layerBoundEnv C m L V H).push k) layerFuelSchema.body ↔
      ∀ c, M.mem c m → ∀ v, M.mem v C.omega → ∀ a, M.mem a C.omega → ∀ d, M.mem d C.omega →
        LayerValue M L H k c v → MemPair M V c a → TruncatedDifference M C.omega C.zero a k d →
          M.mem C.one v → v=d ∨ M.mem v d := by
  simp only [layerFuelSchema,Project.Formula.satisfies_forallMem_iff,Project.Formula.satisfies_imp_iff,
    Project.Formula.satisfies_conj_iff,rowValueFormula_iff he,memPairFormula_iff he,differenceFormula_iff he,
    Project.Formula.satisfies_mem_iff,Project.Formula.satisfies_disj_iff,Project.Formula.satisfies_extensionalEq_iff_eq he,and_imp]
  rfl

theorem LayerRun.above_one_fuel_bound_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {m : M.Domain} {L : LayerStateSpace M.Domain}
    {V P H k c v a d : M.Domain} (h : LayerRun M C m L V P H) (hk : M.mem k C.omega)
    (hValue : LayerValue M L H k c v) (hOriginal : MemPair M V c a)
    (hDiff : TruncatedDifference M C.omega C.zero a k d) (hAbove : M.mem C.one v) : v=d ∨ M.mem v d := by
  have hω := omega_isOrdinal_d hM hC.omega
  have hAll := natural_induction_d hM layerFuelSchema (layerBoundEnv C m L V H) hC.omega
    (fun z hz => (layerFuelSchema_iff hM.1 C m L V H z).mpr (by
      have hzz := hM.1.eq_of_same_members z C.zero (fun x => iff_of_false (hz x) (hC.zero_empty x))
      subst z
      intro c _ v _ a ha d _ hValue hOriginal hDiff _
      have hva := h.base.row.values.unique c v a ((h.value_initial_iff_d hM).mp hValue) hOriginal
      have hda := truncated_difference_unique_d hM hC hDiff (truncated_difference_zero_d hM hC ha)
      exact Or.inl (hva.trans hda.symm)))
    (fun k hk ih k' hs => (layerFuelSchema_iff hM.1 C m L V H k').mpr (by
      intro c hc v _ a ha d _ hValue hOriginal hDiff hAbove
      obtain ⟨x,hx,hPrev⟩ := h.value_exists_d hM.1 hk hc
      have hStep := h.value_successor_d hM hC hs hPrev hValue
      have hxAbove : M.mem C.one x := by
        rcases hStep.1 with he | hvx
        · exact he ▸ hAbove
        · exact (hω.mem hx).transitive v hvx C.one hAbove
      obtain ⟨fuel,hFuel,hBefore⟩ := truncated_difference_exists_d hM hC ha hk
      have hLe := (layerFuelSchema_iff hM.1 C m L V H k).mp ih c hc x hx a ha fuel hFuel hPrev hOriginal hBefore hxAbove
      have hxPos := (hω.mem hx).transitive C.one hxAbove C.zero hC.one_succ.predecessor_mem
      have hFuelPos : M.mem C.zero fuel := by
        rcases hLe with he | hxf
        · exact he ▸ hxPos
        · exact (hω.mem hFuel).transitive x hxf C.zero hxPos
      have hka := (truncated_difference_positive_iff_d hM hC hBefore).mp hFuelPos
      have hFuelSucc := truncated_difference_successor_of_lt_d hM hC hs hka hBefore hDiff
      have hvFuel : M.mem v fuel := by
        rcases hLe with he | hxf
        · exact he ▸ hStep.2 hxAbove
        · exact (hω.mem hFuel).transitive x hxf v (hStep.2 hxAbove)
      rcases (hFuelSucc v).mp hvFuel with hvd | he
      · exact Or.inr hvd
      · exact Or.inl (hM.1.eq_of_same_members v d he)))
  exact (layerFuelSchema_iff hM.1 C m L V H k).mp (hAll k hk) c (hValue.bounds hM.1 h.space).1
    v (hValue.bounds hM.1 h.space).2 a (h.base.row.values.bounds hM.1 hOriginal).2 d (truncated_difference_natural hM.1 hDiff)
    hValue hOriginal hDiff hAbove

theorem LayerRun.above_one_layer_lt_initial_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {m : M.Domain} {L : LayerStateSpace M.Domain}
    {V P H k c v a : M.Domain} (h : LayerRun M C m L V P H) (hk : M.mem k C.omega)
    (hValue : LayerValue M L H k c v) (hOriginal : MemPair M V c a) (hAbove : M.mem C.one v) : M.mem k a := by
  obtain ⟨d,hd,hDiff⟩ := truncated_difference_exists_d hM hC (h.base.row.values.bounds hM.1 hOriginal).2 hk
  have hLe := h.above_one_fuel_bound_d hM hC hk hValue hOriginal hDiff hAbove
  have hPos := h.value_positive hM.1 hValue
  have hdPos : M.mem C.zero d := by
    rcases hLe with he | hvd
    · exact he ▸ hPos
    · exact ((omega_isOrdinal_d hM hC.omega).mem hd).transitive v hvd C.zero hPos
  exact (truncated_difference_positive_iff_d hM hC hDiff).mp hdPos

private theorem one_le_of_positive {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {v : M.Domain} (hv : M.mem v C.omega) (hPos : M.mem C.zero v) : C.one=v ∨ M.mem C.one v := by
  have hω := omega_isOrdinal_d hM hC.omega
  apply ordinal_subset_cases_d hM (hω.mem hC.one_nat) (hω.mem hv)
  intro x hx
  rcases (hC.one_succ x).mp hx with hEmpty | he
  · exact False.elim (hC.zero_empty x hEmpty)
  · exact (hM.1.eq_of_same_members x C.zero he).symm ▸ hPos

theorem LayerRun.value_one_of_bound_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {m : M.Domain} {L : LayerStateSpace M.Domain}
    {V P H k c v a : M.Domain} (h : LayerRun M C m L V P H) (hk : M.mem k C.omega)
    (hValue : LayerValue M L H k c v) (hOriginal : MemPair M V c a) (hNot : ¬M.mem k a) : v=C.one := by
  rcases one_le_of_positive hM hC (hValue.bounds hM.1 h.space).2 (h.value_positive hM.1 hValue) with he | hAbove
  · exact he.symm
  · exact False.elim (hNot (h.above_one_layer_lt_initial_d hM hC hk hValue hOriginal hAbove))

private def layerAntitoneSchema : Project.UnarySchema 9 where
  body := Project.Formula.forallMem (.bound 9) (Project.Formula.forallMem (.bound 4)
    (Project.Formula.forallMem (.bound 11) (Project.Formula.forallMem (.bound 12)
      (.imp (.disj (Project.Formula.extensionalEq (.bound 3) (.bound 4)) (.mem (.bound 3) (.bound 4)))
        (.imp (rowValueFormula (.bound 10) (.bound 9) (.bound 8) (.bound 5) (.bound 3) (.bound 2) (.bound 1))
          (.imp (rowValueFormula (.bound 10) (.bound 9) (.bound 8) (.bound 5) (.bound 4) (.bound 2) (.bound 0))
            (.disj (Project.Formula.extensionalEq (.bound 0) (.bound 1)) (.mem (.bound 0) (.bound 1)))))))))
  freeClosed := by
    have hX := rowValueFormula_freeClosed (n := 14) (.bound 10) (.bound 9) (.bound 8) (.bound 5) (.bound 3) (.bound 2) (.bound 1)
      rfl rfl rfl rfl rfl rfl rfl
    have hY := rowValueFormula_freeClosed (n := 14) (.bound 10) (.bound 9) (.bound 8) (.bound 5) (.bound 4) (.bound 2) (.bound 0)
      rfl rfl rfl rfl rfl rfl rfl
    simp [Project.Formula.forallMem,Definitional.Formula.FreeClosed,hX,hY]

private theorem layerAntitoneSchema_iff {M : SetTheory.Structure.{u}} (he : Extensional M)
    (C : ExpressionData M.Domain) (m : M.Domain) (R : LayerStateSpace M.Domain) (V H r : M.Domain) :
    Project.Formula.satisfies ((layerBoundEnv C m R V H).push r) layerAntitoneSchema.body ↔
      ∀ i, M.mem i C.omega → ∀ c, M.mem c m → ∀ x, M.mem x C.omega → ∀ y, M.mem y C.omega →
        (i=r ∨ M.mem i r) → LayerValue M R H i c x →
          LayerValue M R H r c y → y=x ∨ M.mem y x := by
  simp only [layerAntitoneSchema,Project.Formula.satisfies_forallMem_iff,Project.Formula.satisfies_imp_iff,
    Project.Formula.satisfies_disj_iff,Project.Formula.satisfies_extensionalEq_iff_eq he,Project.Formula.satisfies_mem_iff,rowValueFormula_iff he]
  rfl

theorem LayerRun.value_antitone_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {m : M.Domain} {R : LayerStateSpace M.Domain}
    {V P H i r c x y : M.Domain} (h : LayerRun M C m R V P H) (hi : M.mem i C.omega) (hr : M.mem r C.omega)
    (hir : i=r ∨ M.mem i r) (hX : LayerValue M R H i c x)
    (hY : LayerValue M R H r c y) : y=x ∨ M.mem y x := by
  have hω := omega_isOrdinal_d hM hC.omega
  have hAll := natural_induction_d hM layerAntitoneSchema (layerBoundEnv C m R V H) hC.omega
    (fun z hz => (layerAntitoneSchema_iff hM.1 C m R V H z).mpr (by
      intro i _ c _ x _ y _ hi hX hY
      have hiz := hi.resolve_right (hz i)
      subst i
      exact Or.inl (h.value_unique hM.1 hY hX)))
    (fun r hr ih r' hs => (layerAntitoneSchema_iff hM.1 C m R V H r').mpr (by
      intro i hi c hc x hx y _ hir hX hY
      rcases hir with he | hir
      · subst i
        exact Or.inl (h.value_unique hM.1 hY hX)
      · have hiLe : i=r ∨ M.mem i r := by
          rcases (hs i).mp hir with hir | he
          · exact Or.inr hir
          · exact Or.inl (hM.1.eq_of_same_members i r he)
        obtain ⟨z,hz,hZ⟩ := h.value_exists_d hM.1 hr hc
        have hzx := (layerAntitoneSchema_iff hM.1 C m R V H r).mp ih i hi c hc x hx z hz hiLe hX hZ
        have hyz := (h.value_successor_d hM hC hs hZ hY).1
        rcases hyz with he | hyz
        · exact he.symm ▸ hzx
        · rcases hzx with he | hzx
          · exact Or.inr (he ▸ hyz)
          · exact Or.inr ((hω.mem hx).transitive z hzx y hyz)))
  exact (layerAntitoneSchema_iff hM.1 C m R V H r).mp (hAll r hr) i hi c (hX.bounds hM.1 h.space).1
    x (hX.bounds hM.1 h.space).2 y (hY.bounds hM.1 h.space).2 hir hX hY

theorem LayerRun.value_le_initial_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory) {C : ExpressionData M.Domain} (hC : C.Valid M)
    {m : M.Domain} {L : LayerStateSpace M.Domain} {V P H k c a v : M.Domain} (h : LayerRun M C m L V P H)
    (hk : M.mem k C.omega) (hOriginal : MemPair M V c a) (hValue : LayerValue M L H k c v) : v=a ∨ M.mem v a := by
  have h0k : C.zero=k ∨ M.mem C.zero k := by
    classical
    by_cases hk0 : k=C.zero
    · exact Or.inl hk0.symm
    · exact Or.inr ((hC.zero_mem_iff hM hk).mpr hk0)
  exact h.value_antitone_d hM hC hC.zero_nat hk h0k ((h.value_initial_iff_d hM).mpr hOriginal) hValue

def StrictSequenceBound (M : SetTheory.Structure.{u}) (w zero m V B : M.Domain) : Prop :=
  M.mem B w ∧ M.mem zero B ∧ ∀ i, M.mem i m → ∀ a, M.mem a w → MemPair M V i a → M.mem a B

def SequenceBound (M : SetTheory.Structure.{u}) (C : ExpressionData M.Domain) (m V B : M.Domain) : Prop :=
  StrictSequenceBound M C.omega C.zero m V B ∧
    ∀ b, M.mem b C.omega → StrictSequenceBound M C.omega C.zero m V b → B=b ∨ M.mem B b

def strictSequenceBoundFormula {n : Nat} (w zero m V B : Project.Term n) : Project.Formula 1 n :=
  .conj (.mem B w) (.conj (.mem zero B) (Project.Formula.forallMem m (Project.Formula.forallMem w.weaken
    (.imp (memPairFormula V.weaken.weaken (.bound 1) (.bound 0)) (.mem (.bound 0) B.weaken.weaken)))))

def sequenceBoundFormula {n : Nat} (w zero m V B : Project.Term n) : Project.Formula 1 n :=
  .conj (strictSequenceBoundFormula w zero m V B) (Project.Formula.forallMem w
    (.imp (strictSequenceBoundFormula w.weaken zero.weaken m.weaken V.weaken (.bound 0))
      (.disj (Project.Formula.extensionalEq B.weaken (.bound 0)) (.mem B.weaken (.bound 0)))))

theorem strictSequenceBoundFormula_delta0 {n : Nat} (w zero m V B : Project.Term n) : (strictSequenceBoundFormula w zero m V B).IsDelta0 :=
  .conj (.mem _ _) (.conj (.mem _ _) (.forallMem _ (.forallMem _ (.imp (memPairFormula_delta0 _ _ _) (.mem _ _)))))

theorem sequenceBoundFormula_delta0 {n : Nat} (w zero m V B : Project.Term n) : (sequenceBoundFormula w zero m V B).IsDelta0 :=
  .conj (strictSequenceBoundFormula_delta0 _ _ _ _ _) (.forallMem _ (.imp (strictSequenceBoundFormula_delta0 _ _ _ _ _)
    (.disj (.atom _ _ _) (.mem _ _))))

theorem strictSequenceBoundFormula_freeClosed {n : Nat} (w zero m V B : Project.Term n)
    (hw : w.freeSupport=[]) (hz : zero.freeSupport=[]) (hm : m.freeSupport=[]) (hV : V.freeSupport=[]) (hB : B.freeSupport=[]) :
    (strictSequenceBoundFormula w zero m V B).FreeClosed := by
  simp [strictSequenceBoundFormula,memPairFormula,codeFormula,pairFormula,Project.Formula.forallMem,
    Project.Formula.existsMem,Definitional.Formula.FreeClosed,hw,hz,hm,hV,hB]

theorem sequenceBoundFormula_freeClosed {n : Nat} (w zero m V B : Project.Term n)
    (hw : w.freeSupport=[]) (hz : zero.freeSupport=[]) (hm : m.freeSupport=[]) (hV : V.freeSupport=[]) (hB : B.freeSupport=[]) :
    (sequenceBoundFormula w zero m V B).FreeClosed := by
  simp [sequenceBoundFormula,strictSequenceBoundFormula,memPairFormula,codeFormula,pairFormula,Project.Formula.forallMem,
    Project.Formula.existsMem,Definitional.Formula.FreeClosed,hw,hz,hm,hV,hB]

theorem strictSequenceBoundFormula_iff {M : SetTheory.Structure.{u}} (he : Extensional M) {n : Nat} (e : Env M n)
    (w zero m V B : Project.Term n) : Project.Formula.satisfies e (strictSequenceBoundFormula w zero m V B) ↔
      StrictSequenceBound M (w.eval e) (zero.eval e) (m.eval e) (V.eval e) (B.eval e) := by
  simp only [strictSequenceBoundFormula,Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_mem_iff,
    Project.Formula.satisfies_forallMem_iff,Project.Formula.satisfies_imp_iff,memPairFormula_iff he,Term.eval_weaken]
  rfl

theorem sequenceBoundFormula_iff {M : SetTheory.Structure.{u}} (he : Extensional M) {n : Nat} (e : Env M n)
    (C : ExpressionData (Project.Term n)) (m V B : Project.Term n) :
    Project.Formula.satisfies e (sequenceBoundFormula C.omega C.zero m V B) ↔ SequenceBound M (C.eval e) (m.eval e) (V.eval e) (B.eval e) := by
  simp only [sequenceBoundFormula,Project.Formula.satisfies_conj_iff,strictSequenceBoundFormula_iff he,
    Project.Formula.satisfies_forallMem_iff,Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_disj_iff,
    Project.Formula.satisfies_extensionalEq_iff_eq he,Project.Formula.satisfies_mem_iff,Term.eval_weaken]
  rfl

private def strictBoundSchema : Project.Delta0UnarySchema 4 where
  body := strictSequenceBoundFormula (.bound 4) (.bound 3) (.bound 2) (.bound 1) (.bound 0)
  freeClosed := strictSequenceBoundFormula_freeClosed _ _ _ _ _ rfl rfl rfl rfl rfl
  delta0 := strictSequenceBoundFormula_delta0 _ _ _ _ _

theorem sequence_bound_exists_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory) {C : ExpressionData M.Domain} (hC : C.Valid M)
    {m V : M.Domain} (hm : M.mem m C.omega) (hV : Graph M V m C.omega) : ∃ B, SequenceBound M C m V B := by
  obtain ⟨b,hb,hValues⟩ := finite_natural_range_bounded_d hM hC.omega hm hV
  obtain ⟨b',hSucc,hb'⟩ := hC.omega.1.2 b hb
  have hZero : M.mem C.zero b' := by
    classical
    by_cases hb0 : b=C.zero
    · exact hb0 ▸ hSucc.predecessor_mem
    · exact (hSucc C.zero).mpr (Or.inl ((hC.zero_mem_iff hM hb).mpr hb0))
  have hBound : StrictSequenceBound M C.omega C.zero m V b' :=
    ⟨hb',hZero,fun i _ a _ hAt => (hSucc a).mpr (Or.inl (hValues i a hAt))⟩
  let e := (((oneEnv C.omega).push C.zero).push m).push V
  obtain ⟨Bounds,hBounds⟩ := SetTheory.KP.separation_exists_d (KP1Y.models_weakKP hM) strictBoundSchema e C.omega
  have hφ (a : M.Domain) : Project.Formula.satisfies (e.push a) strictBoundSchema.body ↔ StrictSequenceBound M C.omega C.zero m V a :=
    strictSequenceBoundFormula_iff hM.1 _ _ _ _ _ _
  have hRows (a : M.Domain) : M.mem a Bounds ↔ StrictSequenceBound M C.omega C.zero m V a := by
    have hr := hBounds a
    rw [hφ] at hr
    exact hr.trans ⟨And.right,fun h => ⟨h.1,h⟩⟩
  obtain ⟨B,hB,hLeast⟩ := (omega_isOrdinal_d hM hC.omega).wellOrder.least Bounds
    (fun a ha => ((hRows a).mp ha).1) ⟨b',(hRows b').mpr hBound⟩
  refine ⟨B,(hRows B).mp hB,?_⟩
  intro a _ hA
  rcases hLeast a ((hRows a).mpr hA) with he | hlt
  · exact Or.inl (hM.1.eq_of_same_members B a he)
  · exact Or.inr hlt

theorem SequenceBound.unique_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory) {C : ExpressionData M.Domain} (hC : C.Valid M)
    {m V B D : M.Domain} (hB : SequenceBound M C m V B) (hD : SequenceBound M C m V D) : B=D := by
  rcases hB.2 D hD.1.1 hD.1 with he | hBD
  · exact he
  · rcases hD.2 B hB.1.1 hB.1 with he | hDB
    · exact he.symm
    · exact False.elim (SetTheory.KP.mem_irrefl_d (KP1Y.models_weakKP hM) B
        (((omega_isOrdinal_d hM hC.omega).mem hB.1.1).transitive D hDB B hBD))

theorem SequenceBound.value_lt {M : SetTheory.Structure.{u}} (he : Extensional M) {C : ExpressionData M.Domain}
    {m V B c a : M.Domain} (hV : Graph M V m C.omega) (hB : SequenceBound M C m V B) (hAt : MemPair M V c a) : M.mem a B :=
  hB.1.2.2 c (hV.bounds he hAt).1 a (hV.bounds he hAt).2 hAt

theorem SequenceBound.empty_eq_one_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory) {C : ExpressionData M.Domain} (hC : C.Valid M)
    {m V B : M.Domain} (hB : SequenceBound M C m V B) (hEmpty : ∀ c, ¬M.mem c m) : B=C.one := by
  have hOne : StrictSequenceBound M C.omega C.zero m V C.one :=
    ⟨hC.one_nat,hC.one_succ.predecessor_mem,fun c hc _ _ _ => False.elim (hEmpty c hc)⟩
  rcases hB.2 C.one hC.one_nat hOne with he | hlt
  · exact he
  · rcases (hC.one_succ B).mp hlt with hB0 | he
    · exact False.elim (hC.zero_empty B hB0)
    · exact False.elim (hC.zero_empty C.zero ((hM.1.eq_of_same_members B C.zero he) ▸ hB.1.2.1))

theorem SequenceBound.predecessor_max_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory) {C : ExpressionData M.Domain} (hC : C.Valid M)
    {m V B : M.Domain} (hV : Graph M V m C.omega) (hB : SequenceBound M C m V B) (hNe : ∃ c, M.mem c m) :
    ∃ a, M.mem a C.omega ∧ M.SuccessorOf B a ∧ (∃ c, M.mem c m ∧ MemPair M V c a) ∧
      ∀ c v, MemPair M V c v → v=a ∨ M.mem v a := by
  rcases natural_cases hM hC.omega hB.1.1 with hEmpty | ⟨a,ha,hSucc⟩
  · exact False.elim (hEmpty C.zero hB.1.2.1)
  · have hUpper (c v : M.Domain) (hAt : MemPair M V c v) : v=a ∨ M.mem v a := by
      rcases (hSucc v).mp (hB.value_lt hM.1 hV hAt) with hva | he
      · exact Or.inr hva
      · exact Or.inl (hM.1.eq_of_same_members v a he)
    have hSome : ∃ c, M.mem c m ∧ MemPair M V c a := by
      classical
      apply Classical.byContradiction
      intro hNot
      have hStrict (c v : M.Domain) (hAt : MemPair M V c v) : M.mem v a :=
        (hUpper c v hAt).resolve_left (fun he => hNot ⟨c,(hV.bounds hM.1 hAt).1,he ▸ hAt⟩)
      by_cases ha0 : a=C.zero
      · obtain ⟨c,hc⟩ := hNe
        obtain ⟨v,_,hAt⟩ := hV.total c hc
        exact hC.zero_empty v (ha0 ▸ hStrict c v hAt)
      · have hA : StrictSequenceBound M C.omega C.zero m V a :=
          ⟨ha,(hC.zero_mem_iff hM ha).mpr ha0,fun c _ v _ hAt => hStrict c v hAt⟩
        rcases hB.2 a ha hA with he | hBa
        · exact SetTheory.KP.mem_irrefl_d (KP1Y.models_weakKP hM) a (he ▸ hSucc.predecessor_mem)
        · exact SetTheory.KP.mem_irrefl_d (KP1Y.models_weakKP hM) B
            (((omega_isOrdinal_d hM hC.omega).mem hB.1.1).transitive a hSucc.predecessor_mem B hBa)
    exact ⟨a,ha,hSucc,hSome,hUpper⟩

theorem NumericRow.parent_value_above_one_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {m V P c p y : M.Domain} (hRow : NumericRow M C m V P)
    (hParent : MemPair M P c p) (hY : MemPair M V c y) : M.mem C.one y := by
  obtain ⟨x,hx,hX⟩ := hRow.values.total p (hRow.forest.bounds hM.1 hParent).2
  have hVals := hRow.parentValues c p x y hParent hX hY
  rcases one_le_of_positive hM hC hx hVals.1 with he | hOne
  · exact he.symm ▸ hVals.2
  · exact ((omega_isOrdinal_d hM hC.omega).mem (hRow.values.bounds hM.1 hY).2).transitive x hVals.2 C.one hOne

theorem RowRun.no_parent_of_initial_one_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {m : M.Domain} {R : RowStateSpace M.Domain}
    {V P H r W Q c : M.Domain} (hRun : RowRun M C m R V P H) (hOriginal : MemPair M V c C.one)
    (hAt : RowAt M R.states H r W Q) : NoParent M m Q c := by
  intro p _ hParent
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
  have hValue : RowValue M R.states R.values R.forests H r c y :=
    ⟨W,(hRun.space.values W).mpr hRow.values,Q,(hRun.space.forests Q).mpr hRow.forest,hAt,hY⟩
  have hLe := hRun.value_antitone_d hM hC hC.zero_nat hr h0r ((hRun.value_initial_iff_d hM).mpr hOriginal) hValue
  rcases hLe with he | hLess
  · exact SetTheory.KP.mem_irrefl_d (KP1Y.models_weakKP hM) C.one (he ▸ hAbove)
  · exact SetTheory.KP.mem_irrefl_d (KP1Y.models_weakKP hM) y
      (((omega_isOrdinal_d hM hC.omega).mem hy).transitive C.one hAbove y hLess)

theorem LayerRun.all_one_from_bound_predecessor_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {m : M.Domain} {L : LayerStateSpace M.Domain}
    {V P H B a k c v : M.Domain} (hRun : LayerRun M C m L V P H) (hB : SequenceBound M C m V B)
    (hSucc : M.SuccessorOf B a) (hk : M.mem k C.omega) (hLe : a=k ∨ M.mem a k) (hValue : LayerValue M L H k c v) : v=C.one := by
  obtain ⟨original,_,hOriginal⟩ := hRun.base.row.values.total c (hValue.bounds hM.1 hRun.space).1
  apply hRun.value_one_of_bound_d hM hC hk hValue hOriginal
  intro hkOriginal
  have hka : M.mem k a := by
    rcases (hSucc original).mp (hB.value_lt hM.1 hRun.base.row.values hOriginal) with hOrigA | he
    · exact (((omega_isOrdinal_d hM hC.omega).mem hB.1.1).mem hSucc.predecessor_mem).transitive original hOrigA k hkOriginal
    · exact hM.1.eq_of_same_members original a he ▸ hkOriginal
  rcases hLe with he | hak
  · exact SetTheory.KP.mem_irrefl_d (KP1Y.models_weakKP hM) k (he ▸ hka)
  · exact SetTheory.KP.mem_irrefl_d (KP1Y.models_weakKP hM) k
      (((omega_isOrdinal_d hM hC.omega).mem hk).transitive a hak k hka)

theorem LayerRun.all_one_above_bound_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {m : M.Domain} {L : LayerStateSpace M.Domain}
    {V P H B k c v : M.Domain} (hRun : LayerRun M C m L V P H) (hB : SequenceBound M C m V B)
    (hk : M.mem k C.omega) (hNot : ¬M.mem k B) (hValue : LayerValue M L H k c v) : v=C.one := by
  obtain ⟨original,_,hOriginal⟩ := hRun.base.row.values.total c (hValue.bounds hM.1 hRun.space).1
  apply hRun.value_one_of_bound_d hM hC hk hValue hOriginal
  intro hko
  exact hNot (((omega_isOrdinal_d hM hC.omega).mem hB.1.1).transitive original
    (hB.value_lt hM.1 hRun.base.row.values hOriginal) k hko)

theorem LayerRun.parent_indices_below_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {m : M.Domain} {L : LayerStateSpace M.Domain}
    {V P H B k W Q : M.Domain} (hLayers : LayerRun M C m L V P H) (hB : SequenceBound M C m V B)
    (hLayer : RowAt M L.states H k W Q) {R : RowStateSpace M.Domain} {J r U F c p : M.Domain}
    (hRows : RowRun M C m R W Q J) (hRow : RowAt M R.states J r U F) (hParent : MemPair M F c p) : M.mem k B ∧ M.mem r B := by
  have hLayerBase := hLayers.at_rooted hM.1 hLayer
  have hNumeric := hRows.at_numeric_d hM hC hRow
  have hc := (hNumeric.forest.bounds hM.1 hParent).1
  obtain ⟨x,hx,hX⟩ := hNumeric.values.total c hc
  have hAboveX := hNumeric.parent_value_above_one_d hM hC hParent hX
  obtain ⟨a,ha,hA⟩ := hRows.base.values.total c hc
  obtain ⟨initial,_,hInitial⟩ := hLayers.base.row.values.total c hc
  have hRowValue : RowValue M R.states R.values R.forests J r c x :=
    ⟨U,(hRows.space.values U).mpr hNumeric.values,F,(hRows.space.forests F).mpr hNumeric.forest,hRow,hX⟩
  have hLayerValue : LayerValue M L H k c a :=
    ⟨W,(hLayers.space.rows.values W).mpr hLayerBase.row.values,Q,(hLayers.space.rows.forests Q).mpr hLayerBase.row.forest,hLayer,hA⟩
  have hr : M.mem r C.omega := by
    obtain ⟨_,_,hr,_⟩ := hRow
    exact (hRows.graph.bounds hM.1 hr).1
  have hk : M.mem k C.omega := by
    obtain ⟨_,_,hk,_⟩ := hLayer
    exact (hLayers.graph.bounds hM.1 hk).1
  have hPosX := ((omega_isOrdinal_d hM hC.omega).mem hx).transitive C.one hAboveX C.zero hC.one_succ.predecessor_mem
  have hra := hRows.live_row_lt_initial_d hM hC hr hRowValue hA hPosX
  have h0r : C.zero=r ∨ M.mem C.zero r := by
    classical
    by_cases he : r=C.zero
    · exact Or.inl he.symm
    · exact Or.inr ((hC.zero_mem_iff hM hr).mpr he)
  have hxa := hRows.value_antitone_d hM hC hC.zero_nat hr h0r ((hRows.value_initial_iff_d hM).mpr hA) hRowValue
  have hAboveA : M.mem C.one a := by
    rcases hxa with he | hxa
    · exact he ▸ hAboveX
    · exact ((omega_isOrdinal_d hM hC.omega).mem ha).transitive x hxa C.one hAboveX
  have hkInitial := hLayers.above_one_layer_lt_initial_d hM hC hk hLayerValue hInitial hAboveA
  have hInitialB := hB.value_lt hM.1 hLayers.base.row.values hInitial
  have hAB : M.mem a B := by
    rcases hLayers.value_le_initial_d hM hC hk hInitial hLayerValue with he | hlt
    · exact he.symm ▸ hInitialB
    · exact ((omega_isOrdinal_d hM hC.omega).mem hB.1.1).transitive initial hInitialB a hlt
  exact ⟨((omega_isOrdinal_d hM hC.omega).mem hB.1.1).transitive initial hInitialB k hkInitial,
    ((omega_isOrdinal_d hM hC.omega).mem hB.1.1).transitive a hAB r hra⟩

theorem LayerRun.no_parent_from_bound_predecessor_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {m : M.Domain} {L : LayerStateSpace M.Domain}
    {V P H B a k W Q : M.Domain} (hLayers : LayerRun M C m L V P H) (hB : SequenceBound M C m V B)
    (hSucc : M.SuccessorOf B a) (hLe : a=k ∨ M.mem a k) (hLayer : RowAt M L.states H k W Q)
    {R : RowStateSpace M.Domain} {J r U F c : M.Domain} (hRows : RowRun M C m R W Q J) (hRow : RowAt M R.states J r U F) :
    NoParent M m F c := by
  classical
  by_cases hc : M.mem c m
  · obtain ⟨v,_,hValue⟩ := hRows.base.values.total c hc
    have hBase := hLayers.at_rooted hM.1 hLayer
    have hk : M.mem k C.omega := by
      obtain ⟨_,_,hk,_⟩ := hLayer
      exact (hLayers.graph.bounds hM.1 hk).1
    have hLayerValue : LayerValue M L H k c v :=
      ⟨W,(hLayers.space.rows.values W).mpr hBase.row.values,Q,(hLayers.space.rows.forests Q).mpr hBase.row.forest,hLayer,hValue⟩
    have hv := hLayers.all_one_from_bound_predecessor_d hM hC hB hSucc hk hLe hLayerValue
    exact hRows.no_parent_of_initial_one_d hM hC (hv ▸ hValue) hRow
  · intro p _ hParent
    exact hc ((hRows.at_numeric_d hM hC hRow).forest.bounds hM.1 hParent).1

private def expressionBoundSchema : Project.Delta0BinarySchema 3 where
  body := Project.Formula.existsMem (.bound 4)
    (.conj (legalAtFormula (.bound 5) (.bound 4) (.bound 3) (.bound 2) (.bound 0))
      (sequenceBoundFormula (.bound 5) (.bound 4) (.bound 0) (.bound 2) (.bound 1)))
  freeClosed := by
    have hLegal := legalAtFormula_freeClosed (n := 6) (.bound 5) (.bound 4) (.bound 3) (.bound 2) (.bound 0) rfl rfl rfl rfl rfl
    have hBound := sequenceBoundFormula_freeClosed (n := 6) (.bound 5) (.bound 4) (.bound 0) (.bound 2) (.bound 1) rfl rfl rfl rfl rfl
    simp [Project.Formula.existsMem,Definitional.Formula.FreeClosed,hLegal,hBound]
  delta0 := .existsMem _ (.conj (legalAtFormula_delta0 _ _ _ _ _) (sequenceBoundFormula_delta0 _ _ _ _ _))

theorem expression_bound_graph_exists_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory) {C : ExpressionData M.Domain} (hC : C.Valid M) :
    ∃ Bounds, Graph M Bounds C.expressions C.omega ∧ ∀ V B, MemPair M Bounds V B ↔
      ∃ m, M.mem m C.omega ∧ LegalAt M C.omega C.zero C.one V m ∧ SequenceBound M C m V B := by
  let e := ((oneEnv C.omega).push C.zero).push C.one
  have hφ (V B : M.Domain) : Project.Formula.satisfies ((e.push V).push B) expressionBoundSchema.body ↔
      ∃ m, M.mem m C.omega ∧ LegalAt M C.omega C.zero C.one V m ∧ SequenceBound M C m V B := by
    simp only [expressionBoundSchema,Project.Formula.satisfies_existsMem_iff,Project.Formula.satisfies_conj_iff,legalAtFormula_iff hM.1]
    have hBound (m : M.Domain) := sequenceBoundFormula_iff hM.1 (((e.push V).push B).push m)
      ⟨.bound 5,.bound 4,.bound 3,.bound 3,.bound 3⟩ (.bound 0) (.bound 2) (.bound 1)
    simp only [hBound]
    rfl
  obtain ⟨Bounds,hSupport,hRaw⟩ := relation_comprehension_d hM expressionBoundSchema e C.expressions C.omega
  have hRows (V B : M.Domain) : MemPair M Bounds V B ↔
      ∃ m, M.mem m C.omega ∧ LegalAt M C.omega C.zero C.one V m ∧ SequenceBound M C m V B := by
    have hr := hRaw V B
    rw [hφ] at hr
    refine hr.trans ⟨fun h => h.2.2,?_⟩
    rintro ⟨m,hm,hLegal,hBound⟩
    exact ⟨(hC.expressions V).mpr ⟨m,hm,hLegal⟩,hBound.1.1,m,hm,hLegal,hBound⟩
  refine ⟨Bounds,⟨hSupport,?_,?_⟩,hRows⟩
  · intro V hV
    obtain ⟨m,hm,hLegal⟩ := (hC.expressions V).mp hV
    obtain ⟨B,hB⟩ := sequence_bound_exists_d hM hC hm hLegal.1.2
    exact ⟨B,hB.1.1,(hRows V B).mpr ⟨m,hm,hLegal,hB⟩⟩
  · intro V B D hVB hVD
    obtain ⟨m,_,hLegal,hB⟩ := (hRows V B).mp hVB
    obtain ⟨n,_,hLegal',hD⟩ := (hRows V D).mp hVD
    have hmn := legal_length_unique hM.1 hLegal hLegal'
    subst n
    exact hB.unique_d hM hC hD

def layerValueFormula {n : Nat} (L : LayerStateSpace (Project.Term n)) (H k c v : Project.Term n) : Project.Formula 1 n :=
  rowValueFormula L.states L.rows.values L.rows.forests H k c v

theorem layerValueFormula_delta0 {n : Nat} (L : LayerStateSpace (Project.Term n)) (H k c v : Project.Term n) :
    (layerValueFormula L H k c v).IsDelta0 := rowValueFormula_delta0 _ _ _ _ _ _ _

theorem layerValueFormula_freeClosed {n : Nat} (L : LayerStateSpace (Project.Term n)) (H k c v : Project.Term n)
    (hStates : L.states.freeSupport=[]) (hValues : L.rows.values.freeSupport=[]) (hForests : L.rows.forests.freeSupport=[])
    (hH : H.freeSupport=[]) (hk : k.freeSupport=[]) (hc : c.freeSupport=[]) (hv : v.freeSupport=[]) :
    (layerValueFormula L H k c v).FreeClosed := rowValueFormula_freeClosed _ _ _ _ _ _ _ hStates hValues hForests hH hk hc hv

theorem layerValueFormula_iff {M : SetTheory.Structure.{u}} (he : Extensional M) {n : Nat} (e : Env M n)
    (L : LayerStateSpace (Project.Term n)) (H k c v : Project.Term n) :
    Project.Formula.satisfies e (layerValueFormula L H k c v) ↔
      LayerValue M ⟨L.rows.eval e,L.states.eval e⟩ (H.eval e) (k.eval e) (c.eval e) (v.eval e) :=
  rowValueFormula_iff he e _ _ _ _ _ _ _

private def layerValueGraphSchema : Project.Delta0BinarySchema 6 where
  body := Project.Formula.existsMem (.bound 7) (Project.Formula.existsMem (.bound 7)
    (.conj (codeFormula (.bound 3) (.bound 1) (.bound 0))
      (rowValueFormula (.bound 7) (.bound 6) (.bound 5) (.bound 4) (.bound 1) (.bound 0) (.bound 2))))
  freeClosed := by
    have hValue := rowValueFormula_freeClosed (n := 10) (.bound 7) (.bound 6) (.bound 5) (.bound 4) (.bound 1) (.bound 0) (.bound 2)
      rfl rfl rfl rfl rfl rfl rfl
    simp [Project.Formula.existsMem,Definitional.Formula.FreeClosed,codeFormula,pairFormula,Project.Formula.forallMem,hValue]
  delta0 := .existsMem _ (.existsMem _ (.conj (codeFormula_delta0 _ _ _) (rowValueFormula_delta0 _ _ _ _ _ _ _)))

theorem LayerRun.value_graph_exists_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} {m : M.Domain} {L : LayerStateSpace M.Domain} {V P H : M.Domain} (h : LayerRun M C m L V P H) :
    ∃ Pairs Values, IsProduct M Pairs C.omega m ∧ Graph M Values Pairs C.omega ∧
      ∀ k, M.mem k C.omega → ∀ c, M.mem c m → ∀ key, Codes M key k c → ∀ v,
        MemPair M Values key v ↔ LayerValue M L H k c v := by
  obtain ⟨Pairs,hPairs⟩ := product_exists hM C.omega m
  let e := (((((oneEnv C.omega).push m).push L.states).push L.rows.values).push L.rows.forests).push H
  have hφ (key v : M.Domain) : Project.Formula.satisfies ((e.push key).push v) layerValueGraphSchema.body ↔
      ∃ k, M.mem k C.omega ∧ ∃ c, M.mem c m ∧ Codes M key k c ∧ LayerValue M L H k c v := by
    simp only [layerValueGraphSchema,Project.Formula.satisfies_existsMem_iff,Project.Formula.satisfies_conj_iff,codeFormula_iff hM.1,rowValueFormula_iff hM.1]
    rfl
  obtain ⟨Values,hSupport,hRaw⟩ := relation_comprehension_d hM layerValueGraphSchema e Pairs C.omega
  have hRows (key v : M.Domain) : MemPair M Values key v ↔
      ∃ k, M.mem k C.omega ∧ ∃ c, M.mem c m ∧ Codes M key k c ∧ LayerValue M L H k c v := by
    have hr := hRaw key v
    rw [hφ] at hr
    refine hr.trans ⟨fun h => h.2.2,?_⟩
    rintro ⟨k,hk,c,hc,hCode,hValue⟩
    exact ⟨(hPairs key).mpr ⟨k,hk,c,hc,hCode⟩,(hValue.bounds hM.1 h.space).2,k,hk,c,hc,hCode,hValue⟩
  refine ⟨Pairs,Values,hPairs,⟨hSupport,?_,?_⟩,?_⟩
  · intro key hkey
    obtain ⟨k,hk,c,hc,hCode⟩ := (hPairs key).mp hkey
    obtain ⟨v,hv,hValue⟩ := h.value_exists_d hM.1 hk hc
    exact ⟨v,hv,(hRows key v).mpr ⟨k,hk,c,hc,hCode,hValue⟩⟩
  · intro key v v' hAt hAt'
    obtain ⟨k,_,c,_,hCode,hValue⟩ := (hRows key v).mp hAt
    obtain ⟨k',_,c',_,hCode',hValue'⟩ := (hRows key v').mp hAt'
    obtain ⟨hkk,hcc⟩ := codes_injective hM.1 hCode hCode'
    subst k'
    subst c'
    exact h.value_unique hM.1 hValue hValue'
  · intro k hk c hc key hCode v
    constructor
    · intro hAt
      obtain ⟨k',_,c',_,hCode',hValue⟩ := (hRows key v).mp hAt
      obtain ⟨hkk,hcc⟩ := codes_injective hM.1 hCode hCode'
      subst k'
      subst c'
      exact hValue
    · intro hValue
      exact (hRows key v).mpr ⟨k,hk,c,hc,hCode,hValue⟩

end KP1Y.OneYFinite
