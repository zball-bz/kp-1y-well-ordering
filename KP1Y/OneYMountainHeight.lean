import KP1Y.OneYMountain
import KP1Y.OneYNaturalDifferenceOrder

/-! 数值行的内部燃料界、最后活行及实际高度/顶部值图。 -/
namespace KP1Y.OneYFinite
open YesMetaZFC YesMetaZFC.SetTheory YesMetaZFC.SetTheory.Definitional
open KP1Y.Kuratowski KP1Y.Functions KP1Y.Naturals KP1Y.Bounded
universe u

def RowValue (M : SetTheory.Structure.{u}) (States Values Forests H r c v : M.Domain) : Prop :=
  ∃ V, M.mem V Values ∧ ∃ P, M.mem P Forests ∧ RowAt M States H r V P ∧ MemPair M V c v

def rowValueFormula {n : Nat} (States Values Forests H r c v : Project.Term n) : Project.Formula 1 n :=
  Project.Formula.existsMem Values (Project.Formula.existsMem Forests.weaken
    (.conj (rowAtFormula States.weaken.weaken H.weaken.weaken r.weaken.weaken (.bound 1) (.bound 0))
      (memPairFormula (.bound 1) c.weaken.weaken v.weaken.weaken)))

theorem rowValueFormula_delta0 {n : Nat} (States Values Forests H r c v : Project.Term n) :
    (rowValueFormula States Values Forests H r c v).IsDelta0 :=
  .existsMem _ (.existsMem _ (.conj (rowAtFormula_delta0 _ _ _ _ _) (memPairFormula_delta0 _ _ _)))

theorem rowValueFormula_freeClosed {n : Nat} (States Values Forests H r c v : Project.Term n)
    (hS : States.freeSupport=[]) (hV : Values.freeSupport=[]) (hF : Forests.freeSupport=[])
    (hH : H.freeSupport=[]) (hr : r.freeSupport=[]) (hc : c.freeSupport=[]) (hv : v.freeSupport=[]) :
    (rowValueFormula States Values Forests H r c v).FreeClosed := by
  simp [rowValueFormula,rowAtFormula,memPairFormula,codeFormula,pairFormula,Project.Formula.forallMem,
    Project.Formula.existsMem,Definitional.Formula.FreeClosed,hS,hV,hF,hH,hr,hc,hv]

theorem rowValueFormula_iff {M : SetTheory.Structure.{u}} (he : Extensional M) {n : Nat}
    (e : Env M n) (States Values Forests H r c v : Project.Term n) :
    Project.Formula.satisfies e (rowValueFormula States Values Forests H r c v) ↔
      RowValue M (States.eval e) (Values.eval e) (Forests.eval e) (H.eval e) (r.eval e) (c.eval e) (v.eval e) := by
  simp only [rowValueFormula,Project.Formula.satisfies_existsMem_iff,Project.Formula.satisfies_conj_iff,
    rowAtFormula_iff he,memPairFormula_iff he,Term.eval_weaken]
  rfl

theorem RowValue.bounds {M : SetTheory.Structure.{u}} (he : Extensional M) {C : ExpressionData M.Domain}
    {m : M.Domain} {R : RowStateSpace M.Domain} (hR : R.Valid M C m) {H r c v : M.Domain}
    (h : RowValue M R.states R.values R.forests H r c v) : M.mem c m ∧ M.mem v C.omega := by
  obtain ⟨V,hV,_,_,_,hAt⟩ := h
  exact ((hR.values V).mp hV).bounds he hAt

theorem RowRun.value_exists_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory) {C : ExpressionData M.Domain} (hC : C.Valid M)
    {m : M.Domain} {R : RowStateSpace M.Domain} {V P H r c : M.Domain} (h : RowRun M C m R V P H)
    (hr : M.mem r C.omega) (hc : M.mem c m) : ∃ v, M.mem v C.omega ∧ RowValue M R.states R.values R.forests H r c v := by
  obtain ⟨W,Q,hAt⟩ := h.at_exists_d hr
  have hRow := h.at_numeric_d hM hC hAt
  obtain ⟨v,hv,hValue⟩ := hRow.values.total c hc
  exact ⟨v,hv,W,(h.space.values W).mpr hRow.values,Q,(h.space.forests Q).mpr hRow.forest,hAt,hValue⟩

theorem RowRun.value_unique {M : SetTheory.Structure.{u}} (he : Extensional M) {C : ExpressionData M.Domain}
    {m : M.Domain} {R : RowStateSpace M.Domain} {V P H r c x y : M.Domain} (h : RowRun M C m R V P H)
    (hx : RowValue M R.states R.values R.forests H r c x) (hy : RowValue M R.states R.values R.forests H r c y) : x=y := by
  obtain ⟨W,hW,Q,_,hAt,hWx⟩ := hx
  obtain ⟨W',_,Q',_,hAt',hWy⟩ := hy
  obtain ⟨hWW,hQQ⟩ := h.at_unique he hAt hAt'
  subst W'
  exact ((h.space.values W).mp hW).unique c x y hWx hWy

theorem RowRun.initial_row_at_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory) {C : ExpressionData M.Domain}
    {m : M.Domain} {R : RowStateSpace M.Domain} {V P H : M.Domain} (h : RowRun M C m R V P H) :
    RowAt M R.states H C.zero V P := by
  obtain ⟨state,hs,hCode⟩ := h.space.encode_d hM h.base.values h.base.forest
  exact ⟨state,hs,h.initial state hCode,hCode⟩

theorem RowRun.value_initial_iff_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory) {C : ExpressionData M.Domain}
    {m : M.Domain} {R : RowStateSpace M.Domain} {V P H c v : M.Domain} (h : RowRun M C m R V P H) :
    RowValue M R.states R.values R.forests H C.zero c v ↔ MemPair M V c v := by
  constructor
  · rintro ⟨W,_,Q,_,hAt,hValue⟩
    obtain ⟨hWV,_⟩ := h.at_unique hM.1 hAt (h.initial_row_at_d hM)
    subst W
    exact hValue
  · intro hValue
    exact ⟨V,(h.space.values V).mpr h.base.values,P,(h.space.forests P).mpr h.base.forest,h.initial_row_at_d hM,hValue⟩

theorem NumericRow.difference_le_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {m V P D c x d : M.Domain}
    (h : NumericRow M C m V P) (hD : DifferenceGraph M C m V P D) (hX : MemPair M V c x) (hAt : MemPair M D c d) :
    d=x ∨ M.mem d x := by
  rcases ((hD.rows c d).mp hAt).2 with ⟨_,hd⟩ | ⟨p,_,x',_,y,_,_,hX',_,hDiff⟩
  · subst d
    classical
    by_cases hx : x=C.zero
    · exact Or.inl hx.symm
    · exact Or.inr ((hC.zero_mem_iff hM (h.values.bounds hM.1 hX).2).mpr hx)
  · have hxx := h.values.unique c x x' hX hX'
    subst x'
    exact truncated_difference_le_d hM hC hDiff

theorem NumericRow.difference_strict_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {m V P D c x d : M.Domain}
    (h : NumericRow M C m V P) (hD : DifferenceGraph M C m V P D) (hX : MemPair M V c x) (hAt : MemPair M D c d)
    (hPos : M.mem C.zero x) : M.mem d x := by
  rcases ((hD.rows c d).mp hAt).2 with ⟨_,hd⟩ | ⟨p,_,x',_,y,_,hPc,hX',hPy,hDiff⟩
  · exact hd ▸ hPos
  · have hxx := h.values.unique c x x' hX hX'
    subst x'
    have hValues := h.parentValues c p y x hPc hPy hX
    exact (truncated_difference_strict_d hM hC hDiff hValues.1 hValues.2).2

theorem NumericRow.difference_positive_iff_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {m V P D c d : M.Domain}
    (h : NumericRow M C m V P) (hD : DifferenceGraph M C m V P D) (hAt : MemPair M D c d) :
    M.mem C.zero d ↔ ∃ p, MemPair M P c p := by
  constructor
  · intro hPos
    rcases ((hD.rows c d).mp hAt).2 with ⟨_,hd⟩ | ⟨p,_,_,_,_,_,hPc,_⟩
    · exact False.elim (hC.zero_empty C.zero (hd ▸ hPos))
    · exact ⟨p,hPc⟩
  · rintro ⟨p,hPc⟩
    obtain ⟨hc,hp⟩ := h.forest.bounds hM.1 hPc
    obtain ⟨x,_,hX⟩ := h.values.total c hc
    obtain ⟨y,_,hY⟩ := h.values.total p hp
    have hDiff := hD.at_parent_d hM h.values h.forest hPc hX hY hAt
    exact (truncated_difference_positive_iff_d hM hC hDiff).mpr (h.parentValues c p y x hPc hY hX).2

theorem RowRun.value_successor_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory) {C : ExpressionData M.Domain} (hC : C.Valid M)
    {m : M.Domain} {R : RowStateSpace M.Domain} {V P H r r' c x y : M.Domain} (h : RowRun M C m R V P H)
    (hs : M.SuccessorOf r' r) (hx : RowValue M R.states R.values R.forests H r c x)
    (hy : RowValue M R.states R.values R.forests H r' c y) :
    (y=x ∨ M.mem y x) ∧ (M.mem C.zero x → M.mem y x) := by
  obtain ⟨W,_,Q,_,hAt,hX⟩ := hx
  obtain ⟨W',_,Q',_,hAt',hY⟩ := hy
  have hNext := h.at_next hM.1 hs hAt hAt'
  have hRow := h.at_numeric_d hM hC hAt
  exact ⟨hRow.difference_le_d hM hC hNext.difference hX hY,hRow.difference_strict_d hM hC hNext.difference hX hY⟩

private def heightEnv {M : SetTheory.Structure.{u}} (C : ExpressionData M.Domain) (m : M.Domain)
    (R : RowStateSpace M.Domain) (V H : M.Domain) : Env M 8 :=
  (((((((oneEnv C.omega).push C.zero).push R.states).push R.values).push R.forests).push m).push V).push H

private def liveFuelSchema : Project.UnarySchema 8 where
  body := Project.Formula.forallMem (.bound 3) (Project.Formula.forallMem (.bound 9)
    (Project.Formula.forallMem (.bound 10) (Project.Formula.forallMem (.bound 11)
      (.imp (.conj (rowValueFormula (.bound 10) (.bound 9) (.bound 8) (.bound 5) (.bound 4) (.bound 3) (.bound 2))
        (.conj (memPairFormula (.bound 6) (.bound 3) (.bound 1))
          (.conj (differenceFormula (.bound 12) (.bound 11) (.bound 1) (.bound 4) (.bound 0)) (.mem (.bound 11) (.bound 2)))))
        (.disj (Project.Formula.extensionalEq (.bound 2) (.bound 0)) (.mem (.bound 2) (.bound 0)))))))
  freeClosed := by
    have hValue := rowValueFormula_freeClosed (n := 13) (.bound 10) (.bound 9) (.bound 8) (.bound 5) (.bound 4) (.bound 3) (.bound 2)
      rfl rfl rfl rfl rfl rfl rfl
    have hDiff := differenceFormula_freeClosed (n := 13) (.bound 12) (.bound 11) (.bound 1) (.bound 4) (.bound 0) rfl rfl rfl rfl rfl
    simp [Project.Formula.forallMem,Definitional.Formula.FreeClosed,memPairFormula,codeFormula,pairFormula,
      Project.Formula.existsMem,hValue,hDiff]

private theorem liveFuelSchema_iff {M : SetTheory.Structure.{u}} (he : Extensional M)
    (C : ExpressionData M.Domain) (m : M.Domain) (R : RowStateSpace M.Domain) (V H r : M.Domain) :
    Project.Formula.satisfies ((heightEnv C m R V H).push r) liveFuelSchema.body ↔
      ∀ c, M.mem c m → ∀ v, M.mem v C.omega → ∀ a, M.mem a C.omega → ∀ d, M.mem d C.omega →
        RowValue M R.states R.values R.forests H r c v → MemPair M V c a →
          TruncatedDifference M C.omega C.zero a r d → M.mem C.zero v → v=d ∨ M.mem v d := by
  simp only [liveFuelSchema,Project.Formula.satisfies_forallMem_iff,Project.Formula.satisfies_imp_iff,
    Project.Formula.satisfies_conj_iff,rowValueFormula_iff he,memPairFormula_iff he,differenceFormula_iff he,
    Project.Formula.satisfies_mem_iff,Project.Formula.satisfies_disj_iff,Project.Formula.satisfies_extensionalEq_iff_eq he,and_imp]
  rfl

theorem RowRun.live_fuel_bound_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {m : M.Domain} {R : RowStateSpace M.Domain}
    {V P H r c v a d : M.Domain} (h : RowRun M C m R V P H) (hr : M.mem r C.omega)
    (hValue : RowValue M R.states R.values R.forests H r c v) (hOriginal : MemPair M V c a)
    (hDiff : TruncatedDifference M C.omega C.zero a r d) (hPos : M.mem C.zero v) : v=d ∨ M.mem v d := by
  have hω := omega_isOrdinal_d hM hC.omega
  have hAll := natural_induction_d hM liveFuelSchema (heightEnv C m R V H) hC.omega
    (fun z hz => (liveFuelSchema_iff hM.1 C m R V H z).mpr (by
      have hzz := hM.1.eq_of_same_members z C.zero (fun x => iff_of_false (hz x) (hC.zero_empty x))
      subst z
      intro c _ v _ a ha d _ hValue hOriginal hDiff _
      have hva := h.base.values.unique c v a ((h.value_initial_iff_d hM).mp hValue) hOriginal
      have hda := truncated_difference_unique_d hM hC hDiff (truncated_difference_zero_d hM hC ha)
      exact Or.inl (hva.trans hda.symm)))
    (fun r hr ih r' hs => (liveFuelSchema_iff hM.1 C m R V H r').mpr (by
      intro c hc v hv a ha d hd hValue hOriginal hDiff hPos
      obtain ⟨x,hx,hPrev⟩ := h.value_exists_d hM hC hr hc
      have hStep := h.value_successor_d hM hC hs hPrev hValue
      have hxPos : M.mem C.zero x := by
        rcases hStep.1 with he | hvx
        · exact he ▸ hPos
        · exact (hω.mem hx).transitive v hvx C.zero hPos
      obtain ⟨fuel,hFuel,hBefore⟩ := truncated_difference_exists_d hM hC ha hr
      have hLe := (liveFuelSchema_iff hM.1 C m R V H r).mp ih c hc x hx a ha fuel hFuel hPrev hOriginal hBefore hxPos
      have hFuelPos : M.mem C.zero fuel := by
        rcases hLe with he | hxf
        · exact he ▸ hxPos
        · exact (hω.mem hFuel).transitive x hxf C.zero hxPos
      have hra := (truncated_difference_positive_iff_d hM hC hBefore).mp hFuelPos
      have hFuelSucc := truncated_difference_successor_of_lt_d hM hC hs hra hBefore hDiff
      have hvFuel : M.mem v fuel := by
        rcases hLe with he | hxf
        · exact he ▸ hStep.2 hxPos
        · exact (hω.mem hFuel).transitive x hxf v (hStep.2 hxPos)
      rcases (hFuelSucc v).mp hvFuel with hvd | he
      · exact Or.inr hvd
      · exact Or.inl (hM.1.eq_of_same_members v d he)))
  exact (liveFuelSchema_iff hM.1 C m R V H r).mp (hAll r hr) c (hValue.bounds hM.1 h.space).1
    v (hValue.bounds hM.1 h.space).2 a (h.base.values.bounds hM.1 hOriginal).2 d (truncated_difference_natural hM.1 hDiff)
    hValue hOriginal hDiff hPos

theorem RowRun.live_row_lt_initial_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {m : M.Domain} {R : RowStateSpace M.Domain}
    {V P H r c v a : M.Domain} (h : RowRun M C m R V P H) (hr : M.mem r C.omega)
    (hValue : RowValue M R.states R.values R.forests H r c v) (hOriginal : MemPair M V c a) (hPos : M.mem C.zero v) : M.mem r a := by
  obtain ⟨d,hd,hDiff⟩ := truncated_difference_exists_d hM hC (h.base.values.bounds hM.1 hOriginal).2 hr
  have hLe := h.live_fuel_bound_d hM hC hr hValue hOriginal hDiff hPos
  have hdPos : M.mem C.zero d := by
    rcases hLe with he | hvd
    · exact he ▸ hPos
    · exact ((omega_isOrdinal_d hM hC.omega).mem hd).transitive v hvd C.zero hPos
  exact (truncated_difference_positive_iff_d hM hC hDiff).mp hdPos

theorem RowRun.value_zero_of_bound_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {m : M.Domain} {R : RowStateSpace M.Domain}
    {V P H r c v a : M.Domain} (h : RowRun M C m R V P H) (hr : M.mem r C.omega)
    (hValue : RowValue M R.states R.values R.forests H r c v) (hOriginal : MemPair M V c a) (hNot : ¬M.mem r a) : v=C.zero := by
  classical
  apply Classical.byContradiction
  intro hv
  exact hNot (h.live_row_lt_initial_d hM hC hr hValue hOriginal ((hC.zero_mem_iff hM (hValue.bounds hM.1 h.space).2).mpr hv))

private def antitoneSchema : Project.UnarySchema 8 where
  body := Project.Formula.forallMem (.bound 8) (Project.Formula.forallMem (.bound 4)
    (Project.Formula.forallMem (.bound 10) (Project.Formula.forallMem (.bound 11)
      (.imp (.disj (Project.Formula.extensionalEq (.bound 3) (.bound 4)) (.mem (.bound 3) (.bound 4)))
        (.imp (rowValueFormula (.bound 10) (.bound 9) (.bound 8) (.bound 5) (.bound 3) (.bound 2) (.bound 1))
          (.imp (rowValueFormula (.bound 10) (.bound 9) (.bound 8) (.bound 5) (.bound 4) (.bound 2) (.bound 0))
            (.disj (Project.Formula.extensionalEq (.bound 0) (.bound 1)) (.mem (.bound 0) (.bound 1)))))))))
  freeClosed := by
    have hX := rowValueFormula_freeClosed (n := 13) (.bound 10) (.bound 9) (.bound 8) (.bound 5) (.bound 3) (.bound 2) (.bound 1)
      rfl rfl rfl rfl rfl rfl rfl
    have hY := rowValueFormula_freeClosed (n := 13) (.bound 10) (.bound 9) (.bound 8) (.bound 5) (.bound 4) (.bound 2) (.bound 0)
      rfl rfl rfl rfl rfl rfl rfl
    simp [Project.Formula.forallMem,Definitional.Formula.FreeClosed,hX,hY]

private theorem antitoneSchema_iff {M : SetTheory.Structure.{u}} (he : Extensional M)
    (C : ExpressionData M.Domain) (m : M.Domain) (R : RowStateSpace M.Domain) (V H r : M.Domain) :
    Project.Formula.satisfies ((heightEnv C m R V H).push r) antitoneSchema.body ↔
      ∀ i, M.mem i C.omega → ∀ c, M.mem c m → ∀ x, M.mem x C.omega → ∀ y, M.mem y C.omega →
        (i=r ∨ M.mem i r) → RowValue M R.states R.values R.forests H i c x →
          RowValue M R.states R.values R.forests H r c y → y=x ∨ M.mem y x := by
  simp only [antitoneSchema,Project.Formula.satisfies_forallMem_iff,Project.Formula.satisfies_imp_iff,
    Project.Formula.satisfies_disj_iff,Project.Formula.satisfies_extensionalEq_iff_eq he,Project.Formula.satisfies_mem_iff,rowValueFormula_iff he]
  rfl

theorem RowRun.value_antitone_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {m : M.Domain} {R : RowStateSpace M.Domain}
    {V P H i r c x y : M.Domain} (h : RowRun M C m R V P H) (hi : M.mem i C.omega) (hr : M.mem r C.omega)
    (hir : i=r ∨ M.mem i r) (hX : RowValue M R.states R.values R.forests H i c x)
    (hY : RowValue M R.states R.values R.forests H r c y) : y=x ∨ M.mem y x := by
  have hω := omega_isOrdinal_d hM hC.omega
  have hAll := natural_induction_d hM antitoneSchema (heightEnv C m R V H) hC.omega
    (fun z hz => (antitoneSchema_iff hM.1 C m R V H z).mpr (by
      intro i _ c _ x _ y _ hi hX hY
      have hiz := hi.resolve_right (hz i)
      subst i
      exact Or.inl (h.value_unique hM.1 hY hX)))
    (fun r hr ih r' hs => (antitoneSchema_iff hM.1 C m R V H r').mpr (by
      intro i hi c hc x hx y _ hir hX hY
      rcases hir with he | hir
      · subst i
        exact Or.inl (h.value_unique hM.1 hY hX)
      · have hiLe : i=r ∨ M.mem i r := by
          rcases (hs i).mp hir with hir | he
          · exact Or.inr hir
          · exact Or.inl (hM.1.eq_of_same_members i r he)
        obtain ⟨z,hz,hZ⟩ := h.value_exists_d hM hC hr hc
        have hzx := (antitoneSchema_iff hM.1 C m R V H r).mp ih i hi c hc x hx z hz hiLe hX hZ
        have hyz := (h.value_successor_d hM hC hs hZ hY).1
        rcases hyz with he | hyz
        · exact he.symm ▸ hzx
        · rcases hzx with he | hzx
          · exact Or.inr (he ▸ hyz)
          · exact Or.inr ((hω.mem hx).transitive z hzx y hyz)))
  exact (antitoneSchema_iff hM.1 C m R V H r).mp (hAll r hr) i hi c (hX.bounds hM.1 h.space).1
    x (hX.bounds hM.1 h.space).2 y (hY.bounds hM.1 h.space).2 hir hX hY

def LiveRow (M : SetTheory.Structure.{u}) (w zero States Values Forests H c r : M.Domain) : Prop :=
  ∃ v, M.mem v w ∧ RowValue M States Values Forests H r c v ∧ M.mem zero v

def liveRowFormula {n : Nat} (w zero States Values Forests H c r : Project.Term n) : Project.Formula 1 n :=
  Project.Formula.existsMem w (.conj (rowValueFormula States.weaken Values.weaken Forests.weaken H.weaken r.weaken c.weaken (.bound 0))
    (.mem zero.weaken (.bound 0)))

theorem liveRowFormula_delta0 {n : Nat} (w zero States Values Forests H c r : Project.Term n) :
    (liveRowFormula w zero States Values Forests H c r).IsDelta0 := .existsMem _ (.conj (rowValueFormula_delta0 _ _ _ _ _ _ _) (.mem _ _))

theorem liveRowFormula_freeClosed {n : Nat} (w zero States Values Forests H c r : Project.Term n)
    (hw : w.freeSupport=[]) (hz : zero.freeSupport=[]) (hS : States.freeSupport=[]) (hV : Values.freeSupport=[])
    (hF : Forests.freeSupport=[]) (hH : H.freeSupport=[]) (hc : c.freeSupport=[]) (hr : r.freeSupport=[]) :
    (liveRowFormula w zero States Values Forests H c r).FreeClosed := by
  simp [liveRowFormula,rowValueFormula,rowAtFormula,memPairFormula,codeFormula,pairFormula,Project.Formula.forallMem,
    Project.Formula.existsMem,Definitional.Formula.FreeClosed,hw,hz,hS,hV,hF,hH,hc,hr]

theorem liveRowFormula_iff {M : SetTheory.Structure.{u}} (he : Extensional M) {n : Nat}
    (e : Env M n) (w zero States Values Forests H c r : Project.Term n) :
    Project.Formula.satisfies e (liveRowFormula w zero States Values Forests H c r) ↔
      LiveRow M (w.eval e) (zero.eval e) (States.eval e) (Values.eval e) (Forests.eval e) (H.eval e) (c.eval e) (r.eval e) := by
  simp only [liveRowFormula,Project.Formula.satisfies_existsMem_iff,Project.Formula.satisfies_conj_iff,
    rowValueFormula_iff he,Project.Formula.satisfies_mem_iff,Term.eval_weaken]
  rfl

def HeightAt (M : SetTheory.Structure.{u}) (C : ExpressionData M.Domain) (R : RowStateSpace M.Domain)
    (V H c height : M.Domain) : Prop :=
  ∃ a, M.mem a C.omega ∧ MemPair M V c a ∧
    ((a=C.zero ∧ height=C.zero) ∨ (M.mem height a ∧ LiveRow M C.omega C.zero R.states R.values R.forests H c height ∧
      ∀ r, M.mem r a → LiveRow M C.omega C.zero R.states R.values R.forests H c r → r=height ∨ M.mem r height))

def heightAtFormula {n : Nat} (w zero States Values Forests V H c height : Project.Term n) : Project.Formula 1 n :=
  Project.Formula.existsMem w (.conj (memPairFormula V.weaken c.weaken (.bound 0))
    (.disj (.conj (Project.Formula.extensionalEq (.bound 0) zero.weaken) (Project.Formula.extensionalEq height.weaken zero.weaken))
      (.conj (.mem height.weaken (.bound 0))
        (.conj (liveRowFormula w.weaken zero.weaken States.weaken Values.weaken Forests.weaken H.weaken c.weaken height.weaken)
          (Project.Formula.forallMem (.bound 0) (.imp
            (liveRowFormula w.weaken.weaken zero.weaken.weaken States.weaken.weaken Values.weaken.weaken Forests.weaken.weaken
              H.weaken.weaken c.weaken.weaken (.bound 0))
            (.disj (Project.Formula.extensionalEq (.bound 0) height.weaken.weaken) (.mem (.bound 0) height.weaken.weaken))))))))

theorem heightAtFormula_delta0 {n : Nat} (w zero States Values Forests V H c height : Project.Term n) :
    (heightAtFormula w zero States Values Forests V H c height).IsDelta0 :=
  .existsMem _ (.conj (memPairFormula_delta0 _ _ _) (.disj (.conj (.atom _ _ _) (.atom _ _ _))
    (.conj (.mem _ _) (.conj (liveRowFormula_delta0 _ _ _ _ _ _ _ _) (.forallMem _
      (.imp (liveRowFormula_delta0 _ _ _ _ _ _ _ _) (.disj (.atom _ _ _) (.mem _ _))))))))

theorem heightAtFormula_freeClosed {n : Nat} (w zero States Values Forests V H c height : Project.Term n)
    (hw : w.freeSupport=[]) (hz : zero.freeSupport=[]) (hS : States.freeSupport=[]) (hVs : Values.freeSupport=[])
    (hFs : Forests.freeSupport=[]) (hV : V.freeSupport=[]) (hH : H.freeSupport=[]) (hc : c.freeSupport=[]) (hh : height.freeSupport=[]) :
    (heightAtFormula w zero States Values Forests V H c height).FreeClosed := by
  simp [heightAtFormula,liveRowFormula,rowValueFormula,rowAtFormula,memPairFormula,codeFormula,pairFormula,
    Project.Formula.forallMem,Project.Formula.existsMem,Definitional.Formula.FreeClosed,hw,hz,hS,hVs,hFs,hV,hH,hc,hh]

theorem heightAtFormula_iff {M : SetTheory.Structure.{u}} (he : Extensional M) {n : Nat} (e : Env M n)
    (C : ExpressionData (Project.Term n)) (States Values Forests V H c height : Project.Term n) :
    Project.Formula.satisfies e (heightAtFormula C.omega C.zero States Values Forests V H c height) ↔
      HeightAt M (C.eval e) ⟨Values.eval e,Forests.eval e,States.eval e⟩ (V.eval e) (H.eval e) (c.eval e) (height.eval e) := by
  simp only [heightAtFormula,Project.Formula.satisfies_existsMem_iff,Project.Formula.satisfies_conj_iff,
    memPairFormula_iff he,Project.Formula.satisfies_disj_iff,Project.Formula.satisfies_extensionalEq_iff_eq he,
    Project.Formula.satisfies_mem_iff,liveRowFormula_iff he,Project.Formula.satisfies_forallMem_iff,Project.Formula.satisfies_imp_iff,Term.eval_weaken]
  rfl

theorem HeightAt.natural_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory) {C : ExpressionData M.Domain} (hC : C.Valid M)
    {R : RowStateSpace M.Domain} {V H c height : M.Domain} (h : HeightAt M C R V H c height) : M.mem height C.omega := by
  obtain ⟨a,ha,_,⟨_,hh⟩ | ⟨hh,_,_⟩⟩ := h
  · exact hh ▸ hC.zero_nat
  · exact (omega_isOrdinal_d hM hC.omega).transitive a ha height hh

private def liveSetSchema : Project.Delta0UnarySchema 7 where
  body := liveRowFormula (.bound 7) (.bound 6) (.bound 5) (.bound 4) (.bound 3) (.bound 2) (.bound 1) (.bound 0)
  freeClosed := liveRowFormula_freeClosed _ _ _ _ _ _ _ _ rfl rfl rfl rfl rfl rfl rfl rfl
  delta0 := liveRowFormula_delta0 _ _ _ _ _ _ _ _

theorem height_at_exists_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory) {C : ExpressionData M.Domain} (hC : C.Valid M)
    {m : M.Domain} {R : RowStateSpace M.Domain} {V P H c : M.Domain} (h : RowRun M C m R V P H) (hc : M.mem c m) :
    ∃ height, HeightAt M C R V H c height := by
  obtain ⟨a,ha,hOriginal⟩ := h.base.values.total c hc
  classical
  by_cases ha0 : a=C.zero
  · exact ⟨C.zero,a,ha,hOriginal,Or.inl ⟨ha0,rfl⟩⟩
  · let e := ((((((oneEnv C.omega).push C.zero).push R.states).push R.values).push R.forests).push H).push c
    obtain ⟨L,hL⟩ := SetTheory.KP.separation_exists_d (KP1Y.models_weakKP hM) liveSetSchema e a
    have hφ (r : M.Domain) : Project.Formula.satisfies (e.push r) liveSetSchema.body ↔
        LiveRow M C.omega C.zero R.states R.values R.forests H c r := liveRowFormula_iff hM.1 _ _ _ _ _ _ _ _ _
    have hRows (r : M.Domain) : M.mem r L ↔ M.mem r a ∧ LiveRow M C.omega C.zero R.states R.values R.forests H c r := by
      simpa only [hφ] using hL r
    have h0a := (hC.zero_mem_iff hM ha).mpr ha0
    have hLive0 : LiveRow M C.omega C.zero R.states R.values R.forests H c C.zero :=
      ⟨a,ha,(h.value_initial_iff_d hM).mpr hOriginal,h0a⟩
    obtain ⟨height,hMax⟩ := greatest_below_exists_d (A := L) hM hC.omega ha ⟨C.zero,h0a,(hRows C.zero).mpr ⟨h0a,hLive0⟩⟩
    exact ⟨height,a,ha,hOriginal,Or.inr ⟨hMax.1,((hRows height).mp hMax.2.1).2,
      fun r hr hLive => hMax.2.2 r hr ((hRows r).mpr ⟨hr,hLive⟩)⟩⟩

theorem HeightAt.unique_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory) {C : ExpressionData M.Domain} (hC : C.Valid M)
    {m : M.Domain} {R : RowStateSpace M.Domain} {V H c height height' : M.Domain} (hV : Graph M V m C.omega)
    (h : HeightAt M C R V H c height) (h' : HeightAt M C R V H c height') : height=height' := by
  obtain ⟨a,ha,hA,hCases⟩ := h
  obtain ⟨a',_,hA',hCases'⟩ := h'
  have haa := hV.unique c a a' hA hA'
  subst a'
  rcases hCases with ⟨ha0,hh0⟩ | ⟨hh,hLive,hMax⟩ <;> rcases hCases' with ⟨ha0',hh0'⟩ | ⟨hh',hLive',hMax'⟩
  · exact hh0.trans hh0'.symm
  · exact False.elim (hC.zero_empty height' (ha0 ▸ hh'))
  · exact False.elim (hC.zero_empty height (ha0' ▸ hh))
  · rcases hMax' height hh hLive with he | hlt
    · exact he
    · rcases hMax height' hh' hLive' with he | hgt
      · exact he.symm
      · have hOrd := ((omega_isOrdinal_d hM hC.omega).mem ha).mem hh
        exact False.elim (SetTheory.KP.mem_irrefl_d (KP1Y.models_weakKP hM) height (hOrd.transitive height' hgt height hlt))

theorem HeightAt.positive_spec {M : SetTheory.Structure.{u}} {C : ExpressionData M.Domain} (hC : C.Valid M)
    {m : M.Domain} {R : RowStateSpace M.Domain} {V H c height a : M.Domain} (hV : Graph M V m C.omega)
    (h : HeightAt M C R V H c height) (hOriginal : MemPair M V c a) (hPos : M.mem C.zero a) :
    M.mem height a ∧ LiveRow M C.omega C.zero R.states R.values R.forests H c height ∧
      ∀ r, M.mem r a → LiveRow M C.omega C.zero R.states R.values R.forests H c r → r=height ∨ M.mem r height := by
  obtain ⟨a',_,hA,hCases⟩ := h
  have haa := hV.unique c a' a hA hOriginal
  subst a'
  rcases hCases with ⟨ha,_⟩ | hGood
  · exact False.elim (hC.zero_empty C.zero (ha ▸ hPos))
  · exact hGood

theorem RowRun.live_iff_le_height_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory) {C : ExpressionData M.Domain} (hC : C.Valid M)
    {m : M.Domain} {R : RowStateSpace M.Domain} {V P H c a height r : M.Domain} (h : RowRun M C m R V P H)
    (hOriginal : MemPair M V c a) (hPos : M.mem C.zero a) (hHeight : HeightAt M C R V H c height) (hr : M.mem r C.omega) :
    LiveRow M C.omega C.zero R.states R.values R.forests H c r ↔ r=height ∨ M.mem r height := by
  have hSpec := hHeight.positive_spec hC h.base.values hOriginal hPos
  constructor
  · rintro ⟨v,_,hValue,hLive⟩
    exact hSpec.2.2 r (h.live_row_lt_initial_d hM hC hr hValue hOriginal hLive) ⟨v,(hValue.bounds hM.1 h.space).2,hValue,hLive⟩
  · intro hLe
    obtain ⟨top,hTop,hTopValue,hTopPos⟩ := hSpec.2.1
    obtain ⟨v,hv,hValue⟩ := h.value_exists_d hM hC hr (h.base.values.bounds hM.1 hOriginal).1
    have hOrder := h.value_antitone_d hM hC hr (hHeight.natural_d hM hC) hLe hValue hTopValue
    refine ⟨v,hv,hValue,?_⟩
    rcases hOrder with he | hlt
    · exact he ▸ hTopPos
    · exact ((omega_isOrdinal_d hM hC.omega).mem hv).transitive top hlt C.zero hTopPos

private theorem successor_le_iff_lt {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory) {C : ExpressionData M.Domain} (hC : C.Valid M)
    {r r' height : M.Domain} (hr : M.mem r C.omega) (hh : M.mem height C.omega) (hs : M.SuccessorOf r' r) :
    (r'=height ∨ M.mem r' height) ↔ M.mem r height := by
  have hH := (omega_isOrdinal_d hM hC.omega).mem hh
  constructor
  · rintro (he | hlt)
    · exact he ▸ hs.predecessor_mem
    · exact hH.transitive r' hlt r hs.predecessor_mem
  · intro hlt
    apply ordinal_subset_cases_d hM ((omega_isOrdinal_d hM hC.omega).mem (natural_successor_mem_d hM hC hr hs)) hH
    intro x hx
    rcases (hs x).mp hx with hxr | he
    · exact hH.transitive r hlt x hxr
    · exact (hM.1.eq_of_same_members x r he).symm ▸ hlt

theorem RowRun.parent_iff_lt_height_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory) {C : ExpressionData M.Domain} (hC : C.Valid M)
    {m : M.Domain} {R : RowStateSpace M.Domain} {V P H r W Q c a height : M.Domain} (h : RowRun M C m R V P H)
    (hAt : RowAt M R.states H r W Q) (hOriginal : MemPair M V c a) (hPos : M.mem C.zero a)
    (hHeight : HeightAt M C R V H c height) : (∃ p, MemPair M Q c p) ↔ M.mem r height := by
  have hr : M.mem r C.omega := by
    obtain ⟨_,_,hRow,_⟩ := hAt
    exact (h.graph.bounds hM.1 hRow).1
  obtain ⟨r',hs,hr'⟩ := hC.omega.1.2 r hr
  obtain ⟨W',Q',hAt'⟩ := h.at_exists_d hr'
  have hNext := h.at_next hM.1 hs hAt hAt'
  have hRow := h.at_numeric_d hM hC hAt
  have hRow' := h.at_numeric_d hM hC hAt'
  obtain ⟨d,hd,hD⟩ := hRow'.values.total c (h.base.values.bounds hM.1 hOriginal).1
  have hValue : RowValue M R.states R.values R.forests H r' c d :=
    ⟨W',(h.space.values W').mpr hRow'.values,Q',(h.space.forests Q').mpr hRow'.forest,hAt',hD⟩
  have hLive : M.mem C.zero d ↔ LiveRow M C.omega C.zero R.states R.values R.forests H c r' := by
    constructor
    · exact fun hp => ⟨d,hd,hValue,hp⟩
    · rintro ⟨v,_,hV,hp⟩
      exact h.value_unique hM.1 hV hValue ▸ hp
  exact (hRow.difference_positive_iff_d hM hC hNext.difference hD).symm.trans
    (hLive.trans ((h.live_iff_le_height_d hM hC hOriginal hPos hHeight hr').trans
      (successor_le_iff_lt hM hC hr (hHeight.natural_d hM hC) hs)))

structure HeightGraph (M : SetTheory.Structure.{u}) (C : ExpressionData M.Domain) (m : M.Domain)
    (R : RowStateSpace M.Domain) (V H Heights : M.Domain) : Prop where
  graph : Graph M Heights m C.omega
  rows : ∀ c height, MemPair M Heights c height ↔ M.mem c m ∧ HeightAt M C R V H c height

private def heightGraphSchema : Project.Delta0BinarySchema 7 where
  body := heightAtFormula (.bound 8) (.bound 7) (.bound 6) (.bound 5) (.bound 4) (.bound 3) (.bound 2) (.bound 1) (.bound 0)
  freeClosed := heightAtFormula_freeClosed _ _ _ _ _ _ _ _ _ rfl rfl rfl rfl rfl rfl rfl rfl rfl
  delta0 := heightAtFormula_delta0 _ _ _ _ _ _ _ _ _

theorem height_graph_exists_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory) {C : ExpressionData M.Domain} (hC : C.Valid M)
    {m : M.Domain} {R : RowStateSpace M.Domain} {V P H : M.Domain} (h : RowRun M C m R V P H) :
    ∃ Heights, HeightGraph M C m R V H Heights := by
  let e := ((((((oneEnv C.omega).push C.zero).push R.states).push R.values).push R.forests).push V).push H
  have hφ (c height : M.Domain) : Project.Formula.satisfies ((e.push c).push height) heightGraphSchema.body ↔ HeightAt M C R V H c height := by
    have ht := heightAtFormula_iff hM.1 ((e.push c).push height)
      ⟨.bound 8,.bound 7,.bound 7,.bound 7,.bound 7⟩ (.bound 6) (.bound 5) (.bound 4) (.bound 3) (.bound 2) (.bound 1) (.bound 0)
    exact ht
  obtain ⟨Heights,hSupport,hRaw⟩ := relation_comprehension_d hM heightGraphSchema e m C.omega
  have hRows (c height : M.Domain) : MemPair M Heights c height ↔ M.mem c m ∧ HeightAt M C R V H c height := by
    have hr := hRaw c height
    rw [hφ] at hr
    exact hr.trans ⟨fun h => ⟨h.1,h.2.2⟩,fun h => ⟨h.1,h.2.natural_d hM hC,h.2⟩⟩
  refine ⟨Heights,⟨hSupport,?_,?_⟩,hRows⟩
  · intro c hc
    obtain ⟨height,hHeight⟩ := height_at_exists_d hM hC h hc
    exact ⟨height,hHeight.natural_d hM hC,(hRows c height).mpr ⟨hc,hHeight⟩⟩
  · intro c height height' hAt hAt'
    exact ((hRows c height).mp hAt).2.unique_d hM hC h.base.values ((hRows c height').mp hAt').2

theorem HeightGraph.unique {M : SetTheory.Structure.{u}} (he : Extensional M) {C : ExpressionData M.Domain}
    {m : M.Domain} {R : RowStateSpace M.Domain} {V H Heights Heights' : M.Domain}
    (h : HeightGraph M C m R V H Heights) (h' : HeightGraph M C m R V H Heights') : Heights=Heights' := by
  apply h.graph.ext he h'.graph
  intro c _ height
  exact (h.rows c height).trans (h'.rows c height).symm

structure TopValueGraph (M : SetTheory.Structure.{u}) (C : ExpressionData M.Domain) (m : M.Domain)
    (R : RowStateSpace M.Domain) (H Heights Top : M.Domain) : Prop where
  graph : Graph M Top m C.omega
  rows : ∀ c v, MemPair M Top c v ↔ ∃ height, M.mem height C.omega ∧ MemPair M Heights c height ∧
    RowValue M R.states R.values R.forests H height c v

private def topValueSchema : Project.Delta0BinarySchema 6 where
  body := Project.Formula.existsMem (.bound 7) (.conj (memPairFormula (.bound 3) (.bound 2) (.bound 0))
    (rowValueFormula (.bound 7) (.bound 6) (.bound 5) (.bound 4) (.bound 0) (.bound 2) (.bound 1)))
  freeClosed := by
    have hValue := rowValueFormula_freeClosed (n := 9) (.bound 7) (.bound 6) (.bound 5) (.bound 4) (.bound 0) (.bound 2) (.bound 1)
      rfl rfl rfl rfl rfl rfl rfl
    simp [Project.Formula.existsMem,Definitional.Formula.FreeClosed,memPairFormula,codeFormula,pairFormula,Project.Formula.forallMem,hValue]
  delta0 := .existsMem _ (.conj (memPairFormula_delta0 _ _ _) (rowValueFormula_delta0 _ _ _ _ _ _ _))

theorem top_value_graph_exists_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory) {C : ExpressionData M.Domain} (hC : C.Valid M)
    {m : M.Domain} {R : RowStateSpace M.Domain} {V P H Heights : M.Domain} (h : RowRun M C m R V P H)
    (hHeights : HeightGraph M C m R V H Heights) : ∃ Top, TopValueGraph M C m R H Heights Top := by
  let e := (((((oneEnv C.omega).push R.states).push R.values).push R.forests).push H).push Heights
  have hφ (c v : M.Domain) : Project.Formula.satisfies ((e.push c).push v) topValueSchema.body ↔
      ∃ height, M.mem height C.omega ∧ MemPair M Heights c height ∧ RowValue M R.states R.values R.forests H height c v := by
    simp only [topValueSchema,Project.Formula.satisfies_existsMem_iff,Project.Formula.satisfies_conj_iff,
      memPairFormula_iff hM.1,rowValueFormula_iff hM.1]
    rfl
  obtain ⟨Top,hSupport,hRaw⟩ := relation_comprehension_d hM topValueSchema e m C.omega
  have hRows (c v : M.Domain) : MemPair M Top c v ↔
      ∃ height, M.mem height C.omega ∧ MemPair M Heights c height ∧ RowValue M R.states R.values R.forests H height c v := by
    have hr := hRaw c v
    rw [hφ] at hr
    refine hr.trans ⟨fun h => h.2.2,?_⟩
    rintro ⟨height,hh,hAt,hValue⟩
    exact ⟨(hHeights.graph.bounds hM.1 hAt).1,(hValue.bounds hM.1 h.space).2,height,hh,hAt,hValue⟩
  refine ⟨Top,⟨hSupport,?_,?_⟩,hRows⟩
  · intro c hc
    obtain ⟨height,hh,hAt⟩ := hHeights.graph.total c hc
    obtain ⟨v,hv,hValue⟩ := h.value_exists_d hM hC hh hc
    exact ⟨v,hv,(hRows c v).mpr ⟨height,hh,hAt,hValue⟩⟩
  · intro c v v' hAt hAt'
    obtain ⟨height,_,hh,hValue⟩ := (hRows c v).mp hAt
    obtain ⟨height',_,hh',hValue'⟩ := (hRows c v').mp hAt'
    have he := hHeights.graph.unique c height height' hh hh'
    subst height'
    exact h.value_unique hM.1 hValue hValue'

theorem TopValueGraph.unique {M : SetTheory.Structure.{u}} (he : Extensional M) {C : ExpressionData M.Domain}
    {m : M.Domain} {R : RowStateSpace M.Domain} {H Heights Top Top' : M.Domain}
    (h : TopValueGraph M C m R H Heights Top) (h' : TopValueGraph M C m R H Heights Top') : Top=Top' := by
  apply h.graph.ext he h'.graph
  intro c _ v
  exact (h.rows c v).trans (h'.rows c v).symm

theorem TopValueGraph.positive_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory) {C : ExpressionData M.Domain} (hC : C.Valid M)
    {m : M.Domain} {R : RowStateSpace M.Domain} {V P H Heights Top c a v : M.Domain} (hRun : RowRun M C m R V P H)
    (hH : HeightGraph M C m R V H Heights) (hTop : TopValueGraph M C m R H Heights Top)
    (hOriginal : MemPair M V c a) (hPos : M.mem C.zero a) (hAt : MemPair M Top c v) : M.mem C.zero v := by
  obtain ⟨height,_,hHeight,hValue⟩ := (hTop.rows c v).mp hAt
  obtain ⟨x,_,hX,hLive⟩ := (((hH.rows c height).mp hHeight).2.positive_spec hC hRun.base.values hOriginal hPos).2.1
  exact hRun.value_unique hM.1 hX hValue ▸ hLive

theorem TopValueGraph.le_initial_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory) {C : ExpressionData M.Domain} (hC : C.Valid M)
    {m : M.Domain} {R : RowStateSpace M.Domain} {V P H Heights Top c a v : M.Domain} (hRun : RowRun M C m R V P H)
    (hTop : TopValueGraph M C m R H Heights Top) (hOriginal : MemPair M V c a) (hAt : MemPair M Top c v) : v=a ∨ M.mem v a := by
  obtain ⟨height,hh,_,hValue⟩ := (hTop.rows c v).mp hAt
  have h0h : C.zero=height ∨ M.mem C.zero height := by
    classical
    by_cases he : height=C.zero
    · exact Or.inl he.symm
    · exact Or.inr ((hC.zero_mem_iff hM hh).mpr he)
  exact hRun.value_antitone_d hM hC hC.zero_nat hh h0h ((hRun.value_initial_iff_d hM).mpr hOriginal) hValue

theorem RowRun.top_parent_none_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory) {C : ExpressionData M.Domain} (hC : C.Valid M)
    {m : M.Domain} {R : RowStateSpace M.Domain} {V P H c a height W Q : M.Domain} (h : RowRun M C m R V P H)
    (hOriginal : MemPair M V c a) (hPos : M.mem C.zero a) (hHeight : HeightAt M C R V H c height)
    (hAt : RowAt M R.states H height W Q) : NoParent M m Q c := by
  intro p _ hParent
  exact SetTheory.KP.mem_irrefl_d (KP1Y.models_weakKP hM) height
    ((h.parent_iff_lt_height_d hM hC hAt hOriginal hPos hHeight).mp ⟨p,hParent⟩)

theorem HeightGraph.parent_height_bounds_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {m : M.Domain} {R : RowStateSpace M.Domain}
    {V P H Heights r W Q c p hc hp : M.Domain} (hRun : RowRun M C m R V P H)
    (hHeights : HeightGraph M C m R V H Heights) (hPositive : ∀ j v, MemPair M V j v → M.mem C.zero v)
    (hAt : RowAt M R.states H r W Q) (hParent : MemPair M Q c p)
    (hHC : MemPair M Heights c hc) (hHP : MemPair M Heights p hp) : M.mem r hc ∧ (r=hp ∨ M.mem r hp) := by
  have hRow := hRun.at_numeric_d hM hC hAt
  obtain ⟨hcM,hpM⟩ := hRow.forest.bounds hM.1 hParent
  obtain ⟨a,_,hA⟩ := hRun.base.values.total c hcM
  obtain ⟨b,_,hB⟩ := hRun.base.values.total p hpM
  have hSource := (hRun.parent_iff_lt_height_d hM hC hAt hA (hPositive c a hA) ((hHeights.rows c hc).mp hHC).2).mp ⟨p,hParent⟩
  obtain ⟨x,hx,hX⟩ := hRow.values.total p hpM
  obtain ⟨y,_,hY⟩ := hRow.values.total c hcM
  have hPos := (hRow.parentValues c p x y hParent hX hY).1
  have hValue : RowValue M R.states R.values R.forests H r p x :=
    ⟨W,(hRun.space.values W).mpr hRow.values,Q,(hRun.space.forests Q).mpr hRow.forest,hAt,hX⟩
  have hr := (omega_isOrdinal_d hM hC.omega).transitive hc (hHeights.graph.bounds hM.1 hHC).2 r hSource
  exact ⟨hSource,(hRun.live_iff_le_height_d hM hC hB (hPositive p b hB) ((hHeights.rows p hp).mp hHP).2 hr).mp ⟨x,hx,hValue,hPos⟩⟩

theorem mountain_height_top_exists_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {m : M.Domain} {R : RowStateSpace M.Domain} {V P H : M.Domain}
    (h : RowRun M C m R V P H) : ∃ Heights Top, HeightGraph M C m R V H Heights ∧ TopValueGraph M C m R H Heights Top := by
  obtain ⟨Heights,hHeights⟩ := height_graph_exists_d hM hC h
  obtain ⟨Top,hTop⟩ := top_value_graph_exists_d hM hC h hHeights
  exact ⟨Heights,Top,hHeights,hTop⟩

end KP1Y.OneYFinite
