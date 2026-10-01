import KP1Y.OneYMountainHeight
import KP1Y.OneYFrameMatrix
import KP1Y.OneYSelectionOrder
import KP1Y.FiniteNaturalRange

/-! 稀疏数值选择的深度矩阵恢复：仅当零值都位于继承森林的根时，
才用实际有限哨兵填充值把positive选择变为dense选择。
-/
namespace KP1Y.OneYFinite
open YesMetaZFC YesMetaZFC.SetTheory YesMetaZFC.SetTheory.Definitional
open KP1Y.Kuratowski KP1Y.Functions KP1Y.Naturals KP1Y.Bounded
universe u

/-- dense最右较小值选择的父森林，由其真实计算深度重新选择可完全恢复。 -/
theorem Selects.depth_selection_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {m F V P D : M.Domain}
    (hSel : Selects false M C m F V P) (hD : Graph M D m C.omega)
    (hDepth : ∀ c d, MemPair M D c d ↔ Depth M C m P c d) : Selects false M C m F D P := by
  have hw := omega_isOrdinal_d hM hC.omega
  have hDirect (c p : M.Domain) (hParent : MemPair M P c p) : RestrictedParent false M C m F D c p := by
    obtain ⟨d,hd,hDC⟩ := hD.total c (hSel.forest.bounds hM.1 hParent).1
    obtain ⟨e,he,hDP⟩ := hD.total p (hSel.forest.bounds hM.1 hParent).2
    have hSucc := depth_parent_successor_d hM hC hSel.forest hParent ((hDepth c d).mp hDC) ((hDepth p e).mp hDP)
    refine ⟨⟨hSel.parent_ancestor hParent,e,he,d,hd,hDP,hDC,hSucc.predecessor_mem,True.intro⟩,?_⟩
    intro q _ hCandidate
    have hpNat := hw.transitive m hSel.forest.width p (hSel.forest.bounds hM.1 hParent).2
    have hqNat := hw.transitive m hSel.forest.width q (hCandidate.1.bounds hM.1).1
    rcases hw.wellOrder.linear.compare q hqNat p hpNat with heq | hlt | hgt
    · exact Or.inl (hM.1.eq_of_same_members q p heq)
    · exact Or.inr hlt
    · obtain ⟨b,hb,d',_,hDQ,hDC',hBD,_⟩ := hCandidate.2
      have hDD := hD.unique c d' d hDC' hDC
      subst d'
      have hPQ := hSel.ancestor_of_between_d hM hC hParent hCandidate.1 hgt
      have hEB := ancestor_depth_lt_d hM hC hSel.forest hPQ ((hDepth p e).mp hDP) ((hDepth q b).mp hDQ)
      have hSub : M.MemberSubset d b := by
        intro x hx
        rcases (hSucc x).mp hx with hxe | heq
        · exact (hw.mem hb).transitive e hEB x hxe
        · exact (hM.1.eq_of_same_members x e heq).symm ▸ hEB
      exact False.elim (SetTheory.KP.mem_irrefl_d (KP1Y.models_weakKP hM) b (hSub b hBD))
  refine ⟨hSel.inherited,hD,hSel.forest,?_⟩
  intro c p
  constructor
  · exact hDirect c p
  · intro hRestricted
    have hSome : ∃ q, MemPair M P c q := by
      apply Classical.byContradiction
      intro hNone
      obtain ⟨a,_,d,_,_,hDC,hAD,_⟩ := hRestricted.1.2
      have hZero := depth_of_no_parent_d hM hC hSel.forest (fun q _ hq => hNone ⟨q,hq⟩) ((hDepth c d).mp hDC)
      exact hC.zero_empty a (hZero ▸ hAD)
    obtain ⟨q,hParent⟩ := hSome
    have hpq := restricted_parent_unique_d hM false hC hSel.inherited hRestricted (hDirect c q hParent)
    exact hpq.symm ▸ hParent

def FilledAt (M : SetTheory.Structure.{u}) (w zero V cap c d : M.Domain) : Prop :=
  ∃ a, M.mem a w ∧ MemPair M V c a ∧ ((a=zero ∧ d=cap) ∨ (a≠zero ∧ d=a))

private def filledSchema : Project.Delta0BinarySchema 4 where
  body := Project.Formula.existsMem (.bound 5) (.conj (memPairFormula (.bound 4) (.bound 2) (.bound 0))
    (.disj (.conj (Project.Formula.extensionalEq (.bound 0) (.bound 5)) (Project.Formula.extensionalEq (.bound 1) (.bound 3)))
      (.conj (.neg (Project.Formula.extensionalEq (.bound 0) (.bound 5))) (Project.Formula.extensionalEq (.bound 1) (.bound 0)))))
  freeClosed := by
    simp [memPairFormula,codeFormula,pairFormula,Project.Formula.forallMem,Project.Formula.existsMem,Definitional.Formula.FreeClosed]
  delta0 := .existsMem _ (.conj (memPairFormula_delta0 _ _ _)
    (.disj (.conj (.atom _ _ _) (.atom _ _ _)) (.conj (.neg (.atom _ _ _)) (.atom _ _ _))))

private theorem filledSchema_iff {M : SetTheory.Structure.{u}} (he : Extensional M)
    (w zero V cap c d : M.Domain) :
    Project.Formula.satisfies ((((((oneEnv w).push zero).push V).push cap).push c).push d) filledSchema.body ↔ FilledAt M w zero V cap c d := by
  simp only [filledSchema,FilledAt,Project.Formula.satisfies_existsMem_iff,Project.Formula.satisfies_conj_iff,
    memPairFormula_iff he,Project.Formula.satisfies_disj_iff,Project.Formula.satisfies_neg_iff,
    Project.Formula.satisfies_extensionalEq_iff_eq he]
  rfl

/-- 对实际有限值图构造哨兵填充值图；cap是实际内部自然数。 -/
theorem filled_graph_exists_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {w zero m V cap : M.Domain} (hV : Graph M V m w) (hCap : M.mem cap w) :
    ∃ W, Graph M W m w ∧ ∀ c d, MemPair M W c d ↔ FilledAt M w zero V cap c d := by
  obtain ⟨W,hSupport,hRaw⟩ := relation_comprehension_d hM filledSchema ((((oneEnv w).push zero).push V).push cap) m w
  have hRows (c d : M.Domain) : MemPair M W c d ↔ FilledAt M w zero V cap c d := by
    rw [hRaw c d,filledSchema_iff hM.1]
    constructor
    · exact fun h => h.2.2
    · rintro ⟨a,ha,hAt,hCase⟩
      refine ⟨(hV.bounds hM.1 hAt).1,?_,a,ha,hAt,hCase⟩
      rcases hCase with ⟨_,he⟩ | ⟨_,he⟩
      · exact he.symm ▸ hCap
      · exact he.symm ▸ ha
  refine ⟨W,⟨hSupport,?_,?_⟩,hRows⟩
  · intro c hc
    obtain ⟨a,ha,hAt⟩ := hV.total c hc
    classical
    by_cases he : a=zero
    · exact ⟨cap,hCap,(hRows c cap).mpr ⟨a,ha,hAt,Or.inl ⟨he,rfl⟩⟩⟩
    · exact ⟨a,ha,(hRows c a).mpr ⟨a,ha,hAt,Or.inr ⟨he,rfl⟩⟩⟩
  · intro c d e hd he
    obtain ⟨a,_,hA,hD⟩ := (hRows c d).mp hd
    obtain ⟨b,_,hB,hE⟩ := (hRows c e).mp he
    have hab := hV.unique c a b hA hB
    subst b
    rcases hD with ⟨hz,hd⟩ | ⟨hn,hd⟩ <;> rcases hE with ⟨hz',he⟩ | ⟨hn',he⟩
    · exact hd.trans he.symm
    · exact False.elim (hn' hz)
    · exact False.elim (hn hz')
    · exact hd.trans he.symm

private theorem filled_at_value_iff {M : SetTheory.Structure.{u}} (he : Extensional M) {w zero m V cap c a d : M.Domain}
    (hV : Graph M V m w) (hAt : MemPair M V c a) : FilledAt M w zero V cap c d ↔ ((a=zero ∧ d=cap) ∨ (a≠zero ∧ d=a)) := by
  constructor
  · rintro ⟨b,_,hB,hCase⟩
    exact hV.unique c b a hB hAt ▸ hCase
  · intro hCase
    exact ⟨a,hV.bounds he hAt |>.2,hAt,hCase⟩

private theorem filled_candidate_iff_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {m F V W cap c p : M.Domain}
    (hF : Forest M C.omega m F) (hV : Graph M V m C.omega) (hCap : M.mem cap C.omega)
    (hBound : ∀ i a, MemPair M V i a → M.mem a cap)
    (hRows : ∀ i a, MemPair M W i a ↔ FilledAt M C.omega C.zero V cap i a)
    (hZero : ∀ c, MemPair M V c C.zero → NoParent M m F c) :
    ParentCandidate false M C m F W c p ↔ ParentCandidate true M C m F V c p := by
  have hw := omega_isOrdinal_d hM hC.omega
  constructor
  · rintro ⟨hAnc,x,_,y,_,hWX,hWY,hXY,_⟩
    obtain ⟨a,ha,hVA⟩ := hV.total c (hAnc.bounds hM.1).2
    obtain ⟨b,hb,hVB⟩ := hV.total p (hAnc.bounds hM.1).1
    have ha0 : a≠C.zero := fun he => no_ancestor_of_no_parent_d hM hC hF (hZero c (he ▸ hVA)) hAnc
    have hYA : y=a := ((filled_at_value_iff hM.1 hV hVA).mp ((hRows c y).mp hWY)).elim
      (fun h => False.elim (ha0 h.1)) And.right
    subst y
    rcases (filled_at_value_iff hM.1 hV hVB).mp ((hRows p x).mp hWX) with ⟨_,hXCap⟩ | ⟨hb0,hXB⟩
    · have hCapA : M.mem cap a := hXCap ▸ hXY
      exact False.elim (SetTheory.KP.mem_irrefl_d (KP1Y.models_weakKP hM) cap
        ((hw.mem hCap).transitive a (hBound c a hVA) cap hCapA))
    · subst x
      exact ⟨hAnc,b,hb,a,ha,hVB,hVA,hXY,(hC.zero_mem_iff hM hb).mpr hb0⟩
  · rintro ⟨hAnc,x,hx,y,hy,hVX,hVY,hXY,hPos⟩
    have hx0 : x≠C.zero := fun he => hC.zero_empty C.zero (he ▸ hPos)
    have hy0 : y≠C.zero := fun he => hC.zero_empty x (he ▸ hXY)
    exact ⟨hAnc,x,hx,y,hy,(hRows p x).mpr ((filled_at_value_iff hM.1 hV hVX).mpr (Or.inr ⟨hx0,rfl⟩)),
      (hRows c y).mpr ((filled_at_value_iff hM.1 hV hVY).mpr (Or.inr ⟨hy0,rfl⟩)),hXY,True.intro⟩

/-- 实际有限哨兵填充把满足精确零根条件的positive选择化为dense选择。 -/
theorem Selects.filled_selection_exists_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {m F V P : M.Domain}
    (hSel : Selects true M C m F V P) (hZero : ∀ c, MemPair M V c C.zero → NoParent M m F c) :
    ∃ cap W, M.mem cap C.omega ∧ (∀ i a, MemPair M V i a → M.mem a cap) ∧
      (∀ c d, MemPair M W c d ↔ FilledAt M C.omega C.zero V cap c d) ∧ Selects false M C m F W P := by
  obtain ⟨cap,hCap,hBound⟩ := finite_natural_range_bounded_d hM hC.omega hSel.inherited.width hSel.values
  obtain ⟨W,hW,hRows⟩ := filled_graph_exists_d (zero := C.zero) hM hSel.values hCap
  have hCand (c p : M.Domain) := filled_candidate_iff_d hM hC hSel.inherited hSel.values hCap hBound hRows hZero (c := c) (p := p)
  refine ⟨cap,W,hCap,hBound,hRows,hSel.inherited,hW,hSel.forest,?_⟩
  intro c p
  rw [hSel.parents]
  simp only [RestrictedParent,hCand]

/-- 稀疏选择的真实深度恢复；零根条件保持为精确可实例化条件。 -/
theorem Selects.sparse_depth_selection_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {m F V P D : M.Domain}
    (hSel : Selects true M C m F V P) (hZero : ∀ c, MemPair M V c C.zero → NoParent M m F c)
    (hD : Graph M D m C.omega) (hDepth : ∀ c d, MemPair M D c d ↔ Depth M C m P c d) :
    Selects false M C m F D P := by
  obtain ⟨_,_,_,_,_,hFilled⟩ := hSel.filled_selection_exists_d hM hC hZero
  exact hFilled.depth_selection_d hM hC hD hDepth

/-- 实际差分的零值恰位于旧森林无父列，因此无额外零根假设。 -/
theorem RowNext.depth_selection_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {m V P W Q D : M.Domain}
    (hBase : NumericRow M C m V P) (hNext : RowNext M C m V P W Q)
    (hD : Graph M D m C.omega) (hDepth : ∀ c d, MemPair M D c d ↔ Depth M C m Q c d) :
    Selects false M C m P D Q := by
  apply hNext.selection.sparse_depth_selection_d hM hC ?_ hD hDepth
  intro c hZero p _ hParent
  exact hC.zero_empty C.zero ((hBase.difference_positive_iff_d hM hC hNext.difference hZero).mpr ⟨p,hParent⟩)

theorem RowRun.next_depth_selection_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {m : M.Domain} {R : RowStateSpace M.Domain}
    {V P H r s U F W Q D : M.Domain} (hRun : RowRun M C m R V P H)
    (hs : M.SuccessorOf s r) (hR : RowAt M R.states H r U F) (hS : RowAt M R.states H s W Q)
    (hD : Graph M D m C.omega) (hDepth : ∀ c d, MemPair M D c d ↔ Depth M C m Q c d) :
    Selects false M C m F D Q :=
  (hRun.at_next hM.1 hs hR hS).depth_selection_d hM hC (hRun.at_numeric_d hM hC hR) hD hDepth

end KP1Y.OneYFinite
