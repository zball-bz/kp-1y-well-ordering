import KP1Y.OneYActiveFrame
import KP1Y.OneYMountainRelations
import KP1Y.OneYSelectionDepth
import KP1Y.OneYSelectionBlocker
import KP1Y.OneYDecoratedMatrixExpansion

/-! 数值山形的实际Depth后缀与独立Top坐标比较。-/
namespace KP1Y.OneYFinite.NumericOrder
open YesMetaZFC YesMetaZFC.SetTheory YesMetaZFC.SetTheory.Definitional
open KP1Y.Kuratowski KP1Y.Functions KP1Y.Naturals KP1Y.Bounded KP1Y.Arithmetic
open KP1Y.OneYFinite
universe u

def DepthAt (M : SetTheory.Structure.{u}) (C : ExpressionData M.Domain) (m : M.Domain)
    (R : RowStateSpace M.Domain) (H c r d : M.Domain) : Prop :=
  ∃ W, M.mem W R.values ∧ ∃ Q, M.mem Q R.forests ∧ RowAt M R.states H r W Q ∧ Depth M C m Q c d

def depthAtFormula {n : Nat} (C : ExpressionData (Project.Term n)) (m : Project.Term n) (R : RowStateSpace (Project.Term n))
    (H c r d : Project.Term n) : Project.Formula 1 n :=
  Project.Formula.existsMem R.values (Project.Formula.existsMem R.forests.weaken
    (.conj (rowAtFormula R.states.weaken.weaken H.weaken.weaken r.weaken.weaken (.bound 1) (.bound 0))
      (depthFormula C.weaken.weaken m.weaken.weaken (.bound 0) c.weaken.weaken d.weaken.weaken)))

theorem depthAtFormula_delta0 {n : Nat} (C : ExpressionData (Project.Term n)) (m : Project.Term n) (R : RowStateSpace (Project.Term n))
    (H c r d : Project.Term n) : (depthAtFormula C m R H c r d).IsDelta0 :=
  .existsMem _ (.existsMem _ (.conj (rowAtFormula_delta0 _ _ _ _ _) (depthFormula_delta0 _ _ _ _ _)))

theorem depthAtFormula_freeClosed {n : Nat} {C : ExpressionData (Project.Term n)} (hC : C.Closed)
    {R : RowStateSpace (Project.Term n)} (hR : R.Closed) (m H c r d : Project.Term n)
    (hm : m.freeSupport=[]) (hH : H.freeSupport=[]) (hc : c.freeSupport=[]) (hr : r.freeSupport=[]) (hd : d.freeSupport=[]) :
    (depthAtFormula C m R H c r d).FreeClosed := by
  have hAt := rowAtFormula_freeClosed R.states.weaken.weaken H.weaken.weaken r.weaken.weaken (.bound 1) (.bound 0)
    (by simpa using hR.states) (by simpa using hH) (by simpa using hr) rfl rfl
  have hD := depthFormula_freeClosed hC.weaken.weaken m.weaken.weaken (.bound 0) c.weaken.weaken d.weaken.weaken
    (by simpa using hm) rfl (by simpa using hc) (by simpa using hd)
  simp [depthAtFormula,Project.Formula.existsMem,Definitional.Formula.FreeClosed,hR.values,hR.forests,hAt,hD]

theorem depthAtFormula_iff {M : SetTheory.Structure.{u}} (he : Extensional M) {n : Nat} (e : Env M n)
    (C : ExpressionData (Project.Term n)) (m : Project.Term n) (R : RowStateSpace (Project.Term n)) (H c r d : Project.Term n) :
    Project.Formula.satisfies e (depthAtFormula C m R H c r d) ↔ DepthAt M (C.eval e) (m.eval e) (R.eval e) (H.eval e) (c.eval e) (r.eval e) (d.eval e) := by
  simp only [depthAtFormula,DepthAt,Project.Formula.satisfies_existsMem_iff,Project.Formula.satisfies_conj_iff,
    rowAtFormula_iff he,depthFormula_iff he,ExpressionData.eval_weaken,Term.eval_weaken]
  rfl

def DepthEqAt (M : SetTheory.Structure.{u}) (C : ExpressionData M.Domain) (m : M.Domain)
    (R : RowStateSpace M.Domain) (H c z r : M.Domain) : Prop :=
  ∀ x, M.mem x C.omega → ∀ y, M.mem y C.omega → DepthAt M C m R H c r x → DepthAt M C m R H z r y → x=y

def DepthLtAt (M : SetTheory.Structure.{u}) (C : ExpressionData M.Domain) (m : M.Domain)
    (R : RowStateSpace M.Domain) (H c z r : M.Domain) : Prop :=
  ∃ x, M.mem x C.omega ∧ ∃ y, M.mem y C.omega ∧ DepthAt M C m R H c r x ∧ DepthAt M C m R H z r y ∧ M.mem x y

def depthEqAtFormula {n : Nat} (C : ExpressionData (Project.Term n)) (m : Project.Term n) (R : RowStateSpace (Project.Term n))
    (H c z r : Project.Term n) : Project.Formula 1 n :=
  Project.Formula.forallMem C.omega (Project.Formula.forallMem C.omega.weaken
    (.imp (.conj (depthAtFormula C.weaken.weaken m.weaken.weaken R.weaken.weaken H.weaken.weaken c.weaken.weaken r.weaken.weaken (.bound 1))
      (depthAtFormula C.weaken.weaken m.weaken.weaken R.weaken.weaken H.weaken.weaken z.weaken.weaken r.weaken.weaken (.bound 0)))
      (Project.Formula.extensionalEq (.bound 1) (.bound 0))))

def depthLtAtFormula {n : Nat} (C : ExpressionData (Project.Term n)) (m : Project.Term n) (R : RowStateSpace (Project.Term n))
    (H c z r : Project.Term n) : Project.Formula 1 n :=
  Project.Formula.existsMem C.omega (Project.Formula.existsMem C.omega.weaken
    (.conj (depthAtFormula C.weaken.weaken m.weaken.weaken R.weaken.weaken H.weaken.weaken c.weaken.weaken r.weaken.weaken (.bound 1))
      (.conj (depthAtFormula C.weaken.weaken m.weaken.weaken R.weaken.weaken H.weaken.weaken z.weaken.weaken r.weaken.weaken (.bound 0)) (.mem (.bound 1) (.bound 0)))))

private theorem depthAtPair_freeClosed {n : Nat} {C : ExpressionData (Project.Term n)} (hC : C.Closed)
    {R : RowStateSpace (Project.Term n)} (hR : R.Closed) (m H c z r : Project.Term n)
    (hm : m.freeSupport=[]) (hH : H.freeSupport=[]) (hc : c.freeSupport=[]) (hz : z.freeSupport=[]) (hr : r.freeSupport=[]) :
    (depthEqAtFormula C m R H c z r).FreeClosed ∧ (depthLtAtFormula C m R H c z r).FreeClosed := by
  have hL := depthAtFormula_freeClosed hC.weaken.weaken hR.weaken.weaken m.weaken.weaken H.weaken.weaken c.weaken.weaken r.weaken.weaken (.bound 1)
    (by simpa using hm) (by simpa using hH) (by simpa using hc) (by simpa using hr) rfl
  have hRight := depthAtFormula_freeClosed hC.weaken.weaken hR.weaken.weaken m.weaken.weaken H.weaken.weaken z.weaken.weaken r.weaken.weaken (.bound 0)
    (by simpa using hm) (by simpa using hH) (by simpa using hz) (by simpa using hr) rfl
  constructor <;> simp [depthEqAtFormula,depthLtAtFormula,Project.Formula.forallMem,Project.Formula.existsMem,Definitional.Formula.FreeClosed,hC.omega,hL,hRight]

theorem depthEqAtFormula_iff {M : SetTheory.Structure.{u}} (he : Extensional M) {n : Nat} (e : Env M n)
    (C : ExpressionData (Project.Term n)) (m : Project.Term n) (R : RowStateSpace (Project.Term n)) (H c z r : Project.Term n) :
    Project.Formula.satisfies e (depthEqAtFormula C m R H c z r) ↔ DepthEqAt M (C.eval e) (m.eval e) (R.eval e) (H.eval e) (c.eval e) (z.eval e) (r.eval e) := by
  simp only [depthEqAtFormula,DepthEqAt,Project.Formula.satisfies_forallMem_iff,Project.Formula.satisfies_imp_iff,
    Project.Formula.satisfies_conj_iff,depthAtFormula_iff he,Project.Formula.satisfies_extensionalEq_iff_eq he,
    ExpressionData.eval_weaken,RowStateSpace.eval_weaken,Term.eval_weaken,and_imp]
  rfl

theorem depthLtAtFormula_iff {M : SetTheory.Structure.{u}} (he : Extensional M) {n : Nat} (e : Env M n)
    (C : ExpressionData (Project.Term n)) (m : Project.Term n) (R : RowStateSpace (Project.Term n)) (H c z r : Project.Term n) :
    Project.Formula.satisfies e (depthLtAtFormula C m R H c z r) ↔ DepthLtAt M (C.eval e) (m.eval e) (R.eval e) (H.eval e) (c.eval e) (z.eval e) (r.eval e) := by
  simp only [depthLtAtFormula,DepthLtAt,Project.Formula.satisfies_existsMem_iff,Project.Formula.satisfies_conj_iff,
    depthAtFormula_iff he,Project.Formula.satisfies_mem_iff,ExpressionData.eval_weaken,RowStateSpace.eval_weaken,Term.eval_weaken]
  rfl

def DepthEqFrom (M : SetTheory.Structure.{u}) (C : ExpressionData M.Domain) (m : M.Domain)
    (R : RowStateSpace M.Domain) (H c z start : M.Domain) : Prop :=
  ∀ r, M.mem r C.omega → start=r ∨ M.mem start r → DepthEqAt M C m R H c z r

def DepthLtFrom (M : SetTheory.Structure.{u}) (C : ExpressionData M.Domain) (m : M.Domain)
    (R : RowStateSpace M.Domain) (H c z start : M.Domain) : Prop :=
  ∃ r, M.mem r C.omega ∧ (start=r ∨ M.mem start r) ∧
    (∀ q, M.mem q r → start=q ∨ M.mem start q → DepthEqAt M C m R H c z q) ∧ DepthLtAt M C m R H c z r

def KeyLE (M : SetTheory.Structure.{u}) (C : ExpressionData M.Domain) (m : M.Domain)
    (R : RowStateSpace M.Domain) (H c z start topC topZ : M.Domain) : Prop :=
  DepthLtFrom M C m R H c z start ∨ (DepthEqFrom M C m R H c z start ∧ (topC=topZ ∨ M.mem topC topZ))

def depthEqFromFormula {n : Nat} (C : ExpressionData (Project.Term n)) (m : Project.Term n) (R : RowStateSpace (Project.Term n))
    (H c z start : Project.Term n) : Project.Formula 1 n :=
  Project.Formula.forallMem C.omega (.imp (.disj (Project.Formula.extensionalEq start.weaken (.bound 0)) (.mem start.weaken (.bound 0)))
    (depthEqAtFormula C.weaken m.weaken R.weaken H.weaken c.weaken z.weaken (.bound 0)))

def depthLtFromFormula {n : Nat} (C : ExpressionData (Project.Term n)) (m : Project.Term n) (R : RowStateSpace (Project.Term n))
    (H c z start : Project.Term n) : Project.Formula 1 n :=
  Project.Formula.existsMem C.omega (.conj (.disj (Project.Formula.extensionalEq start.weaken (.bound 0)) (.mem start.weaken (.bound 0)))
    (.conj (Project.Formula.forallMem (.bound 0)
      (.imp (.disj (Project.Formula.extensionalEq start.weaken.weaken (.bound 0)) (.mem start.weaken.weaken (.bound 0)))
        (depthEqAtFormula C.weaken.weaken m.weaken.weaken R.weaken.weaken H.weaken.weaken c.weaken.weaken z.weaken.weaken (.bound 0))))
      (depthLtAtFormula C.weaken m.weaken R.weaken H.weaken c.weaken z.weaken (.bound 0))))

def keyLEFormula {n : Nat} (C : ExpressionData (Project.Term n)) (m : Project.Term n) (R : RowStateSpace (Project.Term n))
    (H c z start topC topZ : Project.Term n) : Project.Formula 1 n :=
  .disj (depthLtFromFormula C m R H c z start) (.conj (depthEqFromFormula C m R H c z start)
    (.disj (Project.Formula.extensionalEq topC topZ) (.mem topC topZ)))

theorem keyLEFormula_freeClosed {n : Nat} {C : ExpressionData (Project.Term n)} (hC : C.Closed)
    {R : RowStateSpace (Project.Term n)} (hR : R.Closed) (m H c z start topC topZ : Project.Term n)
    (hm : m.freeSupport=[]) (hH : H.freeSupport=[]) (hc : c.freeSupport=[]) (hz : z.freeSupport=[])
    (hs : start.freeSupport=[]) (htc : topC.freeSupport=[]) (htz : topZ.freeSupport=[]) : (keyLEFormula C m R H c z start topC topZ).FreeClosed := by
  have hRow := depthAtPair_freeClosed hC.weaken hR.weaken m.weaken H.weaken c.weaken z.weaken (.bound 0)
    (by simpa using hm) (by simpa using hH) (by simpa using hc) (by simpa using hz) rfl
  have hEarlier := depthAtPair_freeClosed hC.weaken.weaken hR.weaken.weaken m.weaken.weaken H.weaken.weaken c.weaken.weaken z.weaken.weaken (.bound 0)
    (by simpa using hm) (by simpa using hH) (by simpa using hc) (by simpa using hz) rfl
  simp [keyLEFormula,depthEqFromFormula,depthLtFromFormula,Project.Formula.forallMem,Project.Formula.existsMem,
    Definitional.Formula.FreeClosed,hC.omega,hs,htc,htz,hRow.1,hRow.2,hEarlier.1]

theorem keyLEFormula_iff {M : SetTheory.Structure.{u}} (he : Extensional M) {n : Nat} (e : Env M n)
    (C : ExpressionData (Project.Term n)) (m : Project.Term n) (R : RowStateSpace (Project.Term n)) (H c z start topC topZ : Project.Term n) :
    Project.Formula.satisfies e (keyLEFormula C m R H c z start topC topZ) ↔
      KeyLE M (C.eval e) (m.eval e) (R.eval e) (H.eval e) (c.eval e) (z.eval e) (start.eval e) (topC.eval e) (topZ.eval e) := by
  simp only [keyLEFormula,KeyLE,depthEqFromFormula,DepthEqFrom,depthLtFromFormula,DepthLtFrom,
    Project.Formula.satisfies_disj_iff,Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_forallMem_iff,
    Project.Formula.satisfies_existsMem_iff,Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_extensionalEq_iff_eq he,
    Project.Formula.satisfies_mem_iff,depthEqAtFormula_iff he,depthLtAtFormula_iff he,
    ExpressionData.eval_weaken,RowStateSpace.eval_weaken,Term.eval_weaken]
  rfl

theorem depth_at_iff_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {m V P H : M.Domain} {R : RowStateSpace M.Domain}
    (hRun : RowRun M C m R V P H) {r W Q : M.Domain} (hAt : RowAt M R.states H r W Q) (c d : M.Domain) :
    DepthAt M C m R H c r d ↔ Depth M C m Q c d := by
  constructor
  · rintro ⟨W',_,Q',_,hAt',hDepth⟩
    exact (hRun.at_unique hM.1 hAt' hAt).2 ▸ hDepth
  · intro hDepth
    have hRow := hRun.at_numeric_d hM hC hAt
    exact ⟨W,(hRun.space.values W).mpr hRow.values,Q,(hRun.space.forests Q).mpr hRow.forest,hAt,hDepth⟩

def ZerosAtRoots (M : SetTheory.Structure.{u}) (m F W zero : M.Domain) : Prop :=
  ∀ c, M.mem c m → MemPair M W c zero → NoParent M m F c

def CommonAncestors (M : SetTheory.Structure.{u}) (C : ExpressionData M.Domain) (m F c z : M.Domain) : Prop :=
  ∀ p, M.mem p m → (Ancestor M C m F p c ↔ Ancestor M C m F p z)

def zerosAtRootsFormula {n : Nat} (m F W zero : Project.Term n) : Project.Formula 1 n :=
  Project.Formula.forallMem m (.imp (memPairFormula W.weaken (.bound 0) zero.weaken) (noParentFormula m.weaken F.weaken (.bound 0)))

def commonAncestorsFormula {n : Nat} (C : ExpressionData (Project.Term n)) (m F c z : Project.Term n) : Project.Formula 1 n :=
  Project.Formula.forallMem m (.iff (ancestorFormula C.weaken m.weaken F.weaken (.bound 0) c.weaken)
    (ancestorFormula C.weaken m.weaken F.weaken (.bound 0) z.weaken))

theorem zerosAtRootsFormula_iff {M : SetTheory.Structure.{u}} (he : Extensional M) {n : Nat} (e : Env M n)
    (m F W zero : Project.Term n) : Project.Formula.satisfies e (zerosAtRootsFormula m F W zero) ↔ ZerosAtRoots M (m.eval e) (F.eval e) (W.eval e) (zero.eval e) := by
  simp only [zerosAtRootsFormula,ZerosAtRoots,Project.Formula.satisfies_forallMem_iff,Project.Formula.satisfies_imp_iff,
    memPairFormula_iff he,noParentFormula_iff he,Term.eval_weaken]
  rfl

theorem commonAncestorsFormula_iff {M : SetTheory.Structure.{u}} (he : Extensional M) {n : Nat} (e : Env M n)
    (C : ExpressionData (Project.Term n)) (m F c z : Project.Term n) :
    Project.Formula.satisfies e (commonAncestorsFormula C m F c z) ↔ CommonAncestors M (C.eval e) (m.eval e) (F.eval e) (c.eval e) (z.eval e) := by
  simp only [commonAncestorsFormula,CommonAncestors,Project.Formula.satisfies_forallMem_iff,Project.Formula.satisfies_iff_iff,
    ancestorFormula_iff he,ExpressionData.eval_weaken,Term.eval_weaken]
  rfl

private theorem common_all_d {M : SetTheory.Structure.{u}} (he : Extensional M)
    {C : ExpressionData M.Domain} {m F c z : M.Domain} (hCommon : CommonAncestors M C m F c z) :
    ∀ p, Ancestor M C m F p c ↔ Ancestor M C m F p z := by
  intro p
  classical
  by_cases hp : M.mem p m
  · exact hCommon p hp
  · exact iff_of_false (fun h => hp (h.bounds he).1) (fun h => hp (h.bounds he).1)

theorem sparse_depth_compare_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {m F W Q c z x y dc dz : M.Domain}
    (hSel : Selects true M C m F W Q) (hZero : ZerosAtRoots M m F W C.zero) (hCommon : CommonAncestors M C m F c z)
    (hX : MemPair M W c x) (hY : MemPair M W z y) (hx : M.mem C.zero x) (hy : M.mem C.zero y) (hLe : x=y ∨ M.mem x y)
    (hDC : Depth M C m Q c dc) (hDZ : Depth M C m Q z dz) :
    (dc=dz ∨ M.mem dc dz) ∧ (dc=dz → ParentRowsEqual M Q c z) := by
  obtain ⟨cap,Filled,_,_,hRows,hFilled⟩ := hSel.filled_selection_exists_d hM hC
    (fun c hc => hZero c (hSel.values.bounds hM.1 hc).1 hc)
  have hFX := (hRows c x).mpr ⟨x,(hSel.values.bounds hM.1 hX).2,hX,Or.inr ⟨fun he => hC.zero_empty C.zero (he ▸ hx),rfl⟩⟩
  have hFY := (hRows z y).mpr ⟨y,(hSel.values.bounds hM.1 hY).2,hY,Or.inr ⟨fun he => hC.zero_empty C.zero (he ▸ hy),rfl⟩⟩
  have hChains := common_all_d hM.1 hCommon
  exact ⟨hFilled.depth_mono_of_common_chain_d hM hC hChains hFX hFY hLe hDC hDZ,
    fun he => hFilled.parent_rows_eq_of_common_chain_depth_d hM hC hChains hDC (he.symm ▸ hDZ)⟩

theorem row_next_zeros_at_roots_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {m V P W Q : M.Domain}
    (hBase : NumericRow M C m V P) (hNext : RowNext M C m V P W Q) : ZerosAtRoots M m P W C.zero := by
  intro c _ hZero p _ hParent
  exact hC.zero_empty C.zero ((hBase.difference_positive_iff_d hM hC hNext.difference hZero).mpr ⟨p,hParent⟩)

theorem row_next_blocker_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {m V P W Q c q p : M.Domain}
    (hBase : NumericRow M C m V P) (hNext : RowNext M C m V P W Q)
    (hOld : MemPair M P c q) (hNew : MemPair M Q c p) (hDistinct : p≠q) :
    ∃ z, M.mem z m ∧ (z=q ∨ Ancestor M C m Q z q) ∧ MemPair M Q z p ∧
      ∀ x y, MemPair M W c x → MemPair M W z y → x=y ∨ M.mem x y := by
  have hZeros := row_next_zeros_at_roots_d hM hC hBase hNext
  obtain ⟨cap,Filled,_,_,hRows,hFilled⟩ := hNext.selection.filled_selection_exists_d hM hC
    (fun c hc => hZeros c (hNext.selection.values.bounds hM.1 hc).1 hc)
  obtain ⟨z,hz,hPath,hParent,hCompare⟩ := hFilled.blocker_d hM hC hOld hNew hDistinct
  refine ⟨z,hz,hPath,hParent,?_⟩
  intro x y hX hY
  have hNonzero (s v : M.Domain) (hP : MemPair M Q s p) (hV : MemPair M W s v) : v≠C.zero := by
    obtain ⟨a,_,b,_,_,hB,hab,_⟩ := hNext.selection.parent_values hP
    have hEq := hNext.selection.values.unique s b v hB hV
    subst b
    exact fun he => hC.zero_empty a (he ▸ hab)
  exact hCompare x y
    ((hRows c x).mpr ⟨x,(hNext.selection.values.bounds hM.1 hX).2,hX,Or.inr ⟨hNonzero c x hNew hX,rfl⟩⟩)
    ((hRows z y).mpr ⟨y,(hNext.selection.values.bounds hM.1 hY).2,hY,Or.inr ⟨hNonzero z y hParent hY,rfl⟩⟩)

theorem difference_mono_common_parent_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {m W Q D c z p a b x y : M.Domain}
    (hRow : NumericRow M C m W Q) (hD : DifferenceGraph M C m W Q D)
    (hCParent : MemPair M Q c p) (hZParent : MemPair M Q z p)
    (hA : MemPair M W c a) (hB : MemPair M W z b) (hLe : a=b ∨ M.mem a b)
    (hX : MemPair M D c x) (hY : MemPair M D z y) : x=y ∨ M.mem x y := by
  have hw := omega_isOrdinal_d hM hC.omega
  obtain ⟨v,_,hV⟩ := hRow.values.total p (hRow.forest.bounds hM.1 hCParent).2
  have hDX := hD.at_parent_d hM hRow.values hRow.forest hCParent hA hV hX
  have hDY := hD.at_parent_d hM hRow.values hRow.forest hZParent hB hV hY
  have hSumX := truncated_difference_add_inverse_d hM hC hDX (Or.inr (hRow.parentValues c p v a hCParent hV hA).2)
  have hSumY := truncated_difference_add_inverse_d hM hC hDY (Or.inr (hRow.parentValues z p v b hZParent hV hB).2)
  have hx := (hD.graph.bounds hM.1 hX).2
  have hy := (hD.graph.bounds hM.1 hY).2
  rcases hw.wellOrder.linear.compare x hx y hy with he | hlt | hgt
  · exact Or.inl (hM.1.eq_of_same_members x y he)
  · exact Or.inr hlt
  · have hBA := sum_strict_right_d hM (hw.mem (hRow.values.bounds hM.1 hV).2) hSumY hSumX hgt
    rcases hLe with he | hAB
    · exact False.elim (SetTheory.KP.mem_irrefl_d (KP1Y.models_weakKP hM) b (he ▸ hBA))
    · exact False.elim (SetTheory.KP.mem_irrefl_d (KP1Y.models_weakKP hM) b
        ((hw.mem (hRow.values.bounds hM.1 hB).2).transitive a hAB b hBA))

theorem depth_eq_tail_of_no_parents_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {m V P H : M.Domain} {R : RowStateSpace M.Domain}
    (hRun : RowRun M C m R V P H) {r W Q c z : M.Domain} (hAt : RowAt M R.states H r W Q)
    (hNoC : NoParent M m Q c) (hNoZ : NoParent M m Q z) : DepthEqFrom M C m R H c z r := by
  intro s hs hLe x _ y _ hX hY
  obtain ⟨U,F,hS⟩ := hRun.at_exists_d hs
  have hRow := hRun.at_numeric_d hM hC hAt
  have hFuture := hRun.at_numeric_d hM hC hS
  have hNo {c : M.Domain} (hNone : NoParent M m Q c) : NoParent M m F c := by
    intro p _ hParent
    exact no_ancestor_of_no_parent_d hM hC hRow.forest hNone
      (hRun.ancestor_lower_d hM hC hAt hS hLe (ancestor_direct_d hM hC hFuture.forest hParent))
  exact (depth_of_no_parent_d hM hC hFuture.forest (hNo hNoC) ((depth_at_iff_d hM hC hRun hS c x).mp hX)).trans
    (depth_of_no_parent_d hM hC hFuture.forest (hNo hNoZ) ((depth_at_iff_d hM hC hRun hS z y).mp hY)).symm

theorem top_at_current_of_no_parent_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {m V P H : M.Domain} {R : RowStateSpace M.Domain}
    (hRun : RowRun M C m R V P H) (hPositive : ∀ c a, MemPair M V c a → M.mem C.zero a) {Heights Top : M.Domain}
    (hHeights : HeightGraph M C m R V H Heights) (hTop : TopValueGraph M C m R H Heights Top)
    {r W Q c x : M.Domain} (hAt : RowAt M R.states H r W Q) (hX : MemPair M W c x)
    (hPos : M.mem C.zero x) (hNo : NoParent M m Q c) : MemPair M Top c x := by
  have hRow := hRun.at_numeric_d hM hC hAt
  have hc := (hRow.values.bounds hM.1 hX).1
  have hr : M.mem r C.omega := by
    obtain ⟨_,_,hR,_⟩ := hAt
    exact (hRun.graph.bounds hM.1 hR).1
  obtain ⟨a,_,hA⟩ := hRun.base.values.total c hc
  obtain ⟨height,hHeightNat,hHeight⟩ := hHeights.graph.total c hc
  have hHeightAt := ((hHeights.rows c height).mp hHeight).2
  have hValue : RowValue M R.states R.values R.forests H r c x :=
    ⟨W,(hRun.space.values W).mpr hRow.values,Q,(hRun.space.forests Q).mpr hRow.forest,hAt,hX⟩
  have hLe := (hRun.live_iff_le_height_d hM hC hA (hPositive c a hA) hHeightAt hr).mp
    ⟨x,(hRow.values.bounds hM.1 hX).2,hValue,hPos⟩
  have hNot : ¬M.mem r height := by
    intro hlt
    obtain ⟨p,hParent⟩ := (hRun.parent_iff_lt_height_d hM hC hAt hA (hPositive c a hA) hHeightAt).mpr hlt
    exact hNo p (hRow.forest.bounds hM.1 hParent).2 hParent
  have hrHeight := hLe.resolve_right hNot
  exact (hTop.rows c x).mpr ⟨height,hHeightNat,hHeight,hrHeight ▸ hValue⟩

private theorem successor_le_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {r s q : M.Domain}
    (hr : M.mem r C.omega) (hq : M.mem q C.omega) (hs : M.SuccessorOf s r) (hrq : M.mem r q) : s=q ∨ M.mem s q := by
  have hw := omega_isOrdinal_d hM hC.omega
  apply ordinal_subset_cases_d hM (hw.mem (natural_successor_mem_d hM hC hr hs)) (hw.mem hq)
  intro x hx
  rcases (hs x).mp hx with hxr | he
  · exact (hw.mem hq).transitive r hrq x hxr
  · exact (hM.1.eq_of_same_members x r he).symm ▸ hrq

theorem key_prepend_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {m : M.Domain} {R : RowStateSpace M.Domain}
    {H c z r s topC topZ : M.Domain} (hr : M.mem r C.omega) (hs : M.SuccessorOf s r)
    (hCurrent : DepthEqAt M C m R H c z r) (hNext : KeyLE M C m R H c z s topC topZ) : KeyLE M C m R H c z r topC topZ := by
  have hw := omega_isOrdinal_d hM hC.omega
  rcases hNext with ⟨q,hq,hSQ,hEarlier,hLess⟩ | ⟨hEq,hTop⟩
  · have hrq : M.mem r q := hSQ.elim (fun he => he ▸ hs.predecessor_mem)
      (fun hsq => (hw.mem hq).transitive s hsq r hs.predecessor_mem)
    refine Or.inl ⟨q,hq,Or.inr hrq,?_,hLess⟩
    intro p hp hRP
    rcases hRP with he | hrp
    · exact he ▸ hCurrent
    · exact hEarlier p hp (successor_le_d hM hC hr (hw.transitive q hq p hp) hs hrp)
  · refine Or.inr ⟨?_,hTop⟩
    intro q hq hRQ
    rcases hRQ with he | hrq
    · exact he ▸ hCurrent
    · exact hEq q hq (successor_le_d hM hC hr hq hs hrq)

private theorem key_lt_at_start_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {m : M.Domain} {R : RowStateSpace M.Domain}
    {H c z r topC topZ : M.Domain} (hr : M.mem r C.omega) (hAt : DepthLtAt M C m R H c z r) : KeyLE M C m R H c z r topC topZ := by
  refine Or.inl ⟨r,hr,Or.inl rfl,?_,hAt⟩
  intro q hqr hRQ
  apply False.elim
  rcases hRQ with he | hrq
  · exact SetTheory.KP.mem_irrefl_d (KP1Y.models_weakKP hM) r (he.symm ▸ hqr)
  · exact SetTheory.KP.mem_irrefl_d (KP1Y.models_weakKP hM) r
      (((omega_isOrdinal_d hM hC.omega).mem hr).transitive q hqr r hrq)

private def keyValueEnv {M : SetTheory.Structure.{u}} (C : ExpressionData M.Domain) (m : M.Domain)
    (R : RowStateSpace M.Domain) (H c z topC topZ : M.Domain) : Env M 14 :=
  (((((((((((((oneEnv C.omega).push C.zero).push C.one).push C.sequences).push C.expressions).push m).push R.values).push R.forests).push R.states).push H).push c).push z).push topC).push topZ

private def keyValueSchema : Project.UnarySchema 14 where
  body := Project.Formula.forallMem (.bound 14) (Project.Formula.forallMem (.bound 9) (Project.Formula.forallMem (.bound 9)
    (Project.Formula.forallMem (.bound 10) (Project.Formula.forallMem (.bound 18)
      (.imp (.conj (rowAtFormula (.bound 11) (.bound 10) (.bound 4) (.bound 3) (.bound 2))
        (.conj (selectsFormula true ⟨.bound 19,.bound 18,.bound 17,.bound 16,.bound 15⟩ (.bound 14) (.bound 1) (.bound 3) (.bound 2))
          (.conj (zerosAtRootsFormula (.bound 14) (.bound 1) (.bound 3) (.bound 18))
            (.conj (commonAncestorsFormula ⟨.bound 19,.bound 18,.bound 17,.bound 16,.bound 15⟩ (.bound 14) (.bound 1) (.bound 9) (.bound 8))
              (.conj (memPairFormula (.bound 3) (.bound 9) (.bound 5)) (.conj (memPairFormula (.bound 3) (.bound 8) (.bound 0))
                (.conj (.mem (.bound 18) (.bound 5)) (.conj (.mem (.bound 18) (.bound 0))
                  (.disj (Project.Formula.extensionalEq (.bound 5) (.bound 0)) (.mem (.bound 5) (.bound 0)))))))))))
        (keyLEFormula ⟨.bound 19,.bound 18,.bound 17,.bound 16,.bound 15⟩ (.bound 14) ⟨.bound 13,.bound 12,.bound 11⟩
          (.bound 10) (.bound 9) (.bound 8) (.bound 4) (.bound 7) (.bound 6)))))))
  freeClosed := by
    have hC : (⟨.bound 19,.bound 18,.bound 17,.bound 16,.bound 15⟩ : ExpressionData (Project.Term 20)).Closed := ⟨rfl,rfl,rfl,rfl,rfl⟩
    have hR : (⟨.bound 13,.bound 12,.bound 11⟩ : RowStateSpace (Project.Term 20)).Closed := ⟨rfl,rfl,rfl⟩
    have hAt := rowAtFormula_freeClosed (n := 20) (.bound 11) (.bound 10) (.bound 4) (.bound 3) (.bound 2) rfl rfl rfl rfl rfl
    have hSel := selectsFormula_freeClosed true hC (.bound 14) (.bound 1) (.bound 3) (.bound 2) rfl rfl rfl rfl
    have hAncC := ancestorFormula_freeClosed hC.weaken ((.bound 14 : Project.Term 20).weaken) ((.bound 1 : Project.Term 20).weaken) (.bound 0) ((.bound 9 : Project.Term 20).weaken) (by simp) (by simp) rfl (by simp)
    have hAncZ := ancestorFormula_freeClosed hC.weaken ((.bound 14 : Project.Term 20).weaken) ((.bound 1 : Project.Term 20).weaken) (.bound 0) ((.bound 8 : Project.Term 20).weaken) (by simp) (by simp) rfl (by simp)
    have hKey := keyLEFormula_freeClosed hC hR (.bound 14) (.bound 10) (.bound 9) (.bound 8) (.bound 4) (.bound 7) (.bound 6) rfl rfl rfl rfl rfl rfl rfl
    simp [Definitional.Formula.FreeClosed,Project.Formula.forallMem,Project.Formula.existsMem,zerosAtRootsFormula,
      commonAncestorsFormula,noParentFormula,memPairFormula,codeFormula,pairFormula,hAt,hSel,hAncC,hAncZ,hKey]

private theorem keyValueSchema_iff {M : SetTheory.Structure.{u}} (he : Extensional M)
    (C : ExpressionData M.Domain) (m : M.Domain) (R : RowStateSpace M.Domain) (H c z topC topZ x : M.Domain) :
    Project.Formula.satisfies ((keyValueEnv C m R H c z topC topZ).push x) keyValueSchema.body ↔
      ∀ r, M.mem r C.omega → ∀ W, M.mem W R.values → ∀ Q, M.mem Q R.forests → ∀ F, M.mem F R.forests →
      ∀ y, M.mem y C.omega → RowAt M R.states H r W Q → Selects true M C m F W Q →
      ZerosAtRoots M m F W C.zero → CommonAncestors M C m F c z → MemPair M W c x → MemPair M W z y →
      M.mem C.zero x → M.mem C.zero y → (x=y ∨ M.mem x y) → KeyLE M C m R H c z r topC topZ := by
  simp only [keyValueSchema,Project.Formula.satisfies_forallMem_iff,Project.Formula.satisfies_imp_iff,
    Project.Formula.satisfies_conj_iff,rowAtFormula_iff he,selectsFormula_iff he,zerosAtRootsFormula_iff he,
    commonAncestorsFormula_iff he,memPairFormula_iff he,Project.Formula.satisfies_mem_iff,
    Project.Formula.satisfies_disj_iff,Project.Formula.satisfies_extensionalEq_iff_eq he,keyLEFormula_iff he,and_imp]
  rfl

/-- 共同候选链下的正值弱序，决定整个真实Depth后缀及独立Top坐标的弱序。
递归参数是实际左值；每次非根步骤严格减小真实difference。归纳仅施于keyValueSchema。
-/
theorem key_le_of_common_values_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {m V P H : M.Domain} {R : RowStateSpace M.Domain}
    (hRun : RowRun M C m R V P H) (hPositive : ∀ c a, MemPair M V c a → M.mem C.zero a)
    {Heights Top : M.Domain} (hHeights : HeightGraph M C m R V H Heights) (hTop : TopValueGraph M C m R H Heights Top)
    {c z topC topZ r W Q F x y : M.Domain} (hTopC : MemPair M Top c topC) (hTopZ : MemPair M Top z topZ)
    (hAt : RowAt M R.states H r W Q) (hSel : Selects true M C m F W Q)
    (hZero : ZerosAtRoots M m F W C.zero) (hCommon : CommonAncestors M C m F c z)
    (hX : MemPair M W c x) (hY : MemPair M W z y) (hx : M.mem C.zero x) (hy : M.mem C.zero y) (hLe : x=y ∨ M.mem x y) :
    KeyLE M C m R H c z r topC topZ := by
  have hc := (hSel.values.bounds hM.1 hX).1
  have hz := (hSel.values.bounds hM.1 hY).1
  have hAll := KP1Y.induction_d hM keyValueSchema (keyValueEnv C m R H c z topC topZ) (by
    intro x ih
    apply (keyValueSchema_iff hM.1 C m R H c z topC topZ x).mpr
    intro r hr W _ Q hQMem F _ y _ hAt hSel hZero hCommon hX hY hx hy hLe
    have hRow := hRun.at_numeric_d hM hC hAt
    obtain ⟨dc,hDC⟩ := depth_exists_d hM hC hRow.forest hc
    obtain ⟨dz,hDZ⟩ := depth_exists_d hM hC hRow.forest hz
    obtain ⟨hCompare,hSame⟩ := sparse_depth_compare_d hM hC hSel hZero hCommon hX hY hx hy hLe hDC hDZ
    rcases hCompare with hEq | hLess
    · have hCurrent : DepthEqAt M C m R H c z r := by
        intro a _ b _ hDA hDB
        have ha := depth_unique_d hM hC hRow.forest ((depth_at_iff_d hM hC hRun hAt c a).mp hDA) hDC
        have hb := depth_unique_d hM hC hRow.forest ((depth_at_iff_d hM hC hRun hAt z b).mp hDB) hDZ
        exact ha.trans (hEq.trans hb.symm)
      have hParents := hSame hEq
      classical
      by_cases hNoC : NoParent M m Q c
      · have hNoZ : NoParent M m Q z := fun p hp hParent => hNoC p hp ((hParents p).mpr hParent)
        have hCX := hTop.graph.unique c topC x hTopC (top_at_current_of_no_parent_d hM hC hRun hPositive hHeights hTop hAt hX hx hNoC)
        have hZY := hTop.graph.unique z topZ y hTopZ (top_at_current_of_no_parent_d hM hC hRun hPositive hHeights hTop hAt hY hy hNoZ)
        exact Or.inr ⟨depth_eq_tail_of_no_parents_d hM hC hRun hAt hNoC hNoZ,by simpa only [hCX,hZY] using hLe⟩
      · have hSome : ∃ p, MemPair M Q c p := by
          apply Classical.byContradiction
          intro hNone
          exact hNoC (fun p _ hp => hNone ⟨p,hp⟩)
        obtain ⟨p,hCP⟩ := hSome
        have hZP := (hParents p).mp hCP
        obtain ⟨next,hs,hNextNat⟩ := hC.omega.1.2 r hr
        obtain ⟨WN,QN,hAtN⟩ := hRun.at_exists_d hNextNat
        have hNext := hRun.at_next hM.1 hs hAt hAtN
        have hRowN := hRun.at_numeric_d hM hC hAtN
        obtain ⟨x',hx',hX'⟩ := hRowN.values.total c hc
        obtain ⟨y',hy',hY'⟩ := hRowN.values.total z hz
        have hSmall := hRow.difference_strict_d hM hC hNext.difference hX hX' hx
        have hPosX := (hRow.difference_positive_iff_d hM hC hNext.difference hX').mpr ⟨p,hCP⟩
        have hPosY := (hRow.difference_positive_iff_d hM hC hNext.difference hY').mpr ⟨p,hZP⟩
        have hLeNext := difference_mono_common_parent_d hM hC hRow hNext.difference hCP hZP hX hY hLe hX' hY'
        have hCommonNext : CommonAncestors M C m Q c z := fun p _ => ancestor_iff_of_parent_rows_eq_d hM hC hRow.forest hParents p
        have hKey := (keyValueSchema_iff hM.1 C m R H c z topC topZ x').mp (ih x' hSmall)
          next hNextNat WN ((hRun.space.values WN).mpr hRowN.values) QN ((hRun.space.forests QN).mpr hRowN.forest) Q hQMem y' hy'
          hAtN hNext.selection (row_next_zeros_at_roots_d hM hC hRow hNext) hCommonNext hX' hY' hPosX hPosY hLeNext
        exact key_prepend_d hM hC hr hs hCurrent hKey
    · exact key_lt_at_start_d hM hC hr ⟨dc,hDC.1,dz,hDZ.1,(depth_at_iff_d hM hC hRun hAt c dc).mpr hDC,
        (depth_at_iff_d hM hC hRun hAt z dz).mpr hDZ,hLess⟩)
  have hRow := hRun.at_numeric_d hM hC hAt
  have hr : M.mem r C.omega := by
    obtain ⟨_,_,hR,_⟩ := hAt
    exact (hRun.graph.bounds hM.1 hR).1
  exact (keyValueSchema_iff hM.1 C m R H c z topC topZ x).mp (hAll x) r hr W ((hRun.space.values W).mpr hRow.values)
    Q ((hRun.space.forests Q).mpr hRow.forest) F ((hRun.space.forests F).mpr hSel.inherited) y (hSel.values.bounds hM.1 hY).2
    hAt hSel hZero hCommon hX hY hx hy hLe

theorem depthEqAtFormula_delta0 {n : Nat} (C : ExpressionData (Project.Term n)) (m : Project.Term n) (R : RowStateSpace (Project.Term n))
    (H c z r : Project.Term n) : (depthEqAtFormula C m R H c z r).IsDelta0 :=
  .forallMem _ (.forallMem _ (.imp (.conj (depthAtFormula_delta0 _ _ _ _ _ _ _) (depthAtFormula_delta0 _ _ _ _ _ _ _)) (.atom _ _ _)))

theorem depthLtAtFormula_delta0 {n : Nat} (C : ExpressionData (Project.Term n)) (m : Project.Term n) (R : RowStateSpace (Project.Term n))
    (H c z r : Project.Term n) : (depthLtAtFormula C m R H c z r).IsDelta0 :=
  .existsMem _ (.existsMem _ (.conj (depthAtFormula_delta0 _ _ _ _ _ _ _) (.conj (depthAtFormula_delta0 _ _ _ _ _ _ _) (.mem _ _))))

theorem depthEqFromFormula_delta0 {n : Nat} (C : ExpressionData (Project.Term n)) (m : Project.Term n) (R : RowStateSpace (Project.Term n))
    (H c z r : Project.Term n) : (depthEqFromFormula C m R H c z r).IsDelta0 :=
  .forallMem _ (.imp (.disj (.atom _ _ _) (.mem _ _)) (depthEqAtFormula_delta0 _ _ _ _ _ _ _))

theorem depthLtFromFormula_delta0 {n : Nat} (C : ExpressionData (Project.Term n)) (m : Project.Term n) (R : RowStateSpace (Project.Term n))
    (H c z r : Project.Term n) : (depthLtFromFormula C m R H c z r).IsDelta0 :=
  .existsMem _ (.conj (.disj (.atom _ _ _) (.mem _ _)) (.conj (.forallMem _ (.imp (.disj (.atom _ _ _) (.mem _ _))
    (depthEqAtFormula_delta0 _ _ _ _ _ _ _))) (depthLtAtFormula_delta0 _ _ _ _ _ _ _)))

theorem keyLEFormula_delta0 {n : Nat} (C : ExpressionData (Project.Term n)) (m : Project.Term n) (R : RowStateSpace (Project.Term n))
    (H c z start topC topZ : Project.Term n) : (keyLEFormula C m R H c z start topC topZ).IsDelta0 :=
  .disj (depthLtFromFormula_delta0 _ _ _ _ _ _ _) (.conj (depthEqFromFormula_delta0 _ _ _ _ _ _ _)
    (.disj (.atom _ _ _) (.mem _ _)))

private theorem shifted_index_lt_iff_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {offset i j r s : M.Domain} (hOffset : M.mem offset C.omega) (hi : M.mem i C.omega) (hj : M.mem j C.omega)
    (hR : AddAt M T.addPairs T.plus offset i r) (hS : AddAt M T.addPairs T.plus offset j s) : M.mem r s ↔ M.mem i j := by
  have hw := omega_isOrdinal_d hM hC.omega
  have hRSum := (hT.add.add_iff_sum hM hOffset hi).mp hR
  have hSSum := (hT.add.add_iff_sum hM hOffset hj).mp hS
  constructor
  · intro hrs
    rcases hw.wellOrder.linear.compare i hi j hj with he | hlt | hgt
    · have hij := hM.1.eq_of_same_members i j he
      subst j
      have hEq := hT.add.add_unique hM.1 hR hS
      exact False.elim (SetTheory.KP.mem_irrefl_d (KP1Y.models_weakKP hM) s (hEq ▸ hrs))
    · exact hlt
    · have hsr := sum_strict_right_d hM (hw.mem hOffset) hSSum hRSum hgt
      exact False.elim (SetTheory.KP.mem_irrefl_d (KP1Y.models_weakKP hM) s
        ((hw.mem (hS.bounds hM.1 hT.add).2.2).transitive r hrs s hsr))
  · exact sum_strict_right_d hM (hw.mem hOffset) hRSum hSSum

private theorem shifted_index_from_ge_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {offset start physical q : M.Domain} (hOffset : M.mem offset C.omega) (hStart : M.mem start C.omega)
    (hq : M.mem q C.omega) (hShift : AddAt M T.addPairs T.plus offset start physical)
    (hLe : physical=q ∨ M.mem physical q) : ∃ j, M.mem j C.omega ∧ AddAt M T.addPairs T.plus offset j q ∧ (start=j ∨ M.mem start j) := by
  have hw := omega_isOrdinal_d hM hC.omega
  have hOffsetPhysical := sum_base_subset_d hM (hw.mem hOffset) ((hT.add.add_iff_sum hM hOffset hStart).mp hShift)
  have hOffsetQ : M.MemberSubset offset q := by
    intro x hx
    rcases hLe with he | hlt
    · exact he ▸ hOffsetPhysical x hx
    · exact (hw.mem hq).transitive physical hlt x (hOffsetPhysical x hx)
  obtain ⟨j,hj,hDiff⟩ := truncated_difference_exists_d hM hC hq hOffset
  have hSum := truncated_difference_add_inverse_d hM hC hDiff (ordinal_subset_cases_d hM (hw.mem hOffset) (hw.mem hq) hOffsetQ)
  have hAdd := (hT.add.add_iff_sum hM hOffset hj).mpr hSum
  refine ⟨j,hj,hAdd,?_⟩
  rcases hw.wellOrder.linear.compare start hStart j hj with he | hlt | hgt
  · exact Or.inl (hM.1.eq_of_same_members start j he)
  · exact Or.inr hlt
  · have hQPhysical := (shifted_index_lt_iff_d hM hC hT hOffset hj hStart hAdd hShift).mpr hgt
    rcases hLe with he | hlt
    · exact False.elim (SetTheory.KP.mem_irrefl_d (KP1Y.models_weakKP hM) q (he ▸ hQPhysical))
    · exact False.elim (SetTheory.KP.mem_irrefl_d (KP1Y.models_weakKP hM) q ((hw.mem hq).transitive physical hlt q hQPhysical))

/-- 真实Numeric KeyLE经精确帧行偏移变为共享装饰列弱序，Top仍是独立末坐标。 -/
theorem key_columns_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {m V P H : M.Domain} {R : RowStateSpace M.Domain} (hRun : RowRun M C m R V P H)
    {A : ActiveFrame M.Domain} (hA : A.Valid M C T m P H R) (hCap : FrameValueCap M V A.cap)
    {B : FiniteMatrix M.Domain} (hTrim : TrimmedMatrix M C (A.raw m) B)
    {c z start physical topC topZ : M.Domain} (hc : M.mem c m) (hz : M.mem z m) (hStart : M.mem start C.omega)
    (hShift : AddAt M T.addPairs T.plus A.frame.height start physical) (hKey : KeyLE M C m R H c z start topC topZ) :
    DecoratedColumnLeFrom M C B B c z physical topC topZ := by
  have hw := omega_isOrdinal_d hM hC.omega
  have hOffset := natural_successor_mem_d hM hC hRun.space.width hA.frame.height
  have hEq (j q : M.Domain) (hj : M.mem j C.omega) (hAdd : AddAt M T.addPairs T.plus A.frame.height j q)
      (hEqual : DepthEqAt M C m R H c z j) : ColumnEqAt M C.omega C.zero B B c z q := by
    intro x hx y hy hX hY
    obtain ⟨W,Q,hAt⟩ := hRun.at_exists_d hj
    exact hEqual x hx y hy
      ((depth_at_iff_d hM hC hRun hAt c x).mpr ((hA.normalized_entry_all_d hM hC hT hRun hCap hTrim hj hAdd hAt hc).mp hX))
      ((depth_at_iff_d hM hC hRun hAt z y).mpr ((hA.normalized_entry_all_d hM hC hT hRun hCap hTrim hj hAdd hAt hz).mp hY))
  rcases hKey with ⟨j,hj,hStartJ,hEarlier,hLess⟩ | ⟨hEqual,hTop⟩
  · obtain ⟨q,hq,hAdd⟩ := hT.add.add_exists_d hM hC hOffset hj
    have hPhysicalQ : physical=q ∨ M.mem physical q := by
      rcases hStartJ with he | hlt
      · subst j
        exact Or.inl (hT.add.add_unique hM.1 hShift hAdd)
      · exact Or.inr ((shifted_index_lt_iff_d hM hC hT hOffset hStart hj hShift hAdd).mpr hlt)
    refine Or.inl ⟨q,hq,hPhysicalQ,?_,?_⟩
    · intro p hp hPhysicalP
      obtain ⟨i,hi,hI,hStartI⟩ := shifted_index_from_ge_d hM hC hT hOffset hStart (hw.transitive q hq p hp) hShift hPhysicalP
      exact hEq i p hi hI (hEarlier i ((shifted_index_lt_iff_d hM hC hT hOffset hi hj hI hAdd).mp hp) hStartI)
    · obtain ⟨x,hx,y,hy,hX,hY,hxy⟩ := hLess
      obtain ⟨W,Q,hAt⟩ := hRun.at_exists_d hj
      exact ⟨x,hx,y,hy,(hA.normalized_entry_all_d hM hC hT hRun hCap hTrim hj hAdd hAt hc).mpr
        ((depth_at_iff_d hM hC hRun hAt c x).mp hX),
        (hA.normalized_entry_all_d hM hC hT hRun hCap hTrim hj hAdd hAt hz).mpr ((depth_at_iff_d hM hC hRun hAt z y).mp hY),hxy⟩
  · refine Or.inr ⟨?_,hTop⟩
    intro q hq hPhysicalQ
    obtain ⟨j,hj,hAdd,hStartJ⟩ := shifted_index_from_ge_d hM hC hT hOffset hStart hq hShift hPhysicalQ
    exact hEq j q hj hAdd (hEqual j hj hStartJ)

private theorem matrix_parent_row_iff {M : SetTheory.Structure.{u}} (he : Extensional M)
    {C : ExpressionData M.Domain} {m height Cells Values Forests Rows L r Q : M.Domain}
    (hRun : MatrixParentRun M C m height Cells Values Forests Rows L) (hQ : MemPair M Rows r Q) (c p : M.Domain) :
    MatrixParentAt M Forests Rows r c p ↔ MemPair M Q c p := by
  constructor
  · rintro ⟨F,_,hF,hParent⟩
    exact hRun.graph.unique r F Q hF hQ ▸ hParent
  · intro hParent
    exact ⟨Q,(hRun.graph.bounds he hQ).2,hQ,hParent⟩

private theorem previous_parent_at_iff_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {B : FiniteMatrix M.Domain} {Forests Rows L r F lower : M.Domain}
    (hRun : MatrixParentRun M C B.width B.height B.cells B.values Forests Rows L)
    (hPrevious : PreviousMatrixForest M C B.height Forests Rows L r F)
    (hLower : M.mem lower C.omega) (hs : M.SuccessorOf r lower) (c p : M.Domain) :
    MemPair M F c p ↔ MatrixParentAt M Forests Rows lower c p := by
  rcases hPrevious with ⟨hr0,_⟩ | ⟨j,_,hSucc,_,hF⟩
  · exact False.elim (hC.zero_empty lower (hr0 ▸ hs.predecessor_mem))
  · have hj := Structure.SuccessorOf.predecessor_eq hM.1 ((omega_isOrdinal_d hM hC.omega).mem hLower) hs hSucc
    subst j
    exact (matrix_parent_row_iff hM.1 hRun hF c p).symm

private theorem numeric_forest_eq_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {m V P H L : M.Domain} {R : RowStateSpace M.Domain} (hRun : RowRun M C m R V P H)
    {A : ActiveFrame M.Domain} (hA : A.Valid M C T m P H R) (hCap : FrameValueCap M V A.cap)
    (hRaw : MatrixParentRun M C m A.height A.cells A.values R.forests A.rows L)
    {B : FiniteMatrix M.Domain} (hTrim : TrimmedMatrix M C (A.raw m) B) {BF BR BL : M.Domain}
    (hBRun : MatrixParentRun M C B.width B.height B.cells B.values BF BR BL)
    {j physical W Q F : M.Domain} (hj : M.mem j C.omega) (hAdd : AddAt M T.addPairs T.plus A.frame.height j physical)
    (hAt : RowAt M R.states H j W Q) (hF : MemPair M BR physical F) : F=Q := by
  have hWidth : B.width=m := hTrim.width
  have hFF : Forest M C.omega m F := hWidth ▸ hBRun.forests physical F hF
  have hQ := (hRun.at_numeric_d hM hC hAt).forest
  apply hFF.ext hM.1 hQ
  intro c p
  classical
  by_cases hc : M.mem c m
  · exact (matrix_parent_row_iff hM.1 hBRun hF c p).symm.trans (hA.normalized_parent_all_d hM hC hT hRun hCap hRaw hTrim hBRun hj hAdd hAt hc)
  · exact iff_of_false (fun h => hc (hFF.bounds hM.1 h).1) (fun h => hc (hQ.bounds hM.1 h).1)

private theorem frame_boundary_parent_at_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {m V P H L : M.Domain} {R : RowStateSpace M.Domain} (hRun : RowRun M C m R V P H)
    {A : ActiveFrame M.Domain} (hA : A.Valid M C T m P H R)
    (hRaw : MatrixParentRun M C m A.height A.cells A.values R.forests A.rows L)
    {B : FiniteMatrix M.Domain} (hTrim : TrimmedMatrix M C (A.raw m) B) {BF BR BL : M.Domain}
    (hBRun : MatrixParentRun M C B.width B.height B.cells B.values BF BR BL) (c p : M.Domain) :
    MatrixParentAt M BF BR m c p ↔ MemPair M P c p := by
  obtain ⟨Q,_,hQ⟩ := hA.frame.rows.total m hA.frame.height.predecessor_mem
  have hQP := hA.frame.terminal_parent_d hM hC hRun.base.forest hQ
  subst Q
  have hJoined := (hA.frame_row_iff_d hM hC hT hRun hA.frame.height.predecessor_mem).mpr hQ
  exact (hTrim.parent_at_iff_d hM hC (hA.raw_valid hRun.space) hRaw hBRun m c p).trans (matrix_parent_row_iff hM.1 hRaw hJoined c p)

/-- 任意真实数值行给出规范活动帧的装饰S；第0数值行与边界父图相同，其他行实际构造blocker。 -/
theorem frame_decorated_row_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {m V P H L : M.Domain} {R : RowStateSpace M.Domain} (hRun : RowRun M C m R V P H)
    (hPositive : ∀ c a, MemPair M V c a → M.mem C.zero a)
    {Heights Top : M.Domain} (hHeights : HeightGraph M C m R V H Heights) (hTop : TopValueGraph M C m R H Heights Top)
    {A : ActiveFrame M.Domain} (hA : A.Valid M C T m P H R) (hCap : FrameValueCap M V A.cap)
    (hRaw : MatrixParentRun M C m A.height A.cells A.values R.forests A.rows L)
    {B : FiniteMatrix M.Domain} (hTrim : TrimmedMatrix M C (A.raw m) B) {BF BR BL : M.Domain}
    (hBRun : MatrixParentRun M C B.width B.height B.cells B.values BF BR BL)
    {j physical F Q start : M.Domain} (hj : M.mem j C.omega) (hAdd : AddAt M T.addPairs T.plus A.frame.height j physical)
    (hPrevious : PreviousMatrixForest M C B.height BF BR BL physical F) (hQ : MemPair M BR physical Q)
    (hStart : M.SuccessorOf start physical) : DecoratedRowBlocker M C B F Q start Top := by
  have hw := omega_isOrdinal_d hM hC.omega
  have hOffset := natural_successor_mem_d hM hC hRun.space.width hA.frame.height
  have hWidth : B.width=m := hTrim.width
  obtain ⟨W,N,hAt⟩ := hRun.at_exists_d hj
  have hCurrent := hRun.at_numeric_d hM hC hAt
  have hQN := numeric_forest_eq_d hM hC hT hRun hA hCap hRaw hTrim hBRun hj hAdd hAt hQ
  subst Q
  intro c hc q _ p _ hPrevParent hCurParent hDistinct
  have hcm : M.mem c m := hWidth ▸ hc
  rcases natural_cases hM hC.omega hj with hEmpty | ⟨old,hOld,hSucc⟩
  · have hjZero := hM.1.eq_of_same_members j C.zero (fun t => iff_of_false (hEmpty t) (hC.zero_empty t))
    subst j
    have hPhysical := ((hT.add.add_iff_sum hM hOffset hC.zero_nat).mp hAdd).zero_value_d hM hC.zero_empty
    have hPrevAt := (previous_parent_at_iff_d hM hC hBRun hPrevious hRun.space.width (hPhysical.symm ▸ hA.frame.height) c q).mp hPrevParent
    have hOldParent := (frame_boundary_parent_at_d hM hC hT hRun hA hRaw hTrim hBRun c q).mp hPrevAt
    have hNP := (hRun.at_unique hM.1 hAt (hRun.initial_row_at_d hM)).2
    subst N
    exact False.elim (hDistinct (hRun.base.forest.unique c p q hCurParent hOldParent))
  · obtain ⟨U,G,hOldAt⟩ := hRun.at_exists_d hOld
    have hOldRow := hRun.at_numeric_d hM hC hOldAt
    have hNext := hRun.at_next hM.1 hSucc hOldAt hAt
    obtain ⟨lower,hLower,hLowerAdd⟩ := hT.add.add_exists_d hM hC hOffset hOld
    have hPhysicalSucc := sum_successor_d hM hSucc ((hT.add.add_iff_sum hM hOffset hOld).mp hLowerAdd)
      ((hT.add.add_iff_sum hM hOffset hj).mp hAdd)
    have hOldParent := (hA.normalized_parent_all_d hM hC hT hRun hCap hRaw hTrim hBRun hOld hLowerAdd hOldAt hcm).mp
      ((previous_parent_at_iff_d hM hC hBRun hPrevious hLower hPhysicalSucc c q).mp hPrevParent)
    obtain ⟨z,hzm,hPath,hZParent,hCompare⟩ := row_next_blocker_d hM hC hOldRow hNext hOldParent hCurParent hDistinct
    obtain ⟨next,hs,hNextNat⟩ := hC.omega.1.2 j hj
    obtain ⟨WN,QN,hNextAt⟩ := hRun.at_exists_d hNextNat
    have hNextRow := hRun.at_numeric_d hM hC hNextAt
    have hNextStep := hRun.at_next hM.1 hs hAt hNextAt
    obtain ⟨a,_,hAValue⟩ := hCurrent.values.total c hcm
    obtain ⟨b,_,hBValue⟩ := hCurrent.values.total z hzm
    obtain ⟨x,_,hX⟩ := hNextRow.values.total c hcm
    obtain ⟨y,_,hY⟩ := hNextRow.values.total z hzm
    have hLe := difference_mono_common_parent_d hM hC hCurrent hNextStep.difference hCurParent hZParent
      hAValue hBValue (hCompare a b hAValue hBValue) hX hY
    have hSame : ParentRowsEqual M N c z := by
      intro t
      constructor
      · intro hParent
        exact (hCurrent.forest.unique c t p hParent hCurParent).symm ▸ hZParent
      · intro hParent
        exact (hCurrent.forest.unique z t p hParent hZParent).symm ▸ hCurParent
    have hCommon : CommonAncestors M C m N c z := fun t _ => ancestor_iff_of_parent_rows_eq_d hM hC hCurrent.forest hSame t
    obtain ⟨topC,hTopCNat,hTopC⟩ := hTop.graph.total c hcm
    obtain ⟨topZ,hTopZNat,hTopZ⟩ := hTop.graph.total z hzm
    have hKey := key_le_of_common_values_d hM hC hRun hPositive hHeights hTop hTopC hTopZ hNextAt hNextStep.selection
      (row_next_zeros_at_roots_d hM hC hCurrent hNextStep) hCommon hX hY
      ((hCurrent.difference_positive_iff_d hM hC hNextStep.difference hX).mpr ⟨p,hCurParent⟩)
      ((hCurrent.difference_positive_iff_d hM hC hNextStep.difference hY).mpr ⟨p,hZParent⟩) hLe
    obtain ⟨start',_,hNextAdd⟩ := hT.add.add_exists_d hM hC hOffset hNextNat
    have hNextPhysicalSucc := sum_successor_d hM hs ((hT.add.add_iff_sum hM hOffset hj).mp hAdd)
      ((hT.add.add_iff_sum hM hOffset hNextNat).mp hNextAdd)
    have hStartEq := Structure.SuccessorOf.eq hM.1 hNextPhysicalSucc hStart
    subst start'
    exact ⟨z,hWidth.symm ▸ hzm,hPath.imp id (fun ha => hWidth.symm ▸ ha),hZParent,
      topC,hTopCNat,topZ,hTopZNat,hTopC,hTopZ,key_columns_d hM hC hT hRun hA hCap hTrim hcm hzm hNextNat hNextAdd hKey⟩

/-- 原始数值山形真正给出活动边界以上的装饰S；帧行不被要求满足S。 -/
theorem frame_decorated_aboveS_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {m V P H L : M.Domain} {R : RowStateSpace M.Domain} (hRun : RowRun M C m R V P H)
    (hPositive : ∀ c a, MemPair M V c a → M.mem C.zero a)
    {Heights Top : M.Domain} (hHeights : HeightGraph M C m R V H Heights) (hTop : TopValueGraph M C m R H Heights Top)
    {A : ActiveFrame M.Domain} (hA : A.Valid M C T m P H R) (hCap : FrameValueCap M V A.cap)
    (hRaw : MatrixParentRun M C m A.height A.cells A.values R.forests A.rows L)
    {B : FiniteMatrix M.Domain} (hTrim : TrimmedMatrix M C (A.raw m) B) {BF BR BL : M.Domain}
    (hBRun : MatrixParentRun M C B.width B.height B.cells B.values BF BR BL) :
    DecoratedAboveS M C B BF BR BL A.frame.height Top := by
  have hOffset := natural_successor_mem_d hM hC hRun.space.width hA.frame.height
  have hZeroAdd := (hT.add.add_iff_sum hM hOffset hC.zero_nat).mpr (sum_zero_d hM A.frame.height hC.zero_empty)
  intro r hr hBase F hPrev Q _ hQ start _ hs
  have hrNat := (omega_isOrdinal_d hM hC.omega).transitive B.height hTrim.matrix.height r hr
  obtain ⟨j,hj,hAdd,_⟩ := shifted_index_from_ge_d hM hC hT hOffset hC.zero_nat hrNat hZeroAdd hBase
  exact frame_decorated_row_d hM hC hT hRun hPositive hHeights hTop hA hCap hRaw hTrim hBRun hj hAdd hPrev hQ hs

/-- 构造具体数值活动帧、top图和装饰S实例，而不是假定存在适当帧或适当装饰。 -/
theorem active_frame_decorated_exists_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {m V P H : M.Domain} {R : RowStateSpace M.Domain} (hRun : RowRun M C m R V P H)
    (hPositive : ∀ c a, MemPair M V c a → M.mem C.zero a) :
    ∃ A : ActiveFrame M.Domain, ∃ B : FiniteMatrix M.Domain, ∃ L BF BR BL Heights Top,
      A.Valid M C T m P H R ∧ FrameValueCap M V A.cap ∧ TrimmedMatrix M C (A.raw m) B ∧ NormalizedMatrix M C B ∧
      MatrixParentRun M C m A.height A.cells A.values R.forests A.rows L ∧
      MatrixParentRun M C B.width B.height B.cells B.values BF BR BL ∧ MatrixDepthRegular M C B BF BR ∧
      HeightGraph M C m R V H Heights ∧ TopValueGraph M C m R H Heights Top ∧ Graph M Top B.width C.omega ∧
      DecoratedAboveS M C B BF BR BL A.frame.height Top := by
  obtain ⟨A,B,L,BF,BR,BL,hA,hCap,hTrim,hNorm,hRaw,hBRun,hI⟩ := active_frame_bounded_exists_d hM hC hT hRun
  obtain ⟨Heights,Top,hHeights,hTop⟩ := mountain_height_top_exists_d hM hC hRun
  have hWidth : B.width=m := hTrim.width
  exact ⟨A,B,L,BF,BR,BL,Heights,Top,hA,hCap,hTrim,hNorm,hRaw,hBRun,hI,hHeights,hTop,hWidth.symm ▸ hTop.graph,
    frame_decorated_aboveS_d hM hC hT hRun hPositive hHeights hTop hA hCap hRaw hTrim hBRun⟩

/-- 实际差一坏根生成完整活动帧接口：精确Context、真实父/深度、独立top和装饰S。 -/
theorem row_bad_active_frame_decorated_exists_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {m V P H level last root : M.Domain} {R : RowStateSpace M.Domain}
    (hRun : RowRun M C m R V P H) (hBase : RootedRow M C m V P) (hWidth : M.SuccessorOf m last)
    (hBad : RowBadAt M C R H level last root) :
    ∃ A : ActiveFrame M.Domain, ∃ B : FiniteMatrix M.Domain, ∃ L BF BR BL Heights Top active,
      A.Valid M C T m P H R ∧ FrameValueCap M V A.cap ∧ TrimmedMatrix M C (A.raw m) B ∧ NormalizedMatrix M C B ∧
      MatrixParentRun M C m A.height A.cells A.values R.forests A.rows L ∧
      MatrixParentRun M C B.width B.height B.cells B.values BF BR BL ∧ MatrixDepthRegular M C B BF BR ∧
      HeightGraph M C m R V H Heights ∧ TopValueGraph M C m R H Heights Top ∧ Graph M Top B.width C.omega ∧ MemPair M Top last C.one ∧
      AddAt M T.addPairs T.plus A.frame.height level active ∧ MatrixExpansionContext M C B BF BR last active root ∧
      DecoratedAboveS M C B BF BR BL A.frame.height Top := by
  obtain ⟨A,B,L,BF,BR,BL,Heights,Top,active,hA,hCap,hTrim,hNorm,hRaw,hBRun,hI,hHeights,hTop,hTopOne,hActive,hContext⟩ :=
    row_bad_active_frame_exists_d hM hC hT hRun hBase hWidth hBad
  have hWidthB : B.width=m := hTrim.width
  exact ⟨A,B,L,BF,BR,BL,Heights,Top,active,hA,hCap,hTrim,hNorm,hRaw,hBRun,hI,hHeights,hTop,hWidthB.symm ▸ hTop.graph,hTopOne,
    hActive,hContext,frame_decorated_aboveS_d hM hC hT hRun hBase.positive hHeights hTop hA hCap hRaw hTrim hBRun⟩

end KP1Y.OneYFinite.NumericOrder
