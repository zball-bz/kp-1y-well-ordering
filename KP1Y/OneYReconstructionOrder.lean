import KP1Y.OneYReconstructionCanonical
import KP1Y.OneYForestDecoratedOrder

/-! 在已恢复的高行上比较实际重建数值。字典序深度与独立Top保持原定义。 -/
namespace KP1Y.OneYFinite.ReconstructionOrder
open YesMetaZFC YesMetaZFC.SetTheory YesMetaZFC.SetTheory.Definitional
open KP1Y.Kuratowski KP1Y.Functions KP1Y.Naturals KP1Y.Bounded
open ReconstructionCanonical Reconstruction MountainReconstruction ForestOrder
universe u

private theorem not_reverse_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {a b : M.Domain} (hb : M.mem b C.omega)
    (hLe : a=b ∨ M.mem a b) : ¬M.mem b a := by
  intro hba
  rcases hLe with he | hab
  · exact SetTheory.KP.mem_irrefl_d (KP1Y.models_weakKP hM) b (he ▸ hba)
  · exact SetTheory.KP.mem_irrefl_d (KP1Y.models_weakKP hM) b
      (((omega_isOrdinal_d hM hC.omega).mem hb).transitive a hab b hba)

private theorem successor_le_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {r s q : M.Domain} (hr : M.mem r C.omega)
    (hq : M.mem q C.omega) (hSucc : M.SuccessorOf s r) (hrq : M.mem r q) : s=q ∨ M.mem s q := by
  have hw := omega_isOrdinal_d hM hC.omega
  apply ordinal_subset_cases_d hM (hw.mem (natural_successor_mem_d hM hC hr hSucc)) (hw.mem hq)
  intro a ha
  rcases (hSucc a).mp ha with har | he
  · exact (hw.mem hq).transitive r hrq a har
  · exact (hM.1.eq_of_same_members a r he).symm ▸ hrq

theorem depth_eq_at_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {X : CopiedMountain.Data M.Domain} (hX : X.Valid M C)
    {r F c z dc dz : M.Domain} (hF : MemPair M X.parents r F)
    (hDC : Depth M C X.width F c dc) (hDZ : Depth M C X.width F z dz) :
    ForestOrder.DepthEqAt M C X c z r ↔ dc=dz := by
  constructor
  · intro h
    exact h dc hDC.1 dz hDZ.1 ((depth_at_row_iff hM.1 hX hF c dc).mpr hDC) ((depth_at_row_iff hM.1 hX hF z dz).mpr hDZ)
  · intro he a _ b _ hA hB
    exact (depth_unique_d hM hC (hX.forest r F hF) ((depth_at_row_iff hM.1 hX hF c a).mp hA) hDC).trans
      (he.trans (depth_unique_d hM hC (hX.forest r F hF) hDZ ((depth_at_row_iff hM.1 hX hF z b).mp hB)))

theorem depth_lt_at_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {X : CopiedMountain.Data M.Domain} (hX : X.Valid M C)
    {r F c z dc dz : M.Domain} (hF : MemPair M X.parents r F)
    (hDC : Depth M C X.width F c dc) (hDZ : Depth M C X.width F z dz) :
    ForestOrder.DepthLtAt M C X c z r ↔ M.mem dc dz := by
  constructor
  · rintro ⟨a,_,b,_,hA,hB,hAB⟩
    have hAD := depth_unique_d hM hC (hX.forest r F hF) ((depth_at_row_iff hM.1 hX hF c a).mp hA) hDC
    have hBD := depth_unique_d hM hC (hX.forest r F hF) ((depth_at_row_iff hM.1 hX hF z b).mp hB) hDZ
    exact hAD ▸ hBD ▸ hAB
  · intro h
    exact ⟨dc,hDC.1,dz,hDZ.1,(depth_at_row_iff hM.1 hX hF c dc).mpr hDC,(depth_at_row_iff hM.1 hX hF z dz).mpr hDZ,h⟩

theorem key_depth_le_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {X : CopiedMountain.Data M.Domain} (hX : X.Valid M C)
    {r F c z dc dz tc tz : M.Domain} (hF : MemPair M X.parents r F)
    (hDC : Depth M C X.width F c dc) (hDZ : Depth M C X.width F z dz)
    (hKey : ForestOrder.KeyLE M C X c z r tc tz) : dc=dz ∨ M.mem dc dz := by
  rcases hKey with ⟨q,_,hrq,hBefore,hDiff⟩ | ⟨hEq,_⟩
  · rcases hrq with he | hlt
    · subst q
      exact Or.inr ((depth_lt_at_d hM hC hX hF hDC hDZ).mp hDiff)
    · exact Or.inl ((depth_eq_at_d hM hC hX hF hDC hDZ).mp (hBefore r hlt (Or.inl rfl)))
  · exact Or.inl ((depth_eq_at_d hM hC hX hF hDC hDZ).mp (hEq r (hX.parents.bounds hM.1 hF).1 (Or.inl rfl)))

theorem key_of_depth_lt_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {X : CopiedMountain.Data M.Domain} (hX : X.Valid M C)
    {r F c z dc dz tc tz : M.Domain} (hF : MemPair M X.parents r F)
    (hDC : Depth M C X.width F c dc) (hDZ : Depth M C X.width F z dz) (hLt : M.mem dc dz) :
    ForestOrder.KeyLE M C X c z r tc tz := by
  refine Or.inl ⟨r,(hX.parents.bounds hM.1 hF).1,Or.inl rfl,?_,(depth_lt_at_d hM hC hX hF hDC hDZ).mpr hLt⟩
  intro q hqr hLe
  exact False.elim (not_reverse_d hM hC ((omega_isOrdinal_d hM hC.omega).transitive r (hX.parents.bounds hM.1 hF).1 q hqr) hLe hqr)

theorem key_successor_iff_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {X : CopiedMountain.Data M.Domain} (_hX : X.Valid M C)
    {r s c z tc tz : M.Domain} (hr : M.mem r C.omega) (hSucc : M.SuccessorOf s r)
    (hEq : ForestOrder.DepthEqAt M C X c z r) :
    ForestOrder.KeyLE M C X c z r tc tz ↔ ForestOrder.KeyLE M C X c z s tc tz := by
  have hw := omega_isOrdinal_d hM hC.omega
  have hLift (q : M.Domain) (hq : M.mem q C.omega) (hLe : s=q ∨ M.mem s q) : M.mem r q := by
    rcases hLe with he | hlt
    · exact he ▸ hSucc.predecessor_mem
    · exact (hw.mem hq).transitive s hlt r hSucc.predecessor_mem
  constructor
  · rintro (⟨q,hq,hLe,hBefore,hDiff⟩ | ⟨hAll,hTop⟩)
    · have hrq : M.mem r q := by
        rcases hLe with he | hlt
        · subst q
          obtain ⟨a,ha,b,hb,hA,hB,hAB⟩ := hDiff
          exact False.elim (SetTheory.KP.mem_irrefl_d (KP1Y.models_weakKP hM) b ((hEq a ha b hb hA hB) ▸ hAB))
        · exact hlt
      exact Or.inl ⟨q,hq,successor_le_d hM hC hr hq hSucc hrq,
        fun p hp hsp => hBefore p hp (Or.inr (hLift p (hw.transitive q hq p hp) hsp)),hDiff⟩
    · exact Or.inr ⟨fun q hq hsq => hAll q hq (Or.inr (hLift q hq hsq)),hTop⟩
  · rintro (⟨q,hq,hLe,hBefore,hDiff⟩ | ⟨hAll,hTop⟩)
    · refine Or.inl ⟨q,hq,Or.inr (hLift q hq hLe),?_,hDiff⟩
      intro p hp hrp
      rcases hrp with he | hlt
      · exact he ▸ hEq
      · exact hBefore p hp (successor_le_d hM hC hr (hw.transitive q hq p hp) hSucc hlt)
    · refine Or.inr ⟨?_,hTop⟩
      intro q hq hrq
      rcases hrq with he | hlt
      · exact he ▸ hEq
      · exact hAll q hq (successor_le_d hM hC hr hq hSucc hlt)

theorem selected_depth_lt_value_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {m V F W Q c z x y dc dz : M.Domain}
    (hBase : NumericRow M C m V F) (hNext : RowNext M C m V F W Q) (hSame : ParentRowsEqual M F c z)
    (hX : MemPair M W c x) (hY : MemPair M W z y) (hx : M.mem C.zero x) (hy : M.mem C.zero y)
    (hDC : Depth M C m Q c dc) (hDZ : Depth M C m Q z dz) (hLt : M.mem dc dz) : M.mem x y := by
  have hCommon : NumericOrder.CommonAncestors M C m F z c := fun p _ =>
    (ancestor_iff_of_parent_rows_eq_d hM hC hBase.forest hSame p).symm
  have hZero := NumericOrder.row_next_zeros_at_roots_d hM hC hBase hNext
  have hCompare (hLe : y=x ∨ M.mem y x) :=
    (NumericOrder.sparse_depth_compare_d hM hC hNext.selection hZero hCommon hY hX hy hx hLe hDZ hDC).1
  rcases (omega_isOrdinal_d hM hC.omega).wellOrder.linear.compare x (hNext.selection.values.bounds hM.1 hX).2
      y (hNext.selection.values.bounds hM.1 hY).2 with he | hlt | hgt
  · have hxy := hM.1.eq_of_same_members x y he
    exact False.elim (not_reverse_d hM hC hDC.1 (hCompare (Or.inl hxy.symm)) hLt)
  · exact hlt
  · exact False.elim (not_reverse_d hM hC hDC.1 (hCompare (Or.inr hgt)) hLt)

theorem selected_same_depth_parents_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {m V F W Q c z x y dc dz : M.Domain}
    (hBase : NumericRow M C m V F) (hNext : RowNext M C m V F W Q) (hSame : ParentRowsEqual M F c z)
    (hX : MemPair M W c x) (hY : MemPair M W z y) (hx : M.mem C.zero x) (hy : M.mem C.zero y)
    (hDC : Depth M C m Q c dc) (hDZ : Depth M C m Q z dz) (hEq : dc=dz) : ParentRowsEqual M Q c z := by
  have hCommon : NumericOrder.CommonAncestors M C m F c z := fun p _ =>
    ancestor_iff_of_parent_rows_eq_d hM hC hBase.forest hSame p
  have hZero := NumericOrder.row_next_zeros_at_roots_d hM hC hBase hNext
  rcases (omega_isOrdinal_d hM hC.omega).wellOrder.linear.compare x (hNext.selection.values.bounds hM.1 hX).2
      y (hNext.selection.values.bounds hM.1 hY).2 with he | hlt | hgt
  · exact (NumericOrder.sparse_depth_compare_d hM hC hNext.selection hZero hCommon hX hY hx hy
      (Or.inl (hM.1.eq_of_same_members x y he)) hDC hDZ).2 hEq
  · exact (NumericOrder.sparse_depth_compare_d hM hC hNext.selection hZero hCommon hX hY hx hy (Or.inr hlt) hDC hDZ).2 hEq
  · have hReverse := (NumericOrder.sparse_depth_compare_d hM hC hNext.selection hZero
      (fun p hp => (hCommon p hp).symm) hY hX hy hx (Or.inr hgt) hDZ hDC).2 hEq.symm
    exact fun p => (hReverse p).symm

theorem padded_top_value_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {D : GridData M.Domain} (hD : D.Valid M) {H c height x top : M.Domain}
    (hH : Reconstructs M D H) (hX : PaddedCell M D H height c x)
    (hHeight : MemPair M D.heights c height) (hTop : MemPair M D.tops c top) : x=top := by
  have hh := (hD.heights.bounds hM.1 hHeight).2
  obtain ⟨f,_,hCf,_,hHX⟩ := hX.inside hh
  exact (hH.column hM.1 hCf).graph.unique height x top hHX
    ((hH.column hM.1 hCf).top height hh top (hD.tops.bounds hM.1 hTop).2 hHeight hTop)

theorem key_after_heights_iff_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {X : CopiedMountain.Data M.Domain} (hX : X.Valid M C)
    {r c z hc hz tc tz : M.Domain} (_hr : M.mem r C.omega)
    (hHC : MemPair M X.heights c hc) (hHZ : MemPair M X.heights z hz)
    (hCLow : hc=r ∨ M.mem hc r) (hZLow : hz=r ∨ M.mem hz r) :
    ForestOrder.KeyLE M C X c z r tc tz ↔ (tc=tz ∨ M.mem tc tz) := by
  have hZero (a ha : M.Domain) (hHA : MemPair M X.heights a ha) (hLow : ha=r ∨ M.mem ha r)
      (j : M.Domain) (hj : M.mem j C.omega) (hrj : r=j ∨ M.mem r j) (d : M.Domain)
      (hDepth : ForestOrder.DepthAt M C X a j d) : d=C.zero := by
    obtain ⟨Q,_,hQ,hD⟩ := hDepth
    apply depth_of_no_parent_d hM hC (hX.forest j Q hQ) ?_ hD
    intro p _ hAP
    have hjh := (hX.source j a ha hHA).mp ⟨p,Q,(hX.parents.bounds hM.1 hQ).2,hQ,hAP⟩
    have hHJ : ha=j ∨ M.mem ha j := by
      rcases hLow with he | hlt
      · exact he.symm ▸ hrj
      · rcases hrj with he | hgt
        · exact Or.inr (he ▸ hlt)
        · exact Or.inr (((omega_isOrdinal_d hM hC.omega).mem hj).transitive r hgt ha hlt)
    exact not_reverse_d hM hC hj hHJ hjh
  have hAll : ForestOrder.DepthEqFrom M C X c z r := by
    intro j hj hrj a _ b _ hA hB
    exact (hZero c hc hHC hCLow j hj hrj a hA).trans (hZero z hz hHZ hZLow j hj hrj b hB).symm
  constructor
  · rintro (⟨j,hj,hrj,_,a,ha,b,hb,hA,hB,hAB⟩ | ⟨_,hTop⟩)
    · exact False.elim (SetTheory.KP.mem_irrefl_d (KP1Y.models_weakKP hM) b ((hAll j hj hrj a ha b hb hA hB) ▸ hAB))
    · exact hTop
  · exact fun h => Or.inr ⟨hAll,h⟩

private theorem same_addend_le_iff_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {Pairs Plus : M.Domain} (hPlus : AdditionTable M C Pairs Plus)
    {a b k x y : M.Domain} (hA : AddAt M Pairs Plus a k x) (hB : AddAt M Pairs Plus b k y) :
    (x=y ∨ M.mem x y) ↔ (a=b ∨ M.mem a b) := by
  have hAB := hA.bounds hM.1 hPlus
  have hBB := hB.bounds hM.1 hPlus
  have hSA := (hPlus.add_iff_sum hM hAB.1 hAB.2.1).mp hA
  have hSB := (hPlus.add_iff_sum hM hBB.1 hBB.2.1).mp hB
  constructor
  · intro hLe
    rcases (omega_isOrdinal_d hM hC.omega).wellOrder.linear.compare a hAB.1 b hBB.1 with he | hlt | hgt
    · exact Or.inl (hM.1.eq_of_same_members a b he)
    · exact Or.inr hlt
    · exact False.elim (not_reverse_d hM hC hBB.2.2 hLe
        (natural_sum_strict_left_d hM hC hBB.1 hAB.1 hAB.2.1 hSB hSA hgt))
  · rintro (he | hlt)
    · subst b
      exact Or.inl (hPlus.add_unique hM.1 hA hB)
    · exact Or.inr (natural_sum_strict_left_d hM hC hAB.1 hBB.1 hAB.2.1 hSA hSB hlt)

def CommonParentsAt (M : SetTheory.Structure.{u}) (X : CopiedMountain.Data M.Domain) (r c z : M.Domain) : Prop :=
  ∃ F, M.mem F X.forests ∧ MemPair M X.parents r F ∧ ParentRowsEqual M F c z

def commonParentsAtFormula {n : Nat} (X : CopiedMountain.Data (Project.Term n)) (r c z : Project.Term n) : Project.Formula 1 n :=
  Project.Formula.existsMem X.forests (.conj (memPairFormula X.parents.weaken r.weaken (.bound 0))
    (parentRowsEqualFormula (.bound 0) c.weaken z.weaken))

theorem commonParentsAtFormula_freeClosed {n : Nat} {X : CopiedMountain.Data (Project.Term n)} (hX : X.Closed)
    (r c z : Project.Term n) (hr : r.freeSupport=[]) (hc : c.freeSupport=[]) (hz : z.freeSupport=[]) :
    (commonParentsAtFormula X r c z).FreeClosed := by
  simp [commonParentsAtFormula,parentRowsEqualFormula,memPairFormula,codeFormula,pairFormula,
    Project.Formula.existsMem,Project.Formula.forallMem,Definitional.Formula.FreeClosed,hX.forests,hX.parents,hr,hc,hz]

theorem commonParentsAtFormula_iff {M : SetTheory.Structure.{u}} (he : Extensional M) {n : Nat}
    (e : Env M n) (X : CopiedMountain.Data (Project.Term n)) (r c z : Project.Term n) :
    Project.Formula.satisfies e (commonParentsAtFormula X r c z) ↔ CommonParentsAt M (X.eval e) (r.eval e) (c.eval e) (z.eval e) := by
  simp only [commonParentsAtFormula,CommonParentsAt,Project.Formula.satisfies_existsMem_iff,
    Project.Formula.satisfies_conj_iff,memPairFormula_iff he,parentRowsEqualFormula_iff he,Term.eval_weaken]
  rfl

private def comparisonCore {n : Nat} (C : ExpressionData (Project.Term n)) (X : CopiedMountain.Data (Project.Term n))
    (D : GridData (Project.Term n)) (H base x r s c z y tc tz : Project.Term n) : Project.Formula 1 n :=
  .imp (.mem r C.omega) (.imp (.mem s C.omega)
    (.imp (.disj (Project.Formula.extensionalEq base r) (.mem base r))
      (.imp (successorFormula s r) (.imp (commonParentsAtFormula X r c z)
        (.imp (paddedCellFormula D H s c x) (.imp (paddedCellFormula D H s z y)
          (.imp (.mem C.zero x) (.imp (.mem C.zero y)
            (.imp (memPairFormula D.tops c tc) (.imp (memPairFormula D.tops z tz)
              (.iff (ForestOrder.keyLEFormula C X c z s tc tz)
                (.disj (Project.Formula.extensionalEq x y) (.mem x y)))))))))))))

private def comparisonC : ExpressionData (Project.Term 24) := ⟨.bound 23,.bound 22,.bound 21,.bound 20,.bound 19⟩
private def comparisonX : CopiedMountain.Data (Project.Term 24) := ⟨.bound 18,.bound 17,.bound 16,.bound 15⟩
private def comparisonD : GridData (Project.Term 24) :=
  grid comparisonC comparisonX (.bound 14) (.bound 11) (.bound 10) (.bound 13) (.bound 12)

private def comparisonSchema : Project.UnarySchema 16 where
  body := .forallE (.forallE (.forallE (.forallE (.forallE (.forallE (.forallE
    (comparisonCore comparisonC comparisonX comparisonD (.bound 9) (.bound 8) (.bound 7)
      (.bound 6) (.bound 5) (.bound 4) (.bound 3) (.bound 2) (.bound 1) (.bound 0))))))))
  freeClosed := by
    have hC : comparisonC.Closed := ⟨rfl,rfl,rfl,rfl,rfl⟩
    have hX : comparisonX.Closed := ⟨rfl,rfl,rfl,rfl⟩
    have hD : comparisonD.Closed := ⟨hC,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩
    have hKey := ForestOrder.keyLEFormula_freeClosed hC hX (.bound 4) (.bound 3) (.bound 5) (.bound 1) (.bound 0) rfl rfl rfl rfl rfl
    have hP := commonParentsAtFormula_freeClosed hX (.bound 6) (.bound 4) (.bound 3) rfl rfl rfl
    have hA := paddedCellFormula_freeClosed hD (.bound 9) (.bound 5) (.bound 4) (.bound 7) rfl rfl rfl rfl
    have hB := paddedCellFormula_freeClosed hD (.bound 9) (.bound 5) (.bound 3) (.bound 2) rfl rfl rfl rfl
    simp only [comparisonCore,Definitional.Formula.FreeClosed,hKey,hP,hA,hB]
    simp [comparisonC,comparisonD,grid,successorFormula,memPairFormula,codeFormula,pairFormula,
      Project.Formula.existsMem,Project.Formula.forallMem,Definitional.Formula.FreeClosed]

private def comparisonEnv {M : SetTheory.Structure.{u}} (C : ExpressionData M.Domain) (X : CopiedMountain.Data M.Domain)
    (Top B Parents Pairs Plus H base : M.Domain) : Env M 16 :=
  (((((((((((((((oneEnv C.omega).push C.zero).push C.one).push C.sequences).push C.expressions).push X.width).push X.heights).push X.forests).push X.parents).push Top).push B).push Parents).push Pairs).push Plus).push H).push base

private theorem comparisonSchema_iff {M : SetTheory.Structure.{u}} (he : Extensional M)
    (C : ExpressionData M.Domain) (X : CopiedMountain.Data M.Domain) (Top B Parents Pairs Plus H base x : M.Domain) :
    Project.Formula.satisfies ((comparisonEnv C X Top B Parents Pairs Plus H base).push x) comparisonSchema.body ↔
      ∀ r s c z y tc tz, M.mem r C.omega → M.mem s C.omega → (base=r ∨ M.mem base r) → M.SuccessorOf s r →
        CommonParentsAt M X r c z → PaddedCell M (grid C X Top Pairs Plus B Parents) H s c x →
        PaddedCell M (grid C X Top Pairs Plus B Parents) H s z y → M.mem C.zero x → M.mem C.zero y →
        MemPair M Top c tc → MemPair M Top z tz →
          (ForestOrder.KeyLE M C X c z s tc tz ↔ (x=y ∨ M.mem x y)) := by
  simp only [comparisonSchema,comparisonCore,Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_imp_iff,
    Project.Formula.satisfies_mem_iff,Project.Formula.satisfies_disj_iff,Project.Formula.satisfies_extensionalEq_iff_eq he,
    successorFormula_iff he,commonParentsAtFormula_iff he,paddedCellFormula_iff he,memPairFormula_iff he,
    Project.Formula.satisfies_iff_iff,ForestOrder.keyLEFormula_iff he]
  rfl

/-- 高行选择是归纳接口；所有重建行图、差图及数值比较都已在本定理内部建立。 -/
theorem key_iff_value_le_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {Pairs Plus : M.Domain} (hPlus : AdditionTable M C Pairs Plus)
    {X : CopiedMountain.Data M.Domain} (hX : X.Valid M C) {Top B Parents H base : M.Domain}
    (hTop : Graph M Top X.width C.omega) (hPositive : ∀ c top, MemPair M Top c top → M.mem C.zero top)
    (hB : SequenceBound M C X.width X.heights B) (hParents : Prefix M Parents X.parents B X.forests)
    (hH : Reconstructs M (grid C X Top Pairs Plus B Parents) H)
    (hCanonical : ∀ r s V W F Q, M.mem r C.omega → (base=r ∨ M.mem base r) → M.SuccessorOf s r →
      RowValues M (grid C X Top Pairs Plus B Parents) H r V → RowValues M (grid C X Top Pairs Plus B Parents) H s W →
      MemPair M X.parents r F → MemPair M X.parents s Q → Selects true M C X.width F W Q)
    {r s c z x y tc tz : M.Domain} (hr : M.mem r C.omega) (hBase : base=r ∨ M.mem base r) (hSucc : M.SuccessorOf s r)
    (hCommon : CommonParentsAt M X r c z) (hCellC : PaddedCell M (grid C X Top Pairs Plus B Parents) H s c x)
    (hCellZ : PaddedCell M (grid C X Top Pairs Plus B Parents) H s z y) (hx : M.mem C.zero x) (hy : M.mem C.zero y)
    (hTC : MemPair M Top c tc) (hTZ : MemPair M Top z tz) :
    ForestOrder.KeyLE M C X c z s tc tz ↔ (x=y ∨ M.mem x y) := by
  let D := grid C X Top Pairs Plus B Parents
  have hD := grid_valid_d hM hC hX hTop hPlus hB hParents
  have hw := omega_isOrdinal_d hM hC.omega
  have hAll := KP1Y.induction_d hM comparisonSchema (comparisonEnv C X Top B Parents Pairs Plus H base) (by
    intro x ih
    apply (comparisonSchema_iff hM.1 C X Top B Parents Pairs Plus H base x).mpr
    intro r s c z y tc tz hr hs hBase hSucc hCommon hCellC hCellZ hx hy hTC hTZ
    obtain ⟨F,_,hF,hSame⟩ := hCommon
    obtain ⟨Q,_,hQ⟩ := hX.parents.total s hs
    obtain ⟨V,hV⟩ := row_values_exists_d hM hD hH hr
    obtain ⟨W,hW⟩ := row_values_exists_d hM hD hH hs
    have hNumericF := hV.numeric_d hM hC hPlus hX hTop hPositive hB hParents hH hF
    have hNumericQ := hW.numeric_d hM hC hPlus hX hTop hPositive hB hParents hH hQ
    have hSelect := hCanonical r s V W F Q hr hBase hSucc hV hW hF hQ
    have hNext : RowNext M C X.width V F W Q :=
      (row_next_iff_selection_d hM hC hPlus hX hTop hB hParents hH hV hW hF hSucc).mpr hSelect
    have hWC := (hW.rows c x).mpr hCellC
    have hWZ := (hW.rows z y).mpr hCellZ
    obtain ⟨dc,hDC⟩ := depth_exists_d hM hC hNumericQ.forest hCellC.2.1
    obtain ⟨dz,hDZ⟩ := depth_exists_d hM hC hNumericQ.forest hCellZ.2.1
    rcases hw.wellOrder.linear.compare dc hDC.1 dz hDZ.1 with he | hLt | hGt
    · have hDepthEq := hM.1.eq_of_same_members dc dz he
      have hSameQ := selected_same_depth_parents_d hM hC hNumericF hNext hSame hWC hWZ hx hy hDC hDZ hDepthEq
      have hEqAt := (depth_eq_at_d hM hC hX hQ hDC hDZ).mpr hDepthEq
      classical
      by_cases hSome : ∃ p, MemPair M Q c p
      · obtain ⟨p,hCP⟩ := hSome
        have hZP := (hSameQ p).mp hCP
        obtain ⟨t,hSuccT,ht⟩ := hC.omega.1.2 s hs
        obtain ⟨Z,hZ⟩ := row_values_exists_d hM hD hH ht
        obtain ⟨x',_,hZX⟩ := hZ.graph.total c hCellC.2.1
        obtain ⟨y',_,hZY⟩ := hZ.graph.total z hCellZ.2.1
        have hDiff := hW.difference_d hM hC hPlus hX hTop hB hParents hH hZ hQ hSuccT
        have hx' := (hNumericQ.difference_positive_iff_d hM hC hDiff hZX).mpr ⟨p,hCP⟩
        have hy' := (hNumericQ.difference_positive_iff_d hM hC hDiff hZY).mpr ⟨p,hZP⟩
        have hDecrease := hNumericQ.difference_strict_d hM hC hDiff hWC hZX hx
        have hBaseS : base=s ∨ M.mem base s := by
          rcases hBase with he | hlt
          · exact Or.inr (he.symm ▸ hSucc.predecessor_mem)
          · exact Or.inr ((hSucc base).mpr (Or.inl hlt))
        have hIH := (comparisonSchema_iff hM.1 C X Top B Parents Pairs Plus H base x').mp (ih x' hDecrease)
          s t c z y' tc tz hs ht hBaseS hSuccT ⟨Q,(hX.parents.bounds hM.1 hQ).2,hQ,hSameQ⟩
          ((hZ.rows c x').mp hZX) ((hZ.rows z y').mp hZY) hx' hy' hTC hTZ
        obtain ⟨pValue,_,hPV⟩ := hW.graph.total p (hNumericQ.forest.bounds hM.1 hCP).2
        have hPC : CopiedMountain.ParentAt M X s c p := ⟨Q,(hX.parents.bounds hM.1 hQ).2,hQ,hCP⟩
        have hPZ : CopiedMountain.ParentAt M X s z p := ⟨Q,(hX.parents.bounds hM.1 hQ).2,hQ,hZP⟩
        have hSumC := hCellC.parent_sum_d hM hD hH ((grid_parent_iff_d hM hC hX hB hParents).mpr hPC) hSuccT
          ((hZ.rows c x').mp hZX) ((hW.rows p pValue).mp hPV)
        have hSumZ := hCellZ.parent_sum_d hM hD hH ((grid_parent_iff_d hM hC hX hB hParents).mpr hPZ) hSuccT
          ((hZ.rows z y').mp hZY) ((hW.rows p pValue).mp hPV)
        exact (key_successor_iff_d hM hC hX hs hSuccT hEqAt).trans
          (hIH.trans (same_addend_le_iff_d hM hC hPlus hSumC hSumZ).symm)
      · have hNo (a value : M.Domain) (hCell : PaddedCell M D H s a value) (hPos : M.mem C.zero value)
            (top : M.Domain) (hTopAt : MemPair M Top a top) (hNone : NoParent M X.width Q a) :
            MemPair M X.heights a s ∧ value=top := by
          obtain ⟨height,_,hHeight⟩ := hX.heights.total a hCell.2.1
          have hLe := (hCell.positive_iff_d hM hD hH hHeight hTopAt (hPositive a top hTopAt)).mp hPos
          have hHeightEq : s=height := by
            rcases hLe with he | hlt
            · exact he
            · obtain ⟨p,F',_,hF',hP⟩ := (hX.source s a height hHeight).mpr hlt
              have he := hX.parents.unique s F' Q hF' hQ
              exact False.elim (hNone p ((hX.forest s F' hF').bounds hM.1 hP).2 (he ▸ hP))
          subst height
          exact ⟨hHeight,padded_top_value_d hM hD hH hCell hHeight hTopAt⟩
        obtain ⟨hHC,hXTop⟩ := hNo c x hCellC hx tc hTC (fun p _ hP => hSome ⟨p,hP⟩)
        obtain ⟨hHZ,hYTop⟩ := hNo z y hCellZ hy tz hTZ (fun p _ hP => hSome ⟨p,(hSameQ p).mpr hP⟩)
        exact (key_after_heights_iff_d hM hC hX hs hHC hHZ (Or.inl rfl) (Or.inl rfl)).trans (by rw [hXTop,hYTop])
    · have hXY := selected_depth_lt_value_d hM hC hNumericF hNext hSame hWC hWZ hx hy hDC hDZ hLt
      exact ⟨fun _ => Or.inr hXY,fun _ => key_of_depth_lt_d hM hC hX hQ hDC hDZ hLt⟩
    · have hYX := selected_depth_lt_value_d hM hC hNumericF hNext (fun p => (hSame p).symm) hWZ hWC hy hx hDZ hDC hGt
      exact iff_of_false (fun h => not_reverse_d hM hC hDZ.1 (key_depth_le_d hM hC hX hQ hDC hDZ h) hGt)
        (fun h => not_reverse_d hM hC (hCellZ.natural hM.1 hD) h hYX))
  exact (comparisonSchema_iff hM.1 C X Top B Parents Pairs Plus H base x).mp (hAll x)
    r s c z y tc tz hr hCellC.1 hBase hSucc hCommon hCellC hCellZ hx hy hTC hTZ

end KP1Y.OneYFinite.ReconstructionOrder
