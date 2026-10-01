import KP1Y.OneYLowerBlockSource
import KP1Y.OneYLowerCanonDepthRoot
import KP1Y.OneYLowerCanonOrder
import KP1Y.OneYLowerValueTransport
import KP1Y.OneYExpansionPrefix

/-! Lower阻挡：原列前缀与好部父（父项严格在root左侧）两支。目标阻挡与KeyLE全部由真实源阻挡运输。 -/
namespace KP1Y.OneYFinite.LowerBlock
open YesMetaZFC YesMetaZFC.SetTheory YesMetaZFC.SetTheory.Definitional
open KP1Y.Kuratowski KP1Y.Functions KP1Y.Naturals KP1Y.Bounded KP1Y.Arithmetic
open KP1Y.OneYFinite KP1Y.OneYFinite.CopyCoordinates KP1Y.OneYFinite.CopiedMountain
open KP1Y.OneYFinite.CopiedMountain.Lower KP1Y.OneYFinite.LowerCanon
universe u

/-- 目标山形Y在列c、s行父图Q上的单点装饰阻挡结论（即 `DecoratedBlockers` 的结论部分）。 -/
def BlockerAt (M : SetTheory.Structure.{u}) (C : ExpressionData M.Domain) (Y : Data M.Domain)
    (Top Q c q p t : M.Domain) : Prop :=
  ∃ z, M.mem z Y.width ∧ (z=q ∨ Ancestor M C Y.width Q z q) ∧ MemPair M Q z p ∧
    ∃ tc, M.mem tc C.omega ∧ ∃ tz, M.mem tz C.omega ∧ MemPair M Top c tc ∧ MemPair M Top z tz ∧
      ForestOrder.KeyLE M C Y c z t tc tz

/-- KeyLE 按起点以上逐行深度等价运输，Top读数不变。 -/
theorem key_of_depth_iff_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {X Y : Data M.Domain} {c z c' z' t tc tz : M.Domain}
    (hCol : ∀ j, M.mem j C.omega → (t=j ∨ M.mem t j) → ∀ d,
      ForestOrder.DepthAt M C X c j d ↔ ForestOrder.DepthAt M C Y c' j d)
    (hZ : ∀ j, M.mem j C.omega → (t=j ∨ M.mem t j) → ∀ d,
      ForestOrder.DepthAt M C X z j d ↔ ForestOrder.DepthAt M C Y z' j d)
    (hKey : ForestOrder.KeyLE M C X c z t tc tz) : ForestOrder.KeyLE M C Y c' z' t tc tz := by
  have hw := omega_isOrdinal_d hM hC.omega
  rcases hKey with ⟨r,hr,hTR,hEarlier,a,ha,b,hb,hA,hB,hab⟩ | ⟨hEq,hTop⟩
  · refine Or.inl ⟨r,hr,hTR,?_,a,ha,b,hb,(hCol r hr hTR a).mp hA,(hZ r hr hTR b).mp hB,hab⟩
    intro q hq hTQ x hx y hy hX hY
    have hqω := hw.transitive r hr q hq
    exact hEarlier q hq hTQ x hx y hy ((hCol q hqω hTQ x).mpr hX) ((hZ q hqω hTQ y).mpr hY)
  · refine Or.inr ⟨?_,hTop⟩
    intro q hq hTQ x hx y hy hX hY
    exact hEq q hq hTQ x hx y hy ((hCol q hq hTQ x).mpr hX) ((hZ q hq hTQ y).mpr hY)

/-- 单向深度运输加存在唯一性得到逐行深度等价。 -/
theorem depth_at_iff_of_forward_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {X Y : Data M.Domain} (hX : X.Valid M C) (hY : Y.Valid M C)
    {c c' j : M.Domain} (hj : M.mem j C.omega) (hc : M.mem c X.width)
    (hFwd : ∀ F G d, MemPair M X.parents j F → MemPair M Y.parents j G →
      Depth M C X.width F c d → Depth M C Y.width G c' d) (d : M.Domain) :
    ForestOrder.DepthAt M C X c j d ↔ ForestOrder.DepthAt M C Y c' j d := by
  obtain ⟨F,hFmem,hF⟩ := hX.parents.total j hj
  obtain ⟨G,hGmem,hG⟩ := hY.parents.total j hj
  rw [ForestOrder.depth_at_row_iff hM.1 hX hF,ForestOrder.depth_at_row_iff hM.1 hY hG]
  refine ⟨hFwd F G d hF hG,fun hD' => ?_⟩
  obtain ⟨e,hE⟩ := depth_exists_d hM hC (hX.forest j F hF) hc
  have hed := depth_unique_d hM hC (hY.forest j G hG) (hFwd F G e hF hG hE) hD'
  exact hed ▸ hE

theorem parent_copy_source_le_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {A : CopyCoordinates.Context M.Domain} {b s c : M.Domain} (hMap : ParentCopy M C T A b s c) : s=c ∨ M.mem s c := by
  rcases hMap.2.2 with ⟨_,he⟩ | ⟨_,hs,_,off,hOff,_,hAdd⟩
  · exact Or.inl he.symm
  · have hw := omega_isOrdinal_d hM hC.omega
    have hSum := (hT.add.add_iff_sum hM hs hOff).mp hAdd
    exact ordinal_subset_cases_d hM (hw.mem hs) (hw.mem (hAdd.bounds hM.1 hT.add).2.2)
      (sum_base_subset_d hM (hw.mem hs) hSum)

theorem parent_copy_unique_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {A : CopyCoordinates.Context M.Domain} (hA : A.Valid M C) {b s c c' : M.Domain}
    (h : ParentCopy M C T A b s c) (h' : ParentCopy M C T A b s c') : c=c' := by
  obtain ⟨J,hJ,hRows⟩ := parent_copy_graph_exists_d hM hC hT hA h.2.1
  exact hJ.graph.unique s c c' ((hRows s c).mpr h) ((hRows s c').mpr h')

theorem parent_copy_good_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain}
    {A : CopyCoordinates.Context M.Domain} (hA : A.Valid M C) {b p : M.Domain} (hb : M.mem b C.omega)
    (hp : M.mem p A.root) : ParentCopy M C T A b p p :=
  (parent_copy_good_iff hb ((omega_isOrdinal_d hM hC.omega).transitive A.root hA.root p hp) hp).mpr rfl

/-- 实际提取父项被任何一行的好部真实父项所界：伪父取自高度前一行的祖先。 -/
theorem extracted_parent_bound_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {m V P H : M.Domain} {R : RowStateSpace M.Domain}
    (hRun : RowRun M C m R V P H) {X : Data M.Domain} (hX : X.Valid M C) (hFrom : FromRun M C m R V H X)
    {oldTop Qnext : M.Domain} (hExtraction : Extraction M C m V P oldTop Qnext)
    {i s p g q : M.Domain} (hParent : ParentAt M X i s p) (hpg : M.mem p g) (hg : M.mem g C.omega)
    (hQ : MemPair M Qnext s q) : M.mem q g := by
  have hw := omega_isOrdinal_d hM hC.omega
  obtain ⟨R',H',Heights,F,hRun',hHeights,_,hPF,hSel⟩ := hExtraction
  have hRR := row_state_space_unique hM.1 hRun'.space hRun.space
  subst R'
  have hHH := hRun'.unique_d hM hC hRun
  subst H'
  have hHeightsEq := hHeights.unique hM.1 hFrom.heights
  subst Heights
  have hAnc := ((hSel.parents s q).mp hQ).1.1
  obtain ⟨a,hFa,hqa⟩ := ancestor_parent_cases_d hM hC hPF.forest hAnc
  obtain ⟨_,⟨hc,_,_,_,r',_,hHC,_,hPrev,W',_,Q',_,hAt',hAnc',_⟩,_⟩ := (hPF.parents s a).mp hFa
  obtain ⟨Fi,_,hFi,hFiP⟩ := hParent
  have hiH : M.mem i hc := (hX.source i s hc hHC).mp ⟨p,Fi,(hX.parents.bounds hM.1 hFi).2,hFi,hFiP⟩
  have hSuccR : M.SuccessorOf hc r' := by
    rcases hPrev.2 with ⟨hz,_⟩ | hS
    · exact False.elim (hC.zero_empty i (hz ▸ hiH))
    · exact hS
  have hir : i=r' ∨ M.mem i r' := (nat_lt_succ_iff hM hSuccR).mp hiH
  have hQ' := (hFrom.parents r' Q').mpr ⟨W',hAt'⟩
  have hAncI := canon_source_ancestor_lower_d hM hC hRun hFrom hFi hQ' hir (hFrom.width.symm ▸ hAnc')
  have hap := ancestor_le_parent_d hM hC (hX.forest i Fi hFi) hFiP hAncI
  have hag : M.mem a g := hap.elim (fun he => he ▸ hpg) (fun h => (hw.mem hg).transitive p hpg a h)
  rcases hqa with he | hqa
  · exact he ▸ hag
  · exact (hw.mem hg).transitive a hag q hqa.1

/-- 好部父项的两种目标祖先运输：低行，或高行且祖先端在锥外。 -/
theorem copy_ancestor_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {D : Lower.Context M.Domain} (hD : D.Valid M C) {Y : Data M.Domain} (hY : Y.Valid M C) {n : M.Domain}
    (hCopy : Copies M C T D n Y) {m : M.Domain} {R : RowStateSpace M.Domain} {V P H : M.Domain}
    (hRun : RowRun M C m R V P H) (hFrom : FromRun M C m R V H D.mountain)
    {w F G a q b x y : M.Domain} (hw : M.mem w C.omega)
    (hF : MemPair M D.mountain.parents w F) (hG : MemPair M Y.parents w G)
    (hAnc : Ancestor M C D.mountain.width F a q) (hqLast : q=D.coordinates.last ∨ M.mem q D.coordinates.last)
    (hMapA : ParentCopy M C T D.coordinates b a x) (hMapQ : ParentCopy M C T D.coordinates b q y) (hy : M.mem y Y.width)
    (hCase : M.mem w D.floor ∨ ¬InCone M C D a) : Ancestor M C Y.width G x y := by
  classical
  by_cases hLow : M.mem w D.floor
  · exact hCopy.low_ancestor_parent_copy_d hM hC hT hD hY hRun hFrom hLow hF hG hAnc hqLast hMapA hMapQ hy
  · have hOut := hCase.resolve_left hLow
    have hHigh := nat_le_of_not_lt hM hC hw (hD.floor_nat hM.1) hLow
    have hOutQ : ¬InCone M C D q := fun h => hOut ((in_cone_ancestor_iff_d hM hC hD hRun hFrom hHigh hF hAnc).mpr h)
    have hqLast' := hqLast.resolve_left (fun he => hOutQ (he ▸ in_cone_last hD))
    exact hCopy.outside_high_ancestor_copy_d hM hC hT hD hY hRun hFrom hHigh hF hG hAnc hqLast' hOutQ hMapA hMapQ hy

/-- 原列（含root左侧）在任意行的深度等价。 -/
theorem original_depth_iff_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {D : Lower.Context M.Domain} (hD : D.Valid M C) {Y : Data M.Domain} (hY : Y.Valid M C) {n : M.Domain}
    (hCopy : Copies M C T D n Y) {c j : M.Domain} (hj : M.mem j C.omega)
    (hcLast : c=D.coordinates.last ∨ M.mem c D.coordinates.last) (hc : M.mem c Y.width) (d : M.Domain) :
    ForestOrder.DepthAt M C D.mountain c j d ↔ ForestOrder.DepthAt M C Y c j d := by
  have hcX : M.mem c D.mountain.width := hcLast.elim (fun he => he ▸ hD.last)
    (fun h => ((omega_isOrdinal_d hM hC.omega).mem hD.mountain.width).transitive D.coordinates.last hD.last c h)
  exact depth_at_iff_of_forward_d hM hC hD.mountain hY hj hcX
    (fun F G d hF hG hDC => hCopy.canon_depth_original_d hM hC hT hD hY hF hG hcLast hc hDC) d

/-- 好部父列的复制在之后各行深度不变。 -/
theorem good_depth_iff_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {D : Lower.Context M.Domain} (hD : D.Valid M C) {Y : Data M.Domain} (hY : Y.Valid M C) {n : M.Domain}
    (hCopy : Copies M C T D n Y) {m : M.Domain} {R : RowStateSpace M.Domain} {V P H : M.Domain}
    (hRun : RowRun M C m R V P H) (hFrom : FromRun M C m R V H D.mountain)
    {u Fu s g b c j : M.Domain} (hsLast : M.mem s D.coordinates.last) (hAfter : M.mem D.coordinates.root s)
    (hFu : MemPair M D.mountain.parents u Fu) (hGood : MemPair M Fu s g) (hg : M.mem g D.coordinates.root)
    (huj : u=j ∨ M.mem u j) (hj : M.mem j C.omega)
    (hMap : ParentCopy M C T D.coordinates b s c) (hc : M.mem c Y.width) (d : M.Domain) :
    ForestOrder.DepthAt M C D.mountain s j d ↔ ForestOrder.DepthAt M C Y c j d := by
  have hsX : M.mem s D.mountain.width :=
    ((omega_isOrdinal_d hM hC.omega).mem hD.mountain.width).transitive D.coordinates.last hD.last s hsLast
  exact depth_at_iff_of_forward_d hM hC hD.mountain hY hj hsX
    (fun F G d hF hG hDC => hCopy.canon_depth_good_eq_d hM hC hT hD hY hRun hFrom hsLast hAfter hFu hGood hg
      huj hF hG hMap hc hDC) d

/-- 原列 c∈last：源阻挡逐字保留，KeyLE与Top由原列前缀不变给出。 -/
theorem original_blocker_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {D : Lower.Context M.Domain} (hD : D.Valid M C) {Y : Data M.Domain} (hY : Y.Valid M C) {n : M.Domain}
    (hCopy : Copies M C T D n Y) {m : M.Domain} {R : RowStateSpace M.Domain} {V P H : M.Domain}
    (hRun : RowRun M C m R V P H) (hPositive : ∀ c a, MemPair M V c a → M.mem C.zero a)
    (hFrom : FromRun M C m R V H D.mountain) {oldTop newTop : M.Domain}
    (hTopOld : TopValueGraph M C m R H D.mountain.heights oldTop)
    (hPrefixTop : RowsAgreeOn M newTop oldTop D.coordinates.last)
    {r s t F0 Q0 Q c q p : M.Domain} (hSucc : M.SuccessorOf s r) (hNext : M.SuccessorOf t s)
    (hF0 : MemPair M D.mountain.parents r F0) (hQ0 : MemPair M D.mountain.parents s Q0) (hQ : MemPair M Y.parents s Q)
    (hOld : MemPair M F0 c q) (hNew : MemPair M Q0 c p) (hNe : p≠q)
    (hcLast : M.mem c D.coordinates.last) (hc : M.mem c Y.width) : BlockerAt M C Y newTop Q c q p t := by
  have hw := omega_isOrdinal_d hM hC.omega
  obtain ⟨z,_,hPath,hZP,tc,htc,tz,htz,hTC,hTZ,hKey⟩ :=
    source_row_blocker_d hM hC hRun hPositive hD.mountain hFrom hTopOld hSucc hNext hF0 hQ0 hOld hNew hNe
  have hcω := hw.transitive Y.width hY.width c hc
  have hqc : M.mem q c := (hD.mountain.forest r F0 hF0).left c q hOld
  have hzc : M.mem z c := hPath.elim (fun he => he ▸ hqc) (fun h => (hw.mem hcω).transitive q hqc z h.1)
  have hqLast := (hw.mem hD.coordinates.last).transitive c hcLast q hqc
  have hzLast := (hw.mem hD.coordinates.last).transitive c hcLast z hzc
  have hqY := (hw.mem hY.width).transitive c hc q hqc
  have hzY := (hw.mem hY.width).transitive c hc z hzc
  have hZPY := (hCopy.original_parents_d hM hC hD (hCopy.width ▸ hzY) (Or.inr hzLast)).mpr
    ⟨Q0,(hD.mountain.parents.bounds hM.1 hQ0).2,hQ0,hZP⟩
  refine ⟨z,hzY,hPath.imp id (fun h => hCopy.prefix_ancestor_d hM hC hT hD hY hQ0 hQ h (Or.inr hqLast) hqY),
    (canon_row_parent_iff hM.1 hY hQ).mp hZPY,tc,htc,tz,htz,(hPrefixTop c hcLast tc).mpr hTC,
    (hPrefixTop z hzLast tz).mpr hTZ,?_⟩
  exact key_of_depth_iff_d hM hC
    (fun j hj _ d => original_depth_iff_d hM hC hT hD hY hCopy hj (Or.inr hcLast) hc d)
    (fun j hj _ d => original_depth_iff_d hM hC hT hD hY hCopy hj (Or.inr hzLast) hzY d) hKey

/-- 好部父分支的核心：给定源行w上的实际阻挡 z（父 p0∈root），构造目标阻挡 blockerCopy z。 -/
theorem good_blocker_of_source_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {D : Lower.Context M.Domain} (hD : D.Valid M C) {Y : Data M.Domain} (hY : Y.Valid M C) {n : M.Domain}
    (hCopy : Copies M C T D n Y) {m : M.Domain} {R : RowStateSpace M.Domain} {V P H : M.Domain}
    (hRun : RowRun M C m R V P H) (hFrom : FromRun M C m R V H D.mountain) {oldTop Qnext newTop : M.Domain}
    (hExtraction : Extraction M C m V P oldTop Qnext)
    (hPrefixTop : RowsAgreeOn M newTop oldTop D.coordinates.last) (hFixed : UpperFixed M C T D oldTop Qnext n newTop)
    {w t Q0 Q s q0 p0 b c q z tc tz : M.Domain} (hNext : M.SuccessorOf t w)
    (hQ0 : MemPair M D.mountain.parents w Q0) (hQ : MemPair M Y.parents w Q)
    (hNew : MemPair M Q0 s p0) (hGood : M.mem p0 D.coordinates.root)
    (hAfter : M.mem D.coordinates.root s) (hsLast : s=D.coordinates.last ∨ M.mem s D.coordinates.last)
    (hMap : ParentCopy M C T D.coordinates b s c) (hc : M.mem c n) (hMapQ : ParentCopy M C T D.coordinates b q0 q)
    (hq0s : M.mem q0 s) (hPath : z=q0 ∨ Ancestor M C D.mountain.width Q0 z q0) (hZP : MemPair M Q0 z p0)
    (htc : M.mem tc C.omega) (htz : M.mem tz C.omega) (hTC : MemPair M oldTop s tc) (hTZ : MemPair M oldTop z tz)
    (hKey : ForestOrder.KeyLE M C D.mountain s z t tc tz) :
    BlockerAt M C Y newTop Q c q p0 t := by
  have hw := omega_isOrdinal_d hM hC.omega
  have hwNat : M.mem w C.omega := (hD.mountain.parents.bounds hM.1 hQ0).1
  have hb : M.mem b C.omega := hMap.2.1
  have hOut : ¬InCone M C D s := canon_good_parent_out_d hM hC hD hRun hFrom hAfter hQ0 hNew hGood
  have hsLast' : M.mem s D.coordinates.last := hsLast.resolve_left (fun he => hOut (he ▸ in_cone_last hD))
  have hsω := hw.transitive D.coordinates.last hD.coordinates.last s hsLast'
  have hNotGood : ¬M.mem s D.coordinates.root := fun h =>
    nat_irrefl hM D.coordinates.root ((hw.mem hD.coordinates.root).transitive s h D.coordinates.root hAfter)
  have hEnc : Encode M C T D.coordinates s b c := (parent_copy_bad_iff hNotGood).mp hMap
  have hcY : M.mem c Y.width := hCopy.width.symm ▸ hc
  have hBelow (a x : M.Domain) (has : M.mem a s) (hMapA : ParentCopy M C T D.coordinates b a x) : M.mem x Y.width :=
    (hw.mem hY.width).transitive c hcY x (parent_copy_below_encode_d hM hC hT hD.coordinates hAfter has hMapA hEnc)
  have hqY := hBelow q0 q hq0s hMapQ
  have hq0Last : q0=D.coordinates.last ∨ M.mem q0 D.coordinates.last :=
    Or.inr ((hw.mem hD.coordinates.last).transitive s hsLast' q0 hq0s)
  have hzs : M.mem z s := hPath.elim (fun he => he ▸ hq0s) (fun h => (hw.mem hsω).transitive q0 hq0s z h.1)
  have hzLast := (hw.mem hD.coordinates.last).transitive s hsLast' z hzs
  have hzω := hw.transitive s hsω z hzs
  have hRootC : M.mem D.coordinates.root c :=
    (parent_copy_source_le_d hM hC hT hMap).elim (fun he => he ▸ hAfter) (fun h => (hw.mem (hw.transitive Y.width hY.width c hcY)).transitive s h D.coordinates.root hAfter)
  have hRootY := (hw.mem hY.width).transitive c hcY D.coordinates.root hRootC
  have hExtrGood (a pa : M.Domain) (hPa : MemPair M Q0 a pa) (hpa : M.mem pa D.coordinates.root) :
      ∀ q', MemPair M Qnext a q' → M.mem q' D.coordinates.root := fun q' hq' =>
    extracted_parent_bound_d hM hC hRun hD.mountain hFrom hExtraction
      ⟨Q0,(hD.mountain.parents.bounds hM.1 hQ0).2,hQ0,hPa⟩ hpa hD.coordinates.root hq'
  have hTCnew : MemPair M newTop c tc := hFixed s hAfter hsLast' (hExtrGood s p0 hNew hGood) b c tc hMap hc hTC
  have hAbove (j : M.Domain) (hj : M.mem j C.omega) (htj : t=j ∨ M.mem t j) : w=j ∨ M.mem w j :=
    Or.inr (nat_lt_of_lt_of_le hM hC hj hNext.predecessor_mem htj)
  have hColDepth : ∀ j, M.mem j C.omega → (t=j ∨ M.mem t j) → ∀ d,
      ForestOrder.DepthAt M C D.mountain s j d ↔ ForestOrder.DepthAt M C Y c j d := fun j hj htj d =>
    good_depth_iff_d hM hC hT hD hY hCopy hRun hFrom hsLast' hAfter hQ0 hNew hGood (hAbove j hj htj) hj hMap hcY d
  have hZPX : ParentAt M D.mountain w z p0 := ⟨Q0,(hD.mountain.parents.bounds hM.1 hQ0).2,hQ0,hZP⟩
  have hp0ω := hw.transitive D.coordinates.root hD.coordinates.root p0 hGood
  rcases hw.wellOrder.linear.compare z hzω D.coordinates.root hD.coordinates.root with he | hlt | hgt
  · have hz := hM.1.eq_of_same_members z D.coordinates.root he
    subst z
    have hLow : M.mem w D.floor := (hD.mountain.source w D.coordinates.root D.floor hD.floor).mp ⟨p0,hZPX⟩
    have hZPY := (hCopy.original_parents_d hM hC hD (hCopy.width ▸ hRootY) (Or.inr hD.coordinates.below)).mpr hZPX
    refine ⟨D.coordinates.root,hRootY,
      hCopy.canon_root_ancestor_low_copy_d hM hC hT hD hY hRun hFrom hLow hQ0 hQ hq0Last hPath hMapQ hqY,
      (canon_row_parent_iff hM.1 hY hQ).mp hZPY,tc,htc,tz,htz,hTCnew,
      (hPrefixTop D.coordinates.root hD.coordinates.below tz).mpr hTZ,?_⟩
    exact key_of_depth_iff_d hM hC hColDepth
      (fun j hj _ d => original_depth_iff_d hM hC hT hD hY hCopy hj (Or.inr hD.coordinates.below) hRootY d) hKey
  · have hzY := (hw.mem hY.width).transitive D.coordinates.root hRootY z hlt
    have hOutZ : ¬InCone M C D z := fun h => (h.root_le hM.1 hD).elim
      (fun he => nat_irrefl hM z (he ▸ hlt)) (fun h' => nat_irrefl hM z ((hw.mem hzω).transitive _ h' z hlt))
    have hZPY := (hCopy.original_parents_d hM hC hD (hCopy.width ▸ hzY) (Or.inr hzLast)).mpr hZPX
    have hMapZ := parent_copy_good_d (T := T) hM hC hD.coordinates hb hlt
    have hPathY : z=q ∨ Ancestor M C Y.width Q z q := by
      rcases hPath with he | hAnc
      · subst z
        exact Or.inl (parent_copy_unique_d hM hC hT hD.coordinates hMapZ hMapQ)
      · exact Or.inr (copy_ancestor_d hM hC hT hD hY hCopy hRun hFrom hwNat hQ0 hQ hAnc hq0Last hMapZ hMapQ hqY
          (Or.inr hOutZ))
    refine ⟨z,hzY,hPathY,(canon_row_parent_iff hM.1 hY hQ).mp hZPY,tc,htc,tz,htz,hTCnew,
      (hPrefixTop z hzLast tz).mpr hTZ,?_⟩
    exact key_of_depth_iff_d hM hC hColDepth
      (fun j hj _ d => original_depth_iff_d hM hC hT hD hY hCopy hj (Or.inr hzLast) hzY d) hKey
  · obtain ⟨J,hJ,hRows⟩ := parent_copy_graph_exists_d hM hC hT hD.coordinates hb
    obtain ⟨z',_,hJz⟩ := hJ.graph.total z hzω
    have hMapZ := (hRows z z').mp hJz
    have hzY' := hBelow z z' hzs hMapZ
    have hOutZ : ¬InCone M C D z := canon_good_parent_out_d hM hC hD hRun hFrom hgt hQ0 hZP hGood
    have hzNe : z≠D.coordinates.root := fun he => nat_irrefl hM D.coordinates.root (he ▸ hgt)
    have hParentZ := (parent_copy_nonroot_unmoved_d hM hC hT hD hwNat hzLast hzNe (fun h => hOutZ h.1) hMapZ).mpr
      ⟨p0,hp0ω,hZPX,parent_copy_good_d hM hC hD.coordinates hb hGood⟩
    have hZPY := (hCopy.parents w z' p0).mpr ⟨hCopy.width ▸ hzY',hParentZ⟩
    have hPathY : z'=q ∨ Ancestor M C Y.width Q z' q := by
      rcases hPath with he | hAnc
      · subst z
        exact Or.inl (parent_copy_unique_d hM hC hT hD.coordinates hMapZ hMapQ)
      · exact Or.inr (copy_ancestor_d hM hC hT hD hY hCopy hRun hFrom hwNat hQ0 hQ hAnc hq0Last hMapZ hMapQ hqY
          (Or.inr hOutZ))
    refine ⟨z',hzY',hPathY,(canon_row_parent_iff hM.1 hY hQ).mp hZPY,tc,htc,tz,htz,hTCnew,
      hFixed z hgt hzLast (hExtrGood z p0 hZP hGood) b z' tz hMapZ (hCopy.width ▸ hzY') hTZ,?_⟩
    exact key_of_depth_iff_d hM hC hColDepth
      (fun j hj htj d => good_depth_iff_d hM hC hT hD hY hCopy hRun hFrom hzLast hgt hQ0 hZP hGood
        (hAbove j hj htj) hj hMapZ hzY' d) hKey

/-- 好部父分支（原 `restrictedParent_good_copy`）：源行v→w的父 p0∈root，阻挡取 blockerCopy。
目标行与源行相同（源列在锥外）；Top由 `UpperFixed` 与原前缀读数给出。 -/
theorem good_blocker_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {D : Lower.Context M.Domain} (hD : D.Valid M C) {Y : Data M.Domain} (hY : Y.Valid M C) {n : M.Domain}
    (hCopy : Copies M C T D n Y) {m : M.Domain} {R : RowStateSpace M.Domain} {V P H : M.Domain}
    (hRun : RowRun M C m R V P H) (hPositive : ∀ c a, MemPair M V c a → M.mem C.zero a)
    (hFrom : FromRun M C m R V H D.mountain) {oldTop Qnext newTop : M.Domain}
    (hExtraction : Extraction M C m V P oldTop Qnext)
    (hPrefixTop : RowsAgreeOn M newTop oldTop D.coordinates.last) (hFixed : UpperFixed M C T D oldTop Qnext n newTop)
    {v w t F0 Q0 Q s q0 p0 b c q : M.Domain} (hSucc : M.SuccessorOf w v) (hNext : M.SuccessorOf t w)
    (hF0 : MemPair M D.mountain.parents v F0) (hQ0 : MemPair M D.mountain.parents w Q0) (hQ : MemPair M Y.parents w Q)
    (hOld : MemPair M F0 s q0) (hNew : MemPair M Q0 s p0) (hNe : p0≠q0) (hGood : M.mem p0 D.coordinates.root)
    (hAfter : M.mem D.coordinates.root s) (hsLast : s=D.coordinates.last ∨ M.mem s D.coordinates.last)
    (hMap : ParentCopy M C T D.coordinates b s c) (hc : M.mem c n) (hMapQ : ParentCopy M C T D.coordinates b q0 q) :
    BlockerAt M C Y newTop Q c q p0 t := by
  have hTopOld := Expansion.extraction_top_for_source_d hM hC hRun hFrom hExtraction
  obtain ⟨z,_,hPath,hZP,tc,htc,tz,htz,hTC,hTZ,hKey⟩ :=
    source_row_blocker_d hM hC hRun hPositive hD.mountain hFrom hTopOld hSucc hNext hF0 hQ0 hOld hNew hNe
  exact good_blocker_of_source_d hM hC hT hD hY hCopy hRun hFrom hExtraction hPrefixTop hFixed hNext hQ0 hQ hNew hGood
    hAfter hsLast hMap hc hMapQ ((hD.mountain.forest v F0 hF0).left s q0 hOld) hPath hZP htc htz hTC hTZ hKey

end KP1Y.OneYFinite.LowerBlock
