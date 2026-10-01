import KP1Y.OneYLowerCanonPaths
import KP1Y.OneYLowerCopyNesting

/-! Lower复制深度的实际运输：低行同块增量、锥外/无根祖先相等、移动行增量与抬升行相等。
不使用目标重建的任何规范性，只读取实际复制图。 -/
namespace KP1Y.OneYFinite.CopiedMountain.Lower
open YesMetaZFC YesMetaZFC.SetTheory YesMetaZFC.SetTheory.Definitional
open KP1Y.Kuratowski KP1Y.Functions KP1Y.Naturals KP1Y.Bounded KP1Y.Arithmetic
open KP1Y.OneYFinite.CopyCoordinates KP1Y.OneYFinite.LowerCanon
universe u

theorem canon_row_parent_iff {M : SetTheory.Structure.{u}} (he : Extensional M) {C : ExpressionData M.Domain}
    {X : Data M.Domain} (hX : X.Valid M C) {r G c p : M.Domain} (hG : MemPair M X.parents r G) :
    ParentAt M X r c p ↔ MemPair M G c p := by
  constructor
  · rintro ⟨G',_,hG',hP⟩
    exact hX.parents.unique r G' G hG' hG ▸ hP
  · exact fun h => ⟨G,(hX.parents.bounds he hG).2,hG,h⟩

theorem canon_no_parent_of_height {M : SetTheory.Structure.{u}} (he : Extensional M) {C : ExpressionData M.Domain}
    {X : Data M.Domain} (hX : X.Valid M C) {r G c h : M.Domain} (hG : MemPair M X.parents r G)
    (hH : MemPair M X.heights c h) (hNot : ¬M.mem r h) : NoParent M X.width G c := by
  intro p _ hP
  exact hNot ((hX.source r c h hH).mp ⟨p,(canon_row_parent_iff he hX hG).mpr hP⟩)

theorem canon_height_of_no_parent {M : SetTheory.Structure.{u}} (he : Extensional M) {C : ExpressionData M.Domain}
    {X : Data M.Domain} (hX : X.Valid M C) {r G c h : M.Domain} (hG : MemPair M X.parents r G)
    (hH : MemPair M X.heights c h) (hNo : NoParent M X.width G c) : ¬M.mem r h := by
  intro hr
  obtain ⟨p,hP⟩ := (hX.source r c h hH).mpr hr
  have hPG := (canon_row_parent_iff he hX hG).mp hP
  exact hNo p ((hX.forest r G hG).bounds he hPG).2 hPG

private theorem not_mem_of_le {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {a b : M.Domain} (hb : M.mem b C.omega)
    (hab : a=b ∨ M.mem a b) : ¬M.mem b a := by
  intro hba
  rcases hab with he | hab
  · exact SetTheory.KP.mem_irrefl_d (KP1Y.models_weakKP hM) b (he ▸ hba)
  · exact SetTheory.KP.mem_irrefl_d (KP1Y.models_weakKP hM) b
      (((omega_isOrdinal_d hM hC.omega).mem hb).transitive a hab b hba)

private theorem le_trans_nat {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {a b c : M.Domain} (hc : M.mem c C.omega)
    (hab : a=b ∨ M.mem a b) (hbc : b=c ∨ M.mem b c) : a=c ∨ M.mem a c := by
  rcases hab with he | hab
  · exact he ▸ hbc
  · rcases hbc with he | hbc
    · exact Or.inr (he ▸ hab)
    · exact Or.inr (((omega_isOrdinal_d hM hC.omega).mem hc).transitive b hbc a hab)

/-- 源列可含末列本身；高度由真实复制高度定义读取。 -/
theorem Copies.canon_copy_heights_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {D : Context M.Domain} (hD : D.Valid M C) {n q b x a h : M.Domain} {Y : Data M.Domain}
    (hCopy : Copies M C T D n Y) (hRoot : D.coordinates.root=q ∨ M.mem D.coordinates.root q)
    (hLast : q=D.coordinates.last ∨ M.mem q D.coordinates.last) (hEnc : Encode M C T D.coordinates q b x)
    (hx : M.mem x n) (hBase : MemPair M D.mountain.heights q a) :
    MemPair M Y.heights x h ↔ ((InCone M C D q ∧ Lifted M C T D a b h) ∨ (¬InCone M C D q ∧ h=a)) := by
  have hw := omega_isOrdinal_d hM hC.omega
  have hNotGood : ¬M.mem q D.coordinates.root := not_mem_of_le hM hC hEnc.1 hRoot
  rcases hLast with he | hlt
  · subst q
    have hSource : Source M D.coordinates D.coordinates.last := ⟨hD.coordinates.below,Or.inl rfl⟩
    have hxNat : M.mem x C.omega := by
      obtain ⟨_,_,_,_,_,hAdd⟩ := hEnc
      exact (hAdd.bounds hM.1 hT.add).2.2
    have hCone := in_cone_last hD
    have hRHS : ((InCone M C D D.coordinates.last ∧ Lifted M C T D a b h) ∨ (¬InCone M C D D.coordinates.last ∧ h=a)) ↔
        Lifted M C T D a b h := ⟨fun h => h.elim And.right (fun h => False.elim (h.1 hCone)),fun h => Or.inl ⟨hCone,h⟩⟩
    rw [hRHS,hCopy.heights x h]
    classical
    by_cases hNew : M.mem D.coordinates.last x
    · have hRaw := encoded_decodes_d hM hC hT hSource hEnc
      constructor
      · rintro ⟨_,hHeight⟩
        obtain ⟨a',_,hA',hCase⟩ := hHeight.new_column_d hM hC hT hD hNew hRaw
        have haa := hD.mountain.heights.unique _ a' a hA' hBase
        subst a'
        exact hCase.elim And.right (fun h => False.elim (h.1 hCone))
      · intro hLift
        obtain ⟨ha,hb,off,hOff,hMul,hAdd⟩ := hLift
        exact ⟨hx,hxNat,Or.inr ⟨hNew,D.coordinates.last,hD.coordinates.last,b,hb,hRaw,a,ha,hBase,
          Or.inl ⟨hCone,off,hOff,hMul,hAdd⟩⟩⟩
    · have hOld : x=D.coordinates.last ∨ M.mem x D.coordinates.last := by
        rcases hw.wellOrder.linear.compare x hxNat D.coordinates.last hD.coordinates.last with he | hlt | hgt
        · exact Or.inl (hM.1.eq_of_same_members x _ he)
        · exact Or.inr hlt
        · exact False.elim (hNew hgt)
      obtain ⟨hsx,hb0⟩ := encoded_original_d hM hC hT hD hSource hEnc hOld
      subst hsx
      subst hb0
      rw [height_original_iff_d hM hC hD hOld]
      have ha := (hD.mountain.heights.bounds hM.1 hBase).2
      constructor
      · rintro ⟨_,hH⟩
        have hha := hD.mountain.heights.unique _ h a hH hBase
        subst h
        exact lifted_zero_d hM hC hT hD ha
      · intro hLift
        have hha := hLift.unique hM.1 hT (lifted_zero_d hM hC hT hD ha)
        subst h
        exact ⟨hx,hBase⟩
  · rw [hCopy.parent_copy_heights_d hM hC hT hD hlt hx ((parent_copy_bad_iff hNotGood).mpr hEnc) hBase]


private theorem chain_last {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {D : Context M.Domain} (hD : D.Valid M C) {m F d c : M.Domain}
    (hcLast : c=D.coordinates.last ∨ M.mem c D.coordinates.last) (hDC : d=c ∨ Ancestor M C m F d c) :
    d=D.coordinates.last ∨ M.mem d D.coordinates.last := by
  rcases hDC with he | hAnc
  · exact he.symm ▸ hcLast
  · exact Or.inr (hcLast.elim (fun he => he ▸ hAnc.1)
      (fun h => ((omega_isOrdinal_d hM hC.omega).mem hD.coordinates.last).transitive c h d hAnc.1))

private theorem image_in_width {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {m F J d c u y w : M.Domain}
    (hJ : ColumnEmbedding M C.omega C.omega J) (hw : M.mem w C.omega)
    (hDC : d=c ∨ Ancestor M C m F d c) (hDU : MemPair M J d u) (hCY : MemPair M J c y) (hy : M.mem y w) : M.mem u w := by
  rcases hDC with he | hAnc
  · subst d
    exact (hJ.graph.unique c u y hDU hCY).symm ▸ hy
  · have hlt := hJ.strict d (hJ.graph.bounds hM.1 hDU).1 c (hJ.graph.bounds hM.1 hCY).1 hAnc.1 u y hDU hCY
    exact ((omega_isOrdinal_d hM hC.omega).mem hw).transitive y hy u hlt

private theorem root_mem_of_le_parent {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {root a p d : M.Domain} (hd : M.mem d C.omega)
    (hRootA : root=a ∨ M.mem root a) (hAP : a=p ∨ M.mem a p) (hpd : M.mem p d) : M.mem root d := by
  have hw := omega_isOrdinal_d hM hC.omega
  have hRootP := le_trans_nat hM hC (hw.transitive d hd p hpd) hRootA hAP
  rcases hRootP with he | hlt
  · exact he ▸ hpd
  · exact (hw.mem hd).transitive p hpd root hlt

/-- 低行：起点不低于root时，同一副本中的深度增量等于源深度增量。 -/
theorem Copies.canon_depth_low_diff_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {D : Context M.Domain} (hD : D.Valid M C) {Y : Data M.Domain} (hY : Y.Valid M C) {n : M.Domain}
    (hCopy : Copies M C T D n Y) {r F G a c b x y da dc dx dy : M.Domain}
    (hLow : M.mem r D.floor) (hF : MemPair M D.mountain.parents r F) (hG : MemPair M Y.parents r G)
    (hRootA : D.coordinates.root=a ∨ M.mem D.coordinates.root a)
    (hcLast : c=D.coordinates.last ∨ M.mem c D.coordinates.last)
    (hAC : a=c ∨ Ancestor M C D.mountain.width F a c)
    (hMapA : ParentCopy M C T D.coordinates b a x) (hMapC : ParentCopy M C T D.coordinates b c y) (hy : M.mem y Y.width)
    (hDA : Depth M C D.mountain.width F a da) (hDC : Depth M C D.mountain.width F c dc)
    (hDX : Depth M C Y.width G x dx) (hDY : Depth M C Y.width G y dy) :
    ∃ e, M.mem e C.omega ∧ Sum M da e dc ∧ Sum M dx e dy := by
  have hw := omega_isOrdinal_d hM hC.omega
  obtain ⟨J,hJ,hRows⟩ := parent_copy_graph_exists_d hM hC hT hD.coordinates hMapC.2.1
  apply depth_mapped_diff_d hM hC (hD.mountain.forest r F hF) (hY.forest r G hG) hJ hAC ((hRows a x).mpr hMapA)
    ((hRows c y).mpr hMapC) hy ?_ hDA hDC hDX hDY
  intro d p u v hDC' hAP hDP hDU hPV
  have hdNat := (hJ.graph.bounds hM.1 hDU).1
  have hpd := (hD.mountain.forest r F hF).left d p hDP
  have hRootD := root_mem_of_le_parent hM hC hdNat hRootA hAP hpd
  have hu := image_in_width hM hC hJ hY.width hDC' hDU ((hRows c y).mpr hMapC) hy
  have hAt := hCopy.low_parent_nonroot_d hM hC hT hD hLow (chain_last hM hC hD hcLast hDC')
    (fun he => SetTheory.KP.mem_irrefl_d (KP1Y.models_weakKP hM) d (he ▸ hRootD))
    ((hRows d u).mp hDU) ((hRows p v).mp hPV) ⟨F,(hD.mountain.parents.bounds hM.1 hF).2,hF,hDP⟩ (hCopy.width ▸ hu)
  exact (canon_row_parent_iff hM.1 hY hG).mp hAt

/-- 无父原列的复制像在目标同行仍无父（低行或锥外高行）。 -/
private theorem copy_no_parent_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {D : Context M.Domain} (hD : D.Valid M C) {Y : Data M.Domain} (hY : Y.Valid M C) {n : M.Domain}
    (hCopy : Copies M C T D n Y) {r F G q b x : M.Domain}
    (hF : MemPair M D.mountain.parents r F) (hG : MemPair M Y.parents r G)
    (hqLast : M.mem q D.coordinates.last) (hOut : ¬InCone M C D q)
    (hNo : NoParent M D.mountain.width F q) (hMap : ParentCopy M C T D.coordinates b q x) :
    NoParent M Y.width G x := by
  intro p _ hP
  have hAt := (canon_row_parent_iff hM.1 hY hG).mpr hP
  have hx : M.mem x n := hCopy.width ▸ (hAt.bounds hM.1 hY).2.1
  obtain ⟨a,_,hA⟩ := hD.mountain.heights.total q
    (((omega_isOrdinal_d hM hC.omega).mem hD.mountain.width).transitive _ hD.last q hqLast)
  have hNotR := canon_height_of_no_parent hM.1 hD.mountain hF hA hNo
  have hHeight : MemPair M Y.heights x a :=
    (hCopy.parent_copy_heights_d hM hC hT hD hqLast hx hMap hA).mpr (Or.inr ⟨hOut,rfl⟩)
  exact hNotR ((hY.source r x a hHeight).mp ⟨p,hAt⟩)

/-- 低行且链不经过root：复制列深度不变。 -/
theorem Copies.canon_depth_low_eq_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {D : Context M.Domain} (hD : D.Valid M C) {Y : Data M.Domain} (hY : Y.Valid M C) {n : M.Domain}
    (hCopy : Copies M C T D n Y) {r F G c b y d : M.Domain}
    (hLow : M.mem r D.floor) (hF : MemPair M D.mountain.parents r F) (hG : MemPair M Y.parents r G)
    (hcLast : c=D.coordinates.last ∨ M.mem c D.coordinates.last) (hNotRoot : c≠D.coordinates.root)
    (hNoAnc : ¬Ancestor M C D.mountain.width F D.coordinates.root c)
    (hMapC : ParentCopy M C T D.coordinates b c y) (hy : M.mem y Y.width)
    (hDC : Depth M C D.mountain.width F c d) : Depth M C Y.width G y d := by
  have hw := omega_isOrdinal_d hM hC.omega
  have hFF := hD.mountain.forest r F hF
  obtain ⟨J,hJ,hRows⟩ := parent_copy_graph_exists_d hM hC hT hD.coordinates hMapC.2.1
  have hNe (d : M.Domain) (hDC' : d=c ∨ Ancestor M C D.mountain.width F d c) : d≠D.coordinates.root := by
    intro he
    subst d
    rcases hDC' with he | hAnc
    · exact hNotRoot he.symm
    · exact hNoAnc hAnc
  apply depth_mapped_eq_d hM hC hFF (hY.forest r G hG) hJ ((hRows c y).mpr hMapC) hy ?_ ?_ hDC
  · intro d p u v hDC' hDP hDU hPV
    have hu := image_in_width hM hC hJ hY.width hDC' hDU ((hRows c y).mpr hMapC) hy
    have hAt := hCopy.low_parent_nonroot_d hM hC hT hD hLow (chain_last hM hC hD hcLast hDC') (hNe d hDC')
      ((hRows d u).mp hDU) ((hRows p v).mp hPV) ⟨F,(hD.mountain.parents.bounds hM.1 hF).2,hF,hDP⟩ (hCopy.width ▸ hu)
    exact (canon_row_parent_iff hM.1 hY hG).mp hAt
  · intro q x hQC hNo hQX
    have hqNat := (hJ.graph.bounds hM.1 hQX).1
    have hqLe := chain_last hM hC hD hcLast hQC
    have hMapQ := (hRows q x).mp hQX
    classical
    by_cases hGood : M.mem q D.coordinates.root
    · have hxq := (parent_copy_good_iff hMapQ.2.1 hqNat hGood).mp hMapQ
      subst x
      intro p _ hP
      have hAt := (canon_row_parent_iff hM.1 hY hG).mpr hP
      have hOld := (hCopy.original_parents_d hM hC hD (hCopy.width ▸ (hAt.bounds hM.1 hY).2.1) hqLe).mp hAt
      have hPF := (canon_row_parent_iff hM.1 hD.mountain hF).mp hOld
      exact hNo p (hFF.bounds hM.1 hPF).2 hPF
    · have hRootQ : M.mem D.coordinates.root q := by
        rcases hw.wellOrder.linear.compare q hqNat D.coordinates.root hD.coordinates.root with he | hlt | hgt
        · exact False.elim (hNe q hQC (hM.1.eq_of_same_members q _ he))
        · exact False.elim (hGood hlt)
        · exact hgt
      have hOut : ¬InCone M C D q := by
        intro hCone
        obtain ⟨h,hh,hH,hFloorH,_⟩ := hCone
        have hrh : M.mem r h := hFloorH.elim (fun he => he ▸ hLow) (fun hlt => (hw.mem hh).transitive _ hlt r hLow)
        exact canon_height_of_no_parent hM.1 hD.mountain hF hH hNo hrh
      have hqLast : M.mem q D.coordinates.last := hqLe.resolve_left (fun he => hOut (he ▸ in_cone_last hD))
      exact copy_no_parent_d hM hC hT hD hY hCopy hF hG hqLast hOut hNo hMapQ


/-- 源山形的高行祖先在低行仍是祖先（实际行运行的逐行细化）。 -/
theorem canon_source_ancestor_lower_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {m : M.Domain} {R : RowStateSpace M.Domain} {V P H : M.Domain}
    (hRun : RowRun M C m R V P H) {X : Data M.Domain} (hFrom : FromRun M C m R V H X)
    {i j Fi Fj a c : M.Domain} (hFi : MemPair M X.parents i Fi) (hFj : MemPair M X.parents j Fj)
    (hLe : i=j ∨ M.mem i j) (hAnc : Ancestor M C X.width Fj a c) : Ancestor M C X.width Fi a c := by
  obtain ⟨Ui,hAti⟩ := (hFrom.parents i Fi).mp hFi
  obtain ⟨Uj,hAtj⟩ := (hFrom.parents j Fj).mp hFj
  exact hFrom.width.symm ▸ hRun.ancestor_lower_d hM hC hAti hAtj hLe (hFrom.width ▸ hAnc)

/-- 高行锥外：复制列深度不变。 -/
theorem Copies.canon_depth_out_eq_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {D : Context M.Domain} (hD : D.Valid M C) {Y : Data M.Domain} (hY : Y.Valid M C) {n : M.Domain}
    (hCopy : Copies M C T D n Y) {m : M.Domain} {R : RowStateSpace M.Domain} {V P H : M.Domain}
    (hRun : RowRun M C m R V P H) (hFrom : FromRun M C m R V H D.mountain) {r F G c b y d : M.Domain}
    (hHigh : D.floor=r ∨ M.mem D.floor r) (hF : MemPair M D.mountain.parents r F) (hG : MemPair M Y.parents r G)
    (hcLast : M.mem c D.coordinates.last) (hOut : ¬InCone M C D c)
    (hMapC : ParentCopy M C T D.coordinates b c y) (hy : M.mem y Y.width)
    (hDC : Depth M C D.mountain.width F c d) : Depth M C Y.width G y d := by
  have hFF := hD.mountain.forest r F hF
  have hr := (hD.mountain.parents.bounds hM.1 hF).1
  obtain ⟨J,hJ,hRows⟩ := parent_copy_graph_exists_d hM hC hT hD.coordinates hMapC.2.1
  have hOutChain (d : M.Domain) (hDC' : d=c ∨ Ancestor M C D.mountain.width F d c) : ¬InCone M C D d := by
    rcases hDC' with he | hAnc
    · exact he ▸ hOut
    · exact fun h => hOut ((in_cone_ancestor_iff_d hM hC hD hRun hFrom hHigh hF hAnc).mp h)
  have hLastChain (d : M.Domain) (hDC' : d=c ∨ Ancestor M C D.mountain.width F d c) : M.mem d D.coordinates.last :=
    (chain_last hM hC hD (Or.inr hcLast) hDC').resolve_left (fun he => hOutChain d hDC' (he ▸ in_cone_last hD))
  apply depth_mapped_eq_d hM hC hFF (hY.forest r G hG) hJ ((hRows c y).mpr hMapC) hy ?_ ?_ hDC
  · intro d p u v hDC' hDP hDU hPV
    have hu := image_in_width hM hC hJ hY.width hDC' hDU ((hRows c y).mpr hMapC) hy
    have hne : d≠D.coordinates.root := fun he => hOutChain d hDC' (he ▸ in_cone_root_d hM hD)
    have hParent := (parent_copy_nonroot_unmoved_d hM hC hT hD hr (hLastChain d hDC') hne (fun h => hOutChain d hDC' h.1)
      ((hRows d u).mp hDU)).mpr ⟨p,(hJ.graph.bounds hM.1 hPV).1,⟨F,(hD.mountain.parents.bounds hM.1 hF).2,hF,hDP⟩,(hRows p v).mp hPV⟩
    exact (canon_row_parent_iff hM.1 hY hG).mp ((hCopy.parents r u v).mpr ⟨hCopy.width ▸ hu,hParent⟩)
  · intro q x hQC hNo hQX
    exact copy_no_parent_d hM hC hT hD hY hCopy hF hG (hLastChain q hQC) (hOutChain q hQC) hNo ((hRows q x).mp hQX)

private theorem nat_le_of_not_lt {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {a b : M.Domain} (ha : M.mem a C.omega) (hb : M.mem b C.omega)
    (hNot : ¬M.mem a b) : b=a ∨ M.mem b a := by
  rcases (omega_isOrdinal_d hM hC.omega).wellOrder.linear.compare a ha b hb with he | hlt | hgt
  · exact Or.inl (hM.1.eq_of_same_members a b he).symm
  · exact False.elim (hNot hlt)
  · exact Or.inr hgt

/-- 移动行（floor≤r，源行为shift行）：锥内链的复制深度增量等于源增量。 -/
theorem Copies.canon_depth_moved_diff_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {D : Context M.Domain} (hD : D.Valid M C) {Y : Data M.Domain} (hY : Y.Valid M C) {n : M.Domain}
    (hCopy : Copies M C T D n Y) {m : M.Domain} {R : RowStateSpace M.Domain} {V P H : M.Domain}
    (hRun : RowRun M C m R V P H) (hFrom : FromRun M C m R V H D.mountain)
    {r u off F G a c b x y da dc dx dy : M.Domain}
    (hr : M.mem r C.omega) (hHighR : D.floor=r ∨ M.mem D.floor r)
    (hTimes : MulAt M T.mulPairs T.times b D.rise off) (hShift : ShiftedRow M C T D.floor off r u)
    (hF : MemPair M D.mountain.parents u F) (hG : MemPair M Y.parents r G)
    (hConeA : InCone M C D a) (hConeC : InCone M C D c) (hcLast : c=D.coordinates.last ∨ M.mem c D.coordinates.last)
    (hAC : a=c ∨ Ancestor M C D.mountain.width F a c)
    (hEncA : Encode M C T D.coordinates a b x) (hEncC : Encode M C T D.coordinates c b y) (hy : M.mem y Y.width)
    (hDA : Depth M C D.mountain.width F a da) (hDC : Depth M C D.mountain.width F c dc)
    (hDX : Depth M C Y.width G x dx) (hDY : Depth M C Y.width G y dy) :
    ∃ e, M.mem e C.omega ∧ Sum M da e dc ∧ Sum M dx e dy := by
  have hFF := hD.mountain.forest u F hF
  have hUHigh := hShift.floor_le_d hM hC hT
  have hOffNat : M.mem off C.omega := by obtain ⟨key,_,_,hAt⟩ := hTimes; exact (hT.mul.graph.bounds hM.1 hAt).2
  obtain ⟨J,hJ,hRows⟩ := parent_copy_graph_exists_d hM hC hT hD.coordinates hEncC.2.1
  have hRootA := hConeA.root_le hM.1 hD
  have hMapA : ParentCopy M C T D.coordinates b a x := (parent_copy_bad_iff (not_mem_of_le hM hC hEncA.1 hRootA)).mpr hEncA
  have hMapC : ParentCopy M C T D.coordinates b c y :=
    (parent_copy_bad_iff (not_mem_of_le hM hC hEncC.1 (hConeC.root_le hM.1 hD))).mpr hEncC
  apply depth_mapped_diff_d hM hC hFF (hY.forest r G hG) hJ hAC ((hRows a x).mpr hMapA) ((hRows c y).mpr hMapC) hy ?_
    hDA hDC hDX hDY
  intro d p u' v hDC' hAP hDP hDU hPV
  have hdNat := (hJ.graph.bounds hM.1 hDU).1
  have hConeD : InCone M C D d := by
    rcases hDC' with he | hAnc
    · exact he ▸ hConeC
    · exact (in_cone_ancestor_iff_d hM hC hD hRun hFrom hUHigh hF hAnc).mpr hConeC
  have hRootD := root_mem_of_le_parent hM hC hdNat hRootA hAP (hFF.left d p hDP)
  have hSourceD : Source M D.coordinates d := ⟨hRootD,chain_last hM hC hD hcLast hDC'⟩
  have hPAt : ParentAt M D.mountain u d p := ⟨F,(hD.mountain.parents.bounds hM.1 hF).2,hF,hDP⟩
  have hConeP := hConeD.high_parent_d hM hC hD hUHigh hPAt
  have hEncD := (parent_copy_bad_iff (not_mem_of_le hM hC hdNat (Or.inr hRootD))).mp ((hRows d u').mp hDU)
  have hEncP := (parent_copy_bad_iff (not_mem_of_le hM hC (hJ.graph.bounds hM.1 hPV).1 (hConeP.root_le hM.1 hD))).mp
    ((hRows p v).mp hPV)
  have hu := image_in_width hM hC hJ hY.width hDC' hDU ((hRows c y).mpr hMapC) hy
  have hAt := (hCopy.encoded_parent_iff_d hM hC hT hD hr hSourceD hEncD (hCopy.width ▸ hu)).mpr
    (Or.inl ⟨⟨hConeD,hHighR⟩,off,hOffNat,hTimes,u,hShift.2.1,hShift,p,hEncP.1,hPAt,hEncP⟩)
  exact (canon_row_parent_iff hM.1 hY hG).mp hAt

/-- 抬升行（r≥floor+b·rise）：锥内列的复制深度等于源shift行深度。 -/
theorem Copies.canon_depth_lifted_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {D : Context M.Domain} (hD : D.Valid M C) {Y : Data M.Domain} (hY : Y.Valid M C) {n : M.Domain}
    (hCopy : Copies M C T D n Y) {m : M.Domain} {R : RowStateSpace M.Domain} {V P H : M.Domain}
    (hRun : RowRun M C m R V P H) (hFrom : FromRun M C m R V H D.mountain)
    {r u off level F G c b y d : M.Domain}
    (hr : M.mem r C.omega) (hTimes : MulAt M T.mulPairs T.times b D.rise off) (hShift : ShiftedRow M C T D.floor off r u)
    (hLevel : AddAt M T.addPairs T.plus D.floor off level) (hNotGap : ¬M.mem r level)
    (hF : MemPair M D.mountain.parents u F) (hG : MemPair M Y.parents r G)
    (hConeC : InCone M C D c) (hcLast : c=D.coordinates.last ∨ M.mem c D.coordinates.last)
    (hEncC : Encode M C T D.coordinates c b y) (hy : M.mem y Y.width)
    (hDC : Depth M C D.mountain.width F c d) : Depth M C Y.width G y d := by
  have hw := omega_isOrdinal_d hM hC.omega
  have hFF := hD.mountain.forest u F hF
  have hUHigh := hShift.floor_le_d hM hC hT
  have hOffNat : M.mem off C.omega := by obtain ⟨key,_,_,hAt⟩ := hTimes; exact (hT.mul.graph.bounds hM.1 hAt).2
  have hLevelBounds := hLevel.bounds hM.1 hT.add
  have hLevelR := nat_le_of_not_lt hM hC hr hLevelBounds.2.2 hNotGap
  have hFloorLevel := ordinal_subset_cases_d hM (hw.mem hLevelBounds.1) (hw.mem hLevelBounds.2.2)
    (sum_base_subset_d hM (hw.mem hLevelBounds.1) ((hT.add.add_iff_sum hM hLevelBounds.1 hOffNat).mp hLevel))
  have hHighR := le_trans_nat hM hC hr hFloorLevel hLevelR
  have hUR := hShift.high_sum_d hM hC hT hLevel hNotGap
  obtain ⟨J,hJ,hRows⟩ := parent_copy_graph_exists_d hM hC hT hD.coordinates hEncC.2.1
  have hMapC : ParentCopy M C T D.coordinates b c y :=
    (parent_copy_bad_iff (not_mem_of_le hM hC hEncC.1 (hConeC.root_le hM.1 hD))).mpr hEncC
  have hConeChain (d : M.Domain) (hDC' : d=c ∨ Ancestor M C D.mountain.width F d c) : InCone M C D d := by
    rcases hDC' with he | hAnc
    · exact he ▸ hConeC
    · exact (in_cone_ancestor_iff_d hM hC hD hRun hFrom hUHigh hF hAnc).mpr hConeC
  apply depth_mapped_eq_d hM hC hFF (hY.forest r G hG) hJ ((hRows c y).mpr hMapC) hy ?_ ?_ hDC
  · intro d p u' v hDC' hDP hDU hPV
    have hdNat := (hJ.graph.bounds hM.1 hDU).1
    have hConeD := hConeChain d hDC'
    have hPAt : ParentAt M D.mountain u d p := ⟨F,(hD.mountain.parents.bounds hM.1 hF).2,hF,hDP⟩
    have hRootD : M.mem D.coordinates.root d := by
      rcases hConeD.root_le hM.1 hD with he | hlt
      · have hAtRoot : ParentAt M D.mountain u D.coordinates.root p := he.symm ▸ hPAt
        exact False.elim (not_mem_of_le hM hC hShift.2.1 hUHigh
          ((hD.mountain.source u D.coordinates.root D.floor hD.floor).mp ⟨p,hAtRoot⟩))
      · exact hlt
    have hSourceD : Source M D.coordinates d := ⟨hRootD,chain_last hM hC hD hcLast hDC'⟩
    have hConeP := hConeD.high_parent_d hM hC hD hUHigh hPAt
    have hEncD := (parent_copy_bad_iff (not_mem_of_le hM hC hdNat (Or.inr hRootD))).mp ((hRows d u').mp hDU)
    have hEncP := (parent_copy_bad_iff (not_mem_of_le hM hC (hJ.graph.bounds hM.1 hPV).1 (hConeP.root_le hM.1 hD))).mp
      ((hRows p v).mp hPV)
    have hu := image_in_width hM hC hJ hY.width hDC' hDU ((hRows c y).mpr hMapC) hy
    have hAt := (hCopy.encoded_parent_iff_d hM hC hT hD hr hSourceD hEncD (hCopy.width ▸ hu)).mpr
      (Or.inl ⟨⟨hConeD,hHighR⟩,off,hOffNat,hTimes,u,hShift.2.1,hShift,p,hEncP.1,hPAt,hEncP⟩)
    exact (canon_row_parent_iff hM.1 hY hG).mp hAt
  · intro q x hQC hNo hQX p _ hP
    have hConeQ := hConeChain q hQC
    have hqNat := (hJ.graph.bounds hM.1 hQX).1
    have hRootQ := hConeQ.root_le hM.1 hD
    have hEncQ := (parent_copy_bad_iff (not_mem_of_le hM hC hqNat hRootQ)).mp ((hRows q x).mp hQX)
    have hAt := (canon_row_parent_iff hM.1 hY hG).mpr hP
    have hx : M.mem x n := hCopy.width ▸ (hAt.bounds hM.1 hY).2.1
    have hqX : M.mem q D.mountain.width := by
      rcases chain_last hM hC hD hcLast hQC with he | hlt
      · exact he ▸ hD.last
      · exact (hw.mem hD.mountain.width).transitive _ hD.last q hlt
    obtain ⟨a,ha,hA⟩ := hD.mountain.heights.total q hqX
    obtain ⟨h,_,hLift⟩ := lifted_exists_d hM hC hT hD ha hEncQ.2.1
    have hYH := (hCopy.canon_copy_heights_d hM hC hT hD hRootQ (chain_last hM hC hD hcLast hQC) hEncQ hx hA).mpr
      (Or.inl ⟨hConeQ,hLift⟩)
    have hrh := (hY.source r x h hYH).mp ⟨p,hAt⟩
    obtain ⟨_,_,off',_,hMul',hAdd⟩ := hLift
    have hoo := hT.mul.mul_unique hM.1 hMul' hTimes
    subst off'
    have hNotU := canon_height_of_no_parent hM.1 hD.mountain hF hA hNo
    have hAU := nat_le_of_not_lt hM hC hShift.2.1 ha hNotU
    have hHR := (add_same_right_le_iff_d hM hC hT hAdd hUR).mpr hAU
    exact not_mem_of_le hM hC hr hHR hrh

end KP1Y.OneYFinite.CopiedMountain.Lower
