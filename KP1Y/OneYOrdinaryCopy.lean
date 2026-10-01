import KP1Y.OneYCopiedMountain

/-! 普通高层复制的实际有限高度图与整条内部 ω 父行家族。 -/
namespace KP1Y.OneYFinite.CopiedMountain.Ordinary
open YesMetaZFC YesMetaZFC.SetTheory YesMetaZFC.SetTheory.Definitional
open KP1Y.Kuratowski KP1Y.Functions KP1Y.Naturals KP1Y.Bounded
open KP1Y.OneYFinite.CopyCoordinates
universe u

theorem Height.parent_copy_iff_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {A : Context M.Domain} (hA : A.Valid M C) {X : Data M.Domain} {p b q h : M.Domain}
    (hp : M.mem p A.last) (hCopy : ParentCopy M C T A b p q) : Height M C T A X q h ↔ MemPair M X.heights p h := by
  constructor
  · rintro ⟨s,_,block,_,hDec,hAt⟩
    have hsp := hDec.source_parent_copy_d hM hC hT hA hp hCopy
    exact hsp ▸ hAt
  · intro hAt
    obtain ⟨block,hDec⟩ := OrdinaryCoordinates.decoded_parent_copy_d hM hC hT hA hp hCopy
    exact ⟨p,hDec.2.1,block,hDec.2.2.1,hDec,hAt⟩

theorem source_iff_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {A : Context M.Domain} (hA : A.Valid M C) {X : Data M.Domain} (hX : X.Valid M C)
    {r c h : M.Domain} (hHeight : Height M C T A X c h) : (∃q,Parent M C T A X r c q) ↔ M.mem r h := by
  obtain ⟨s,hs,b,hb,hDec,hAt⟩ := hHeight
  constructor
  · rintro ⟨q,s',_,b',_,p,_,hDec',hParent,_⟩
    have hss := (hDec.unique_d hM hC hT hA hDec').1
    subst s'
    exact (hX.source r s h hAt).mp ⟨p,hParent⟩
  · intro hr
    obtain ⟨p,hParent⟩ := (hX.source r s h hAt).mpr hr
    have hp := (omega_isOrdinal_d hM hC.omega).transitive X.width hX.width p (hParent.bounds hM.1 hX).2.2.1
    obtain ⟨J,hJ,hRows⟩ := parent_copy_graph_exists_d hM hC hT hA hb
    obtain ⟨q,_,hQ⟩ := hJ.graph.total p hp
    exact ⟨q,s,hs,b,hb,p,hp,hDec,hParent,(hRows p q).mp hQ⟩

theorem endpoint_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {A : Context M.Domain} (hA : A.Valid M C) {X : Data M.Domain} (hX : X.Valid M C)
    {r c q h : M.Domain} (hParent : Parent M C T A X r c q) (hHeight : Height M C T A X q h) : r=h ∨ M.mem r h := by
  obtain ⟨s,_,b,_,p,_,hDec,hParent,hCopy⟩ := hParent
  have hLeft := (hParent.bounds hM.1 hX).2.2.2
  have hp := ((omega_isOrdinal_d hM hC.omega).mem hA.last).transitive s (hDec.source_lt_last_d hM hC hT hA) p hLeft
  exact hX.endpoint r s p h hParent ((Height.parent_copy_iff_d hM hC hT hA hp hCopy).mp hHeight)

private def copyEnv {M : SetTheory.Structure.{u}} (C : ExpressionData M.Domain) (T : MatrixArithmetic M.Domain)
    (A : Context M.Domain) (X : Data M.Domain) : Env M 19 :=
  (((((((((((((((((((oneEnv C.omega).push C.zero).push C.one).push C.sequences).push C.expressions).push T.addPairs).push T.plus).push T.mulPairs).push T.times).push T.diffPairs).push T.difference).push A.last).push A.root).push A.length).push A.first).push X.width).push X.heights).push X.forests).push X.parents)

private def heightSchema : Project.Delta0BinarySchema 19 where
  body := heightFormula ⟨.bound 20,.bound 19,.bound 18,.bound 17,.bound 16⟩ ⟨.bound 15,.bound 14,.bound 13,.bound 12,.bound 11,.bound 10⟩
    ⟨.bound 9,.bound 8,.bound 7,.bound 6⟩ ⟨.bound 5,.bound 4,.bound 3,.bound 2⟩ (.bound 1) (.bound 0)
  freeClosed := heightFormula_freeClosed ⟨rfl,rfl,rfl,rfl,rfl⟩ ⟨rfl,rfl,rfl,rfl,rfl,rfl⟩ ⟨rfl,rfl,rfl,rfl⟩ ⟨rfl,rfl,rfl,rfl⟩ _ _ rfl rfl
  delta0 := heightFormula_delta0 _ _ _ _ _ _

private def parentSchema : Project.Delta0BinarySchema 20 where
  body := parentFormula ⟨.bound 21,.bound 20,.bound 19,.bound 18,.bound 17⟩ ⟨.bound 16,.bound 15,.bound 14,.bound 13,.bound 12,.bound 11⟩
    ⟨.bound 10,.bound 9,.bound 8,.bound 7⟩ ⟨.bound 6,.bound 5,.bound 4,.bound 3⟩ (.bound 2) (.bound 1) (.bound 0)
  freeClosed := parentFormula_freeClosed ⟨rfl,rfl,rfl,rfl,rfl⟩ ⟨rfl,rfl,rfl,rfl,rfl,rfl⟩ ⟨rfl,rfl,rfl,rfl⟩ ⟨rfl,rfl,rfl,rfl⟩ _ _ _ rfl rfl rfl
  delta0 := parentFormula_delta0 _ _ _ _ _ _ _

private theorem heightSchema_iff {M : SetTheory.Structure.{u}} (he : Extensional M)
    (C : ExpressionData M.Domain) (T : MatrixArithmetic M.Domain) (A : Context M.Domain) (X : Data M.Domain) (c h : M.Domain) :
    Project.Formula.satisfies (((copyEnv C T A X).push c).push h) heightSchema.body ↔ Height M C T A X c h :=
  heightFormula_iff he _ _ _ _ _ _ _

private theorem parentSchema_iff {M : SetTheory.Structure.{u}} (he : Extensional M)
    (C : ExpressionData M.Domain) (T : MatrixArithmetic M.Domain) (A : Context M.Domain) (X : Data M.Domain) (r c p : M.Domain) :
    Project.Formula.satisfies ((((copyEnv C T A X).push r).push c).push p) parentSchema.body ↔ Parent M C T A X r c p :=
  parentFormula_iff he _ _ _ _ _ _ _ _

theorem height_graph_exists_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {A : Context M.Domain} (hA : A.Valid M C) {X : Data M.Domain} (hX : X.Valid M C)
    (hLast : M.mem A.last X.width) {n : M.Domain} (hn : M.mem n C.omega) :
    ∃ H, Graph M H n C.omega ∧ ∀ c h, MemPair M H c h ↔ M.mem c n ∧ Height M C T A X c h := by
  obtain ⟨H,hSupport,hRaw⟩ := relation_comprehension_d hM heightSchema (copyEnv C T A X) n C.omega
  have hRows (c h : M.Domain) : MemPair M H c h ↔ M.mem c n ∧ Height M C T A X c h := by
    have hr := hRaw c h
    rw [heightSchema_iff hM.1] at hr
    refine hr.trans ⟨fun h => ⟨h.1,h.2.2⟩,?_⟩
    rintro ⟨hc,hHeight⟩
    have hh : M.mem h C.omega := by
      obtain ⟨s,_,b,_,_,hAt⟩ := hHeight
      exact (hX.heights.bounds hM.1 hAt).2
    exact ⟨hc,hh,hHeight⟩
  refine ⟨H,⟨hSupport,?_,?_⟩,hRows⟩
  · intro c hc
    obtain ⟨h,hh,hHeight⟩ := height_exists_d hM hC hT hA hX hLast ((omega_isOrdinal_d hM hC.omega).transitive n hn c hc)
    exact ⟨h,hh,(hRows c h).mpr ⟨hc,hHeight⟩⟩
  · intro c h h' hAt hAt'
    exact ((hRows c h).mp hAt).2.unique_d hM hC hT hA hX ((hRows c h').mp hAt').2

structure Copies (M : SetTheory.Structure.{u}) (C : ExpressionData M.Domain) (T : MatrixArithmetic M.Domain)
    (A : Context M.Domain) (X : Data M.Domain) (n : M.Domain) (Y : Data M.Domain) : Prop where
  width : Y.width=n
  forests : ∀ F, M.mem F Y.forests ↔ Forest M C.omega n F
  heights : ∀ c h, MemPair M Y.heights c h ↔ M.mem c n ∧ Height M C T A X c h
  parents : ∀ r c p, ParentAt M Y r c p ↔ M.mem c n ∧ Parent M C T A X r c p

theorem copy_exists_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {A : Context M.Domain} (hA : A.Valid M C) {X : Data M.Domain} (hX : X.Valid M C)
    (hLast : M.mem A.last X.width) {n : M.Domain} (hn : M.mem n C.omega) :
    ∃ Y, Y.Valid M C ∧ Copies M C T A X n Y := by
  obtain ⟨Heights,hHeights,hHeightRows⟩ := height_graph_exists_d hM hC hT hA hX hLast hn
  obtain ⟨Forests,Parents,hParents,hForests,hParentRows⟩ := forest_family_exists_d hM hC parentSchema (copyEnv C T A X) hn
    (fun r _ c _ p _ hφ => ((parentSchema_iff hM.1 C T A X r c p).mp hφ).left_d hM hC hT hA hX)
    (fun r _ c _ p _ q _ hφ hφ' => ((parentSchema_iff hM.1 C T A X r c p).mp hφ).unique_d hM hC hT hA hX
      ((parentSchema_iff hM.1 C T A X r c q).mp hφ'))
  let Y : Data M.Domain := ⟨n,Heights,Forests,Parents⟩
  have hForest (r F : M.Domain) (hRow : MemPair M Parents r F) : Forest M C.omega n F := ((hParentRows r F).mp hRow).2.1
  have hRows (r c p : M.Domain) : ParentAt M Y r c p ↔ M.mem c n ∧ Parent M C T A X r c p := by
    constructor
    · rintro ⟨F,_,hF,hAt⟩
      obtain ⟨hc,hp⟩ := (hForest r F hF).bounds hM.1 hAt
      exact ⟨hc,(parentSchema_iff hM.1 C T A X r c p).mp ((((hParentRows r F).mp hF).2.2 c hc p hp).mp hAt)⟩
    · rintro ⟨hc,hParent⟩
      have hr : M.mem r C.omega := by
        obtain ⟨s,_,b,_,q,_,_,hBase,_⟩ := hParent
        exact (hBase.bounds hM.1 hX).1
      have hp := ((omega_isOrdinal_d hM hC.omega).mem hn).transitive c hc p (hParent.left_d hM hC hT hA hX)
      obtain ⟨F,hF,hRow⟩ := hParents.total r hr
      exact ⟨F,hF,hRow,(((hParentRows r F).mp hRow).2.2 c hc p hp).mpr ((parentSchema_iff hM.1 C T A X r c p).mpr hParent)⟩
  refine ⟨Y,⟨hn,hHeights,hParents,hForest,?_,?_⟩,rfl,hForests,hHeightRows,hRows⟩
  · intro r c h hAt
    obtain ⟨hc,hHeight⟩ := (hHeightRows c h).mp hAt
    refine Iff.trans ?_ (source_iff_d hM hC hT hA hX hHeight)
    exact ⟨fun ⟨p,hp⟩ => ⟨p,((hRows r c p).mp hp).2⟩,fun ⟨p,hp⟩ => ⟨p,(hRows r c p).mpr ⟨hc,hp⟩⟩⟩
  · intro r c p h hParent hAt
    exact endpoint_d hM hC hT hA hX ((hRows r c p).mp hParent).2 ((hHeightRows p h).mp hAt).2


private theorem row_parent_iff {M : SetTheory.Structure.{u}} (he : Extensional M)
    {C : ExpressionData M.Domain} {X : Data M.Domain} (hX : X.Valid M C) {r F : M.Domain}
    (hRow : MemPair M X.parents r F) (c p : M.Domain) : MemPair M F c p ↔ ParentAt M X r c p := by
  constructor
  · intro hAt
    exact ⟨F,(hX.parents.bounds he hRow).2,hRow,hAt⟩
  · rintro ⟨G,_,hG,hAt⟩
    have hGF := hX.parents.unique r G F hG hRow
    exact hGF ▸ hAt

/-- 有限山形数据的外延性，供所有复制分支共用。 -/
theorem data_ext {M : SetTheory.Structure.{u}} (he : Extensional M)
    {C : ExpressionData M.Domain} {Y Z : Data M.Domain} (hY : Y.Valid M C) (hZ : Z.Valid M C)
    (hWidths : Y.width=Z.width) (hForests : Y.forests=Z.forests)
    (hHeightRows : ∀ c v, MemPair M Y.heights c v ↔ MemPair M Z.heights c v)
    (hParentRows : ∀ r c p, ParentAt M Y r c p ↔ ParentAt M Z r c p) : Y=Z := by
  have hHeights : Y.heights=Z.heights := by
    have hZG : Graph M Z.heights Y.width C.omega := hWidths.symm ▸ hZ.heights
    exact hY.heights.ext he hZG (fun c _ v => hHeightRows c v)
  have row_eq (r F G : M.Domain) (hF : MemPair M Y.parents r F) (hG : MemPair M Z.parents r G) : F=G := by
    have hGF : Forest M C.omega Y.width G := hWidths.symm ▸ hZ.forest r G hG
    apply (hY.forest r F hF).ext he hGF
    intro c p
    exact (row_parent_iff he hY hF c p).trans ((hParentRows r c p).trans (row_parent_iff he hZ hG c p).symm)
  have hParents : Y.parents=Z.parents := by
    have hZG : Graph M Z.parents C.omega Y.forests := hForests.symm ▸ hZ.parents
    apply hY.parents.ext he hZG
    intro r hr F
    obtain ⟨G,_,hG⟩ := hY.parents.total r hr
    obtain ⟨G',_,hG'⟩ := hZ.parents.total r hr
    have hGG := row_eq r G G' hG hG'
    subst G'
    constructor
    · intro hF
      exact (hY.parents.unique r F G hF hG).symm ▸ hG'
    · intro hF
      exact (hZ.parents.unique r F G hF hG').symm ▸ hG
  cases Y
  cases Z
  simp_all

theorem Copies.unique {M : SetTheory.Structure.{u}} (he : Extensional M)
    {C : ExpressionData M.Domain} {T : MatrixArithmetic M.Domain} {A : Context M.Domain} {X Y Z : Data M.Domain} {n : M.Domain}
    (hY : Y.Valid M C) (hZ : Z.Valid M C) (h : Copies M C T A X n Y) (h' : Copies M C T A X n Z) : Y=Z :=
  data_ext he hY hZ (h.width.trans h'.width.symm)
    (he.eq_of_same_members _ _ (fun F => (h.forests F).trans (h'.forests F).symm))
    (fun c v => (h.heights c v).trans (h'.heights c v).symm)
    (fun r c p => (h.parents r c p).trans (h'.parents r c p).symm)

theorem height_original_iff_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {A : Context M.Domain} (hA : A.Valid M C) {X : Data M.Domain} {c h : M.Domain}
    (hc : M.mem c A.last) : Height M C T A X c h ↔ MemPair M X.heights c h := by
  constructor
  · rintro ⟨s,_,b,_,hDec,hAt⟩
    exact (hDec.original_d hM hC hT hA hc).1 ▸ hAt
  · intro hAt
    have hDec := OrdinaryCoordinates.decoded_original_d hM hC hT hA hc
    exact ⟨c,hDec.2.1,C.zero,hC.zero_nat,hDec,hAt⟩

theorem parent_original_iff_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {A : Context M.Domain} (hA : A.Valid M C) {X : Data M.Domain} (hX : X.Valid M C) {r c q : M.Domain}
    (hc : M.mem c A.last) : Parent M C T A X r c q ↔ ParentAt M X r c q := by
  constructor
  · rintro ⟨s,_,b,_,p,hp,hDec,hParent,hCopy⟩
    obtain ⟨hsc,hb⟩ := hDec.original_d hM hC hT hA hc
    subst s
    subst b
    obtain ⟨J,hJ,hRows⟩ := parent_copy_graph_exists_d hM hC hT hA hC.zero_nat
    have hqp := hJ.graph.unique p q p ((hRows p q).mpr hCopy) ((hRows p p).mpr (parent_copy_zero_d hM hC hT hA hp))
    exact hqp.symm ▸ hParent
  · intro hParent
    have hcNat := (omega_isOrdinal_d hM hC.omega).transitive A.last hA.last c hc
    have hqNat := (omega_isOrdinal_d hM hC.omega).transitive X.width hX.width q (hParent.bounds hM.1 hX).2.2.1
    exact ⟨c,hcNat,C.zero,hC.zero_nat,q,hqNat,OrdinaryCoordinates.decoded_original_d hM hC hT hA hc,
      hParent,parent_copy_zero_d hM hC hT hA hqNat⟩

theorem Copies.original_heights_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {A : Context M.Domain} (hA : A.Valid M C) {X Y : Data M.Domain} {n c height : M.Domain}
    (h : Copies M C T A X n Y) (hc : M.mem c n) (hLast : M.mem c A.last) :
    MemPair M Y.heights c height ↔ MemPair M X.heights c height :=
  (h.heights c height).trans (⟨And.right,fun h => ⟨hc,h⟩⟩ : (M.mem c n ∧ Height M C T A X c height) ↔ Height M C T A X c height) |>.trans
    (height_original_iff_d hM hC hT hA hLast)

theorem Copies.original_parents_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {A : Context M.Domain} (hA : A.Valid M C) {X Y : Data M.Domain} (hX : X.Valid M C) {n r c p : M.Domain}
    (h : Copies M C T A X n Y) (hc : M.mem c n) (hLast : M.mem c A.last) : ParentAt M Y r c p ↔ ParentAt M X r c p := by
  rw [h.parents r c p,parent_original_iff_d hM hC hT hA hX hLast]
  exact ⟨And.right,fun h => ⟨hc,h⟩⟩

end KP1Y.OneYFinite.CopiedMountain.Ordinary
