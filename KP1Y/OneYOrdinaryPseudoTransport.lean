import KP1Y.OneYOrdinaryForestTransport
import KP1Y.OneYGraphPseudo

/-! 普通复制的实际伪父与提取候选森林；不存在未解除的目标选择假设。 -/
namespace KP1Y.OneYFinite.CopiedMountain.Ordinary
open YesMetaZFC YesMetaZFC.SetTheory YesMetaZFC.SetTheory.Definitional
open KP1Y.Kuratowski KP1Y.Functions KP1Y.Assignments KP1Y.Naturals
open KP1Y.OneYFinite.CopyCoordinates
universe u

theorem Copies.pseudo_candidate_copy_iff_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {A : Context M.Domain} (hA : A.Valid M C) {X Y : Data M.Domain} (hX : X.Valid M C) (hY : Y.Valid M C)
    {n s b c a : M.Domain} (hCopy : Copies M C T A X n Y)
    (hs : M.mem s A.last) (hc : M.mem c Y.width) (hMap : ParentCopy M C T A b s c) :
    GraphPseudoCandidate M C Y c a ↔ ∃p, GraphPseudoCandidate M C X s p ∧ ParentCopy M C T A b p a := by
  have hHeight (h : M.Domain) : MemPair M Y.heights c h ↔ MemPair M X.heights s h := by
    rw [hCopy.heights c h]
    have hcN := hCopy.width ▸ hc
    simp only [hcN,true_and]
    exact Height.parent_copy_iff_d hM hC hT hA hs hMap
  constructor
  · rintro ⟨height,hh,hp,hhp,r,hr,hCH,hAH,hSucc,G,_,hG,hAnc,hRel⟩
    obtain ⟨F,hF,hRow⟩ := hX.parents.total r hr
    obtain ⟨p,hOldAnc,hMapP⟩ := (hCopy.ancestor_parent_copy_iff_d hM hC hT hA hX hY hRow hG hs hMap hc).mp hAnc
    have hpLast := ((omega_isOrdinal_d hM hC.omega).mem hA.last).transitive s hs p hOldAnc.1
    have hPH := (Height.parent_copy_iff_d hM hC hT hA hpLast hMapP).mp ((hCopy.heights a hp).mp hAH).2
    exact ⟨p,⟨height,hh,hp,hhp,r,hr,(hHeight height).mp hCH,hPH,hSucc,F,hF,hRow,hOldAnc,hRel⟩,hMapP⟩
  · rintro ⟨p,⟨height,hh,hp,hhp,r,hr,hSH,hPH,hSucc,F,_,hF,hAnc,hRel⟩,hMapP⟩
    obtain ⟨G,hG,hRow⟩ := hY.parents.total r hr
    have hNewAnc := hCopy.ancestor_parent_copy_d hM hC hT hA hX hY hF hRow hAnc hs hMapP hMap hc
    have hpLast := ((omega_isOrdinal_d hM hC.omega).mem hA.last).transitive s hs p hAnc.1
    have hAH := (hCopy.heights a hp).mpr ⟨hCopy.width ▸ (hNewAnc.bounds hM.1).1,
      (Height.parent_copy_iff_d hM hC hT hA hpLast hMapP).mpr hPH⟩
    exact ⟨height,hh,hp,hhp,r,hr,(hHeight height).mpr hSH,hAH,hSucc,G,hG,hRow,hNewAnc,hRel⟩

theorem Copies.pseudo_parent_copy_iff_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {A : Context M.Domain} (hA : A.Valid M C) {X Y : Data M.Domain} (hX : X.Valid M C) (hY : Y.Valid M C)
    {n s b c a : M.Domain} (hCopy : Copies M C T A X n Y)
    (hs : M.mem s A.last) (hc : M.mem c Y.width) (hMap : ParentCopy M C T A b s c) :
    GraphPseudoParent M C Y c a ↔ ∃p, GraphPseudoParent M C X s p ∧ ParentCopy M C T A b p a := by
  have hCandidate := fun a => hCopy.pseudo_candidate_copy_iff_d hM hC hT hA hX hY hs hc hMap (a := a)
  constructor
  · rintro ⟨hCand,hMax⟩
    obtain ⟨p,hp,hMapP⟩ := (hCandidate a).mp hCand
    refine ⟨p,⟨hp,?_⟩,hMapP⟩
    intro q _ hq
    obtain ⟨J,hJ,hRows⟩ := parent_copy_graph_exists_d hM hC hT hA hMap.2.1
    have hqω := (omega_isOrdinal_d hM hC.omega).transitive X.width hX.width q (hq.bounds hM.1).1
    obtain ⟨x,_,hQX⟩ := hJ.graph.total q hqω
    have hMapQ := (hRows q x).mp hQX
    have hNew := (hCandidate x).mpr ⟨q,hq,hMapQ⟩
    exact (parent_copy_le_iff_d hM hC hT hA hMapQ hMapP).mp (hMax x (hNew.bounds hM.1).2.2 hNew)
  · rintro ⟨p,⟨hp,hMax⟩,hMapP⟩
    refine ⟨(hCandidate a).mpr ⟨p,hp,hMapP⟩,?_⟩
    intro x _ hx
    obtain ⟨q,hq,hMapQ⟩ := (hCandidate x).mp hx
    exact (parent_copy_le_iff_d hM hC hT hA hMapQ hMapP).mpr (hMax q (hq.bounds hM.1).2.2 hq)

/-- 任意实际有限森林的普通复制规格，在每个固定块像上给出完整父行对应。 -/
def ForestCopies (M : SetTheory.Structure.{u}) (C : ExpressionData M.Domain) (T : MatrixArithmetic M.Domain)
    (A : Context M.Domain) (n F G : M.Domain) : Prop :=
  ∀s b c, M.mem s A.last → M.mem c n → ParentCopy M C T A b s c → ∀a,
    MemPair M G c a ↔ ∃p, MemPair M F s p ∧ ParentCopy M C T A b p a

theorem Copies.pseudo_forests_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {A : Context M.Domain} (hA : A.Valid M C) {X Y : Data M.Domain} (hX : X.Valid M C) (hY : Y.Valid M C)
    {n F G : M.Domain} (hCopy : Copies M C T A X n Y)
    (hF : GraphPseudoForest M C X F) (hG : GraphPseudoForest M C Y G) : ForestCopies M C T A n F G := by
  intro s b c hs hc hMap a
  rw [hG.rows c a,hCopy.pseudo_parent_copy_iff_d hM hC hT hA hX hY hs (hCopy.width.symm ▸ hc) hMap]
  exact ⟨fun ⟨p,hp,hMapP⟩ => ⟨p,(hF.rows s p).mpr hp,hMapP⟩,
    fun ⟨p,hp,hMapP⟩ => ⟨p,(hF.rows s p).mp hp,hMapP⟩⟩

theorem ForestCopies.ancestor_iff_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {A : Context M.Domain} (hA : A.Valid M C) {m n F G s b c a : M.Domain}
    (hF : Forest M C.omega m F) (hG : Forest M C.omega n G) (hCopy : ForestCopies M C T A n F G)
    (hs : M.mem s A.last) (hc : M.mem c n) (hMap : ParentCopy M C T A b s c) :
    Ancestor M C n G a c ↔ ∃p, Ancestor M C m F p s ∧ ParentCopy M C T A b p a := by
  have hw := omega_isOrdinal_d hM hC.omega
  obtain ⟨J,hJ,hRows⟩ := parent_copy_graph_exists_d hM hC hT hA hMap.2.1
  constructor
  · intro hAnc
    obtain ⟨p,hp,hMapP⟩ := ancestor_pullback_below_d hM hC hF hG hA.last (J := J)
      (fun d hd u hu hDU v => by
        rw [hCopy d b u hd hu ((hRows d u).mp hDU) v]
        exact ⟨fun ⟨p,hp,hMapP⟩ => ⟨p,hp,(hRows p v).mpr hMapP⟩,
          fun ⟨p,hp,hMapP⟩ => ⟨p,hp,(hRows p v).mp hMapP⟩⟩)
      hs ((hRows s c).mpr hMap) hAnc
    exact ⟨p,hp,(hRows p a).mp hMapP⟩
  · rintro ⟨p,hp,hMapP⟩
    have hSC := (hRows s c).mpr hMap
    apply ancestor_map_global_bounded_d hM hC hF hG.width hJ hp ((hRows p a).mpr hMapP) hSC hc
    intro d q u v hD hParent hDU hQV
    have hdLast : M.mem d A.last := by
      rcases hD with he | hAnc
      · exact he.symm ▸ hs
      · exact (hw.mem hA.last).transitive s hs d hAnc.1
    have hu : M.mem u n := by
      rcases hD with he | hAnc
      · exact (hJ.graph.unique s u c (he ▸ hDU) hSC).symm ▸ hc
      · exact (hw.mem hG.width).transitive c hc u
          (hJ.strict d (hJ.graph.bounds hM.1 hDU).1 s hMap.1 hAnc.1 u c hDU hSC)
    exact (hCopy d b u hdLast hu ((hRows d u).mp hDU) v).mpr ⟨q,hParent,(hRows q v).mp hQV⟩

theorem ForestCopies.candidate_iff_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    (positive : Bool) {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {A : Context M.Domain} (hA : A.Valid M C) {m n F G V W s b c a : M.Domain}
    (hF : Forest M C.omega m F) (hG : Forest M C.omega n G) (hCopy : ForestCopies M C T A n F G)
    (hValues : ValueCopies M C T A V n C.omega W)
    (hs : M.mem s A.last) (hc : M.mem c n) (hMap : ParentCopy M C T A b s c) :
    ParentCandidate positive M C n G W c a ↔ ∃p, ParentCandidate positive M C m F V s p ∧ ParentCopy M C T A b p a := by
  have hAnc := hCopy.ancestor_iff_d hM hC hT hA hF hG hs hc hMap (a := a)
  constructor
  · rintro ⟨ha,x,hx,y,hy,hAX,hCY,hXY,hPos⟩
    obtain ⟨p,hp,hMapP⟩ := hAnc.mp ha
    have hpLast := ((omega_isOrdinal_d hM hC.omega).mem hA.last).transitive s hs p hp.1
    exact ⟨p,⟨hp,x,hx,y,hy,((hValues.parent_copy_iff_d hM hC hT hA hpLast hMapP).mp hAX).2,
      ((hValues.parent_copy_iff_d hM hC hT hA hs hMap).mp hCY).2,hXY,hPos⟩,hMapP⟩
  · rintro ⟨p,⟨hp,x,hx,y,hy,hPX,hSY,hXY,hPos⟩,hMapP⟩
    have ha := hAnc.mpr ⟨p,hp,hMapP⟩
    have hpLast := ((omega_isOrdinal_d hM hC.omega).mem hA.last).transitive s hs p hp.1
    exact ⟨ha,x,hx,y,hy,(hValues.parent_copy_iff_d hM hC hT hA hpLast hMapP).mpr ⟨(ha.bounds hM.1).1,hPX⟩,
      (hValues.parent_copy_iff_d hM hC hT hA hs hMap).mpr ⟨hc,hSY⟩,hXY,hPos⟩

theorem ForestCopies.restricted_iff_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    (positive : Bool) {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {A : Context M.Domain} (hA : A.Valid M C) {m n F G V W s b c a : M.Domain}
    (hF : Forest M C.omega m F) (hG : Forest M C.omega n G) (hCopy : ForestCopies M C T A n F G)
    (hValues : ValueCopies M C T A V n C.omega W)
    (hs : M.mem s A.last) (hc : M.mem c n) (hMap : ParentCopy M C T A b s c) :
    RestrictedParent positive M C n G W c a ↔ ∃p, RestrictedParent positive M C m F V s p ∧ ParentCopy M C T A b p a := by
  have hCandidate := fun a => hCopy.candidate_iff_d hM positive hC hT hA hF hG hValues hs hc hMap (a := a)
  constructor
  · rintro ⟨hCand,hMax⟩
    obtain ⟨p,hp,hMapP⟩ := (hCandidate a).mp hCand
    refine ⟨p,⟨hp,?_⟩,hMapP⟩
    intro q _ hq
    obtain ⟨J,hJ,hRows⟩ := parent_copy_graph_exists_d hM hC hT hA hMap.2.1
    have hqω := (omega_isOrdinal_d hM hC.omega).transitive m hF.width q (hq.1.bounds hM.1).1
    obtain ⟨x,_,hQX⟩ := hJ.graph.total q hqω
    have hMapQ := (hRows q x).mp hQX
    have hNew := (hCandidate x).mpr ⟨q,hq,hMapQ⟩
    exact (parent_copy_le_iff_d hM hC hT hA hMapQ hMapP).mp (hMax x hNew.1.1 hNew)
  · rintro ⟨p,⟨hp,hMax⟩,hMapP⟩
    refine ⟨(hCandidate a).mpr ⟨p,hp,hMapP⟩,?_⟩
    intro x _ hx
    obtain ⟨q,hq,hMapQ⟩ := (hCandidate x).mp hx
    exact (parent_copy_le_iff_d hM hC hT hA hMapQ hMapP).mpr (hMax q hq.1.1 hq)

theorem ForestCopies.selected_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    (positive : Bool) {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {A : Context M.Domain} (hA : A.Valid M C) {m n F G V W P Q : M.Domain}
    (hCopy : ForestCopies M C T A n F G) (hValues : ValueCopies M C T A V n C.omega W)
    (hSource : Selects positive M C m F V P) (hTarget : Selects positive M C n G W Q) :
    ForestCopies M C T A n P Q := by
  intro s b c hs hc hMap a
  rw [hTarget.parents c a,hCopy.restricted_iff_d hM positive hC hT hA hSource.inherited hTarget.inherited hValues hs hc hMap]
  exact ⟨fun ⟨p,hp,hMapP⟩ => ⟨p,(hSource.parents s p).mpr hp,hMapP⟩,
    fun ⟨p,hp,hMapP⟩ => ⟨p,(hSource.parents s p).mp hp,hMapP⟩⟩

/-- 工厂先实际计算目标最右选择，再由运输定理证明其恰是源所选父森林的复制。 -/
theorem Copies.pseudo_selection_exists_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {A : Context M.Domain} (hA : A.Valid M C) {X Y : Data M.Domain} (hX : X.Valid M C) (hY : Y.Valid M C)
    {n F G Top Top' P : M.Domain} (hCopy : Copies M C T A X n Y)
    (hF : GraphPseudoForest M C X F) (hG : GraphPseudoForest M C Y G)
    (hTop : ValueCopies M C T A Top n C.omega Top') (hSource : Selects true M C X.width F Top P) :
    ∃Q, Selects true M C Y.width G Top' Q ∧ ForestCopies M C T A n P Q := by
  obtain ⟨Q,hQ⟩ := select_forest_exists_d hM true hC hG.forest (hCopy.width.symm ▸ hTop.graph)
  have hQn : Selects true M C n G Top' Q := hCopy.width ▸ hQ
  exact ⟨Q,hQ,(hCopy.pseudo_forests_d hM hC hT hA hX hY hF hG).selected_d hM true hC hT hA hTop hSource hQn⟩

end KP1Y.OneYFinite.CopiedMountain.Ordinary
