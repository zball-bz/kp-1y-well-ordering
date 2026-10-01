import KP1Y.OneYLowerCanonPseudoSeam
import KP1Y.OneYLowerPseudoTransport

/-! Lower复制目标图伪父的低高度情形（0<H(s)≤floor，s在锥外）：经接缝的阈值搜索只保留root本身
（原 firstMatch_copy_low / pseudo_parent_low）。 -/
namespace KP1Y.OneYFinite.CopiedMountain.Lower
open YesMetaZFC YesMetaZFC.SetTheory YesMetaZFC.SetTheory.Definitional
open KP1Y.Kuratowski KP1Y.Functions KP1Y.Naturals KP1Y.Bounded KP1Y.Arithmetic
open KP1Y.OneYFinite.CopyCoordinates KP1Y.OneYFinite.LowerCanon
universe u

/-- 低行伪父的root收缩关系：root映到root，其余列按同块ParentCopy。 -/
def LowCopy (M : SetTheory.Structure.{u}) (C : ExpressionData M.Domain) (T : MatrixArithmetic M.Domain)
    (A : CopyCoordinates.Context M.Domain) (b q a : M.Domain) : Prop :=
  (q=A.root ∧ a=A.root) ∨ (q≠A.root ∧ ParentCopy M C T A b q a)

theorem Copies.canon_pseudo_cand_low_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {D : Context M.Domain} (hD : D.Valid M C) {Y : Data M.Domain} (hY : Y.Valid M C) {n : M.Domain}
    (hCopy : Copies M C T D n Y) {m : M.Domain} {R : RowStateSpace M.Domain} {V P H : M.Domain}
    (hRun : RowRun M C m R V P H) (hFrom : FromRun M C m R V H D.mountain) {s b c hs : M.Domain}
    (hRootS : M.mem D.coordinates.root s) (hsLast : M.mem s D.coordinates.last) (hOut : ¬InCone M C D s)
    (hHS : MemPair M D.mountain.heights s hs) (hPos : M.mem C.zero hs) (hLowH : hs=D.floor ∨ M.mem hs D.floor)
    (hMap : ParentCopy M C T D.coordinates b s c) (hc : M.mem c Y.width) (a : M.Domain) :
    GraphPseudoCandidate M C Y c a ↔ ∃ q, GraphPseudoCandidate M C D.mountain s q ∧ LowCopy M C T D.coordinates b q a := by
  have hw := omega_isOrdinal_d hM hC.omega
  have hFloorNat := hD.floor_nat hM.1
  have hsX := canon_last_in_width hM hC hD (Or.inr hsLast)
  have hsNat := (hD.mountain.heights.bounds hM.1 hHS).2
  obtain ⟨r,hrNat,hSuccR⟩ : ∃ r, M.mem r C.omega ∧ M.SuccessorOf hs r := by
    rcases natural_cases hM hC.omega hsNat with hEmpty | ⟨r,hr,hSucc⟩
    · exact False.elim (hEmpty _ hPos)
    · exact ⟨r,hr,hSucc⟩
  have hLow : M.mem r D.floor := nat_lt_of_lt_of_le hM hC hFloorNat hSuccR.predecessor_mem hLowH
  have hRootNot : ¬M.mem D.coordinates.root D.coordinates.root := nat_irrefl hM _
  have hRootLast := hD.coordinates.below
  have hRootY : MemPair M D.mountain.heights D.coordinates.root D.floor := hD.floor
  have hHC : MemPair M Y.heights c hs :=
    (hCopy.parent_copy_heights_d hM hC hT hD hsLast (hCopy.width ▸ hc) hMap hHS).mpr (Or.inr ⟨hOut,rfl⟩)
  obtain ⟨F,hFm,hF⟩ := hD.mountain.parents.total r hrNat
  obtain ⟨G,hGm,hG⟩ := hY.parents.total r hrNat
  have hFF := hD.mountain.forest r F hF
  have hGF := hY.forest r G hG
  obtain ⟨J,hJ,hRows⟩ := parent_copy_graph_exists_d hM hC hT hD.coordinates hMap.2.1
  -- s ≤ c，用作公共前缀界
  have hEncS := (parent_copy_bad_iff (nat_not_lt_of_le hM hC hMap.1 (Or.inr hRootS))).mp hMap
  have hSC : M.MemberSubset s c := by
    obtain ⟨_,_,off,hOff,_,hAdd⟩ := hEncS
    exact sum_base_subset_d hM (hw.mem hMap.1) ((hT.add.add_iff_sum hM hMap.1 hOff).mp hAdd)
  have hsY : M.MemberSubset s Y.width := fun d hd => (hw.mem hY.width).transitive c hc d (hSC d hd)
  have hsXsub : M.MemberSubset s D.mountain.width := fun d hd => (hw.mem hD.mountain.width).transitive s hsX d hd
  have hPrefixAnc (p : M.Domain) (hp : M.mem p s) (q : M.Domain) :
      Ancestor M C D.mountain.width F q p ↔ Ancestor M C Y.width G q p :=
    ancestor_row_prefix_iff_d hM hC hD.mountain hY hMap.1 hsXsub hsY hF hG
      (fun d hd q => (hCopy.original_parents_d hM hC hD (hCopy.width ▸ hsY d hd)
        (Or.inr (nat_lt_trans hM hC hD.coordinates.last hd hsLast))).symm) hp
  have hOrigHeight (d hd : M.Domain) (hdS : M.mem d s) : MemPair M Y.heights d hd ↔ MemPair M D.mountain.heights d hd :=
    hCopy.original_heights_d hM hC hD (hCopy.width ▸ hsY d hdS) (Or.inr (nat_lt_trans hM hC hD.coordinates.last hdS hsLast))
  have hNoMid (h : M.Domain) (hRel : h=hs ∨ h=r) (hMid : M.mem hs h) : False := by
    rcases hRel with he | he
    · rw [he] at hMid
      exact nat_irrefl hM hs hMid
    · rw [he] at hMid
      exact nat_irrefl hM hs (nat_lt_trans hM hC hsNat hMid hSuccR.predecessor_mem)
  have hRootCand (hAnc : Ancestor M C D.mountain.width F D.coordinates.root s) (hRel : D.floor=hs ∨ D.floor=r) :
      GraphPseudoCandidate M C D.mountain s D.coordinates.root :=
    ⟨hs,hsNat,D.floor,hFloorNat,r,hrNat,hHS,hRootY,hSuccR,F,hFm,hF,hAnc,hRel⟩
  have hRootYH (h : M.Domain) : MemPair M Y.heights D.coordinates.root h ↔ MemPair M D.mountain.heights D.coordinates.root h :=
    hOrigHeight D.coordinates.root h hRootS
  constructor
  · rintro ⟨hc'',_,hp,hpNat,r',hr',hHC',hHA,hSucc,G',_,hG',hAnc,hRel⟩
    have he1 := hY.heights.unique c hc'' hs hHC' hHC
    subst hc''
    have he2 := Structure.SuccessorOf.predecessor_eq hM.1 (hw.mem hr') hSucc hSuccR
    subst r'
    have he3 := hY.parents.unique r G' G hG' hG
    subst G'
    have haY := (hAnc.bounds hM.1).1
    have haNat := hw.transitive Y.width hY.width a haY
    have hEdge : ∀ d u' v, (d=s ∨ Ancestor M C D.mountain.width F d s) → d≠D.coordinates.root →
        MemPair M J d u' → MemPair M G u' v → ∃ p, MemPair M F d p ∧ MemPair M J p v := by
      intro d u' v hChain hne hDU hUV
      have hdLast : d=D.coordinates.last ∨ M.mem d D.coordinates.last := by
        rcases hChain with he | hDS
        · exact Or.inr (he ▸ hsLast)
        · exact Or.inr (nat_lt_trans hM hC hD.coordinates.last hDS.1 hsLast)
      obtain ⟨p,hP,hMapP⟩ := (hCopy.canon_low_parent_iff_d hM hC hT hD hLow hdLast hne ((hRows d u').mp hDU)
        (hCopy.width ▸ (hGF.bounds hM.1 hUV).1)).mp ((canon_row_parent_iff hM.1 hY hG).mpr hUV)
      exact ⟨p,(canon_row_parent_iff hM.1 hD.mountain hF).mp hP,(hRows p v).mpr hMapP⟩
    have hSeam (w : M.Domain) (hMapW : ParentCopy M C T D.coordinates b D.coordinates.root w) (hwY : M.mem w Y.width)
        (hAW : a=w ∨ Ancestor M C Y.width G a w) (hRA : M.mem D.coordinates.root a) : False :=
      hNoMid hp hRel (hCopy.canon_seam_heights_low_d hM hC hT hD hY hRun hFrom hLow hSuccR hLowH hG hMapW hwY haY hAW hRA hHA)
    rcases ancestor_preimage_d (y₀ := D.coordinates.root) hM hC hFF hGF hEdge ((hRows s c).mpr hMap) hAnc with
      ⟨q,hQS,hJQ⟩ | ⟨hY0,w,hJW,hAW⟩
    · have hqNat := (hJ.graph.bounds hM.1 hJQ).1
      have hMapQ := (hRows q a).mp hJQ
      have hqs := hQS.1
      rcases (omega_isOrdinal_d hM hC.omega).wellOrder.linear.compare q hqNat D.coordinates.root hD.coordinates.root with
        he | hqr | hrq
      · have he := hM.1.eq_of_same_members q _ he
        subst he
        rcases (omega_isOrdinal_d hM hC.omega).wellOrder.linear.compare a haNat D.coordinates.root hD.coordinates.root with
          ha | har | hra
        · have ha := hM.1.eq_of_same_members a _ ha
          subst ha
          have hHR := (hRootYH hp).mp hHA
          have hpFloor := hD.mountain.heights.unique _ hp D.floor hHR hRootY
          subst hpFloor
          exact ⟨D.coordinates.root,hRootCand hQS hRel,Or.inl ⟨rfl,rfl⟩⟩
        · have hEncR := (parent_copy_bad_iff hRootNot).mp hMapQ
          obtain ⟨_,_,off,hOff,_,hAdd⟩ := hEncR
          have hle := sum_base_subset_d hM (hw.mem hD.coordinates.root)
            ((hT.add.add_iff_sum hM hD.coordinates.root hOff).mp hAdd)
          exact False.elim (nat_irrefl hM a (hle a har))
        · exact False.elim (hSeam a hMapQ haY (Or.inl rfl) hra)
      · have haq := (parent_copy_good_iff hMapQ.2.1 hqNat hqr).mp hMapQ
        subst haq
        have hHQ := (hOrigHeight a hp hqs).mp hHA
        exact ⟨a,⟨hs,hsNat,hp,hpNat,r,hrNat,hHS,hHQ,hSuccR,F,hFm,hF,hQS,hRel⟩,
          Or.inr ⟨fun he => hRootNot (he ▸ hqr),hMapQ⟩⟩
      · have hqLast : M.mem q D.coordinates.last := nat_lt_trans hM hC hD.coordinates.last hqs hsLast
        obtain ⟨hq,hqhNat,hHQ⟩ := hD.mountain.heights.total q (hQS.bounds hM.1).1
        have hHeights := (hCopy.parent_copy_heights_d hM hC hT hD hqLast (hCopy.width ▸ haY) hMapQ hHQ).mp hHA
        rcases hHeights with ⟨hConeQ,hLift⟩ | ⟨hOutQ,hpq⟩
        · have hFloorQ := hConeQ.height_strict_d hM hC hD hrq hHQ
          have hLe := hLift.base_le_d hM hC hT
          exact False.elim (hNoMid hp hRel (nat_lt_of_le_of_lt hM hC hpNat hLowH (nat_lt_of_lt_of_le hM hC hpNat hFloorQ hLe)))
        · subst hpq
          exact ⟨q,⟨hs,hsNat,hp,hqhNat,r,hrNat,hHS,hHQ,hSuccR,F,hFm,hF,hQS,hRel⟩,
            Or.inr ⟨fun he => hRootNot (he ▸ hrq),hMapQ⟩⟩
    · have hMapW := (hRows _ w).mp hJW
      have hwY : M.mem w Y.width := hAW.elim (fun he => he ▸ haY) (fun h => (h.bounds hM.1).2)
      have hRS : Ancestor M C D.mountain.width F D.coordinates.root s := hY0.resolve_left (fun he => hRootNot (he ▸ hRootS))
      rcases (omega_isOrdinal_d hM hC.omega).wellOrder.linear.compare a haNat D.coordinates.root hD.coordinates.root with
        ha | har | hra
      · have ha := hM.1.eq_of_same_members a _ ha
        subst ha
        have hHR := (hRootYH hp).mp hHA
        have hpFloor := hD.mountain.heights.unique _ hp D.floor hHR hRootY
        subst hpFloor
        exact ⟨D.coordinates.root,hRootCand hRS hRel,Or.inl ⟨rfl,rfl⟩⟩
      · have hAR : Ancestor M C Y.width G a D.coordinates.root := by
          have hSeamRoot := hCopy.canon_root_seam_low_d hM hC hT hD hY hRun hFrom hLow hF hG hMapW hwY
          rcases hAW with he | hAW'
          · subst he
            have hEncW := (parent_copy_bad_iff hRootNot).mp hMapW
            obtain ⟨_,_,off,hOff,_,hAdd⟩ := hEncW
            have hle := sum_base_subset_d hM (hw.mem hD.coordinates.root)
              ((hT.add.add_iff_sum hM hD.coordinates.root hOff).mp hAdd)
            exact False.elim (nat_irrefl hM a (hle a har))
          · rcases hSeamRoot with he | hRW
            · exact he ▸ hAW'
            · exact ancestor_between_d hM hC hGF hAW' hRW har
        have hARX := (hPrefixAnc D.coordinates.root hRootS a).mpr hAR
        have hAS := ancestor_trans_d hM hC hFF hARX hRS
        have hHQ := (hOrigHeight a hp hAS.1).mp hHA
        exact ⟨a,⟨hs,hsNat,hp,hpNat,r,hrNat,hHS,hHQ,hSuccR,F,hFm,hF,hAS,hRel⟩,
          Or.inr ⟨fun he => hRootNot (he ▸ har),(parent_copy_good_iff hMap.2.1 haNat har).mpr rfl⟩⟩
      · exact False.elim (hSeam w hMapW hwY hAW hra)
  · rintro ⟨q,⟨hs',_,hq,hqhNat,r',_,hHS',hHQ,hSucc',F',_,hF',hAnc,hRel⟩,hLk⟩
    have he1 := hD.mountain.heights.unique s hs' hs hHS' hHS
    subst hs'
    have he2 := Structure.SuccessorOf.predecessor_eq hM.1 (hw.mem (nat_mem_omega hM hC hsNat hSucc'.predecessor_mem)) hSucc' hSuccR
    subst r'
    have he3 := hD.mountain.parents.unique r F' F hF' hF
    subst F'
    rcases hLk with ⟨hqR,haR⟩ | ⟨hqR,hMapQ⟩
    · subst hqR
      subst haR
      have hAncY : Ancestor M C Y.width G D.coordinates.root c := by
        rcases hCopy.canon_root_ancestor_low_copy_d hM hC hT hD hY hRun hFrom hLow hF hG (Or.inr hsLast) (Or.inr hAnc) hMap hc with
          he | h
        · have hrc := hSC _ hRootS
          rw [← he] at hrc
          exact False.elim (hRootNot hrc)
        · exact h
      exact ⟨hs,hsNat,hq,hqhNat,r,hrNat,hHC,(hRootYH hq).mpr hHQ,hSuccR,G,hGm,hG,hAncY,hRel⟩
    · have hqNat := hw.transitive D.mountain.width hD.mountain.width q (hAnc.bounds hM.1).1
      have hAncY := hCopy.low_ancestor_parent_copy_d hM hC hT hD hY hRun hFrom hLow hF hG hAnc (Or.inr hsLast) hMapQ hMap hc
      have haY := (hAncY.bounds hM.1).1
      have hHA : MemPair M Y.heights a hq := by
        rcases (omega_isOrdinal_d hM hC.omega).wellOrder.linear.compare q hqNat D.coordinates.root hD.coordinates.root with
          he | hqr | hrq
        · exact False.elim (hqR (hM.1.eq_of_same_members q _ he))
        · have haq := (parent_copy_good_iff hMapQ.2.1 hqNat hqr).mp hMapQ
          subst haq
          exact (hOrigHeight a hq hAnc.1).mpr hHQ
        · have hqLast : M.mem q D.coordinates.last := nat_lt_trans hM hC hD.coordinates.last hAnc.1 hsLast
          have hOutQ : ¬InCone M C D q := by
            intro hConeQ
            have hFloorQ := hConeQ.height_strict_d hM hC hD hrq hHQ
            rcases hRel with he | he
            · subst he
              exact nat_not_lt_of_le hM hC hFloorNat hLowH hFloorQ
            · subst he
              exact nat_not_lt_of_le hM hC hFloorNat (Or.inr hLow) hFloorQ
          exact (hCopy.parent_copy_heights_d hM hC hT hD hqLast (hCopy.width ▸ haY) hMapQ hHQ).mpr (Or.inr ⟨hOutQ,rfl⟩)
      exact ⟨hs,hsNat,hq,hqhNat,r,hrNat,hHC,hHA,hSuccR,G,hGm,hG,hAncY,hRel⟩


/-- 目标伪父的统一收缩关系：仅当源高度恰为floor且源伪父为root时收缩到root。 -/
def PseudoCopy (M : SetTheory.Structure.{u}) (C : ExpressionData M.Domain) (T : MatrixArithmetic M.Domain)
    (D : Context M.Domain) (s b q a : M.Domain) : Prop :=
  (q=D.coordinates.root ∧ MemPair M D.mountain.heights s D.floor ∧ a=D.coordinates.root) ∨
    (¬(q=D.coordinates.root ∧ MemPair M D.mountain.heights s D.floor) ∧ ParentCopy M C T D.coordinates b q a)

private theorem parent_copy_ge {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {A : CopyCoordinates.Context M.Domain} {b q a : M.Domain} (hMap : ParentCopy M C T A b q a) : q=a ∨ M.mem q a := by
  have hw := omega_isOrdinal_d hM hC.omega
  rcases hMap.2.2 with ⟨_,he⟩ | ⟨_,_,_,off,hOff,_,hAdd⟩
  · exact Or.inl he.symm
  · exact ordinal_subset_cases_d hM (hw.mem hMap.1) (hw.mem (hAdd.bounds hM.1 hT.add).2.2)
      (sum_base_subset_d hM (hw.mem hMap.1) ((hT.add.add_iff_sum hM hMap.1 hOff).mp hAdd))

theorem canon_pseudo_copy_fun {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {D : Context M.Domain} (hD : D.Valid M C) {s b q a a' : M.Domain}
    (h : PseudoCopy M C T D s b q a) (h' : PseudoCopy M C T D s b q a') : a=a' := by
  rcases h with ⟨_,_,ha⟩ | ⟨hN,hMap⟩ <;> rcases h' with ⟨hq',hs',ha'⟩ | ⟨hN',hMap'⟩
  · exact ha.trans ha'.symm
  · exact False.elim (hN' ⟨by assumption,by assumption⟩)
  · exact False.elim (hN ⟨hq',hs'⟩)
  · exact canon_parent_copy_fun hM hC hT hD.coordinates hMap hMap'

theorem canon_parent_copy_target_nat {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {A : CopyCoordinates.Context M.Domain} {b q a : M.Domain} (hMap : ParentCopy M C T A b q a) : M.mem a C.omega := by
  rcases hMap.2.2 with ⟨_,he⟩ | ⟨_,_,_,off,_,_,hAdd⟩
  · exact he ▸ hMap.1
  · exact (hAdd.bounds hM.1 hT.add).2.2

theorem canon_pseudo_copy_mono {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {D : Context M.Domain} (hD : D.Valid M C) {s b q q' a a' : M.Domain}
    (h : PseudoCopy M C T D s b q a) (h' : PseudoCopy M C T D s b q' a') (hqq : M.mem q q') : M.mem a a' := by
  rcases h with ⟨hq,_,ha⟩ | ⟨_,hMap⟩ <;> rcases h' with ⟨hq',_,ha'⟩ | ⟨_,hMap'⟩
  · rw [hq,hq'] at hqq
    exact False.elim (nat_irrefl hM _ hqq)
  · rw [hq] at hqq
    rw [ha]
    exact nat_lt_of_lt_of_le hM hC (canon_parent_copy_target_nat hM hT hMap') hqq (parent_copy_ge hM hC hT hMap')
  · rw [hq'] at hqq
    rw [ha']
    rcases hMap.2.2 with ⟨_,he⟩ | ⟨hNot,_⟩
    · exact he ▸ hqq
    · exact False.elim (hNot hqq)
  · exact canon_parent_copy_mono hM hC hT hD.coordinates hMap hMap' hqq

end KP1Y.OneYFinite.CopiedMountain.Lower
