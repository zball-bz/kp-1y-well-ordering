import KP1Y.OneYLowerCopy
import KP1Y.OneYCopyPathTransport
import KP1Y.OneYTerminalCopyRoots

/-! Lower复制的真实父/根运输。所有行、块、路径均为对象内部有限编码。 -/
namespace KP1Y.OneYFinite.CopiedMountain.Lower
open YesMetaZFC YesMetaZFC.SetTheory YesMetaZFC.SetTheory.Definitional
open KP1Y.Kuratowski KP1Y.Functions KP1Y.Naturals KP1Y.Bounded
open KP1Y.Arithmetic
open CopyCoordinates
universe u

private theorem nat_not_reverse_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {a b : M.Domain} (hb : M.mem b C.omega)
    (hab : a=b ∨ M.mem a b) : ¬M.mem b a := by
  intro hba
  rcases hab with he | hab
  · exact SetTheory.KP.mem_irrefl_d (KP1Y.models_weakKP hM) b (he ▸ hba)
  · exact SetTheory.KP.mem_irrefl_d (KP1Y.models_weakKP hM) b
      (((omega_isOrdinal_d hM hC.omega).mem hb).transitive a hab b hba)

theorem encoded_original_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {D : Context M.Domain} (hD : D.Valid M C) {s b c : M.Domain}
    (hs : Source M D.coordinates s) (hEncode : Encode M C T D.coordinates s b c)
    (hc : c=D.coordinates.last ∨ M.mem c D.coordinates.last) : s=c ∧ b=C.zero := by
  obtain ⟨_,_,off,hOff,_,hAdd⟩ := show Encode M C T D.coordinates s b c from hEncode
  have hSourceSub := sum_base_subset_d hM ((omega_isOrdinal_d hM hC.omega).mem hEncode.1)
    ((hT.add.add_iff_sum hM hEncode.1 hOff).mp hAdd)
  have hAfter := hSourceSub D.coordinates.root hs.1
  exact raw_decode_unique_d hM hC hT hD.coordinates
    (encoded_decodes_d hM hC hT hs hEncode) (raw_original_coordinates_d hM hC hT hD.coordinates ⟨hAfter,hc⟩)

theorem moved_parent_zero_iff_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {D : Context M.Domain} (hD : D.Valid M C) {r s q : M.Domain}
    (hr : M.mem r C.omega) (hHigh : D.floor=r ∨ M.mem D.floor r) :
    MovedParent M C T D r s C.zero q ↔ ParentAt M D.mountain r s q := by
  have hNot := nat_not_reverse_d hM hC hr hHigh
  have hFloorAdd : AddAt M T.addPairs T.plus D.floor C.zero D.floor :=
    (hT.add.add_iff_sum hM (hD.floor_nat hM.1) hC.zero_nat).mpr (sum_zero_d hM D.floor hC.zero_empty)
  constructor
  · rintro ⟨off,_,hTimes,u,_,hShift,p,hp,hP,hEncode⟩
    have hOff := natural_product_zero_left_d hM hC (hD.rise_nat hM.1)
      ((hT.mul.mul_iff_product hM hC.zero_nat (hD.rise_nat hM.1)).mp hTimes)
    subst off
    have hSum := hShift.high_sum_d hM hC hT hFloorAdd hNot
    have hu := hT.add.add_unique hM.1 hSum
      ((hT.add.add_iff_sum hM hShift.2.1 hC.zero_nat).mpr (sum_zero_d hM u hC.zero_empty))
    subst u
    have hq := encode_unique hM.1 hT hEncode (encode_zero_d hM hC hT hD.coordinates hp)
    exact hq ▸ hP
  · intro hP
    have hp := (omega_isOrdinal_d hM hC.omega).transitive D.mountain.width hD.mountain.width q (hP.bounds hM.1 hD.mountain).2.2.1
    obtain ⟨off,_,hTimes⟩ := hT.mul.mul_exists_d hM hC hC.zero_nat (hD.rise_nat hM.1)
    have hOff := natural_product_zero_left_d hM hC (hD.rise_nat hM.1)
      ((hT.mul.mul_iff_product hM hC.zero_nat (hD.rise_nat hM.1)).mp hTimes)
    subst off
    have hDiff : DifferenceRead M T r C.zero r := (difference_read_iff_d hM hT hr hC.zero_nat).mpr
      (truncated_difference_of_sum_d hM hC hC.zero_nat hr (natural_sum_comm_d hM hC hr hC.zero_nat (sum_zero_d hM r hC.zero_empty)))
    exact ⟨C.zero,hC.zero_nat,hTimes,r,hr,⟨hr,hr,D.floor,hD.floor_nat hM.1,hFloorAdd,Or.inr ⟨hNot,hDiff⟩⟩,
      q,hp,hP,encode_zero_d hM hC hT hD.coordinates hp⟩

theorem parent_encoded_iff_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {D : Context M.Domain} (hD : D.Valid M C) {r s b c q : M.Domain}
    (hr : M.mem r C.omega) (hs : Source M D.coordinates s) (hEncode : Encode M C T D.coordinates s b c) :
    Parent M C T D r c q ↔
      (((InCone M C D s ∧ (D.floor=r ∨ M.mem D.floor r)) ∧ MovedParent M C T D r s b q) ∨
        (¬(InCone M C D s ∧ (D.floor=r ∨ M.mem D.floor r)) ∧ ∃ p, M.mem p C.omega ∧
          ParentAt M D.mountain r s p ∧ ParentCopy M C T D.coordinates b p q)) := by
  classical
  have hcNat : M.mem c C.omega := by obtain ⟨_,_,_,_,_,hA⟩ := hEncode; exact (hA.bounds hM.1 hT.add).2.2
  by_cases hNew : M.mem D.coordinates.last c
  · constructor
    · intro h
      rcases h.2.2 with ⟨hOld,_⟩ | ⟨_,s',_,b',_,hRaw,hCase⟩
      · exact False.elim (nat_not_reverse_d hM hC hD.coordinates.last hOld hNew)
      · obtain ⟨heS,heB⟩ := raw_decode_unique_d hM hC hT hD.coordinates hRaw (encoded_decodes_d hM hC hT hs hEncode)
        subst s'
        subst b'
        exact hCase
    · intro h
      exact ⟨hr,hcNat,Or.inr ⟨hNew,s,hEncode.1,b,hEncode.2.1,encoded_decodes_d hM hC hT hs hEncode,h⟩⟩
  · have hOld : c=D.coordinates.last ∨ M.mem c D.coordinates.last := by
      rcases (omega_isOrdinal_d hM hC.omega).wellOrder.linear.compare c hcNat D.coordinates.last hD.coordinates.last with he | hlt | hgt
      · exact Or.inl (hM.1.eq_of_same_members c D.coordinates.last he)
      · exact Or.inr hlt
      · exact False.elim (hNew hgt)
    obtain ⟨hSC,hBZ⟩ := encoded_original_d hM hC hT hD hs hEncode hOld
    subst s
    subst b
    rw [parent_original_iff_d hM hC hD hOld]
    have hPlain : (∃ p, M.mem p C.omega ∧ ParentAt M D.mountain r c p ∧ ParentCopy M C T D.coordinates C.zero p q) ↔
        ParentAt M D.mountain r c q := by
      obtain ⟨J,hJ,hRows⟩ := parent_copy_graph_exists_d hM hC hT hD.coordinates hC.zero_nat
      constructor
      · rintro ⟨p,hp,hP,hCopy⟩
        have he := hJ.graph.unique p q p ((hRows p q).mpr hCopy) ((hRows p p).mpr (parent_copy_zero_d hM hC hT hD.coordinates hp))
        exact he ▸ hP
      · intro hP
        have hp := (omega_isOrdinal_d hM hC.omega).transitive D.mountain.width hD.mountain.width q (hP.bounds hM.1 hD.mountain).2.2.1
        exact ⟨q,hp,hP,parent_copy_zero_d hM hC hT hD.coordinates hp⟩
    by_cases hMove : InCone M C D c ∧ (D.floor=r ∨ M.mem D.floor r)
    · rw [moved_parent_zero_iff_d hM hC hT hD hr hMove.2,hPlain]
      exact ⟨fun h => Or.inl ⟨hMove,h⟩,fun h => h.elim And.right (fun h => False.elim (h.1 hMove))⟩
    · rw [hPlain]
      exact ⟨fun h => Or.inr ⟨hMove,h⟩,fun h => h.elim (fun h => False.elim (hMove h.1)) And.right⟩

theorem Copies.encoded_parent_iff_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {D : Context M.Domain} (hD : D.Valid M C) {n r s b c q : M.Domain} {Y : Data M.Domain}
    (hCopy : Copies M C T D n Y) (hr : M.mem r C.omega) (hs : Source M D.coordinates s)
    (hEncode : Encode M C T D.coordinates s b c) (hc : M.mem c n) :
    ParentAt M Y r c q ↔
      (((InCone M C D s ∧ (D.floor=r ∨ M.mem D.floor r)) ∧ MovedParent M C T D r s b q) ∨
        (¬(InCone M C D s ∧ (D.floor=r ∨ M.mem D.floor r)) ∧ ∃ p, M.mem p C.omega ∧
          ParentAt M D.mountain r s p ∧ ParentCopy M C T D.coordinates b p q)) := by
  rw [hCopy.parents,parent_encoded_iff_d hM hC hT hD hr hs hEncode]
  exact ⟨And.right,fun h => ⟨hc,h⟩⟩

theorem source_ancestor_root_iff_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {D : Context M.Domain} (_hD : D.Valid M C)
    {m : M.Domain} {R : RowStateSpace M.Domain} {V P H : M.Domain}
    (hRun : RowRun M C m R V P H) (hFrom : FromRun M C m R V H D.mountain)
    {r u F a c q : M.Domain} (hLe : r=u ∨ M.mem r u) (hRow : MemPair M D.mountain.parents u F)
    (hAnc : Ancestor M C D.mountain.width F a c) :
    RootAt M C D.mountain r c q ↔ RootAt M C D.mountain r a q := by
  obtain ⟨U,hU⟩ := (hFrom.parents u F).mp hRow
  have hAt (G : M.Domain) (hG : MemPair M D.mountain.parents r G) :
      Root M C D.mountain.width G c q ↔ Root M C D.mountain.width G a q := by
    obtain ⟨W,hW⟩ := (hFrom.parents r G).mp hG
    have hLow := hRun.ancestor_lower_d hM hC hW hU hLe (hFrom.width ▸ hAnc)
    have hRoots := root_ancestor_iff_d hM hC (hRun.at_numeric_d hM hC hW).forest hLow (q := q)
    exact hFrom.width.symm ▸ hRoots
  constructor
  · rintro ⟨G,hG,hRowG,hRoot⟩
    exact ⟨G,hG,hRowG,(hAt G hRowG).mp hRoot⟩
  · rintro ⟨G,hG,hRowG,hRoot⟩
    exact ⟨G,hG,hRowG,(hAt G hRowG).mpr hRoot⟩

theorem in_cone_ancestor_iff_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {D : Context M.Domain} (hD : D.Valid M C)
    {m : M.Domain} {R : RowStateSpace M.Domain} {V P H : M.Domain}
    (hRun : RowRun M C m R V P H) (hFrom : FromRun M C m R V H D.mountain)
    {u F a c : M.Domain} (hHigh : D.floor=u ∨ M.mem D.floor u) (hRow : MemPair M D.mountain.parents u F)
    (hAnc : Ancestor M C D.mountain.width F a c) : InCone M C D a ↔ InCone M C D c := by
  have hF := hD.mountain.forest u F hRow
  have hMemF := (hD.mountain.parents.bounds hM.1 hRow).2
  obtain ⟨z,_,_,hZA⟩ := ancestor_child_above_d hM hC hF hAnc
  obtain ⟨p,hCP,_⟩ := ancestor_parent_cases_d hM hC hF hAnc
  obtain ⟨ha,hha,hHA⟩ := hD.mountain.heights.total a (hAnc.bounds hM.1).1
  obtain ⟨hc,hhc,hHC⟩ := hD.mountain.heights.total c (hAnc.bounds hM.1).2
  have hUA : u=ha ∨ M.mem u ha := hD.mountain.endpoint u z a ha ⟨F,hMemF,hRow,hZA⟩ hHA
  have hUC := (hD.mountain.source u c hc hHC).mp ⟨p,F,hMemF,hRow,hCP⟩
  have hFloorA : D.floor=ha ∨ M.mem D.floor ha := by
    rcases hHigh with he | hlt
    · exact he.symm ▸ hUA
    · rcases hUA with he | hgt
      · exact Or.inr (he ▸ hlt)
      · exact Or.inr (((omega_isOrdinal_d hM hC.omega).mem hha).transitive u hgt D.floor hlt)
  have hFloorC : D.floor=hc ∨ M.mem D.floor hc := by
    rcases hHigh with he | hlt
    · exact Or.inr (he.symm ▸ hUC)
    · exact Or.inr (((omega_isOrdinal_d hM hC.omega).mem hhc).transitive u hUC D.floor hlt)
  have hRoots := source_ancestor_root_iff_d hM hC hD hRun hFrom hHigh hRow hAnc (q := D.coordinates.root)
  constructor
  · rintro ⟨_,_,_,_,hRoot⟩
    exact ⟨hc,hhc,hHC,hFloorC,hRoots.mpr hRoot⟩
  · rintro ⟨_,_,_,_,hRoot⟩
    exact ⟨ha,hha,hHA,hFloorA,hRoots.mp hRoot⟩

theorem InCone.high_root_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {D : Context M.Domain} (hD : D.Valid M C)
    {m : M.Domain} {R : RowStateSpace M.Domain} {V P H : M.Domain}
    (hRun : RowRun M C m R V P H) (hFrom : FromRun M C m R V H D.mountain)
    {u c q : M.Domain} (hCone : InCone M C D c) (hHigh : D.floor=u ∨ M.mem D.floor u)
    (hRoot : RootAt M C D.mountain u c q) : InCone M C D q := by
  obtain ⟨F,_,hRow,hRoot⟩ := hRoot
  rcases hRoot.2.2 with he | hAnc
  · exact he.symm ▸ hCone
  · exact (in_cone_ancestor_iff_d hM hC hD hRun hFrom hHigh hRow hAnc).mpr hCone

theorem root_no_parent_height_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} {X : Data M.Domain} (hX : X.Valid M C)
    {r c q height : M.Domain} (hRoot : RootAt M C X r c q) (hH : MemPair M X.heights q height) : ¬M.mem r height := by
  intro hr
  obtain ⟨p,F,_,hF,hP⟩ := (hX.source r q height hH).mpr hr
  obtain ⟨G,_,hG,hRootG⟩ := hRoot
  have he := hX.parents.unique r F G hF hG
  subst F
  exact hRootG.2.1 p ((hX.forest r G hG).bounds hM.1 hP).2 hP

theorem source_root_low_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {D : Context M.Domain} (hD : D.Valid M C)
    {m : M.Domain} {R : RowStateSpace M.Domain} {V P H : M.Domain}
    (hRun : RowRun M C m R V P H) (hFrom : FromRun M C m R V H D.mountain)
    {r s q : M.Domain} (hLow : M.mem r D.floor) (hCone : InCone M C D s)
    (hRoot : RootAt M C D.mountain r s q) : M.mem q D.coordinates.root := by
  obtain ⟨_,_,_,_,F,_,hF,hRootF⟩ := hCone
  obtain ⟨G,hG,hRowG,hRootG⟩ := hRoot
  obtain ⟨U,hAtF⟩ := (hFrom.parents D.floor F).mp hF
  obtain ⟨W,hAtG⟩ := (hFrom.parents r G).mp hRowG
  have hThrough := (hRun.root_through_higher_d hM hC hAtG hAtF (Or.inr hLow)
    (hFrom.width ▸ hRootF)).mp (hFrom.width ▸ hRootG)
  have hRootRoot : RootAt M C D.mountain r D.coordinates.root q := ⟨G,hG,hRowG,hFrom.width.symm ▸ hThrough⟩
  obtain ⟨p,hParent⟩ := (hD.mountain.source r D.coordinates.root D.floor hD.floor).mpr hLow
  exact Terminal.root_at_lt_of_parent_d hM hC hD.mountain hParent hRootRoot

theorem Copies.high_ancestor_copy_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {D : Context M.Domain} (hD : D.Valid M C) {m : M.Domain} {R : RowStateSpace M.Domain} {V P H : M.Domain}
    (hRun : RowRun M C m R V P H) (hFrom : FromRun M C m R V H D.mountain)
    {Y : Data M.Domain} (hY : Y.Valid M C) {n r u off b s c a x F G : M.Domain}
    (hCopy : Copies M C T D n Y) (hs : Source M D.coordinates s) (hCone : InCone M C D s)
    (hHigh : D.floor=r ∨ M.mem D.floor r) (hTimes : MulAt M T.mulPairs T.times b D.rise off)
    (hShift : ShiftedRow M C T D.floor off r u) (hEncode : Encode M C T D.coordinates s b c) (hc : M.mem c n)
    (hF : MemPair M D.mountain.parents u F) (hG : MemPair M Y.parents r G)
    (hAnc : Ancestor M C D.mountain.width F a s) (hMapA : ParentCopy M C T D.coordinates b a x) :
    Ancestor M C Y.width G x c := by
  have hw := omega_isOrdinal_d hM hC.omega
  have hUHigh := hShift.floor_le_d hM hC hT
  have hMapS : ParentCopy M C T D.coordinates b s c :=
    (parent_copy_bad_iff (nat_not_reverse_d hM hC hEncode.1 (Or.inr hs.1))).mpr hEncode
  obtain ⟨J,hJ,hRows⟩ := parent_copy_graph_exists_d hM hC hT hD.coordinates hEncode.2.1
  apply ancestor_map_global_bounded_d hM hC (hD.mountain.forest u F hF) hY.width hJ hAnc
    ((hRows a x).mpr hMapA) ((hRows s c).mpr hMapS) (hCopy.width.symm ▸ hc)
  intro d p v w hReach hDP hDV hPW
  have hConeD : InCone M C D d := by
    rcases hReach with he | hAncestor
    · exact he.symm ▸ hCone
    · exact (in_cone_ancestor_iff_d hM hC hD hRun hFrom hUHigh hF hAncestor).mpr hCone
  have hOldP : ParentAt M D.mountain u d p := ⟨F,(hD.mountain.parents.bounds hM.1 hF).2,hF,hDP⟩
  have hConeP := hConeD.high_parent_d hM hC hD hUHigh hOldP
  have hdRoot : M.mem D.coordinates.root d := by
    rcases hConeD.root_le hM.1 hD with he | hlt
    · have hAtRoot : ParentAt M D.mountain u D.coordinates.root p := he.symm ▸ hOldP
      exact False.elim ((nat_not_reverse_d hM hC hShift.2.1 hUHigh)
        ((hD.mountain.source u D.coordinates.root D.floor hD.floor).mp ⟨p,hAtRoot⟩))
    · exact hlt
  have hdLast : d=D.coordinates.last ∨ M.mem d D.coordinates.last := by
    rcases hReach with he | hAncestor
    · exact he ▸ hs.2
    · rcases hs.2 with he | hlt
      · exact Or.inr (he ▸ hAncestor.1)
      · exact Or.inr ((hw.mem hD.coordinates.last).transitive s hlt d hAncestor.1)
  have hMapD := (hRows d v).mp hDV
  have hMapP := (hRows p w).mp hPW
  have hEncD := (parent_copy_bad_iff (hConeD.not_good_d hM hC hD)).mp hMapD
  have hEncP := (parent_copy_bad_iff (hConeP.not_good_d hM hC hD)).mp hMapP
  have hv : M.mem v n := by
    rcases hReach with he | hAncestor
    · subst d
      exact (hJ.graph.unique s v c hDV ((hRows s c).mpr hMapS)).symm ▸ hc
    · exact ((hw.mem (hCopy.width ▸ hY.width)).transitive c hc v
        (hJ.strict d hMapD.1 s hEncode.1 hAncestor.1 v c hDV ((hRows s c).mpr hMapS)))
  have hTarget : ParentAt M Y r v w := (hCopy.encoded_parent_iff_d hM hC hT hD hShift.1 ⟨hdRoot,hdLast⟩ hEncD hv).mpr
    (Or.inl ⟨⟨hConeD,hHigh⟩,off,(by obtain ⟨key,_,_,hAt⟩ := hTimes; exact (hT.mul.graph.bounds hM.1 hAt).2),hTimes,u,hShift.2.1,hShift,p,hMapP.1,hOldP,hEncP⟩)
  obtain ⟨G',_,hG',hAt⟩ := hTarget
  have he := hY.parents.unique r G' G hG' hG
  exact he ▸ hAt

theorem Copies.high_root_copy_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {D : Context M.Domain} (hD : D.Valid M C) {m : M.Domain} {R : RowStateSpace M.Domain} {V P H : M.Domain}
    (hRun : RowRun M C m R V P H) (hFrom : FromRun M C m R V H D.mountain)
    {Y : Data M.Domain} (hY : Y.Valid M C) {n r u off level b s c q z : M.Domain}
    (hCopy : Copies M C T D n Y) (hs : Source M D.coordinates s) (hCone : InCone M C D s)
    (hHigh : D.floor=r ∨ M.mem D.floor r) (hTimes : MulAt M T.mulPairs T.times b D.rise off)
    (hShift : ShiftedRow M C T D.floor off r u) (hLevel : AddAt M T.addPairs T.plus D.floor off level)
    (hNotGap : ¬M.mem r level) (hEncode : Encode M C T D.coordinates s b c) (hc : M.mem c n)
    (hRoot : RootAt M C D.mountain u s q) (hqLast : M.mem q D.coordinates.last)
    (hMapQ : ParentCopy M C T D.coordinates b q z) : RootAt M C Y r c z := by
  have hConeQ := hCone.high_root_d hM hC hD hRun hFrom (hShift.floor_le_d hM hC hT) hRoot
  obtain ⟨F,_,hF,hRootF⟩ := hRoot
  obtain ⟨G,hG,hRowG⟩ := hY.parents.total r hShift.1
  have hReach : z=c ∨ Ancestor M C Y.width G z c := by
    rcases hRootF.2.2 with he | hAnc
    · subst q
      have hEncQ := (parent_copy_bad_iff (hConeQ.not_good_d hM hC hD)).mp hMapQ
      exact Or.inl (encode_unique hM.1 hT hEncQ hEncode)
    · exact Or.inr (hCopy.high_ancestor_copy_d hM hC hT hD hRun hFrom hY hs hCone hHigh hTimes hShift hEncode hc hF hRowG hAnc hMapQ)
  have hz : M.mem z Y.width := by
    rcases hReach with he | hAnc
    · exact he.symm ▸ (hCopy.width.symm ▸ hc)
    · exact (hAnc.bounds hM.1).1
  obtain ⟨height,hHeight,hAtHeight⟩ := hD.mountain.heights.total q hRootF.1
  obtain ⟨lifted,_,hLifted⟩ := hT.add.add_exists_d hM hC hHeight (by obtain ⟨key,_,_,hAt⟩ := hTimes; exact (hT.mul.graph.bounds hM.1 hAt).2)
  have hNewHeight : MemPair M Y.heights z lifted := (hCopy.parent_copy_heights_d hM hC hT hD hqLast (hCopy.width ▸ hz) hMapQ hAtHeight).mpr
    (Or.inl ⟨hConeQ,hHeight,hMapQ.2.1,off,(by obtain ⟨key,_,_,hAt⟩ := hTimes; exact (hT.mul.graph.bounds hM.1 hAt).2),hTimes,hLifted⟩)
  refine ⟨G,hG,hRowG,hz,?_,hReach⟩
  intro p _ hP
  have hrHeight := (hY.source r z lifted hNewHeight).mp ⟨p,G,hG,hRowG,hP⟩
  have huHeight := (add_same_right_lt_iff_d hM hC hT (hShift.high_sum_d hM hC hT hLevel hNotGap) hLifted).mp hrHeight
  exact root_no_parent_height_d hM hD.mountain ⟨F,(hD.mountain.parents.bounds hM.1 hF).2,hF,hRootF⟩ hAtHeight huHeight

/-- 插入参考行的根严格位于当前复制root之前；直接由cut的实际活跃高度推出。 -/
theorem Copies.gap_root_lt_cut_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {D : Context M.Domain} (hD : D.Valid M C) {m : M.Domain} {R : RowStateSpace M.Domain} {V P H : M.Domain}
    (hRun : RowRun M C m R V P H) (hFrom : FromRun M C m R V H D.mountain)
    {Y : Data M.Domain} (hY : Y.Valid M C) {n r off level b s c cut q : M.Domain}
    (hCopy : Copies M C T D n Y) (hs : Source M D.coordinates s) (hCone : InCone M C D s)
    (hr : M.mem r C.omega) (hHigh : D.floor=r ∨ M.mem D.floor r)
    (hTimes : MulAt M T.mulPairs T.times b D.rise off) (hLevel : AddAt M T.addPairs T.plus D.floor off level)
    (hGap : M.mem r level) (hEncode : Encode M C T D.coordinates s b c) (hc : M.mem c n)
    (hCut : Encode M C T D.coordinates D.coordinates.root b cut) (hRoot : RootAt M C Y r c q) : M.mem q cut := by
  have hConeRoot := hCone
  obtain ⟨_,_,_,_,F,_,hF,hRootF⟩ := hConeRoot
  have hAnc : Ancestor M C D.mountain.width F D.coordinates.root s := by
    rcases hRootF.2.2 with he | hAnc
    · exact False.elim (SetTheory.KP.mem_irrefl_d (KP1Y.models_weakKP hM) s (he ▸ hs.1))
    · exact hAnc
  obtain ⟨G,hG,hRowG,hRootG⟩ := hRoot
  have hMapRoot : ParentCopy M C T D.coordinates b D.coordinates.root cut :=
    (parent_copy_bad_iff (SetTheory.KP.mem_irrefl_d (KP1Y.models_weakKP hM) D.coordinates.root)).mpr hCut
  have hShift : ShiftedRow M C T D.floor off r D.floor :=
    ⟨hr,hD.floor_nat hM.1,level,(hLevel.bounds hM.1 hT.add).2.2,hLevel,Or.inl ⟨hGap,rfl⟩⟩
  have hAncNew := hCopy.high_ancestor_copy_d hM hC hT hD hRun hFrom hY hs hCone hHigh hTimes hShift hEncode hc hF hRowG hAnc hMapRoot
  have hRootCut : RootAt M C Y r cut q := ⟨G,hG,hRowG,(root_ancestor_iff_d hM hC (hY.forest r G hRowG) hAncNew).mp hRootG⟩
  have hNewHeight : MemPair M Y.heights cut level := (hCopy.parent_copy_heights_d hM hC hT hD hD.coordinates.below
    (hCopy.width ▸ (hAncNew.bounds hM.1).1) hMapRoot hD.floor).mpr
      (Or.inl ⟨in_cone_root_d hM hD,hD.floor_nat hM.1,hCut.2.1,off,(by obtain ⟨key,_,_,hAt⟩ := hTimes; exact (hT.mul.graph.bounds hM.1 hAt).2),hTimes,hLevel⟩)
  obtain ⟨p,hParent⟩ := (hY.source r cut level hNewHeight).mpr hGap
  exact Terminal.root_at_lt_of_parent_d hM hC hY hParent hRootCut

private def lowRootCopyCore {d : Nat} (C : ExpressionData (Project.Term d)) (T : MatrixArithmetic (Project.Term d))
    (A : CopyCoordinates.Context (Project.Term d)) (X Y : Data (Project.Term d)) (r c : Project.Term d) : Project.Formula 1 d :=
  .imp (.mem c Y.width) (Project.Formula.forallMem A.last (Project.Formula.forallMem C.omega.weaken
    (Project.Formula.forallMem X.width.weaken.weaken (Project.Formula.forallMem Y.width.weaken.weaken.weaken
      (.imp (.conj (parentCopyFormula C.weaken.weaken.weaken.weaken T.weaken.weaken.weaken.weaken A.weaken.weaken.weaken.weaken
          (.bound 2) (.bound 3) c.weaken.weaken.weaken.weaken)
        (.conj (Lower.rootAtFormula C.weaken.weaken.weaken.weaken X.weaken.weaken.weaken.weaken r.weaken.weaken.weaken.weaken (.bound 3) (.bound 1))
          (parentCopyFormula C.weaken.weaken.weaken.weaken T.weaken.weaken.weaken.weaken A.weaken.weaken.weaken.weaken (.bound 2) (.bound 1) (.bound 0))))
        (Lower.rootAtFormula C.weaken.weaken.weaken.weaken Y.weaken.weaken.weaken.weaken r.weaken.weaken.weaken.weaken c.weaken.weaken.weaken.weaken (.bound 0)))))))

private theorem lowRootCopyCore_freeClosed {d : Nat} {C : ExpressionData (Project.Term d)} (hC : C.Closed)
    {T : MatrixArithmetic (Project.Term d)} (hT : ArithmeticClosed T) {A : CopyCoordinates.Context (Project.Term d)} (hA : A.Closed)
    {X Y : Data (Project.Term d)} (hX : X.Closed) (hY : Y.Closed) (r c : Project.Term d)
    (hr : r.freeSupport=[]) (hc : c.freeSupport=[]) : (lowRootCopyCore C T A X Y r c).FreeClosed := by
  have hPC := parentCopyFormula_freeClosed hC.weaken.weaken.weaken.weaken hT.weaken.weaken.weaken.weaken hA.weaken.weaken.weaken.weaken
    (.bound 2) (.bound 3) c.weaken.weaken.weaken.weaken rfl rfl (by simpa using hc)
  have hPQ := parentCopyFormula_freeClosed hC.weaken.weaken.weaken.weaken hT.weaken.weaken.weaken.weaken hA.weaken.weaken.weaken.weaken
    (.bound 2) (.bound 1) (.bound 0) rfl rfl rfl
  have hRX := Lower.rootAtFormula_freeClosed hC.weaken.weaken.weaken.weaken hX.weaken.weaken.weaken.weaken
    r.weaken.weaken.weaken.weaken (.bound 3) (.bound 1) (by simpa using hr) rfl rfl
  have hRY := Lower.rootAtFormula_freeClosed hC.weaken.weaken.weaken.weaken hY.weaken.weaken.weaken.weaken
    r.weaken.weaken.weaken.weaken c.weaken.weaken.weaken.weaken (.bound 0) (by simpa using hr) (by simpa using hc) rfl
  simp [lowRootCopyCore,Project.Formula.forallMem,Definitional.Formula.FreeClosed,hC.omega,hA.last,hX.width,hY.width,hc,hPC,hPQ,hRX,hRY]

private def lowRootCopySchema : Project.UnarySchema 24 where
  body := lowRootCopyCore ⟨.bound 24,.bound 23,.bound 22,.bound 21,.bound 20⟩
    ⟨.bound 19,.bound 18,.bound 17,.bound 16,.bound 15,.bound 14⟩ ⟨.bound 13,.bound 12,.bound 11,.bound 10⟩
    ⟨.bound 9,.bound 8,.bound 7,.bound 6⟩ ⟨.bound 5,.bound 4,.bound 3,.bound 2⟩ (.bound 1) (.bound 0)
  freeClosed := lowRootCopyCore_freeClosed ⟨rfl,rfl,rfl,rfl,rfl⟩ ⟨rfl,rfl,rfl,rfl,rfl,rfl⟩
    ⟨rfl,rfl,rfl,rfl⟩ ⟨rfl,rfl,rfl,rfl⟩ ⟨rfl,rfl,rfl,rfl⟩ _ _ rfl rfl

private def lowRootCopyEnv {M : SetTheory.Structure.{u}} (C : ExpressionData M.Domain) (T : MatrixArithmetic M.Domain)
    (A : CopyCoordinates.Context M.Domain) (X Y : Data M.Domain) (r : M.Domain) : Env M 24 :=
  (((((((((((((((((((((((oneEnv C.omega).push C.zero).push C.one).push C.sequences).push C.expressions).push T.addPairs).push T.plus).push T.mulPairs).push T.times).push T.diffPairs).push T.difference).push A.last).push A.root).push A.length).push A.first).push X.width).push X.heights).push X.forests).push X.parents).push Y.width).push Y.heights).push Y.forests).push Y.parents).push r

private theorem lowRootCopySchema_iff {M : SetTheory.Structure.{u}} (he : Extensional M)
    (C : ExpressionData M.Domain) (T : MatrixArithmetic M.Domain) (A : CopyCoordinates.Context M.Domain) (X Y : Data M.Domain) (r c : M.Domain) :
    Project.Formula.satisfies ((lowRootCopyEnv C T A X Y r).push c) lowRootCopySchema.body ↔
      (M.mem c Y.width → ∀ s, M.mem s A.last → ∀ b, M.mem b C.omega → ∀ q, M.mem q X.width → ∀ z, M.mem z Y.width →
        ParentCopy M C T A b s c ∧ RootAt M C X r s q ∧ ParentCopy M C T A b q z → RootAt M C Y r c z) := by
  simp only [lowRootCopySchema,lowRootCopyCore,Project.Formula.satisfies_forallMem_iff,Project.Formula.satisfies_imp_iff,
    Project.Formula.satisfies_mem_iff,Project.Formula.satisfies_conj_iff,parentCopyFormula_iff he,Lower.rootAtFormula_iff he,
    ExpressionData.eval_weaken,MatrixArithmetic.eval_weaken,Data.eval_weaken,Term.eval_weaken]
  rfl

theorem parent_copy_nonroot_unmoved_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {D : Context M.Domain} (hD : D.Valid M C) {r s b c q : M.Domain}
    (hr : M.mem r C.omega) (hs : M.mem s D.coordinates.last) (hne : s≠D.coordinates.root)
    (hNoMove : ¬(InCone M C D s ∧ (D.floor=r ∨ M.mem D.floor r)))
    (hMap : ParentCopy M C T D.coordinates b s c) :
    Parent M C T D r c q ↔ ∃ p, M.mem p C.omega ∧ ParentAt M D.mountain r s p ∧ ParentCopy M C T D.coordinates b p q := by
  classical
  by_cases hGood : M.mem s D.coordinates.root
  · have hcs := (parent_copy_good_iff hMap.2.1 hMap.1 hGood).mp hMap
    subst c
    rw [parent_original_iff_d hM hC hD (Or.inr hs)]
    constructor
    · intro hP
      have hps := (hP.bounds hM.1 hD.mountain).2.2.2
      have hpGood := ((omega_isOrdinal_d hM hC.omega).mem hD.coordinates.root).transitive s hGood q hps
      have hpNat := (omega_isOrdinal_d hM hC.omega).transitive D.coordinates.root hD.coordinates.root q hpGood
      exact ⟨q,hpNat,hP,(parent_copy_good_iff hMap.2.1 hpNat hpGood).mpr rfl⟩
    · rintro ⟨p,hp,hP,hCopy⟩
      have hpGood := ((omega_isOrdinal_d hM hC.omega).mem hD.coordinates.root).transitive s hGood p (hP.bounds hM.1 hD.mountain).2.2.2
      have hqp := (parent_copy_good_iff hMap.2.1 hp hpGood).mp hCopy
      exact hqp ▸ hP
  · have hRootS : M.mem D.coordinates.root s := by
      rcases (omega_isOrdinal_d hM hC.omega).wellOrder.linear.compare s hMap.1 D.coordinates.root hD.coordinates.root with he | hlt | hgt
      · exact False.elim (hne (hM.1.eq_of_same_members s D.coordinates.root he))
      · exact False.elim (hGood hlt)
      · exact hgt
    rw [parent_encoded_iff_d hM hC hT hD hr ⟨hRootS,Or.inr hs⟩ ((parent_copy_bad_iff hGood).mp hMap)]
    exact ⟨fun h => h.elim (fun h => False.elim (hNoMove h.1)) And.right,fun h => Or.inr ⟨hNoMove,h⟩⟩

theorem Copies.low_root_parent_copy_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {D : Context M.Domain} (hD : D.Valid M C) {Y : Data M.Domain} (hY : Y.Valid M C)
    {m : M.Domain} {R : RowStateSpace M.Domain} {V P H : M.Domain}
    (hRun : RowRun M C m R V P H) (hFrom : FromRun M C m R V H D.mountain)
    {n r b s c q z : M.Domain} (hCopy : Copies M C T D n Y)
    (hLow : M.mem r D.floor) (hSource : M.mem s D.coordinates.last) (hChild : M.mem c Y.width)
    (hMap : ParentCopy M C T D.coordinates b s c) (hRoot : RootAt M C D.mountain r s q)
    (hMapRoot : ParentCopy M C T D.coordinates b q z) : RootAt M C Y r c z := by
  have hw := omega_isOrdinal_d hM hC.omega
  have hr := hw.transitive D.floor (hD.floor_nat hM.1) r hLow
  have hNoHigh : ¬(D.floor=r ∨ M.mem D.floor r) := fun h => nat_not_reverse_d hM hC hr h hLow
  have hAll := KP1Y.ordinal_induction_d hM lowRootCopySchema (lowRootCopyEnv C T D.coordinates D.mountain Y r) (by
    intro child _ ih
    apply (lowRootCopySchema_iff hM.1 C T D.coordinates D.mountain Y r child).mpr
    intro hChild source hSource block hBlock oldRoot hOldRoot newRoot hNewRoot hAnte
    obtain ⟨hMap,hRoot,hMapRoot⟩ := hAnte
    have hChildN : M.mem child n := hCopy.width ▸ hChild
    have hSourceX := (hw.mem hD.mountain.width).transitive D.coordinates.last hD.last source hSource
    obtain ⟨J,hJ,hRows⟩ := parent_copy_graph_exists_d hM hC hT hD.coordinates hBlock
    have hStep (p block' target : M.Domain) (hpLast : M.mem p D.coordinates.last)
        (hParent : ParentAt M Y r child target) (hSourceRoot : RootAt M C D.mountain r p oldRoot)
        (hMapP : ParentCopy M C T D.coordinates block' p target) (hMapQ : ParentCopy M C T D.coordinates block' oldRoot newRoot) :
        RootAt M C Y r child newRoot := by
      have hBounds := hParent.bounds hM.1 hY
      apply (Terminal.root_at_parent_iff_d hM hC hY hParent).mpr
      exact (lowRootCopySchema_iff hM.1 C T D.coordinates D.mountain Y r target).mp (ih target hBounds.2.2.2)
        hBounds.2.2.1 p hpLast block' hMapP.2.1 oldRoot hOldRoot newRoot hNewRoot ⟨hMapP,hSourceRoot,hMapQ⟩
    classical
    by_cases hSome : ∃ p, ParentAt M D.mountain r source p
    · obtain ⟨p,hP⟩ := hSome
      have hpNat := hw.transitive D.mountain.width hD.mountain.width p (hP.bounds hM.1 hD.mountain).2.2.1
      have hpLast := (hw.mem hD.coordinates.last).transitive source hSource p (hP.bounds hM.1 hD.mountain).2.2.2
      by_cases hIsRoot : source=D.coordinates.root
      · subst source
        rcases natural_cases hM hC.omega hBlock with hEmpty | ⟨previous,hPrevious,hSucc⟩
        · have hZero := hM.1.eq_of_same_members block C.zero (fun a => ⟨fun h => False.elim (hEmpty a h),fun h => False.elim (hC.zero_empty a h)⟩)
          subst block
          have hChildEq := hJ.graph.unique D.coordinates.root child D.coordinates.root ((hRows D.coordinates.root child).mpr hMap)
            ((hRows D.coordinates.root D.coordinates.root).mpr (parent_copy_zero_d hM hC hT hD.coordinates hD.coordinates.root))
          have hPMap := parent_copy_zero_d hM hC hT hD.coordinates hpNat
          have hNewP : ParentAt M Y r child p := (hCopy.parents r child p).mpr
            ⟨hChildN,hChildEq.symm ▸ (parent_original_iff_d hM hC hD (Or.inr hD.coordinates.below)).mpr hP⟩
          exact hStep p C.zero p hpLast hNewP ((Terminal.root_at_parent_iff_d hM hC hD.mountain hP).mp hRoot) hPMap hMapRoot
        · obtain ⟨boundary,_,hWidth⟩ := encode_exists_d hM hC hT hD.coordinates hD.coordinates.last hPrevious
          have hBad : ¬M.mem D.coordinates.root D.coordinates.root := SetTheory.KP.mem_irrefl_d (KP1Y.models_weakKP hM) D.coordinates.root
          have hChildEq := encode_unique hM.1 hT ((parent_copy_bad_iff hBad).mp hMap)
            (width_is_next_cut_d hM hC hT hD.coordinates hSucc hWidth)
          have hWidthChild : Width M C T D.coordinates previous child := hChildEq.symm ▸ hWidth
          have hRootGood := Terminal.root_at_lt_of_parent_d hM hC hD.mountain hP hRoot
          have hNewEq := (parent_copy_good_iff hBlock hMapRoot.1 hRootGood).mp hMapRoot
          have hPrevMapRoot : ParentCopy M C T D.coordinates previous oldRoot newRoot :=
            (parent_copy_good_iff hPrevious hMapRoot.1 hRootGood).mpr hNewEq
          obtain ⟨F,_,hF,hFloorRoot⟩ := hD.last_root
          obtain ⟨G,hG,hRowG,hRootG⟩ := hRoot
          obtain ⟨UF,hRF⟩ := (hFrom.parents D.floor F).mp hF
          obtain ⟨UG,hRG⟩ := (hFrom.parents r G).mp hRowG
          have hLastRoot : RootAt M C D.mountain r D.coordinates.last oldRoot :=
            ⟨G,hG,hRowG,hFrom.width.symm ▸ ((hRun.root_through_higher_d hM hC hRG hRF (Or.inr hLow)
              (hFrom.width ▸ hFloorRoot)).mpr (hFrom.width ▸ hRootG))⟩
          obtain ⟨height,hh,hHeight,hFloorHeight,_⟩ := hD.rise
          have hRH := (hw.mem hh).transitive D.floor hFloorHeight r hLow
          obtain ⟨pOld,hOldP⟩ := (hD.mountain.source r D.coordinates.last height hHeight).mpr hRH
          have hpOld := hw.transitive D.mountain.width hD.mountain.width pOld (hOldP.bounds hM.1 hD.mountain).2.2.1
          obtain ⟨JPrev,hJPrev,hPrevRows⟩ := parent_copy_graph_exists_d hM hC hT hD.coordinates hPrevious
          obtain ⟨target,_,hAtTarget⟩ := hJPrev.graph.total pOld hpOld
          have hMapTarget := (hPrevRows pOld target).mp hAtTarget
          have hNewP : ParentAt M Y r child target := (hCopy.encoded_parent_iff_d hM hC hT hD hr
            ⟨hD.coordinates.below,Or.inl rfl⟩ hWidthChild hChildN).mpr
              (Or.inr ⟨fun h => hNoHigh h.2,pOld,hpOld,hOldP,hMapTarget⟩)
          exact hStep pOld previous target (hOldP.bounds hM.1 hD.mountain).2.2.2 hNewP
            ((Terminal.root_at_parent_iff_d hM hC hD.mountain hOldP).mp hLastRoot) hMapTarget hPrevMapRoot
      · obtain ⟨target,_,hAtTarget⟩ := hJ.graph.total p hpNat
        have hMapTarget := (hRows p target).mp hAtTarget
        have hNewP : ParentAt M Y r child target := (hCopy.parents r child target).mpr
          ⟨hChildN,(parent_copy_nonroot_unmoved_d hM hC hT hD hr hSource hIsRoot (fun h => hNoHigh h.2) hMap).mpr
            ⟨p,hpNat,hP,hMapTarget⟩⟩
        exact hStep p block target hpLast hNewP ((Terminal.root_at_parent_iff_d hM hC hD.mountain hP).mp hRoot) hMapTarget hMapRoot
    · obtain ⟨F,_,hRow,hRF⟩ := hRoot
      have hNo : NoParent M D.mountain.width F source := fun p _ hP => hSome ⟨p,F,(hD.mountain.parents.bounds hM.1 hRow).2,hRow,hP⟩
      have hRootEq := root_of_no_parent_d hM hC (hD.mountain.forest r F hRow) hNo hRF
      subst oldRoot
      have hTargetEq := hJ.graph.unique source newRoot child ((hRows source newRoot).mpr hMapRoot) ((hRows source child).mpr hMap)
      subst newRoot
      obtain ⟨height,hh,hHeight⟩ := hD.mountain.heights.total source hSourceX
      have hOut : ¬InCone M C D source := by
        rintro ⟨height',_,hHeight',hLe,_⟩
        have he := hD.mountain.heights.unique source height' height hHeight' hHeight
        subst height'
        have hRH : M.mem r height := by
          rcases hLe with he | hlt
          · exact he ▸ hLow
          · exact (hw.mem hh).transitive D.floor hlt r hLow
        exact hSome ((hD.mountain.source r source height hHeight).mpr hRH)
      have hTargetHeight : MemPair M Y.heights child height := (hCopy.parent_copy_heights_d hM hC hT hD hSource hChildN hMap hHeight).mpr
        (Or.inr ⟨hOut,rfl⟩)
      obtain ⟨G,hG,hRowG⟩ := hY.parents.total r hr
      refine ⟨G,hG,hRowG,hChild,?_,Or.inl rfl⟩
      intro p _ hP
      have hRH := (hY.source r child height hTargetHeight).mp ⟨p,G,hG,hRowG,hP⟩
      exact hSome ((hD.mountain.source r source height hHeight).mpr hRH))
  have hZ : M.mem z Y.width := by
    have hBounds := hRoot.bounds hM.1 hD.mountain
    obtain ⟨J,hJ,hRows⟩ := parent_copy_graph_exists_d hM hC hT hD.coordinates hMap.2.1
    rcases hBounds.2.2.2 with he | hlt
    · have hzc := hJ.graph.unique s z c ((hRows s z).mpr (he ▸ hMapRoot)) ((hRows s c).mpr hMap)
      exact hzc.symm ▸ hChild
    · have hzc := hJ.strict q hMapRoot.1 s hMap.1 hlt z c ((hRows q z).mpr hMapRoot) ((hRows s c).mpr hMap)
      exact (hw.mem hY.width).transitive c hChild z hzc
  exact (lowRootCopySchema_iff hM.1 C T D.coordinates D.mountain Y r c).mp (hAll c (hw.mem (hw.transitive Y.width hY.width c hChild)))
    hChild s hSource b hMap.2.1 q (hRoot.bounds hM.1 hD.mountain).2.1 z hZ ⟨hMap,hRoot,hMapRoot⟩

theorem Copies.outside_high_root_copy_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {D : Context M.Domain} (hD : D.Valid M C) {m : M.Domain} {R : RowStateSpace M.Domain} {V P H : M.Domain}
    (hRun : RowRun M C m R V P H) (hFrom : FromRun M C m R V H D.mountain)
    {Y : Data M.Domain} (hY : Y.Valid M C) {n r b s c q z : M.Domain}
    (hCopy : Copies M C T D n Y) (hs : M.mem s D.coordinates.last) (hOut : ¬InCone M C D s)
    (hHigh : D.floor=r ∨ M.mem D.floor r) (hMap : ParentCopy M C T D.coordinates b s c) (hc : M.mem c Y.width)
    (hRoot : RootAt M C D.mountain r s q) (hMapQ : ParentCopy M C T D.coordinates b q z) : RootAt M C Y r c z := by
  have hw := omega_isOrdinal_d hM hC.omega
  obtain ⟨F,hF,hRowF,hRootF⟩ := hRoot
  have hr := (hD.mountain.parents.bounds hM.1 hRowF).1
  obtain ⟨G,hG,hRowG⟩ := hY.parents.total r hr
  obtain ⟨J,hJ,hRows⟩ := parent_copy_graph_exists_d hM hC hT hD.coordinates hMap.2.1
  have hOutQ : ¬InCone M C D q := by
    rcases hRootF.2.2 with he | hAnc
    · exact he.symm ▸ hOut
    · exact fun h => hOut ((in_cone_ancestor_iff_d hM hC hD hRun hFrom hHigh hRowF hAnc).mp h)
  have hqLast : M.mem q D.coordinates.last := by
    rcases hRootF.2.2 with he | hAnc
    · exact he.symm ▸ hs
    · exact (hw.mem hD.coordinates.last).transitive s hs q hAnc.1
  have hz : M.mem z Y.width := by
    rcases hRootF.2.2 with he | hAnc
    · subst q
      exact (hJ.graph.unique s z c ((hRows s z).mpr hMapQ) ((hRows s c).mpr hMap)).symm ▸ hc
    · exact (hw.mem hY.width).transitive c hc z
        (hJ.strict q hMapQ.1 s hMap.1 hAnc.1 z c ((hRows q z).mpr hMapQ) ((hRows s c).mpr hMap))
  obtain ⟨height,_,hHeight⟩ := hD.mountain.heights.total q hRootF.1
  have hHeightNew := (hCopy.parent_copy_heights_d hM hC hT hD hqLast (hCopy.width ▸ hz) hMapQ hHeight).mpr (Or.inr ⟨hOutQ,rfl⟩)
  refine ⟨G,hG,hRowG,root_map_global_bounded_d hM hC (hD.mountain.forest r F hRowF) hY.width hJ hRootF
    ((hRows q z).mpr hMapQ) ((hRows s c).mpr hMap) hc ?_ ?_⟩
  · intro p _ hP
    exact root_no_parent_height_d hM hD.mountain ⟨F,hF,hRowF,hRootF⟩ hHeight
      ((hY.source r z height hHeightNew).mp ⟨p,G,hG,hRowG,hP⟩)
  · intro d p v w hReach hDP hDV hPW
    have hOutD : ¬InCone M C D d := by
      rcases hReach with he | hAnc
      · exact he.symm ▸ hOut
      · exact fun h => hOut ((in_cone_ancestor_iff_d hM hC hD hRun hFrom hHigh hRowF hAnc).mp h)
    have hdLast : M.mem d D.coordinates.last := by
      rcases hReach with he | hAnc
      · exact he.symm ▸ hs
      · exact (hw.mem hD.coordinates.last).transitive s hs d hAnc.1
    have hMapD := (hRows d v).mp hDV
    have hMapP := (hRows p w).mp hPW
    have hv : M.mem v n := by
      rcases hReach with he | hAnc
      · subst d
        exact hCopy.width ▸ ((hJ.graph.unique s v c hDV ((hRows s c).mpr hMap)).symm ▸ hc)
      · exact hCopy.width ▸ ((hw.mem hY.width).transitive c hc v
          (hJ.strict d hMapD.1 s hMap.1 hAnc.1 v c hDV ((hRows s c).mpr hMap)))
    have hNonroot : d≠D.coordinates.root := fun he => hOutD (he.symm ▸ in_cone_root_d hM hD)
    have hNewP : ParentAt M Y r v w := (hCopy.parents r v w).mpr ⟨hv,
      (parent_copy_nonroot_unmoved_d hM hC hT hD hr hdLast hNonroot (fun h => hOutD h.1) hMapD).mpr
        ⟨p,hMapP.1,⟨F,hF,hRowF,hDP⟩,hMapP⟩⟩
    obtain ⟨G',_,hG',hP⟩ := hNewP
    exact (hY.parents.unique r G' G hG' hRowG) ▸ hP

/-- 任意真实Lower复制边及其计算根都有同层的实际源行证书。 -/
theorem Copies.encoded_source_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {D : Context M.Domain} (hD : D.Valid M C) {m : M.Domain} {R : RowStateSpace M.Domain} {V P H : M.Domain}
    (hRun : RowRun M C m R V P H) (hFrom : FromRun M C m R V H D.mountain)
    {Y : Data M.Domain} (hY : Y.Valid M C) {n r b s c cut pNew qNew : M.Domain}
    (hCopy : Copies M C T D n Y) (hs : Source M D.coordinates s)
    (hEncode : Encode M C T D.coordinates s b c) (hc : M.mem c Y.width)
    (hCut : Encode M C T D.coordinates D.coordinates.root b cut)
    (hParent : ParentAt M Y r c pNew) (hRoot : RootAt M C Y r c qNew) :
    ∃ u pOld qOld, M.mem u C.omega ∧ ParentAt M D.mountain u s pOld ∧ RootAt M C D.mountain u s qOld ∧
      ParentCopy M C T D.coordinates b pOld pNew ∧
      (ParentCopy M C T D.coordinates b qOld qNew ∨
        (M.mem qNew cut ∧ (D.coordinates.root=qOld ∨ M.mem D.coordinates.root qOld))) := by
  have hw := omega_isOrdinal_d hM hC.omega
  have hr := (hParent.bounds hM.1 hY).1
  have hsX : M.mem s D.mountain.width := by
    rcases hs.2 with he | hlt
    · exact he.symm ▸ hD.last
    · exact (hw.mem hD.mountain.width).transitive D.coordinates.last hD.last s hlt
  obtain ⟨J,hJ,hRows⟩ := parent_copy_graph_exists_d hM hC hT hD.coordinates hEncode.2.1
  rcases (hCopy.encoded_parent_iff_d hM hC hT hD hr hs hEncode (hCopy.width ▸ hc)).mp hParent with ⟨⟨hCone,hHigh⟩,hMoved⟩ | ⟨hNoMove,pOld,hPOld,hOldP,hMapP⟩
  · obtain ⟨off,hOff,hTimes,u,hu,hShift,pOld,_,hOldP,hEncP⟩ := hMoved
    have hConeP := hCone.high_parent_d hM hC hD (hShift.floor_le_d hM hC hT) hOldP
    have hMapP : ParentCopy M C T D.coordinates b pOld pNew := (parent_copy_bad_iff (hConeP.not_good_d hM hC hD)).mpr hEncP
    obtain ⟨qOld,hOldRoot⟩ := root_at_exists_d hM hC hD.mountain hu hsX
    refine ⟨u,pOld,qOld,hu,hOldP,hOldRoot,hMapP,?_⟩
    obtain ⟨level,_,hLevel⟩ := hT.add.add_exists_d hM hC (hD.floor_nat hM.1) hOff
    classical
    by_cases hGap : M.mem r level
    · have hUF := hShift.gap_value hM.1 hT hLevel hGap
      have hAtFloor : RootAt M C D.mountain D.floor s qOld := hUF ▸ hOldRoot
      obtain ⟨_,_,_,_,hRootFloor⟩ := hCone
      have hQRoot := hRootFloor.unique_d hM hC hD.mountain hAtFloor
      exact Or.inr ⟨hCopy.gap_root_lt_cut_d hM hC hT hD hRun hFrom hY hs
        (by obtain ⟨height,hh,hHeight⟩ := hD.mountain.heights.total s hsX
            have hFloorHeight : D.floor=height ∨ M.mem D.floor height := by
              have hSome := (hD.mountain.source D.floor s height hHeight).mp ⟨pOld,hUF ▸ hOldP⟩
              exact Or.inr hSome
            exact ⟨height,hh,hHeight,hFloorHeight,hRootFloor⟩)
        hr hHigh hTimes hLevel hGap hEncode (hCopy.width ▸ hc) hCut hRoot,Or.inl hQRoot⟩
    · have hqNat := hw.transitive D.mountain.width hD.mountain.width qOld (hOldRoot.bounds hM.1 hD.mountain).2.1
      obtain ⟨z,_,hQZ⟩ := hJ.graph.total qOld hqNat
      have hMapQ := (hRows qOld z).mp hQZ
      have hqS := Terminal.root_at_lt_of_parent_d hM hC hD.mountain hOldP hOldRoot
      have hqLast : M.mem qOld D.coordinates.last := by
        rcases hs.2 with he | hlt
        · exact he ▸ hqS
        · exact (hw.mem hD.coordinates.last).transitive s hlt qOld hqS
      have hNewRoot := hCopy.high_root_copy_d hM hC hT hD hRun hFrom hY hs hCone hHigh hTimes hShift hLevel hGap
        hEncode (hCopy.width ▸ hc) hOldRoot hqLast hMapQ
      exact Or.inl ((hNewRoot.unique_d hM hC hY hRoot) ▸ hMapQ)
  · obtain ⟨qOld,hOldRoot⟩ := root_at_exists_d hM hC hD.mountain hr hsX
    have hqNat := hw.transitive D.mountain.width hD.mountain.width qOld (hOldRoot.bounds hM.1 hD.mountain).2.1
    obtain ⟨z,_,hQZ⟩ := hJ.graph.total qOld hqNat
    have hMapQ := (hRows qOld z).mp hQZ
    refine ⟨r,pOld,qOld,hr,hOldP,hOldRoot,hMapP,Or.inl ?_⟩
    have hNewRoot : RootAt M C Y r c z := by
      classical
      by_cases hLow : M.mem r D.floor
      · have hpLast : M.mem pOld D.coordinates.last := by
          have hps := (hOldP.bounds hM.1 hD.mountain).2.2.2
          rcases hs.2 with he | hlt
          · exact he ▸ hps
          · exact (hw.mem hD.coordinates.last).transitive s hlt pOld hps
        have hRootP := (Terminal.root_at_parent_iff_d hM hC hD.mountain hOldP).mp hOldRoot
        exact (Terminal.root_at_parent_iff_d hM hC hY hParent).mpr
          (hCopy.low_root_parent_copy_d hM hC hT hD hY hRun hFrom hLow hpLast (hParent.bounds hM.1 hY).2.2.1 hMapP hRootP hMapQ)
      · have hHigh : D.floor=r ∨ M.mem D.floor r := by
          rcases hw.wellOrder.linear.compare D.floor (hD.floor_nat hM.1) r hr with he | hlt | hgt
          · exact Or.inl (hM.1.eq_of_same_members D.floor r he)
          · exact Or.inr hlt
          · exact False.elim (hLow hgt)
        have hOut : ¬InCone M C D s := fun h => hNoMove ⟨h,hHigh⟩
        have hsLast : M.mem s D.coordinates.last := by
          rcases hs.2 with he | hlt
          · exact False.elim (hOut (he.symm ▸ in_cone_last hD))
          · exact hlt
        have hMapS : ParentCopy M C T D.coordinates b s c :=
          (parent_copy_bad_iff (nat_not_reverse_d hM hC hEncode.1 (Or.inr hs.1))).mpr hEncode
        exact hCopy.outside_high_root_copy_d hM hC hT hD hRun hFrom hY hsLast hOut hHigh hMapS hc hOldRoot hMapQ
    exact (hNewRoot.unique_d hM hC hY hRoot) ▸ hMapQ

/-- VirtualNeeds使用的实际旧末列/新边界实例，不增加任何根假设。 -/
theorem Copies.seam_source_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {D : Context M.Domain} (hD : D.Valid M C) {m : M.Domain} {R : RowStateSpace M.Domain} {V P H : M.Domain}
    (hRun : RowRun M C m R V P H) (hFrom : FromRun M C m R V H D.mountain)
    {Y : Data M.Domain} (hY : Y.Valid M C) {n r b boundary cut pNew qNew : M.Domain}
    (hCopy : Copies M C T D n Y) (hWidth : Width M C T D.coordinates b boundary) (hc : M.mem boundary Y.width)
    (hCut : Encode M C T D.coordinates D.coordinates.root b cut)
    (hParent : ParentAt M Y r boundary pNew) (hRoot : RootAt M C Y r boundary qNew) :
    ∃ u pOld qOld, M.mem u C.omega ∧ ParentAt M D.mountain u D.coordinates.last pOld ∧
      RootAt M C D.mountain u D.coordinates.last qOld ∧ ParentCopy M C T D.coordinates b pOld pNew ∧
      (ParentCopy M C T D.coordinates b qOld qNew ∨
        (M.mem qNew cut ∧ (D.coordinates.root=qOld ∨ M.mem D.coordinates.root qOld))) :=
  hCopy.encoded_source_d hM hC hT hD hRun hFrom hY ⟨hD.coordinates.below,Or.inl rfl⟩ hWidth hc hCut hParent hRoot

end KP1Y.OneYFinite.CopiedMountain.Lower
