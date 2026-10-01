import KP1Y.OneYLowerCanonPreimage
import KP1Y.OneYLowerCanonKeyStart

/-! Lower复制目标图的伪父：锥内（抬升行）与锥外高行两种情形与源伪父逐项对应。 -/
namespace KP1Y.OneYFinite.CopiedMountain.Lower
open YesMetaZFC YesMetaZFC.SetTheory YesMetaZFC.SetTheory.Definitional
open KP1Y.Kuratowski KP1Y.Functions KP1Y.Naturals KP1Y.Bounded KP1Y.Arithmetic
open KP1Y.OneYFinite.CopyCoordinates KP1Y.OneYFinite.LowerCanon
universe u

/-- 候选集合经严格单调函数关系对应时，最大候选（伪父）也对应。 -/
theorem canon_pseudo_parent_transfer_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {X Y : Data M.Domain} (hX : X.Valid M C) (hY : Y.Valid M C)
    {s c : M.Domain} (Lk : M.Domain → M.Domain → Prop)
    (hFun : ∀ q a a', Lk q a → Lk q a' → a=a')
    (hTot : ∀ q, GraphPseudoCandidate M C X s q → ∃ a, Lk q a)
    (hMono : ∀ q q' a a', Lk q a → Lk q' a' → M.mem q q' → M.mem a a')
    (hCand : ∀ a, GraphPseudoCandidate M C Y c a ↔ ∃ q, GraphPseudoCandidate M C X s q ∧ Lk q a) (a : M.Domain) :
    GraphPseudoParent M C Y c a ↔ ∃ q, GraphPseudoParent M C X s q ∧ Lk q a := by
  have hw := omega_isOrdinal_d hM hC.omega
  have hXNat (q : M.Domain) (h : GraphPseudoCandidate M C X s q) : M.mem q C.omega :=
    hw.transitive X.width hX.width q (h.bounds hM.1).1
  have hYNat (q : M.Domain) (h : GraphPseudoCandidate M C Y c q) : M.mem q C.omega :=
    hw.transitive Y.width hY.width q (h.bounds hM.1).1
  constructor
  · rintro ⟨hCa,hMaxY⟩
    obtain ⟨q,hCq,hR⟩ := (hCand a).mp hCa
    refine ⟨q,⟨hCq,?_⟩,hR⟩
    intro q' _ hCq'
    obtain ⟨a',hR'⟩ := hTot q' hCq'
    have hCa' := (hCand a').mpr ⟨q',hCq',hR'⟩
    have hLe := hMaxY a' (hCa'.bounds hM.1).2.2 hCa'
    rcases nat_le_or_lt hM hC (hXNat q' hCq') (hXNat q hCq) with hle | hgt
    · exact hle
    · exact False.elim (nat_not_lt_of_le hM hC (hYNat a hCa) hLe (hMono q q' a a' hR hR' hgt))
  · rintro ⟨q,⟨hCq,hMaxX⟩,hR⟩
    refine ⟨(hCand a).mpr ⟨q,hCq,hR⟩,?_⟩
    intro a' _ hCa'
    obtain ⟨q',hCq',hR'⟩ := (hCand a').mp hCa'
    rcases hMaxX q' (hCq'.bounds hM.1).2.2 hCq' with he | hlt
    · subst he
      exact Or.inl (hFun q' a' a hR' hR)
    · exact Or.inr (hMono q' q a' a hR' hR hlt)

theorem canon_parent_copy_mono {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {A : CopyCoordinates.Context M.Domain} (hA : A.Valid M C) {b q q' a a' : M.Domain}
    (hR : ParentCopy M C T A b q a) (hR' : ParentCopy M C T A b q' a') (hqq : M.mem q q') : M.mem a a' := by
  obtain ⟨J,hJ,hRows⟩ := parent_copy_graph_exists_d hM hC hT hA hR.2.1
  exact hJ.strict q hR.1 q' hR'.1 hqq a a' ((hRows q a).mpr hR) ((hRows q' a').mpr hR')

theorem canon_parent_copy_fun {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {A : CopyCoordinates.Context M.Domain} (hA : A.Valid M C) {b q a a' : M.Domain}
    (hR : ParentCopy M C T A b q a) (hR' : ParentCopy M C T A b q a') : a=a' := by
  obtain ⟨J,hJ,hRows⟩ := parent_copy_graph_exists_d hM hC hT hA hR.2.1
  exact hJ.graph.unique q a a' ((hRows q a).mpr hR) ((hRows q a').mpr hR')

/-- 锥内源列：目标伪父候选恰为源候选在同一块中的编码。 -/
theorem Copies.canon_pseudo_cand_lifted_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {D : Context M.Domain} (hD : D.Valid M C) {Y : Data M.Domain} (hY : Y.Valid M C) {n : M.Domain}
    (hCopy : Copies M C T D n Y) {m : M.Domain} {R : RowStateSpace M.Domain} {V P H : M.Domain}
    (hRun : RowRun M C m R V P H) (hFrom : FromRun M C m R V H D.mountain) {s b c : M.Domain}
    (hRootS : M.mem D.coordinates.root s) (hsLast : s=D.coordinates.last ∨ M.mem s D.coordinates.last)
    (hCone : InCone M C D s) (hEnc : Encode M C T D.coordinates s b c) (hc : M.mem c Y.width) (a : M.Domain) :
    GraphPseudoCandidate M C Y c a ↔ ∃ q, GraphPseudoCandidate M C D.mountain s q ∧ Encode M C T D.coordinates q b a := by
  have hw := omega_isOrdinal_d hM hC.omega
  have hFloorNat := hD.floor_nat hM.1
  have hsX := canon_last_in_width hM hC hD hsLast
  obtain ⟨hs,hsNat,hHS⟩ := hD.mountain.heights.total s hsX
  have hFloorHs := hCone.height_strict_d hM hC hD hRootS hHS
  obtain ⟨u,huNat,hSuccU⟩ : ∃ u, M.mem u C.omega ∧ M.SuccessorOf hs u := by
    rcases natural_cases hM hC.omega hsNat with hEmpty | ⟨u,hu,hSucc⟩
    · exact False.elim (hEmpty _ hFloorHs)
    · exact ⟨u,hu,hSucc⟩
  have hFloorU : D.floor=u ∨ M.mem D.floor u := (nat_lt_succ_iff hM hSuccU).mp hFloorHs
  obtain ⟨off,hOff,hTimes⟩ := hT.mul.mul_exists_d hM hC hEnc.2.1 (hD.rise_nat hM.1)
  obtain ⟨level,_,hLevel⟩ := hT.add.add_exists_d hM hC hFloorNat hOff
  obtain ⟨hc',hc'Nat,hAddC⟩ := hT.add.add_exists_d hM hC hsNat hOff
  obtain ⟨r',hr'Nat,hAddR⟩ := hT.add.add_exists_d hM hC huNat hOff
  have hSuccR : M.SuccessorOf hc' r' := natural_sum_left_successor_d hM hC hOff hSuccU
    ((hT.add.add_iff_sum hM huNat hOff).mp hAddR) ((hT.add.add_iff_sum hM hsNat hOff).mp hAddC)
  obtain ⟨hShift,hNotGap⟩ := canon_shift_high_d hM hC hT hLevel huNat hFloorU hAddR
  have hHighR : D.floor=r' ∨ M.mem D.floor r' := by
    have hLR := (add_same_right_le_iff_d hM hC hT hLevel hAddR).mpr hFloorU
    have hFL := ordinal_subset_cases_d hM (hw.mem hFloorNat) (hw.mem (hLevel.bounds hM.1 hT.add).2.2)
      (sum_base_subset_d hM (hw.mem hFloorNat) ((hT.add.add_iff_sum hM hFloorNat hOff).mp hLevel))
    exact nat_le_trans hM hC hr'Nat hFL hLR
  have hLiftedC : Lifted M C T D hs b hc' := ⟨hsNat,hEnc.2.1,off,hOff,hTimes,hAddC⟩
  have hHC : MemPair M Y.heights c hc' := (hCopy.canon_copy_heights_d hM hC hT hD (Or.inr hRootS) hsLast hEnc
    (hCopy.width ▸ hc) hHS).mpr (Or.inl ⟨hCone,hLiftedC⟩)
  obtain ⟨F,hFm,hF⟩ := hD.mountain.parents.total u huNat
  obtain ⟨G,hGm,hG⟩ := hY.parents.total r' hr'Nat
  have hFF := hD.mountain.forest u F hF
  have hGF := hY.forest r' G hG
  obtain ⟨J,hJ,hRows⟩ := parent_copy_graph_exists_d hM hC hT hD.coordinates hEnc.2.1
  have hNotGood (q : M.Domain) (hq : M.mem q C.omega) (hRQ : D.coordinates.root=q ∨ M.mem D.coordinates.root q) :
      ¬M.mem q D.coordinates.root := nat_not_lt_of_le hM hC hq hRQ
  have hMapS : ParentCopy M C T D.coordinates b s c := (parent_copy_bad_iff (hNotGood s hEnc.1 (Or.inr hRootS))).mpr hEnc
  have hConeChain (d : M.Domain) (h : d=s ∨ Ancestor M C D.mountain.width F d s) : InCone M C D d := by
    rcases h with he | hAnc
    · exact he ▸ hCone
    · exact (in_cone_ancestor_iff_d hM hC hD hRun hFrom hFloorU hF hAnc).mpr hCone
  -- 候选高度：源q高度hq，目标编码高度hq+off
  have hHeightCopy (q a hq : M.Domain) (hConeQ : InCone M C D q) (hqLast : q=D.coordinates.last ∨ M.mem q D.coordinates.last)
      (hEncQ : Encode M C T D.coordinates q b a) (ha : M.mem a n) (hHQ : MemPair M D.mountain.heights q hq) (hp : M.Domain) :
      MemPair M Y.heights a hp ↔ AddAt M T.addPairs T.plus hq off hp := by
    rw [hCopy.canon_copy_heights_d hM hC hT hD (hConeQ.root_le hM.1 hD) hqLast hEncQ ha hHQ]
    constructor
    · rintro (⟨_,_,_,off',_,hMul',hAdd⟩ | ⟨hNot,_⟩)
      · exact (hT.mul.mul_unique hM.1 hMul' hTimes) ▸ hAdd
      · exact False.elim (hNot hConeQ)
    · intro hAdd
      exact Or.inl ⟨hConeQ,(hD.mountain.heights.bounds hM.1 hHQ).2,hEnc.2.1,off,hOff,hTimes,hAdd⟩
  constructor
  · rintro ⟨hc'',_,hp,hpNat,r,hr,hHC',hHA,hSucc,G',_,hG',hAnc,hRel⟩
    have he1 := hY.heights.unique c hc'' hc' hHC' hHC
    subst he1
    have he2 := Structure.SuccessorOf.predecessor_eq hM.1 (hw.mem hr) hSucc hSuccR
    subst he2
    have he3 := hY.parents.unique r G' G hG' hG
    subst he3
    have hEdge : ∀ d u' v, (d=s ∨ Ancestor M C D.mountain.width F d s) → d≠D.mountain.width →
        MemPair M J d u' → MemPair M G' u' v → ∃ p, MemPair M F d p ∧ MemPair M J p v := by
      intro d u' v hChain _ hDU hUV
      have hConeD := hConeChain d hChain
      have hdNat := (hJ.graph.bounds hM.1 hDU).1
      have hMapD := (hRows d u').mp hDU
      have hu'Y := (hGF.bounds hM.1 hUV).1
      classical
      by_cases hdRoot : d=D.coordinates.root
      · subst hdRoot
        have hRootHeight : MemPair M Y.heights u' level :=
          (hCopy.parent_copy_heights_d hM hC hT hD hD.coordinates.below (hCopy.width ▸ hu'Y) hMapD hD.floor).mpr
            (Or.inl ⟨in_cone_root_d hM hD,hFloorNat,hEnc.2.1,off,hOff,hTimes,hLevel⟩)
        exact False.elim (hNotGap ((hY.source r u' level hRootHeight).mp ⟨v,(canon_row_parent_iff hM.1 hY hG').mpr hUV⟩))
      · have hRootD : M.mem D.coordinates.root d := by
          rcases hConeD.root_le hM.1 hD with he | hlt
          · exact False.elim (hdRoot he.symm)
          · exact hlt
        have hdLast : d=D.coordinates.last ∨ M.mem d D.coordinates.last := by
          rcases hChain with he | hAnc
          · exact he ▸ hsLast
          · exact Or.inr (nat_lt_of_lt_of_le hM hC hD.coordinates.last hAnc.1 hsLast)
        have hEncD := (parent_copy_bad_iff (hNotGood d hdNat (Or.inr hRootD))).mp hMapD
        rcases (hCopy.encoded_parent_iff_d hM hC hT hD hr ⟨hRootD,hdLast⟩ hEncD (hCopy.width ▸ hu'Y)).mp
            ((canon_row_parent_iff hM.1 hY hG').mpr hUV) with ⟨_,off',_,hMul',u'',_,hShift',p,_,hPAt,hEncP⟩ | ⟨hNo,_⟩
        · have ho := hT.mul.mul_unique hM.1 hMul' hTimes
          subst ho
          have hu := shifted_row_unique hM.1 hT hShift' hShift
          subst hu
          have hPF := (canon_row_parent_iff hM.1 hD.mountain hF).mp hPAt
          have hConeP := hConeD.high_parent_d hM hC hD hFloorU hPAt
          exact ⟨p,hPF,(hRows p v).mpr ((parent_copy_bad_iff (hNotGood p hEncP.1 (hConeP.root_le hM.1 hD))).mpr hEncP)⟩
        · exact False.elim (hNo ⟨hConeD,hHighR⟩)
    rcases ancestor_preimage_d (y₀ := D.mountain.width) hM hC hFF hGF hEdge ((hRows s c).mpr hMapS) hAnc with
      ⟨q,hQS,hJQ⟩ | ⟨hY0,_⟩
    · have hConeQ := hConeChain q (Or.inr hQS)
      have hqLast : q=D.coordinates.last ∨ M.mem q D.coordinates.last :=
        Or.inr (nat_lt_of_lt_of_le hM hC hD.coordinates.last hQS.1 hsLast)
      have hqX := (hQS.bounds hM.1).1
      obtain ⟨hq,hqNat,hHQ⟩ := hD.mountain.heights.total q hqX
      have hEncQ := (parent_copy_bad_iff (hNotGood q (hJ.graph.bounds hM.1 hJQ).1 (hConeQ.root_le hM.1 hD))).mp
        ((hRows q a).mp hJQ)
      have hAddQ := (hHeightCopy q a hq hConeQ hqLast hEncQ (hCopy.width ▸ (hAnc.bounds hM.1).1) hHQ hp).mp hHA
      have hRel' : hq=hs ∨ hq=u := by
        rcases hRel with he | he
        · exact Or.inl ((add_same_right_eq_iff_d hM hC hT hAddQ hAddC).mp he)
        · exact Or.inr ((add_same_right_eq_iff_d hM hC hT hAddQ hAddR).mp he)
      exact ⟨q,⟨hs,hsNat,hq,hqNat,u,huNat,hHS,hHQ,hSuccU,F,hFm,hF,hQS,hRel'⟩,hEncQ⟩
    · rcases hY0 with he | hAnc'
      · exact False.elim (nat_irrefl hM s (he ▸ hsX))
      · exact False.elim (nat_irrefl hM D.mountain.width ((hw.mem hD.mountain.width).transitive s hsX _ hAnc'.1))
  · rintro ⟨q,⟨hs',_,hq,hqNat,u',_,hHS',hHQ,hSucc',F',_,hF',hAnc,hRel⟩,hEncQ⟩
    have he1 := hD.mountain.heights.unique s hs' hs hHS' hHS
    subst he1
    have he2 := Structure.SuccessorOf.predecessor_eq hM.1 (hw.mem (nat_mem_omega hM hC hsNat hSucc'.predecessor_mem)) hSucc' hSuccU
    subst he2
    have he3 := hD.mountain.parents.unique u' F' F hF' hF
    subst he3
    have hConeQ := hConeChain q (Or.inr hAnc)
    have hqLast : q=D.coordinates.last ∨ M.mem q D.coordinates.last :=
      Or.inr (nat_lt_of_lt_of_le hM hC hD.coordinates.last hAnc.1 hsLast)
    have hMapQ : ParentCopy M C T D.coordinates b q a :=
      (parent_copy_bad_iff (hNotGood q hEncQ.1 (hConeQ.root_le hM.1 hD))).mpr hEncQ
    have hNewAnc := hCopy.high_ancestor_copy_d hM hC hT hD hRun hFrom hY ⟨hRootS,hsLast⟩ hCone hHighR hTimes hShift hEnc
      (hCopy.width ▸ hc) hF hG hAnc hMapQ
    obtain ⟨hp,hpNat,hAddQ⟩ := hT.add.add_exists_d hM hC hqNat hOff
    have hHA := (hHeightCopy q a hq hConeQ hqLast hEncQ (hCopy.width ▸ (hNewAnc.bounds hM.1).1) hHQ hp).mpr hAddQ
    have hRel' : hp=hc' ∨ hp=r' := by
      rcases hRel with he | he
      · subst he
        exact Or.inl (hT.add.add_unique hM.1 hAddQ hAddC)
      · subst he
        exact Or.inr (hT.add.add_unique hM.1 hAddQ hAddR)
    exact ⟨hc',hc'Nat,hp,hpNat,r',hr'Nat,hHC,hHA,hSuccR,G,hGm,hG,hNewAnc,hRel'⟩


/-- 锥外且高度在floor以上的源列：目标伪父候选恰为源候选的ParentCopy像。 -/
theorem Copies.canon_pseudo_cand_out_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {D : Context M.Domain} (hD : D.Valid M C) {Y : Data M.Domain} (hY : Y.Valid M C) {n : M.Domain}
    (hCopy : Copies M C T D n Y) {m : M.Domain} {R : RowStateSpace M.Domain} {V P H : M.Domain}
    (hRun : RowRun M C m R V P H) (hFrom : FromRun M C m R V H D.mountain) {s b c hs : M.Domain}
    (hsLast : M.mem s D.coordinates.last) (hOut : ¬InCone M C D s)
    (hHS : MemPair M D.mountain.heights s hs) (hFloorHs : M.mem D.floor hs)
    (hMap : ParentCopy M C T D.coordinates b s c) (hc : M.mem c Y.width) (a : M.Domain) :
    GraphPseudoCandidate M C Y c a ↔ ∃ q, GraphPseudoCandidate M C D.mountain s q ∧ ParentCopy M C T D.coordinates b q a := by
  have hw := omega_isOrdinal_d hM hC.omega
  have hsX := canon_last_in_width hM hC hD (Or.inr hsLast)
  have hsNat := (hD.mountain.heights.bounds hM.1 hHS).2
  obtain ⟨u,huNat,hSuccU⟩ : ∃ u, M.mem u C.omega ∧ M.SuccessorOf hs u := by
    rcases natural_cases hM hC.omega hsNat with hEmpty | ⟨u,hu,hSucc⟩
    · exact False.elim (hEmpty _ hFloorHs)
    · exact ⟨u,hu,hSucc⟩
  have hFloorU : D.floor=u ∨ M.mem D.floor u := (nat_lt_succ_iff hM hSuccU).mp hFloorHs
  have hHC : MemPair M Y.heights c hs :=
    (hCopy.parent_copy_heights_d hM hC hT hD hsLast (hCopy.width ▸ hc) hMap hHS).mpr (Or.inr ⟨hOut,rfl⟩)
  obtain ⟨F,hFm,hF⟩ := hD.mountain.parents.total u huNat
  obtain ⟨G,hGm,hG⟩ := hY.parents.total u huNat
  have hFF := hD.mountain.forest u F hF
  have hGF := hY.forest u G hG
  obtain ⟨J,hJ,hRows⟩ := parent_copy_graph_exists_d hM hC hT hD.coordinates hMap.2.1
  have hOutChain (d : M.Domain) (h : d=s ∨ Ancestor M C D.mountain.width F d s) : ¬InCone M C D d := by
    rcases h with he | hAnc
    · exact he ▸ hOut
    · exact fun hc => hOut ((in_cone_ancestor_iff_d hM hC hD hRun hFrom hFloorU hF hAnc).mp hc)
  have hLastChain (d : M.Domain) (h : d=s ∨ Ancestor M C D.mountain.width F d s) : M.mem d D.coordinates.last := by
    rcases h with he | hAnc
    · exact he ▸ hsLast
    · exact nat_lt_trans hM hC hD.coordinates.last hAnc.1 hsLast
  have hHeightCopy (q a hq : M.Domain) (hOutQ : ¬InCone M C D q) (hqLast : M.mem q D.coordinates.last)
      (hMapQ : ParentCopy M C T D.coordinates b q a) (ha : M.mem a n) (hHQ : MemPair M D.mountain.heights q hq) (hp : M.Domain) :
      MemPair M Y.heights a hp ↔ hp=hq := by
    rw [hCopy.parent_copy_heights_d hM hC hT hD hqLast ha hMapQ hHQ]
    exact ⟨fun h => h.elim (fun h => False.elim (hOutQ h.1)) And.right,fun h => Or.inr ⟨hOutQ,h⟩⟩
  constructor
  · rintro ⟨hc'',_,hp,hpNat,r,hr,hHC',hHA,hSucc,G',_,hG',hAnc,hRel⟩
    have he1 := hY.heights.unique c hc'' hs hHC' hHC
    subst hc''
    have he2 := Structure.SuccessorOf.predecessor_eq hM.1 (hw.mem hr) hSucc hSuccU
    subst r
    have he3 := hY.parents.unique u G' G hG' hG
    subst G'
    have hEdge : ∀ d u' v, (d=s ∨ Ancestor M C D.mountain.width F d s) → d≠D.mountain.width →
        MemPair M J d u' → MemPair M G u' v → ∃ p, MemPair M F d p ∧ MemPair M J p v := by
      intro d u' v hChain _ hDU hUV
      have hOutD := hOutChain d hChain
      have hne : d≠D.coordinates.root := fun he => hOutD (he ▸ in_cone_root_d hM hD)
      have hu'Y := (hGF.bounds hM.1 hUV).1
      have hPar := ((hCopy.parents u u' v).mp ((canon_row_parent_iff hM.1 hY hG).mpr hUV)).2
      obtain ⟨p,_,hPAt,hMapP⟩ := (parent_copy_nonroot_unmoved_d hM hC hT hD huNat (hLastChain d hChain) hne
        (fun h => hOutD h.1) ((hRows d u').mp hDU)).mp hPar
      exact ⟨p,(canon_row_parent_iff hM.1 hD.mountain hF).mp hPAt,(hRows p v).mpr hMapP⟩
    rcases ancestor_preimage_d (y₀ := D.mountain.width) hM hC hFF hGF hEdge ((hRows s c).mpr hMap) hAnc with
      ⟨q,hQS,hJQ⟩ | ⟨hY0,_⟩
    · have hOutQ := hOutChain q (Or.inr hQS)
      have hqLast := hLastChain q (Or.inr hQS)
      obtain ⟨hq,hqNat,hHQ⟩ := hD.mountain.heights.total q (hQS.bounds hM.1).1
      have hMapQ := (hRows q a).mp hJQ
      have hpq := (hHeightCopy q a hq hOutQ hqLast hMapQ (hCopy.width ▸ (hAnc.bounds hM.1).1) hHQ hp).mp hHA
      subst hpq
      exact ⟨q,⟨hs,hsNat,hp,hqNat,u,huNat,hHS,hHQ,hSuccU,F,hFm,hF,hQS,hRel⟩,hMapQ⟩
    · rcases hY0 with he | hAnc'
      · exact False.elim (nat_irrefl hM s (he ▸ hsX))
      · exact False.elim (nat_irrefl hM D.mountain.width ((hw.mem hD.mountain.width).transitive s hsX _ hAnc'.1))
  · rintro ⟨q,⟨hs',_,hq,hqNat,u',_,hHS',hHQ,hSucc',F',_,hF',hAnc,hRel⟩,hMapQ⟩
    have he1 := hD.mountain.heights.unique s hs' hs hHS' hHS
    subst hs'
    have he2 := Structure.SuccessorOf.predecessor_eq hM.1 (hw.mem (nat_mem_omega hM hC hsNat hSucc'.predecessor_mem)) hSucc' hSuccU
    subst u'
    have he3 := hD.mountain.parents.unique u F' F hF' hF
    subst F'
    have hNewAnc := hCopy.outside_high_ancestor_copy_d hM hC hT hD hY hRun hFrom hFloorU hF hG hAnc hsLast hOut hMapQ hMap hc
    have hHA := (hHeightCopy q a hq (hOutChain q (Or.inr hAnc)) (hLastChain q (Or.inr hAnc)) hMapQ
      (hCopy.width ▸ (hNewAnc.bounds hM.1).1) hHQ hq).mpr rfl
    exact ⟨hs,hsNat,hq,hqNat,u,huNat,hHC,hHA,hSuccU,G,hGm,hG,hNewAnc,hRel⟩

end KP1Y.OneYFinite.CopiedMountain.Lower
