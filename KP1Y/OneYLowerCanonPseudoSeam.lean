import KP1Y.OneYLowerCanonPreimage
import KP1Y.OneYLowerCanonPseudoHigh

/-! 低行接缝隔离：源末列到root的低行路径中间列高度严格大于阈值；目标中root副本链上root之后的列
高度亦严格大于阈值（原 seam_intermediate_height 与 firstMatch_old_last）。 -/
namespace KP1Y.OneYFinite.CopiedMountain.Lower
open YesMetaZFC YesMetaZFC.SetTheory YesMetaZFC.SetTheory.Definitional
open KP1Y.Kuratowski KP1Y.Functions KP1Y.Naturals KP1Y.Bounded KP1Y.Arithmetic
open KP1Y.OneYFinite.CopyCoordinates KP1Y.OneYFinite.LowerCanon
universe u

private def betweenEnv {M : SetTheory.Structure.{u}} (C : ExpressionData M.Domain) (m F P : M.Domain) : Env M 8 :=
  (((((((oneEnv C.omega).push C.zero).push C.one).push C.sequences).push C.expressions).push m).push F).push P

private def betweenSchema : Project.UnarySchema 8 where
  body := .forallE (.forallE (.imp
    (ancestorFormula ⟨.bound 10,.bound 9,.bound 8,.bound 7,.bound 6⟩ (.bound 5) (.bound 3) (.bound 1) (.bound 2))
    (.imp (ancestorFormula ⟨.bound 10,.bound 9,.bound 8,.bound 7,.bound 6⟩ (.bound 5) (.bound 4) (.bound 0) (.bound 2))
      (.imp (.mem (.bound 1) (.bound 0))
        (ancestorFormula ⟨.bound 10,.bound 9,.bound 8,.bound 7,.bound 6⟩ (.bound 5) (.bound 3) (.bound 1) (.bound 0))))))
  freeClosed := by
    have hC : (⟨.bound 10,.bound 9,.bound 8,.bound 7,.bound 6⟩ : ExpressionData (Project.Term 11)).Closed := ⟨rfl,rfl,rfl,rfl,rfl⟩
    have h1 := ancestorFormula_freeClosed hC (.bound 5) (.bound 3) (.bound 1) (.bound 2) rfl rfl rfl rfl
    have h2 := ancestorFormula_freeClosed hC (.bound 5) (.bound 4) (.bound 0) (.bound 2) rfl rfl rfl rfl
    have h3 := ancestorFormula_freeClosed hC (.bound 5) (.bound 3) (.bound 1) (.bound 0) rfl rfl rfl rfl
    simp [Definitional.Formula.FreeClosed,h1,h2,h3]

private theorem betweenSchema_iff {M : SetTheory.Structure.{u}} (he : Extensional M)
    (C : ExpressionData M.Domain) (m F P c : M.Domain) :
    Project.Formula.satisfies ((betweenEnv C m F P).push c) betweenSchema.body ↔
      ∀ a z, Ancestor M C m P a c → Ancestor M C m F z c → M.mem a z → Ancestor M C m P a z := by
  simp only [betweenSchema,Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_imp_iff,
    ancestorFormula_iff he,Project.Formula.satisfies_mem_iff]
  rfl

/-- 稠密选择森林中保留的祖先，对任意更靠近的继承候选也是祖先（原 ancestor_between_selected）。 -/
theorem canon_selects_ancestor_between_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {m F V P a c z : M.Domain}
    (hS : Selects false M C m F V P) (ha : Ancestor M C m P a c) (hz : Ancestor M C m F z c) (haz : M.mem a z) :
    Ancestor M C m P a z := by
  have hw := omega_isOrdinal_d hM hC.omega
  have hAll := KP1Y.induction_d hM betweenSchema (betweenEnv C m F P) (by
    intro c ih
    apply (betweenSchema_iff hM.1 C m F P c).mpr
    intro a z ha hz haz
    obtain ⟨p,hCP,hTail⟩ := ancestor_parent_cases_d hM hC hS.forest ha
    have hPF := hS.parent_ancestor hCP
    have hpNat := hw.transitive m hS.forest.width p (hS.forest.bounds hM.1 hCP).2
    have hzNat := hw.transitive m hS.forest.width z (hz.bounds hM.1).1
    have hTail' (h : Ancestor M C m P p z) : Ancestor M C m P a z := by
      rcases hTail with he | hAP
      · exact he ▸ h
      · exact ancestor_trans_d hM hC hS.forest hAP h
    rcases hw.wellOrder.linear.compare p hpNat z hzNat with he | hpz | hzp
    · have he := hM.1.eq_of_same_members p z he
      subst he
      rcases hTail with he | hAP
      · exact False.elim (nat_irrefl hM a (he ▸ haz))
      · exact hAP
    · exact hTail' (hS.ancestor_of_between_d hM hC hCP hz hpz)
    · have hZP := ancestor_between_d hM hC hS.inherited hz hPF hzp
      rcases hTail with he | hAP
      · subst he
        exact False.elim (nat_irrefl hM a ((hw.mem hpNat).transitive z hzp a haz))
      · exact (betweenSchema_iff hM.1 C m F P p).mp (ih p (hS.forest.left c p hCP)) a z hAP hZP haz)
  exact (betweenSchema_iff hM.1 C m F P c).mp (hAll c) a z ha hz haz

/-- 源低行r（r+1=t≤floor）中，末列祖先链上root之后的列在第t行仍有父，即高度>t。 -/
theorem canon_seam_intermediate_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {D : Context M.Domain} (hD : D.Valid M C)
    {m : M.Domain} {R : RowStateSpace M.Domain} {V P H : M.Domain}
    (hRun : RowRun M C m R V P H) (hFrom : FromRun M C m R V H D.mountain)
    {r t F z hz : M.Domain} (hSucc : M.SuccessorOf t r) (hTF : t=D.floor ∨ M.mem t D.floor)
    (hF : MemPair M D.mountain.parents r F) (hZ : Ancestor M C D.mountain.width F z D.coordinates.last)
    (hRootZ : M.mem D.coordinates.root z) (hHZ : MemPair M D.mountain.heights z hz) : M.mem t hz := by
  have hr := (hD.mountain.parents.bounds hM.1 hF).1
  have ht := natural_successor_mem_d hM hC hr hSucc
  obtain ⟨Q,_,hQ⟩ := hD.mountain.parents.total t ht
  have hQF := hD.mountain.forest t Q hQ
  obtain ⟨Depths,hDepths,hRows⟩ := depth_graph_exists_d hM hC hQF
  have hSel := source_depth_selection_d hM hC hRun hFrom hSucc hF hQ
    (hDepths.mono_values (fun d hd => (omega_isOrdinal_d hM hC.omega).transitive D.mountain.width hD.mountain.width d hd)) hRows
  have hRootLast := source_root_ancestor_last_d hM hC hD hRun hFrom hQ hTF
  have hRootZQ := canon_selects_ancestor_between_d hM hC hSel hRootLast hZ hRootZ
  obtain ⟨p,hZP,_⟩ := ancestor_parent_cases_d hM hC hQF hRootZQ
  exact (hD.mountain.source t z hz hHZ).mp ⟨p,(canon_row_parent_iff hM.1 hD.mountain hQ).mpr hZP⟩

/-- 低行（未移动）中，非root源/原列d的副本的目标父恰为源父的副本。 -/
theorem Copies.canon_low_parent_iff_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {D : Context M.Domain} (hD : D.Valid M C) {Y : Data M.Domain} {n : M.Domain}
    (hCopy : Copies M C T D n Y) {r d b x v : M.Domain}
    (hLow : M.mem r D.floor) (hdLast : d=D.coordinates.last ∨ M.mem d D.coordinates.last) (hne : d≠D.coordinates.root)
    (hMap : ParentCopy M C T D.coordinates b d x) (hx : M.mem x n) :
    ParentAt M Y r x v ↔ ∃ p, ParentAt M D.mountain r d p ∧ ParentCopy M C T D.coordinates b p v := by
  have hr := nat_mem_omega hM hC (hD.floor_nat hM.1) hLow
  have hNoHigh : ¬(D.floor=r ∨ M.mem D.floor r) := fun h => nat_not_lt_of_le hM hC hr h hLow
  rcases hdLast with he | hlt
  · subst he
    have hNot : ¬M.mem D.coordinates.last D.coordinates.root := nat_not_lt_of_le hM hC hD.coordinates.last (Or.inr hD.coordinates.below)
    rw [hCopy.encoded_parent_iff_d hM hC hT hD hr ⟨hD.coordinates.below,Or.inl rfl⟩ ((parent_copy_bad_iff hNot).mp hMap) hx]
    constructor
    · rintro (⟨hMv,_⟩ | ⟨_,p,_,hP,hMapP⟩)
      · exact False.elim (hNoHigh hMv.2)
      · exact ⟨p,hP,hMapP⟩
    · rintro ⟨p,hP,hMapP⟩
      exact Or.inr ⟨fun h => hNoHigh h.2,p,hMapP.1,hP,hMapP⟩
  · rw [hCopy.parents r x v,parent_copy_nonroot_unmoved_d hM hC hT hD hr hlt hne (fun h => hNoHigh h.2) hMap]
    constructor
    · rintro ⟨_,p,_,hP,hMapP⟩
      exact ⟨p,hP,hMapP⟩
    · rintro ⟨p,hP,hMapP⟩
      exact ⟨hx,p,hMapP.1,hP,hMapP⟩


private def seamHEnv {M : SetTheory.Structure.{u}} (C : ExpressionData M.Domain) (T : MatrixArithmetic M.Domain)
    (A : CopyCoordinates.Context M.Domain) (Yw Yh G t : M.Domain) : Env M 19 :=
  ((((((((((((((((((oneEnv C.omega).push C.zero).push C.one).push C.sequences).push C.expressions).push T.addPairs).push T.plus).push T.mulPairs).push T.times).push T.diffPairs).push T.difference).push A.last).push A.root).push A.length).push A.first).push Yw).push Yh).push G).push t

private def seamHSchema : Project.UnarySchema 19 where
  body := Project.Formula.forallMem (.bound 4)
    (.imp (parentCopyFormula ⟨.bound 20,.bound 19,.bound 18,.bound 17,.bound 16⟩
      ⟨.bound 15,.bound 14,.bound 13,.bound 12,.bound 11,.bound 10⟩ ⟨.bound 9,.bound 8,.bound 7,.bound 6⟩
      (.bound 1) (.bound 8) (.bound 0))
      (Project.Formula.forallMem (.bound 5)
        (.imp (.disj (Project.Formula.extensionalEq (.bound 0) (.bound 1))
            (ancestorFormula ⟨.bound 21,.bound 20,.bound 19,.bound 18,.bound 17⟩ (.bound 6) (.bound 4) (.bound 0) (.bound 1)))
          (.imp (.mem (.bound 9) (.bound 0))
            (.forallE (.imp (memPairFormula (.bound 6) (.bound 1) (.bound 0)) (.mem (.bound 4) (.bound 0))))))))
  freeClosed := by
    have hC : (⟨.bound 20,.bound 19,.bound 18,.bound 17,.bound 16⟩ : ExpressionData (Project.Term 21)).Closed := ⟨rfl,rfl,rfl,rfl,rfl⟩
    have hC' : (⟨.bound 21,.bound 20,.bound 19,.bound 18,.bound 17⟩ : ExpressionData (Project.Term 22)).Closed := ⟨rfl,rfl,rfl,rfl,rfl⟩
    have hMap := parentCopyFormula_freeClosed hC (T := ⟨.bound 15,.bound 14,.bound 13,.bound 12,.bound 11,.bound 10⟩)
      ⟨rfl,rfl,rfl,rfl,rfl,rfl⟩ (A := ⟨.bound 9,.bound 8,.bound 7,.bound 6⟩) ⟨rfl,rfl,rfl,rfl⟩ (.bound 1) (.bound 8) (.bound 0) rfl rfl rfl
    have hAnc := ancestorFormula_freeClosed hC' (.bound 6) (.bound 4) (.bound 0) (.bound 1) rfl rfl rfl rfl
    simp [Project.Formula.forallMem,Definitional.Formula.FreeClosed,Project.Formula.extensionalEq,memPairFormula,
      codeFormula,pairFormula,Project.Formula.existsMem,hMap,hAnc]

private theorem seamHSchema_iff {M : SetTheory.Structure.{u}} (he : Extensional M)
    (C : ExpressionData M.Domain) (T : MatrixArithmetic M.Domain) (A : CopyCoordinates.Context M.Domain)
    (Yw Yh G t b : M.Domain) :
    Project.Formula.satisfies ((seamHEnv C T A Yw Yh G t).push b) seamHSchema.body ↔
      ∀ w, M.mem w Yw → ParentCopy M C T A b A.root w → ∀ a, M.mem a Yw → (a=w ∨ Ancestor M C Yw G a w) →
        M.mem A.root a → ∀ h, MemPair M Yh a h → M.mem t h := by
  simp only [seamHSchema,Project.Formula.satisfies_forallMem_iff,Project.Formula.satisfies_imp_iff,
    parentCopyFormula_iff he,Project.Formula.satisfies_disj_iff,Project.Formula.satisfies_extensionalEq_iff_eq he,
    ancestorFormula_iff he,Project.Formula.satisfies_mem_iff,Project.Formula.satisfies_forall_iff,memPairFormula_iff he]
  rfl

/-- 目标低行中root任意副本w链上严格位于root之后的列，高度都严格大于阈值t（t-1为该低行）。 -/
theorem Copies.canon_seam_heights_low_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {D : Context M.Domain} (hD : D.Valid M C) {Y : Data M.Domain} (hY : Y.Valid M C) {n : M.Domain}
    (hCopy : Copies M C T D n Y) {m : M.Domain} {R : RowStateSpace M.Domain} {V P H : M.Domain}
    (hRun : RowRun M C m R V P H) (hFrom : FromRun M C m R V H D.mountain) {r t G : M.Domain}
    (hLow : M.mem r D.floor) (hSucc : M.SuccessorOf t r) (hTF : t=D.floor ∨ M.mem t D.floor)
    (hG : MemPair M Y.parents r G) {b w a h : M.Domain}
    (hMap : ParentCopy M C T D.coordinates b D.coordinates.root w) (hw : M.mem w Y.width)
    (ha : M.mem a Y.width) (hAW : a=w ∨ Ancestor M C Y.width G a w) (hRootA : M.mem D.coordinates.root a)
    (hH : MemPair M Y.heights a h) : M.mem t h := by
  have hω := omega_isOrdinal_d hM hC.omega
  have hr := nat_mem_omega hM hC (hD.floor_nat hM.1) hLow
  obtain ⟨F,_,hF⟩ := hD.mountain.parents.total r hr
  have hFF := hD.mountain.forest r F hF
  have hGF := hY.forest r G hG
  have hRootNot : ¬M.mem D.coordinates.root D.coordinates.root := nat_irrefl hM _
  have hLastNot : ¬M.mem D.coordinates.last D.coordinates.root :=
    nat_not_lt_of_le hM hC hD.coordinates.last (Or.inr hD.coordinates.below)
  have hRootLast := source_root_ancestor_last_d hM hC hD hRun hFrom hF (Or.inr hLow)
  obtain ⟨hl,_,hHL,hFloorL,_⟩ := hD.rise
  have hAll := natural_induction_d hM seamHSchema (seamHEnv C T D.coordinates Y.width Y.heights G t) hC.omega
    (fun z hz => (seamHSchema_iff hM.1 C T D.coordinates Y.width Y.heights G t z).mpr (by
      intro w _ hMap a _ hAW hRootA h _
      have hZ := hM.1.eq_of_same_members z C.zero (fun x => iff_of_false (hz x) (hC.zero_empty x))
      subst hZ
      have hw0 := encode_unique hM.1 hT (encode_zero_d hM hC hT hD.coordinates hD.coordinates.root)
        ((parent_copy_bad_iff hRootNot).mp hMap)
      subst hw0
      rcases hAW with he | hAnc
      · exact False.elim (hRootNot (he ▸ hRootA))
      · exact False.elim (hRootNot (nat_lt_trans hM hC hD.coordinates.root hRootA hAnc.1))))
    (fun block hBlock ih next hSuccB => (seamHSchema_iff hM.1 C T D.coordinates Y.width Y.heights G t next).mpr (by
      intro w hw hMap a ha hAW hRootA h hH
      obtain ⟨boundary,_,hWidth⟩ := encode_exists_d hM hC hT hD.coordinates hD.coordinates.last hBlock
      have hwEq := encode_unique hM.1 hT ((parent_copy_bad_iff hRootNot).mp hMap)
        (width_is_next_cut_d hM hC hT hD.coordinates hSuccB hWidth)
      have hWidthW : Width M C T D.coordinates block w := hwEq.symm ▸ hWidth
      obtain ⟨cut,_,hCut⟩ := encode_exists_d hM hC hT hD.coordinates hD.coordinates.root hBlock
      have hRootCopy : ParentCopy M C T D.coordinates block D.coordinates.root cut := (parent_copy_bad_iff hRootNot).mpr hCut
      have hCutW := cut_lt_width_d hM hC hT hD.coordinates hWidthW hCut
      have hCutY := (hω.mem hY.width).transitive w hw cut hCutW
      have hIH := (seamHSchema_iff hM.1 C T D.coordinates Y.width Y.heights G t block).mp ih cut hCutY hRootCopy
      have hLastCopy : ParentCopy M C T D.coordinates block D.coordinates.last w := (parent_copy_bad_iff hLastNot).mpr hWidthW
      rcases hAW with he | hAnc
      · subst he
        have hHW := (hCopy.canon_copy_heights_d hM hC hT hD (Or.inr hD.coordinates.below) (Or.inl rfl) hWidthW
          (hCopy.width ▸ ha) hHL).mp hH
        rcases hHW with ⟨_,hLift⟩ | ⟨hNot,_⟩
        · have hLe := hLift.base_le_d hM hC hT
          have hhNat : M.mem h C.omega := (hY.heights.bounds hM.1 hH).2
          exact nat_lt_of_le_of_lt hM hC hhNat hTF (nat_lt_of_lt_of_le hM hC hhNat hFloorL hLe)
        · exact False.elim (hNot (in_cone_last hD))
      · obtain ⟨J,hJ,hRows⟩ := parent_copy_graph_exists_d hM hC hT hD.coordinates hBlock
        have hEdge : ∀ d u' v, (d=D.coordinates.last ∨ Ancestor M C D.mountain.width F d D.coordinates.last) →
            d≠D.coordinates.root → MemPair M J d u' → MemPair M G u' v → ∃ p, MemPair M F d p ∧ MemPair M J p v := by
          intro d u' v hChain hne hDU hUV
          have hdLast : d=D.coordinates.last ∨ M.mem d D.coordinates.last := hChain.imp id (fun h => h.1)
          obtain ⟨p,hP,hMapP⟩ := (hCopy.canon_low_parent_iff_d hM hC hT hD hLow hdLast hne ((hRows d u').mp hDU)
            (hCopy.width ▸ (hGF.bounds hM.1 hUV).1)).mp ((canon_row_parent_iff hM.1 hY hG).mpr hUV)
          exact ⟨p,(canon_row_parent_iff hM.1 hD.mountain hF).mp hP,(hRows p v).mpr hMapP⟩
        rcases ancestor_preimage_d (y₀ := D.coordinates.root) hM hC hFF hGF hEdge ((hRows _ w).mpr hLastCopy) hAnc with
          ⟨q,hQL,hJQ⟩ | ⟨_,w',hJW,hAW'⟩
        · have hqNat := (hJ.graph.bounds hM.1 hJQ).1
          have hMapQ := (hRows q a).mp hJQ
          rcases (omega_isOrdinal_d hM hC.omega).wellOrder.linear.compare q hqNat D.coordinates.root hD.coordinates.root with
            he | hqr | hrq
          · have he := hM.1.eq_of_same_members q _ he
            subst he
            have haCut := canon_parent_copy_fun hM hC hT hD.coordinates hMapQ hRootCopy
            subst haCut
            exact hIH a ha (Or.inl rfl) hRootA h hH
          · have haq := (parent_copy_good_iff hMapQ.2.1 hqNat hqr).mp hMapQ
            subst haq
            exact False.elim (hRootNot (nat_lt_trans hM hC hD.coordinates.root hRootA hqr))
          · obtain ⟨hq,_,hHQ⟩ := hD.mountain.heights.total q (hQL.bounds hM.1).1
            have hTQ := canon_seam_intermediate_d hM hC hD hRun hFrom hSucc hTF hF hQL hrq hHQ
            have hHeight := ((hCopy.heights a h).mp hH).2
            have hLe := hHeight.parent_copy_ge_d hM hC hT hD hQL.1 hMapQ hHQ
            exact nat_lt_of_lt_of_le hM hC (hY.heights.bounds hM.1 hH).2 hTQ hLe
        · have hw' := canon_parent_copy_fun hM hC hT hD.coordinates ((hRows _ w').mp hJW) hRootCopy
          subst hw'
          exact hIH a ha hAW' hRootA h hH))
  exact (seamHSchema_iff hM.1 C T D.coordinates Y.width Y.heights G t b).mp (hAll b hMap.2.1) w hw hMap a ha hAW hRootA h hH

end KP1Y.OneYFinite.CopiedMountain.Lower
