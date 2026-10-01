import KP1Y.OneYBadRoot
import KP1Y.OneYSelectionOrder

/-! 真实数值行/提取层之间的祖先运输及顶部根几何。 -/
namespace KP1Y.OneYFinite
open YesMetaZFC YesMetaZFC.SetTheory YesMetaZFC.SetTheory.Definitional
open KP1Y.Kuratowski KP1Y.Functions KP1Y.Naturals KP1Y.Bounded
universe u

private def rowLowerTerms : ExpressionData (Project.Term 17) := ⟨.bound 16,.bound 15,.bound 14,.bound 13,.bound 12⟩

private def rowLowerSchema : Project.UnarySchema 14 where
  body := Project.Formula.forallMem (.bound 8) (Project.Formula.forallMem (.bound 8)
    (.imp (rowAtFormula (.bound 8) (.bound 7) (.bound 2) (.bound 1) (.bound 0))
      (.imp (.disj (Project.Formula.extensionalEq (.bound 6) (.bound 2)) (.mem (.bound 6) (.bound 2)))
        (.imp (ancestorFormula rowLowerTerms (.bound 11) (.bound 0) (.bound 4) (.bound 3))
          (ancestorFormula rowLowerTerms (.bound 11) (.bound 5) (.bound 4) (.bound 3))))))
  freeClosed := by
    have hC : rowLowerTerms.Closed := ⟨rfl,rfl,rfl,rfl,rfl⟩
    have hAt := rowAtFormula_freeClosed (n := 17) (.bound 8) (.bound 7) (.bound 2) (.bound 1) (.bound 0) rfl rfl rfl rfl rfl
    have hIn := ancestorFormula_freeClosed hC (.bound 11) (.bound 0) (.bound 4) (.bound 3) rfl rfl rfl rfl
    have hOut := ancestorFormula_freeClosed hC (.bound 11) (.bound 5) (.bound 4) (.bound 3) rfl rfl rfl rfl
    simp [Project.Formula.forallMem,Definitional.Formula.FreeClosed,hAt,hIn,hOut]

private def rowLowerEnv {M : SetTheory.Structure.{u}} (C : ExpressionData M.Domain) (m : M.Domain) (R : RowStateSpace M.Domain)
    (H i Pi a c : M.Domain) : Env M 14 :=
  (((((((((((((oneEnv C.omega).push C.zero).push C.one).push C.sequences).push C.expressions).push m).push R.values).push R.forests).push R.states).push H).push i).push Pi).push a).push c

private theorem rowLowerSchema_iff {M : SetTheory.Structure.{u}} (he : Extensional M) (C : ExpressionData M.Domain)
    (m : M.Domain) (R : RowStateSpace M.Domain) (H i Pi a c j : M.Domain) :
    Project.Formula.satisfies ((rowLowerEnv C m R H i Pi a c).push j) rowLowerSchema.body ↔
      ∀ W, M.mem W R.values → ∀ Q, M.mem Q R.forests → RowAt M R.states H j W Q →
        (i=j ∨ M.mem i j) → Ancestor M C m Q a c → Ancestor M C m Pi a c := by
  simp only [rowLowerSchema,Project.Formula.satisfies_forallMem_iff,Project.Formula.satisfies_imp_iff,rowAtFormula_iff he,
    Project.Formula.satisfies_disj_iff,Project.Formula.satisfies_extensionalEq_iff_eq he,Project.Formula.satisfies_mem_iff,ancestorFormula_iff he]
  rfl

theorem RowRun.ancestor_lower_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory) {C : ExpressionData M.Domain} (hC : C.Valid M)
    {m : M.Domain} {R : RowStateSpace M.Domain} {V P H i j Wi Pi Wj Pj a c : M.Domain} (h : RowRun M C m R V P H)
    (hI : RowAt M R.states H i Wi Pi) (hJ : RowAt M R.states H j Wj Pj) (hLe : i=j ∨ M.mem i j)
    (hAnc : Ancestor M C m Pj a c) : Ancestor M C m Pi a c := by
  have hAll := natural_induction_d hM rowLowerSchema (rowLowerEnv C m R H i Pi a c) hC.omega
    (fun z hz => (rowLowerSchema_iff hM.1 C m R H i Pi a c z).mpr (by
      intro W _ Q _ hAt hLe hAnc
      have hiz := hLe.resolve_right (hz i)
      subst i
      have hPiQ := (h.at_unique hM.1 hI hAt).2
      exact hPiQ.symm ▸ hAnc))
    (fun j hj ih j' hs => (rowLowerSchema_iff hM.1 C m R H i Pi a c j').mpr (by
      intro W _ Q _ hAt hLe hAnc
      rcases hLe with he | hLess
      · subst i
        have hPiQ := (h.at_unique hM.1 hI hAt).2
        exact hPiQ.symm ▸ hAnc
      · have hiLe : i=j ∨ M.mem i j := by
          rcases (hs i).mp hLess with hij | he
          · exact Or.inr hij
          · exact Or.inl (hM.1.eq_of_same_members i j he)
        obtain ⟨W0,Q0,hAt0⟩ := h.at_exists_d hj
        have hRow0 := h.at_numeric_d hM hC hAt0
        have hOld := (h.at_next hM.1 hs hAt0 hAt).selection.ancestor_inherited_d hM hC hAnc
        exact (rowLowerSchema_iff hM.1 C m R H i Pi a c j).mp ih W0 ((h.space.values W0).mpr hRow0.values)
          Q0 ((h.space.forests Q0).mpr hRow0.forest) hAt0 hiLe hOld))
  have hj : M.mem j C.omega := by
    obtain ⟨_,_,hAt,_⟩ := hJ
    exact (h.graph.bounds hM.1 hAt).1
  have hRowJ := h.at_numeric_d hM hC hJ
  exact (rowLowerSchema_iff hM.1 C m R H i Pi a c j).mp (hAll j hj) Wj ((h.space.values Wj).mpr hRowJ.values)
    Pj ((h.space.forests Pj).mpr hRowJ.forest) hJ hLe hAnc

theorem RowRun.ancestor_base_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory) {C : ExpressionData M.Domain} (hC : C.Valid M)
    {m : M.Domain} {R : RowStateSpace M.Domain} {V P H j W Q a c : M.Domain} (h : RowRun M C m R V P H)
    (hAt : RowAt M R.states H j W Q) (hAnc : Ancestor M C m Q a c) : Ancestor M C m P a c := by
  have hj : M.mem j C.omega := by
    obtain ⟨_,_,hAt,_⟩ := hAt
    exact (h.graph.bounds hM.1 hAt).1
  have hLe : C.zero=j ∨ M.mem C.zero j := by
    classical
    by_cases he : j=C.zero
    · exact Or.inl he.symm
    · exact Or.inr ((hC.zero_mem_iff hM hj).mpr he)
  exact h.ancestor_lower_d hM hC (h.initial_row_at_d hM) hAt hLe hAnc

theorem RowRun.parent_refines_base_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory) {C : ExpressionData M.Domain} (hC : C.Valid M)
    {m : M.Domain} {R : RowStateSpace M.Domain} {V P H j W Q : M.Domain} (h : RowRun M C m R V P H)
    (hAt : RowAt M R.states H j W Q) : ForestRefines M C m Q P := by
  intro c p hParent
  exact h.ancestor_base_d hM hC hAt (ancestor_direct_d hM hC (h.at_numeric_d hM hC hAt).forest hParent)

theorem PseudoForest.refines_base_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory) {C : ExpressionData M.Domain} (hC : C.Valid M)
    {m : M.Domain} {R : RowStateSpace M.Domain} {V P H Heights F : M.Domain}
    (hRun : RowRun M C m R V P H) (hF : PseudoForest M C m R H Heights F) : ForestRefines M C m F P := by
  intro c p hParent
  obtain ⟨_,_,_,_,r,_,_,_,_,W,_,Q,_,hRow,hAnc,_⟩ := ((hF.parents c p).mp hParent).2.1
  exact hRun.ancestor_base_d hM hC hRow hAnc

theorem Extraction.ancestor_base_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory) {C : ExpressionData M.Domain} (hC : C.Valid M)
    {m V P Top Q a c : M.Domain} (h : Extraction M C m V P Top Q) (hAnc : Ancestor M C m Q a c) : Ancestor M C m P a c := by
  obtain ⟨_,_,_,_,hRun,_,_,hF,hSelected⟩ := h
  have hIn := hSelected.ancestor_inherited_d hM hC hAnc
  exact ancestor_refines_d hM hC hRun.base.forest (hF.refines_base_d hM hC hRun) hIn

theorem Extraction.refines_base_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory) {C : ExpressionData M.Domain} (hC : C.Valid M)
    {m V P Top Q : M.Domain} (h : Extraction M C m V P Top Q) : ForestRefines M C m Q P := by
  intro c p hParent
  exact h.ancestor_base_d hM hC (ancestor_direct_d hM hC h.numeric_row.forest hParent)

theorem LayerRun.ancestor_lower_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory) {C : ExpressionData M.Domain} (hC : C.Valid M)
    {m : M.Domain} {L : LayerStateSpace M.Domain} {V P H i j Wi Pi Wj Pj a c : M.Domain} (h : LayerRun M C m L V P H)
    (hI : RowAt M L.states H i Wi Pi) (hJ : RowAt M L.states H j Wj Pj) (hLe : i=j ∨ M.mem i j)
    (hAnc : Ancestor M C m Pj a c) : Ancestor M C m Pi a c := by
  have hAll := natural_induction_d hM rowLowerSchema (rowLowerEnv C m ⟨L.rows.values,L.rows.forests,L.states⟩ H i Pi a c) hC.omega
    (fun z hz => (rowLowerSchema_iff hM.1 C m ⟨L.rows.values,L.rows.forests,L.states⟩ H i Pi a c z).mpr (by
      intro W _ Q _ hAt hLe hAnc
      have hiz := hLe.resolve_right (hz i)
      subst i
      have hPiQ := (h.at_unique hM.1 hI hAt).2
      exact hPiQ.symm ▸ hAnc))
    (fun j hj ih j' hs => (rowLowerSchema_iff hM.1 C m ⟨L.rows.values,L.rows.forests,L.states⟩ H i Pi a c j').mpr (by
      intro W _ Q _ hAt hLe hAnc
      rcases hLe with he | hLess
      · subst i
        have hPiQ := (h.at_unique hM.1 hI hAt).2
        exact hPiQ.symm ▸ hAnc
      · have hiLe : i=j ∨ M.mem i j := by
          rcases (hs i).mp hLess with hij | he
          · exact Or.inr hij
          · exact Or.inl (hM.1.eq_of_same_members i j he)
        obtain ⟨W0,Q0,hAt0⟩ := h.at_exists_d hj
        have hRow0 := h.at_rooted hM.1 hAt0
        have hOld := (h.at_next hM.1 hs hAt0 hAt).ancestor_base_d hM hC hAnc
        exact (rowLowerSchema_iff hM.1 C m ⟨L.rows.values,L.rows.forests,L.states⟩ H i Pi a c j).mp ih W0 ((h.space.rows.values W0).mpr hRow0.row.values)
          Q0 ((h.space.rows.forests Q0).mpr hRow0.row.forest) hAt0 hiLe hOld))
  have hj : M.mem j C.omega := by
    obtain ⟨_,_,hAt,_⟩ := hJ
    exact (h.graph.bounds hM.1 hAt).1
  have hRowJ := h.at_rooted hM.1 hJ
  exact (rowLowerSchema_iff hM.1 C m ⟨L.rows.values,L.rows.forests,L.states⟩ H i Pi a c j).mp (hAll j hj) Wj ((h.space.rows.values Wj).mpr hRowJ.row.values)
    Pj ((h.space.rows.forests Pj).mpr hRowJ.row.forest) hJ hLe hAnc

theorem root_ancestor_iff_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory) {C : ExpressionData M.Domain} (hC : C.Valid M)
    {m P a c q : M.Domain} (hP : Forest M C.omega m P) (hAnc : Ancestor M C m P a c) :
    Root M C m P c q ↔ Root M C m P a q := by
  constructor
  · rintro ⟨hq,hNo,hReach⟩
    refine ⟨hq,hNo,?_⟩
    rcases hReach with he | hQC
    · subst q
      exact False.elim (no_ancestor_of_no_parent_d hM hC hP hNo hAnc)
    · rcases ancestor_common_target_compare_d hM hC hP hQC hAnc with he | hQA | hAQ
      · exact Or.inl he
      · exact Or.inr hQA
      · exact False.elim (no_ancestor_of_no_parent_d hM hC hP hNo hAQ)
  · rintro ⟨hq,hNo,he | hQA⟩
    · exact ⟨hq,hNo,Or.inr (he.symm ▸ hAnc)⟩
    · exact ⟨hq,hNo,Or.inr (ancestor_trans_d hM hC hP hQA hAnc)⟩

theorem RowRun.root_through_higher_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory) {C : ExpressionData M.Domain} (hC : C.Valid M)
    {m : M.Domain} {R : RowStateSpace M.Domain} {V P H i j Wi Pi Wj Pj c q a : M.Domain} (h : RowRun M C m R V P H)
    (hI : RowAt M R.states H i Wi Pi) (hJ : RowAt M R.states H j Wj Pj) (hLe : i=j ∨ M.mem i j)
    (hRoot : Root M C m Pj c q) : Root M C m Pi c a ↔ Root M C m Pi q a := by
  rcases hRoot.2.2 with he | hAnc
  · subst q
    exact Iff.rfl
  · exact root_ancestor_iff_d hM hC (h.at_numeric_d hM hC hI).forest (h.ancestor_lower_d hM hC hI hJ hLe hAnc)

theorem TopValueGraph.at_height_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory) {C : ExpressionData M.Domain}
    {m : M.Domain} {R : RowStateSpace M.Domain} {V P H Heights Top c height U F v : M.Domain}
    (hRun : RowRun M C m R V P H) (hHeights : HeightGraph M C m R V H Heights) (hTop : TopValueGraph M C m R H Heights Top)
    (hHeight : MemPair M Heights c height) (hAt : RowAt M R.states H height U F) (hValue : MemPair M Top c v) : MemPair M U c v := by
  obtain ⟨height',_,hHeight',W,_,Q,_,hRow,hValue⟩ := (hTop.rows c v).mp hValue
  have hhh := hHeights.graph.unique c height' height hHeight' hHeight
  subst height'
  have hWU := (hRun.at_unique hM.1 hRow hAt).1
  subst W
  exact hValue

theorem PseudoForest.parent_row_ancestor_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory) {C : ExpressionData M.Domain} (hC : C.Valid M)
    {m : M.Domain} {R : RowStateSpace M.Domain} {V P H Heights F c p hc r U Q : M.Domain}
    (hRun : RowRun M C m R V P H) (hHeights : HeightGraph M C m R V H Heights) (hF : PseudoForest M C m R H Heights F)
    (hParent : MemPair M F c p) (hHeight : MemPair M Heights c hc) (hPrev : PreviousLength M C.omega C.zero hc r)
    (hAt : RowAt M R.states H r U Q) : Ancestor M C m Q p c := by
  obtain ⟨hc',_,_,_,r',_,hHeight',_,hPrev',W,_,Q',_,hRow,hAnc,_⟩ := ((hF.parents c p).mp hParent).2.1
  have hhh := hHeights.graph.unique c hc' hc hHeight' hHeight
  subst hc'
  have hrr := previous_length_unique_d hM hC hPrev' hPrev
  subst r'
  have hQQ := (hRun.at_unique hM.1 hRow hAt).2
  subst Q'
  exact hAnc

private def pseudoHeightTerms : ExpressionData (Project.Term 12) := ⟨.bound 11,.bound 10,.bound 9,.bound 8,.bound 7⟩

private def pseudoHeightSchema : Project.UnarySchema 8 where
  body := Project.Formula.forallMem (.bound 3) (Project.Formula.forallMem (.bound 9) (Project.Formula.forallMem (.bound 10)
    (.imp (memPairFormula (.bound 4) (.bound 2) (.bound 1)) (.imp (memPairFormula (.bound 4) (.bound 3) (.bound 0))
      (.imp (ancestorFormula pseudoHeightTerms (.bound 6) (.bound 5) (.bound 2) (.bound 3))
        (.disj (Project.Formula.extensionalEq (.bound 1) (.bound 0)) (.mem (.bound 1) (.bound 0))))))))
  freeClosed := by
    have hC : pseudoHeightTerms.Closed := ⟨rfl,rfl,rfl,rfl,rfl⟩
    have hAnc := ancestorFormula_freeClosed hC (.bound 6) (.bound 5) (.bound 2) (.bound 3) rfl rfl rfl rfl
    simp [Project.Formula.forallMem,Definitional.Formula.FreeClosed,memPairFormula,codeFormula,pairFormula,Project.Formula.existsMem,hAnc]

private def pseudoHeightEnv {M : SetTheory.Structure.{u}} (C : ExpressionData M.Domain) (m F Heights : M.Domain) : Env M 8 :=
  (((((((oneEnv C.omega).push C.zero).push C.one).push C.sequences).push C.expressions).push m).push F).push Heights

private theorem pseudoHeightSchema_iff {M : SetTheory.Structure.{u}} (he : Extensional M) (C : ExpressionData M.Domain) (m F Heights c : M.Domain) :
    Project.Formula.satisfies ((pseudoHeightEnv C m F Heights).push c) pseudoHeightSchema.body ↔
      ∀ a, M.mem a m → ∀ ha, M.mem ha C.omega → ∀ hc, M.mem hc C.omega →
        MemPair M Heights a ha → MemPair M Heights c hc → Ancestor M C m F a c → ha=hc ∨ M.mem ha hc := by
  simp only [pseudoHeightSchema,Project.Formula.satisfies_forallMem_iff,Project.Formula.satisfies_imp_iff,memPairFormula_iff he,
    ancestorFormula_iff he,Project.Formula.satisfies_disj_iff,Project.Formula.satisfies_extensionalEq_iff_eq he,Project.Formula.satisfies_mem_iff]
  rfl

theorem PseudoForest.ancestor_height_le_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory) {C : ExpressionData M.Domain} (hC : C.Valid M)
    {m : M.Domain} {R : RowStateSpace M.Domain} {V H Heights F a c ha hc : M.Domain}
    (hHeights : HeightGraph M C m R V H Heights) (hF : PseudoForest M C m R H Heights F)
    (hAnc : Ancestor M C m F a c) (hHA : MemPair M Heights a ha) (hHC : MemPair M Heights c hc) : ha=hc ∨ M.mem ha hc := by
  have hAll := KP1Y.induction_d hM pseudoHeightSchema (pseudoHeightEnv C m F Heights) (by
    intro c ih
    apply (pseudoHeightSchema_iff hM.1 C m F Heights c).mpr
    intro a haM ha haNat hc hcNat hHA hHC hAnc
    obtain ⟨p,hParent,hAP⟩ := ancestor_parent_cases_d hM hC hF.forest hAnc
    obtain ⟨hp,hpNat,hHP⟩ := hHeights.graph.total p (hF.forest.bounds hM.1 hParent).2
    have hpc : hp=hc ∨ M.mem hp hc := (hF.parent_heights hHeights hParent hHC hHP).imp id Structure.SuccessorOf.predecessor_mem
    have hap : ha=hp ∨ M.mem ha hp := by
      rcases hAP with he | hAP
      · subst a
        exact Or.inl (hHeights.graph.unique p ha hp hHA hHP)
      · exact (pseudoHeightSchema_iff hM.1 C m F Heights p).mp (ih p (hF.forest.left c p hParent)) a haM ha haNat hp hpNat hHA hHP hAP
    rcases hap with he | hap
    · exact he.symm ▸ hpc
    · rcases hpc with he | hpc
      · exact Or.inr (he ▸ hap)
      · exact Or.inr (((omega_isOrdinal_d hM hC.omega).mem hcNat).transitive hp hpc ha hap))
  exact (pseudoHeightSchema_iff hM.1 C m F Heights c).mp (hAll c) a (hAnc.bounds hM.1).1
    ha (hHeights.graph.bounds hM.1 hHA).2 hc (hHeights.graph.bounds hM.1 hHC).2 hHA hHC hAnc

private def sameHeightTerms : ExpressionData (Project.Term 12) := ⟨.bound 11,.bound 10,.bound 9,.bound 8,.bound 7⟩

private def sameHeightSchema : Project.UnarySchema 11 where
  body := .imp (memPairFormula (.bound 4) (.bound 0) (.bound 2))
    (.imp (ancestorFormula sameHeightTerms (.bound 6) (.bound 5) (.bound 1) (.bound 0))
      (ancestorFormula sameHeightTerms (.bound 6) (.bound 3) (.bound 1) (.bound 0)))
  freeClosed := by
    have hC : sameHeightTerms.Closed := ⟨rfl,rfl,rfl,rfl,rfl⟩
    have hIn := ancestorFormula_freeClosed hC (.bound 6) (.bound 5) (.bound 1) (.bound 0) rfl rfl rfl rfl
    have hOut := ancestorFormula_freeClosed hC (.bound 6) (.bound 3) (.bound 1) (.bound 0) rfl rfl rfl rfl
    simp [Definitional.Formula.FreeClosed,memPairFormula,codeFormula,pairFormula,Project.Formula.forallMem,Project.Formula.existsMem,hIn,hOut]

theorem PseudoForest.same_height_row_ancestor_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory) {C : ExpressionData M.Domain} (hC : C.Valid M)
    {m : M.Domain} {R : RowStateSpace M.Domain} {V P H Heights F a c height r U Q : M.Domain}
    (hRun : RowRun M C m R V P H) (hHeights : HeightGraph M C m R V H Heights) (hF : PseudoForest M C m R H Heights F)
    (hAnc : Ancestor M C m F a c) (hHA : MemPair M Heights a height) (hHC : MemPair M Heights c height)
    (hPrev : PreviousLength M C.omega C.zero height r) (hAt : RowAt M R.states H r U Q) : Ancestor M C m Q a c := by
  let e := (((pseudoHeightEnv C m F Heights).push Q).push height).push a
  have hφ (c : M.Domain) : Project.Formula.satisfies (e.push c) sameHeightSchema.body ↔
      MemPair M Heights c height → Ancestor M C m F a c → Ancestor M C m Q a c := by
    simp only [sameHeightSchema,Project.Formula.satisfies_imp_iff,memPairFormula_iff hM.1,ancestorFormula_iff hM.1]
    rfl
  have hAll := KP1Y.induction_d hM sameHeightSchema e (by
    intro c ih
    apply (hφ c).mpr
    intro hHC hAnc
    obtain ⟨p,hParent,hAP⟩ := ancestor_parent_cases_d hM hC hF.forest hAnc
    obtain ⟨hp,hpNat,hHP⟩ := hHeights.graph.total p (hF.forest.bounds hM.1 hParent).2
    have hpc : hp=height ∨ M.mem hp height := (hF.parent_heights hHeights hParent hHC hHP).imp id Structure.SuccessorOf.predecessor_mem
    have hap : height=hp ∨ M.mem height hp := by
      rcases hAP with he | hAP
      · subst a
        exact Or.inl (hHeights.graph.unique p height hp hHA hHP)
      · exact hF.ancestor_height_le_d hM hC hHeights hAP hHA hHP
    have hpHeight : hp=height := by
      rcases hpc with he | hpc
      · exact he
      · rcases hap with he | hap
        · exact False.elim (SetTheory.KP.mem_irrefl_d (KP1Y.models_weakKP hM) hp (he ▸ hpc))
        · exact False.elim (SetTheory.KP.mem_irrefl_d (KP1Y.models_weakKP hM) hp
            (((omega_isOrdinal_d hM hC.omega).mem hpNat).transitive height hap hp hpc))
    have hPC := hF.parent_row_ancestor_d hM hC hRun hHeights hParent hHC hPrev hAt
    rcases hAP with he | hAP
    · exact he.symm ▸ hPC
    · have hAQ := (hφ p).mp (ih p (hF.forest.left c p hParent)) (hpHeight ▸ hHP) hAP
      exact ancestor_trans_d hM hC (hRun.at_numeric_d hM hC hAt).forest hAQ hPC)
  exact (hφ c).mp (hAll c) hHC hAnc

theorem TopValueGraph.same_height_pseudo_antitone_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {m : M.Domain} {R : RowStateSpace M.Domain}
    {V P H Heights Top F a c height x y : M.Domain} (hRun : RowRun M C m R V P H)
    (hHeights : HeightGraph M C m R V H Heights) (hTop : TopValueGraph M C m R H Heights Top)
    (hF : PseudoForest M C m R H Heights F) (hPositive : ∀ i v, MemPair M V i v → M.mem C.zero v)
    (hAnc : Ancestor M C m F a c) (hHA : MemPair M Heights a height) (hHC : MemPair M Heights c height)
    (hX : MemPair M Top a x) (hY : MemPair M Top c y) : y=x ∨ M.mem y x := by
  have hh := (hHeights.graph.bounds hM.1 hHC).2
  rcases natural_cases hM hC.omega hh with hEmpty | ⟨r,hr,hs⟩
  · have hHeightZero := hM.1.eq_of_same_members height C.zero (fun z => iff_of_false (hEmpty z) (hC.zero_empty z))
    have hNo := (hF.no_parent_iff_height_zero_d hM hC hRun hHeights hPositive hHC).mpr hHeightZero
    exact False.elim (no_ancestor_of_no_parent_d hM hC hF.forest hNo hAnc)
  · obtain ⟨U,Q,hAt⟩ := hRun.at_exists_d hr
    obtain ⟨U',Q',hAt'⟩ := hRun.at_exists_d hh
    have hNext := hRun.at_next hM.1 hs hAt hAt'
    have hAncRow := hF.same_height_row_ancestor_d hM hC hRun hHeights hAnc hHA hHC ⟨hr,Or.inr hs⟩ hAt
    have hXa := hTop.at_height_d hM hRun hHeights hHA hAt' hX
    have hYc := hTop.at_height_d hM hRun hHeights hHC hAt' hY
    obtain ⟨original,_,hOriginal⟩ := hRun.base.values.total c (hHeights.graph.bounds hM.1 hHC).1
    have hNo := hRun.top_parent_none_d hM hC hOriginal (hPositive c original hOriginal) ((hHeights.rows c height).mp hHC).2 hAt'
    obtain ⟨originalA,_,hOriginalA⟩ := hRun.base.values.total a (hHeights.graph.bounds hM.1 hHA).1
    have hPosX := hTop.positive_d hM hC hRun hHeights hOriginalA (hPositive a originalA hOriginalA) hX
    have hx := (hTop.graph.bounds hM.1 hX).2
    have hy := (hTop.graph.bounds hM.1 hY).2
    rcases (omega_isOrdinal_d hM hC.omega).wellOrder.linear.compare y hy x hx with he | hLess | hMore
    · exact Or.inl (hM.1.eq_of_same_members y x he)
    · exact Or.inr hLess
    · exact False.elim ((hNext.selection.no_parent_iff_d hM hC).mp hNo a ⟨hAncRow,x,hx,y,hy,hXa,hYc,hMore,hPosX⟩)

theorem parent_candidate_equal_parent_iff_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {positive : Bool} {m F V c p v a : M.Domain}
    (hF : Forest M C.omega m F) (hV : Graph M V m C.omega) (hParent : MemPair M F c p)
    (hCValue : MemPair M V c v) (hPValue : MemPair M V p v) :
    ParentCandidate positive M C m F V c a ↔ ParentCandidate positive M C m F V p a := by
  constructor
  · rintro ⟨hAnc,x,hx,y,_,hAX,hCY,hXY,hPos⟩
    have hyv := hV.unique c y v hCY hCValue
    subst y
    obtain ⟨q,hQ,hAQ⟩ := ancestor_parent_cases_d hM hC hF hAnc
    have hqp := hF.unique c q p hQ hParent
    subst q
    rcases hAQ with he | hAP
    · subst a
      have hxv := hV.unique p x v hAX hPValue
      exact False.elim (SetTheory.KP.mem_irrefl_d (KP1Y.models_weakKP hM) v (hxv ▸ hXY))
    · exact ⟨hAP,x,hx,v,(hV.bounds hM.1 hPValue).2,hAX,hPValue,hXY,hPos⟩
  · rintro ⟨hAP,x,hx,y,_,hAX,hPY,hXY,hPos⟩
    have hyv := hV.unique p y v hPY hPValue
    subst y
    exact ⟨ancestor_step_d hM hC hF hAP hParent,x,hx,v,(hV.bounds hM.1 hCValue).2,hAX,hCValue,hXY,hPos⟩

theorem Selects.parent_rows_of_equal_parent_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {positive : Bool} {m F V Q c p v : M.Domain}
    (h : Selects positive M C m F V Q) (hParent : MemPair M F c p) (hCValue : MemPair M V c v) (hPValue : MemPair M V p v) :
    ∀ a, MemPair M Q c a ↔ MemPair M Q p a := by
  have hCand (a : M.Domain) := parent_candidate_equal_parent_iff_d (positive := positive) (a := a) hM hC h.inherited h.values hParent hCValue hPValue
  intro a
  rw [h.parents c a,h.parents p a]
  constructor
  · rintro ⟨hA,hMax⟩
    refine ⟨(hCand a).mp hA,?_⟩
    intro b _ hB
    have hBC := (hCand b).mpr hB
    exact hMax b hBC.1.1 hBC
  · rintro ⟨hA,hMax⟩
    refine ⟨(hCand a).mpr hA,?_⟩
    intro b _ hB
    have hBP := (hCand b).mp hB
    exact hMax b hBP.1.1 hBP

theorem Selects.parent_less_d {M : SetTheory.Structure.{u}} {C : ExpressionData M.Domain} {positive : Bool} {m F V Q c p x y : M.Domain}
    (h : Selects positive M C m F V Q) (hParent : MemPair M Q c p) (hP : MemPair M V p x) (hC : MemPair M V c y) : M.mem x y := by
  obtain ⟨x',_,y',_,hP',hC',hLess,_⟩ := h.parent_values hParent
  have hxx := h.values.unique p x x' hP hP'
  have hyy := h.values.unique c y y' hC hC'
  subst x'
  subst y'
  exact hLess

theorem top_forest_exists_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory) {C : ExpressionData M.Domain} (hC : C.Valid M)
    {m : M.Domain} {R : RowStateSpace M.Domain} {V H Heights F : M.Domain}
    (hHeights : HeightGraph M C m R V H Heights) (hF : PseudoForest M C m R H Heights F) :
    ∃ T, Selects false M C m F Heights T := select_forest_exists_d hM false hC hF.forest hHeights.graph

private def topGeometryTerms : ExpressionData (Project.Term 19) := ⟨.bound 18,.bound 17,.bound 16,.bound 15,.bound 14⟩

private def topParentSchema : Project.UnarySchema 13 where
  body := Project.Formula.forallMem (.bound 8) (Project.Formula.forallMem (.bound 14)
    (Project.Formula.forallMem (.bound 15) (Project.Formula.forallMem (.bound 10) (Project.Formula.forallMem (.bound 10)
      (.imp (memPairFormula (.bound 6) (.bound 5) (.bound 4)) (.imp (memPairFormula (.bound 8) (.bound 5) (.bound 3))
        (.imp (memPairFormula (.bound 8) (.bound 4) (.bound 2))
          (.imp (rowAtFormula (.bound 10) (.bound 9) (.bound 2) (.bound 1) (.bound 0))
            (.conj (successorFormula (.bound 3) (.bound 2)) (rootFormula topGeometryTerms (.bound 13) (.bound 0) (.bound 5) (.bound 4)))))))))))
  freeClosed := by
    have hC : topGeometryTerms.Closed := ⟨rfl,rfl,rfl,rfl,rfl⟩
    have hRow := rowAtFormula_freeClosed (n := 19) (.bound 10) (.bound 9) (.bound 2) (.bound 1) (.bound 0) rfl rfl rfl rfl rfl
    have hRoot := rootFormula_freeClosed hC (.bound 13) (.bound 0) (.bound 5) (.bound 4) rfl rfl rfl rfl
    simp [Project.Formula.forallMem,Definitional.Formula.FreeClosed,memPairFormula,codeFormula,pairFormula,
      successorFormula,Project.Formula.existsMem,hRow,hRoot]

private def topGeometryEnv {M : SetTheory.Structure.{u}} (C : ExpressionData M.Domain) (m : M.Domain) (R : RowStateSpace M.Domain)
    (H Heights F T : M.Domain) : Env M 13 :=
  ((((((((((((oneEnv C.omega).push C.zero).push C.one).push C.sequences).push C.expressions).push m).push R.values).push R.forests).push R.states).push H).push Heights).push F).push T

private theorem topParentSchema_iff {M : SetTheory.Structure.{u}} (he : Extensional M) (C : ExpressionData M.Domain)
    (m : M.Domain) (R : RowStateSpace M.Domain) (H Heights F T c : M.Domain) :
    Project.Formula.satisfies ((topGeometryEnv C m R H Heights F T).push c) topParentSchema.body ↔
      ∀ p, M.mem p m → ∀ hc, M.mem hc C.omega → ∀ hp, M.mem hp C.omega → ∀ U, M.mem U R.values → ∀ Q, M.mem Q R.forests →
        MemPair M T c p → MemPair M Heights c hc → MemPair M Heights p hp → RowAt M R.states H hp U Q →
          M.SuccessorOf hc hp ∧ Root M C m Q c p := by
  simp only [topParentSchema,Project.Formula.satisfies_forallMem_iff,Project.Formula.satisfies_imp_iff,memPairFormula_iff he,
    rowAtFormula_iff he,Project.Formula.satisfies_conj_iff,successorFormula_iff he,rootFormula_iff he]
  rfl

theorem top_forest_parent_root_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory) {C : ExpressionData M.Domain} (hC : C.Valid M)
    {m : M.Domain} {R : RowStateSpace M.Domain} {V P H Heights F T c p hc hp U Q : M.Domain}
    (hRun : RowRun M C m R V P H) (hHeights : HeightGraph M C m R V H Heights) (hF : PseudoForest M C m R H Heights F)
    (hT : Selects false M C m F Heights T) (hPositive : ∀ i v, MemPair M V i v → M.mem C.zero v)
    (hParent : MemPair M T c p) (hHC : MemPair M Heights c hc) (hHP : MemPair M Heights p hp)
    (hRow : RowAt M R.states H hp U Q) : M.SuccessorOf hc hp ∧ Root M C m Q c p := by
  have hAll := KP1Y.induction_d hM topParentSchema (topGeometryEnv C m R H Heights F T) (by
    intro c ih
    apply (topParentSchema_iff hM.1 C m R H Heights F T c).mpr
    intro p hpM hc hcNat hp hpNat U hU Q hQ hParent hHC hHP hRow
    have hAncestor := hT.parent_ancestor hParent
    obtain ⟨b,hPseudo,hPB⟩ := ancestor_parent_cases_d hM hC hF.forest hAncestor
    obtain ⟨hb,hbNat,hHB⟩ := hHeights.graph.total b (hF.forest.bounds hM.1 hPseudo).2
    rcases hF.parent_heights hHeights hPseudo hHC hHB with hSame | hSucc
    · have hParentB := (hT.parent_rows_of_equal_parent_d hM hC hPseudo hHC (hSame ▸ hHB) p).mp hParent
      obtain ⟨hSucc,hRoot⟩ := (topParentSchema_iff hM.1 C m R H Heights F T b).mp (ih b (hF.forest.left c b hPseudo))
        p hpM hc hcNat hp hpNat U hU Q hQ hParentB (hSame ▸ hHB) hHP hRow
      have hBC := hF.parent_row_ancestor_d hM hC hRun hHeights hPseudo hHC ⟨hpNat,Or.inr hSucc⟩ hRow
      exact ⟨hSucc,(root_ancestor_iff_d hM hC (hRun.at_numeric_d hM hC hRow).forest hBC).mpr hRoot⟩
    · have hCand : ParentCandidate false M C m F Heights c b :=
        ⟨ancestor_direct_d hM hC hF.forest hPseudo,hb,hbNat,hc,hcNat,hHB,hHC,hSucc.predecessor_mem,trivial⟩
      have hBP := ((hT.parents c p).mp hParent).2 b hCand.1.1 hCand
      have hpb : p=b := by
        rcases hPB with he | hAncPB
        · exact he
        · rcases hBP with he | hbp
          · exact he.symm
          · have hOrd := ((omega_isOrdinal_d hM hC.omega).mem hRun.space.width).mem hpM
            exact False.elim (SetTheory.KP.mem_irrefl_d (KP1Y.models_weakKP hM) p (hOrd.transitive b hbp p hAncPB.1))
      subst b
      have hbhp := hHeights.graph.unique p hb hp hHB hHP
      subst hb
      have hAncRow := hF.parent_row_ancestor_d hM hC hRun hHeights hPseudo hHC ⟨hpNat,Or.inr hSucc⟩ hRow
      obtain ⟨a,_,hA⟩ := hRun.base.values.total p hpM
      have hNo := hRun.top_parent_none_d hM hC hA (hPositive p a hA) ((hHeights.rows p hp).mp hHP).2 hRow
      exact ⟨hSucc,hpM,hNo,Or.inr hAncRow⟩)
  have hNumeric := hRun.at_numeric_d hM hC hRow
  exact (topParentSchema_iff hM.1 C m R H Heights F T c).mp (hAll c) p (hT.forest.bounds hM.1 hParent).2
    hc (hHeights.graph.bounds hM.1 hHC).2 hp (hHeights.graph.bounds hM.1 hHP).2
    U ((hRun.space.values U).mpr hNumeric.values) Q ((hRun.space.forests Q).mpr hNumeric.forest) hParent hHC hHP hRow

private def topAncestorSchema : Project.UnarySchema 13 where
  body := Project.Formula.forallMem (.bound 8) (Project.Formula.forallMem (.bound 14)
    (Project.Formula.forallMem (.bound 15) (Project.Formula.forallMem (.bound 10) (Project.Formula.forallMem (.bound 10)
      (.imp (ancestorFormula topGeometryTerms (.bound 13) (.bound 6) (.bound 4) (.bound 5))
        (.imp (memPairFormula (.bound 8) (.bound 5) (.bound 3)) (.imp (memPairFormula (.bound 8) (.bound 4) (.bound 2))
          (.imp (rowAtFormula (.bound 10) (.bound 9) (.bound 2) (.bound 1) (.bound 0))
            (.conj (.mem (.bound 2) (.bound 3)) (rootFormula topGeometryTerms (.bound 13) (.bound 0) (.bound 5) (.bound 4)))))))))))
  freeClosed := by
    have hC : topGeometryTerms.Closed := ⟨rfl,rfl,rfl,rfl,rfl⟩
    have hRow := rowAtFormula_freeClosed (n := 19) (.bound 10) (.bound 9) (.bound 2) (.bound 1) (.bound 0) rfl rfl rfl rfl rfl
    have hRoot := rootFormula_freeClosed hC (.bound 13) (.bound 0) (.bound 5) (.bound 4) rfl rfl rfl rfl
    have hAnc := ancestorFormula_freeClosed hC (.bound 13) (.bound 6) (.bound 4) (.bound 5) rfl rfl rfl rfl
    simp [Project.Formula.forallMem,Definitional.Formula.FreeClosed,memPairFormula,codeFormula,pairFormula,
      Project.Formula.existsMem,hRow,hRoot,hAnc]

private theorem topAncestorSchema_iff {M : SetTheory.Structure.{u}} (he : Extensional M) (C : ExpressionData M.Domain)
    (m : M.Domain) (R : RowStateSpace M.Domain) (H Heights F T c : M.Domain) :
    Project.Formula.satisfies ((topGeometryEnv C m R H Heights F T).push c) topAncestorSchema.body ↔
      ∀ a, M.mem a m → ∀ hc, M.mem hc C.omega → ∀ ha, M.mem ha C.omega → ∀ U, M.mem U R.values → ∀ Q, M.mem Q R.forests →
        Ancestor M C m T a c → MemPair M Heights c hc → MemPair M Heights a ha → RowAt M R.states H ha U Q →
          M.mem ha hc ∧ Root M C m Q c a := by
  simp only [topAncestorSchema,Project.Formula.satisfies_forallMem_iff,Project.Formula.satisfies_imp_iff,ancestorFormula_iff he,
    memPairFormula_iff he,rowAtFormula_iff he,Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_mem_iff,rootFormula_iff he]
  rfl

theorem top_forest_ancestor_root_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory) {C : ExpressionData M.Domain} (hC : C.Valid M)
    {m : M.Domain} {R : RowStateSpace M.Domain} {V P H Heights F T a c ha hc U Q : M.Domain}
    (hRun : RowRun M C m R V P H) (hHeights : HeightGraph M C m R V H Heights) (hF : PseudoForest M C m R H Heights F)
    (hT : Selects false M C m F Heights T) (hPositive : ∀ i v, MemPair M V i v → M.mem C.zero v)
    (hAnc : Ancestor M C m T a c) (hHA : MemPair M Heights a ha) (hHC : MemPair M Heights c hc)
    (hRow : RowAt M R.states H ha U Q) : M.mem ha hc ∧ Root M C m Q c a := by
  have hAll := KP1Y.induction_d hM topAncestorSchema (topGeometryEnv C m R H Heights F T) (by
    intro c ih
    apply (topAncestorSchema_iff hM.1 C m R H Heights F T c).mpr
    intro a haM hc hcNat ha haNat U hU Q hQ hAnc hHC hHA hRow
    obtain ⟨p,hParent,hAP⟩ := ancestor_parent_cases_d hM hC hT.forest hAnc
    rcases hAP with he | hAP
    · subst a
      obtain ⟨hSucc,hRoot⟩ := top_forest_parent_root_d hM hC hRun hHeights hF hT hPositive hParent hHC hHA hRow
      exact ⟨hSucc.predecessor_mem,hRoot⟩
    · obtain ⟨hp,hpNat,hHP⟩ := hHeights.graph.total p (hT.forest.bounds hM.1 hParent).2
      obtain ⟨Up,Qp,hRowP⟩ := hRun.at_exists_d hpNat
      obtain ⟨hSucc,hRootP⟩ := top_forest_parent_root_d hM hC hRun hHeights hF hT hPositive hParent hHC hHP hRowP
      obtain ⟨hLess,hRoot⟩ := (topAncestorSchema_iff hM.1 C m R H Heights F T p).mp (ih p (hT.forest.left c p hParent))
        a haM hp hpNat ha haNat U hU Q hQ hAP hHP hHA hRow
      exact ⟨((omega_isOrdinal_d hM hC.omega).mem hcNat).transitive hp hSucc.predecessor_mem ha hLess,
        (hRun.root_through_higher_d hM hC hRow hRowP (Or.inr hLess) hRootP).mpr hRoot⟩)
  have hNumeric := hRun.at_numeric_d hM hC hRow
  exact (topAncestorSchema_iff hM.1 C m R H Heights F T c).mp (hAll c) a (hAnc.bounds hM.1).1
    hc (hHeights.graph.bounds hM.1 hHC).2 ha (hHeights.graph.bounds hM.1 hHA).2
    U ((hRun.space.values U).mpr hNumeric.values) Q ((hRun.space.forests Q).mpr hNumeric.forest) hAnc hHC hHA hRow

theorem selected_top_values_refine_height_forest_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {m : M.Domain} {R : RowStateSpace M.Domain}
    {V P H Heights Top F Q T : M.Domain} (hRun : RowRun M C m R V P H)
    (hHeights : HeightGraph M C m R V H Heights) (hTop : TopValueGraph M C m R H Heights Top)
    (hF : PseudoForest M C m R H Heights F) (hSelected : Selects true M C m F Top Q) (hT : Selects false M C m F Heights T)
    (hPositive : ∀ i v, MemPair M V i v → M.mem C.zero v) : ForestRefines M C m Q T := by
  intro c p hParent
  have hAnc := hSelected.parent_ancestor hParent
  obtain ⟨hp,hpNat,hHP⟩ := hHeights.graph.total p (hSelected.forest.bounds hM.1 hParent).2
  obtain ⟨hc,hcNat,hHC⟩ := hHeights.graph.total c (hSelected.forest.bounds hM.1 hParent).1
  obtain ⟨x,hx,y,hy,hPX,hCY,hLess,_⟩ := hSelected.parent_values hParent
  have hpLess : M.mem hp hc := by
    rcases hF.ancestor_height_le_d hM hC hHeights hAnc hHP hHC with he | hlt
    · have hAnti := hTop.same_height_pseudo_antitone_d hM hC hRun hHeights hF hPositive hAnc (he ▸ hHP) hHC hPX hCY
      rcases hAnti with hEq | hRev
      · exact False.elim (SetTheory.KP.mem_irrefl_d (KP1Y.models_weakKP hM) x (hEq ▸ hLess))
      · exact False.elim (SetTheory.KP.mem_irrefl_d (KP1Y.models_weakKP hM) x
          (((omega_isOrdinal_d hM hC.omega).mem hx).transitive y hRev x hLess))
    · exact hlt
  have hRecord : RecordMinimum M C m F Heights p c := by
    refine ⟨hAnc,hp,hpNat,hc,hcNat,hHP,hHC,hpLess,?_⟩
    intro b hbM hBC hPB hb hbNat hHB
    have hPBAnc := ancestor_between_d hM hC hF.forest hAnc hBC hPB
    rcases hF.ancestor_height_le_d hM hC hHeights hPBAnc hHP hHB with he | hlt
    · obtain ⟨z,hz,hBZ⟩ := hTop.graph.total b hbM
      have hAnti := hTop.same_height_pseudo_antitone_d hM hC hRun hHeights hF hPositive hPBAnc hHP (he.symm ▸ hHB) hPX hBZ
      have hZY : M.mem z y := by
        rcases hAnti with hzEq | hzx
        · exact hzEq.symm ▸ hLess
        · exact ((omega_isOrdinal_d hM hC.omega).mem hy).transitive x hLess z hzx
      obtain ⟨base,_,hBase⟩ := hRun.base.values.total b hbM
      have hPosZ := hTop.positive_d hM hC hRun hHeights hBase (hPositive b base hBase) hBZ
      have hCandidate : ParentCandidate true M C m F Top c b := ⟨hBC,z,hz,y,hy,hBZ,hCY,hZY,hPosZ⟩
      have hMax := ((hSelected.parents c p).mp hParent).2 b hBC.1 hCandidate
      rcases hMax with hEq | hbp
      · exact False.elim (SetTheory.KP.mem_irrefl_d (KP1Y.models_weakKP hM) p (hEq ▸ hPB))
      · have hOrd := ((omega_isOrdinal_d hM hC.omega).mem hRun.space.width).mem (hSelected.forest.bounds hM.1 hParent).2
        exact False.elim (SetTheory.KP.mem_irrefl_d (KP1Y.models_weakKP hM) p (hOrd.transitive b hbp p hPB))
    · exact hlt
  exact hT.record_minimum_ancestor_d hM hC hRecord

theorem Extraction.ancestor_height_root_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {m V P Top Q a c : M.Domain} (hExtraction : Extraction M C m V P Top Q)
    {R : RowStateSpace M.Domain} {H Heights ha hc U Frow : M.Domain} (hRun : RowRun M C m R V P H)
    (hHeights : HeightGraph M C m R V H Heights) (hPositive : ∀ i v, MemPair M V i v → M.mem C.zero v)
    (hAnc : Ancestor M C m Q a c) (hHA : MemPair M Heights a ha) (hHC : MemPair M Heights c hc)
    (hRow : RowAt M R.states H ha U Frow) : M.mem ha hc ∧ Root M C m Frow c a := by
  obtain ⟨R',H',Heights',F,hRun',hHeights',hTop,hF,hSelected⟩ := hExtraction
  have hRR := row_state_space_unique hM.1 hRun'.space hRun.space
  subst R'
  have hHH := hRun'.unique_d hM hC hRun
  subst H'
  have hHeightEq := hHeights'.unique hM.1 hHeights
  subst Heights'
  obtain ⟨T,hT⟩ := top_forest_exists_d hM hC hHeights hF
  have hRefines := selected_top_values_refine_height_forest_d hM hC hRun hHeights hTop hF hSelected hT hPositive
  have hTopAnc := ancestor_refines_d hM hC hT.forest hRefines hAnc
  exact top_forest_ancestor_root_d hM hC hRun hHeights hF hT hPositive hTopAnc hHA hHC hRow

theorem top_forest_parent_exists_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {m : M.Domain} {R : RowStateSpace M.Domain}
    {V P H Heights F T c hc : M.Domain} (hRun : RowRun M C m R V P H) (hHeights : HeightGraph M C m R V H Heights)
    (hF : PseudoForest M C m R H Heights F) (hT : Selects false M C m F Heights T)
    (hPositive : ∀ i v, MemPair M V i v → M.mem C.zero v) (hHC : MemPair M Heights c hc) (hPos : M.mem C.zero hc) :
    ∃ p, MemPair M T c p := by
  obtain ⟨q,hRoot⟩ := root_exists_d hM hC hF.forest (hHeights.graph.bounds hM.1 hHC).1
  obtain ⟨hq,_,hHQ⟩ := hHeights.graph.total q hRoot.1
  have hq0 := (hF.no_parent_iff_height_zero_d hM hC hRun hHeights hPositive hHQ).mp hRoot.2.1
  have hQZero : MemPair M Heights q C.zero := hq0 ▸ hHQ
  have hAnc : Ancestor M C m F q c := by
    rcases hRoot.2.2 with he | hAnc
    · subst q
      have hhc0 := hHeights.graph.unique c hc C.zero hHC hQZero
      exact False.elim (hC.zero_empty C.zero (hhc0 ▸ hPos))
    · exact hAnc
  have hCandidate : ParentCandidate false M C m F Heights c q :=
    ⟨hAnc,C.zero,hC.zero_nat,hc,(hHeights.graph.bounds hM.1 hHC).2,hQZero,hHC,hPos,trivial⟩
  obtain ⟨p,hParent⟩ := restricted_parent_exists_d hM false hC hF.forest ⟨q,hCandidate⟩
  exact ⟨p,(hT.parents c p).mpr hParent⟩

private def topRootBackSchema : Project.UnarySchema 13 where
  body := Project.Formula.forallMem (.bound 8) (Project.Formula.forallMem (.bound 14)
    (Project.Formula.forallMem (.bound 15) (Project.Formula.forallMem (.bound 10) (Project.Formula.forallMem (.bound 10)
      (.imp (memPairFormula (.bound 8) (.bound 5) (.bound 3)) (.imp (memPairFormula (.bound 8) (.bound 4) (.bound 2))
        (.imp (rowAtFormula (.bound 10) (.bound 9) (.bound 2) (.bound 1) (.bound 0)) (.imp (.mem (.bound 2) (.bound 3))
          (.imp (rootFormula topGeometryTerms (.bound 13) (.bound 0) (.bound 5) (.bound 4))
            (ancestorFormula topGeometryTerms (.bound 13) (.bound 6) (.bound 4) (.bound 5)))))))))))
  freeClosed := by
    have hC : topGeometryTerms.Closed := ⟨rfl,rfl,rfl,rfl,rfl⟩
    have hRow := rowAtFormula_freeClosed (n := 19) (.bound 10) (.bound 9) (.bound 2) (.bound 1) (.bound 0) rfl rfl rfl rfl rfl
    have hRoot := rootFormula_freeClosed hC (.bound 13) (.bound 0) (.bound 5) (.bound 4) rfl rfl rfl rfl
    have hAnc := ancestorFormula_freeClosed hC (.bound 13) (.bound 6) (.bound 4) (.bound 5) rfl rfl rfl rfl
    simp [Project.Formula.forallMem,Definitional.Formula.FreeClosed,memPairFormula,codeFormula,pairFormula,
      Project.Formula.existsMem,hRow,hRoot,hAnc]

private theorem topRootBackSchema_iff {M : SetTheory.Structure.{u}} (he : Extensional M) (C : ExpressionData M.Domain)
    (m : M.Domain) (R : RowStateSpace M.Domain) (H Heights F T c : M.Domain) :
    Project.Formula.satisfies ((topGeometryEnv C m R H Heights F T).push c) topRootBackSchema.body ↔
      ∀ a, M.mem a m → ∀ hc, M.mem hc C.omega → ∀ ha, M.mem ha C.omega → ∀ U, M.mem U R.values → ∀ Q, M.mem Q R.forests →
        MemPair M Heights c hc → MemPair M Heights a ha → RowAt M R.states H ha U Q → M.mem ha hc → Root M C m Q c a → Ancestor M C m T a c := by
  simp only [topRootBackSchema,Project.Formula.satisfies_forallMem_iff,Project.Formula.satisfies_imp_iff,memPairFormula_iff he,
    rowAtFormula_iff he,Project.Formula.satisfies_mem_iff,rootFormula_iff he,ancestorFormula_iff he]
  rfl

theorem top_forest_ancestor_of_root_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {m : M.Domain} {R : RowStateSpace M.Domain}
    {V P H Heights F T a c ha hc U Q : M.Domain} (hRun : RowRun M C m R V P H) (hHeights : HeightGraph M C m R V H Heights)
    (hF : PseudoForest M C m R H Heights F) (hT : Selects false M C m F Heights T)
    (hPositive : ∀ i v, MemPair M V i v → M.mem C.zero v) (hHA : MemPair M Heights a ha) (hHC : MemPair M Heights c hc)
    (hRow : RowAt M R.states H ha U Q) (hLess : M.mem ha hc) (hRoot : Root M C m Q c a) : Ancestor M C m T a c := by
  have hAll := KP1Y.induction_d hM topRootBackSchema (topGeometryEnv C m R H Heights F T) (by
    intro c ih
    apply (topRootBackSchema_iff hM.1 C m R H Heights F T c).mpr
    intro a haM hc hcNat ha haNat U hU Q hQ hHC hHA hRow hLess hRoot
    have hPos := (hC.zero_mem_iff hM hcNat).mpr (fun he => hC.zero_empty ha (he ▸ hLess))
    obtain ⟨p,hParent⟩ := top_forest_parent_exists_d hM hC hRun hHeights hF hT hPositive hHC hPos
    obtain ⟨hp,hpNat,hHP⟩ := hHeights.graph.total p (hT.forest.bounds hM.1 hParent).2
    obtain ⟨Up,Qp,hRowP⟩ := hRun.at_exists_d hpNat
    obtain ⟨hSucc,hRootP⟩ := top_forest_parent_root_d hM hC hRun hHeights hF hT hPositive hParent hHC hHP hRowP
    rcases (hSucc ha).mp hLess with hLessP | hEqual
    · have hRootLower := (hRun.root_through_higher_d hM hC hRow hRowP (Or.inr hLessP) hRootP).mp hRoot
      have hAP := (topRootBackSchema_iff hM.1 C m R H Heights F T p).mp (ih p (hT.forest.left c p hParent))
        a haM hp hpNat ha haNat U hU Q hQ hHP hHA hRow hLessP hRootLower
      exact ancestor_step_d hM hC hT.forest hAP hParent
    · have hh := hM.1.eq_of_same_members ha hp hEqual
      subst ha
      have hQeq := (hRun.at_unique hM.1 hRowP hRow).2
      have hRootP' : Root M C m Q c p := hQeq ▸ hRootP
      have hap := root_unique_d hM hC (hRun.at_numeric_d hM hC hRow).forest hRoot hRootP'
      subst a
      exact ancestor_direct_d hM hC hT.forest hParent)
  have hNumeric := hRun.at_numeric_d hM hC hRow
  exact (topRootBackSchema_iff hM.1 C m R H Heights F T c).mp (hAll c) a (hHeights.graph.bounds hM.1 hHA).1
    hc (hHeights.graph.bounds hM.1 hHC).2 ha (hHeights.graph.bounds hM.1 hHA).2
    U ((hRun.space.values U).mpr hNumeric.values) Q ((hRun.space.forests Q).mpr hNumeric.forest) hHC hHA hRow hLess hRoot

theorem top_forest_ancestor_iff_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {m : M.Domain} {R : RowStateSpace M.Domain}
    {V P H Heights F T a c ha hc U Q : M.Domain} (hRun : RowRun M C m R V P H) (hHeights : HeightGraph M C m R V H Heights)
    (hF : PseudoForest M C m R H Heights F) (hT : Selects false M C m F Heights T)
    (hPositive : ∀ i v, MemPair M V i v → M.mem C.zero v) (hHA : MemPair M Heights a ha) (hHC : MemPair M Heights c hc)
    (hRow : RowAt M R.states H ha U Q) : Ancestor M C m T a c ↔ M.mem ha hc ∧ Root M C m Q c a :=
  ⟨fun h => top_forest_ancestor_root_d hM hC hRun hHeights hF hT hPositive h hHA hHC hRow,
    fun h => top_forest_ancestor_of_root_d hM hC hRun hHeights hF hT hPositive hHA hHC hRow h.1 h.2⟩

theorem top_forest_ancestor_or_eq_iff_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {m : M.Domain} {R : RowStateSpace M.Domain}
    {V P H Heights F T a c ha hc U Q : M.Domain} (hRun : RowRun M C m R V P H) (hHeights : HeightGraph M C m R V H Heights)
    (hF : PseudoForest M C m R H Heights F) (hT : Selects false M C m F Heights T)
    (hPositive : ∀ i v, MemPair M V i v → M.mem C.zero v) (hHA : MemPair M Heights a ha) (hHC : MemPair M Heights c hc)
    (hRow : RowAt M R.states H ha U Q) :
    (Ancestor M C m T a c ∨ a=c) ↔ (ha=hc ∨ M.mem ha hc) ∧ Root M C m Q c a := by
  constructor
  · rintro (hAnc | he)
    · have h := top_forest_ancestor_root_d hM hC hRun hHeights hF hT hPositive hAnc hHA hHC hRow
      exact ⟨Or.inr h.1,h.2⟩
    · subst a
      obtain ⟨v,_,hV⟩ := hRun.base.values.total c (hHeights.graph.bounds hM.1 hHA).1
      have hNo := hRun.top_parent_none_d hM hC hV (hPositive c v hV) ((hHeights.rows c ha).mp hHA).2 hRow
      exact ⟨Or.inl (hHeights.graph.unique c ha hc hHA hHC),(hHeights.graph.bounds hM.1 hHA).1,hNo,Or.inl rfl⟩
  · rintro ⟨he | hLess,hRoot⟩
    · subst ha
      obtain ⟨v,_,hV⟩ := hRun.base.values.total c (hHeights.graph.bounds hM.1 hHC).1
      have hNo := hRun.top_parent_none_d hM hC hV (hPositive c v hV) ((hHeights.rows c hc).mp hHC).2 hRow
      exact Or.inr (root_of_no_parent_d hM hC (hRun.at_numeric_d hM hC hRow).forest hNo hRoot)
    · exact Or.inl (top_forest_ancestor_of_root_d hM hC hRun hHeights hF hT hPositive hHA hHC hRow hLess hRoot)

end KP1Y.OneYFinite
