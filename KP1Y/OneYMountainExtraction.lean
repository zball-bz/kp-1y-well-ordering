import KP1Y.OneYMountainHeight
import KP1Y.OneYForestClosure

/-! 实际伪父选择及保留该候选森林的数值提取。 -/
namespace KP1Y.OneYFinite
open YesMetaZFC YesMetaZFC.SetTheory YesMetaZFC.SetTheory.Definitional
open KP1Y.Kuratowski KP1Y.Functions KP1Y.Naturals KP1Y.Bounded
universe u

def PseudoCandidate (M : SetTheory.Structure.{u}) (C : ExpressionData M.Domain) (m : M.Domain)
    (R : RowStateSpace M.Domain) (H Heights c p : M.Domain) : Prop :=
  ∃ hc, M.mem hc C.omega ∧ ∃ hp, M.mem hp C.omega ∧ ∃ r, M.mem r C.omega ∧
    MemPair M Heights c hc ∧ MemPair M Heights p hp ∧ PreviousLength M C.omega C.zero hc r ∧
      ∃ W, M.mem W R.values ∧ ∃ Q, M.mem Q R.forests ∧ RowAt M R.states H r W Q ∧
        Ancestor M C m Q p c ∧ (hp=hc ∨ M.SuccessorOf hc hp)

def pseudoCandidateFormula {n : Nat} (C : ExpressionData (Project.Term n))
    (m States Values Forests H Heights c p : Project.Term n) : Project.Formula 1 n :=
  Project.Formula.existsMem C.omega (Project.Formula.existsMem C.omega.weaken
    (Project.Formula.existsMem C.omega.weaken.weaken
      (.conj (memPairFormula Heights.weaken.weaken.weaken c.weaken.weaken.weaken (.bound 2))
        (.conj (memPairFormula Heights.weaken.weaken.weaken p.weaken.weaken.weaken (.bound 1))
          (.conj (previousLengthFormula C.omega.weaken.weaken.weaken C.zero.weaken.weaken.weaken (.bound 2) (.bound 0))
            (Project.Formula.existsMem Values.weaken.weaken.weaken (Project.Formula.existsMem Forests.weaken.weaken.weaken.weaken
              (.conj (rowAtFormula States.weaken.weaken.weaken.weaken.weaken H.weaken.weaken.weaken.weaken.weaken (.bound 2) (.bound 1) (.bound 0))
                (.conj (ancestorFormula C.weaken.weaken.weaken.weaken.weaken m.weaken.weaken.weaken.weaken.weaken (.bound 0)
                  p.weaken.weaken.weaken.weaken.weaken c.weaken.weaken.weaken.weaken.weaken)
                  (.disj (Project.Formula.extensionalEq (.bound 3) (.bound 4)) (successorFormula (.bound 4) (.bound 3))))))))))))

theorem pseudoCandidateFormula_delta0 {n : Nat} (C : ExpressionData (Project.Term n))
    (m States Values Forests H Heights c p : Project.Term n) : (pseudoCandidateFormula C m States Values Forests H Heights c p).IsDelta0 :=
  .existsMem _ (.existsMem _ (.existsMem _ (.conj (memPairFormula_delta0 _ _ _) (.conj (memPairFormula_delta0 _ _ _)
    (.conj (previousLengthFormula_delta0 _ _ _ _) (.existsMem _ (.existsMem _ (.conj (rowAtFormula_delta0 _ _ _ _ _)
      (.conj (ancestorFormula_delta0 _ _ _ _ _) (.disj (.atom _ _ _) (successorFormula_delta0 _ _)))))))))))

theorem pseudoCandidateFormula_freeClosed {n : Nat} {C : ExpressionData (Project.Term n)} (hC : C.Closed)
    (m States Values Forests H Heights c p : Project.Term n) (hm : m.freeSupport=[]) (hS : States.freeSupport=[])
    (hV : Values.freeSupport=[]) (hF : Forests.freeSupport=[]) (hH : H.freeSupport=[]) (hHs : Heights.freeSupport=[])
    (hc : c.freeSupport=[]) (hp : p.freeSupport=[]) : (pseudoCandidateFormula C m States Values Forests H Heights c p).FreeClosed := by
  have hAnc := ancestorFormula_freeClosed hC.weaken.weaken.weaken.weaken.weaken
    m.weaken.weaken.weaken.weaken.weaken (.bound 0) p.weaken.weaken.weaken.weaken.weaken c.weaken.weaken.weaken.weaken.weaken
    (by simpa using hm) rfl (by simpa using hp) (by simpa using hc)
  simp [pseudoCandidateFormula,rowAtFormula,previousLengthFormula,successorFormula,memPairFormula,codeFormula,pairFormula,
    Project.Formula.forallMem,Project.Formula.existsMem,Definitional.Formula.FreeClosed,hC.omega,hC.zero,hS,hV,hF,hH,hHs,hc,hp,hAnc]

theorem pseudoCandidateFormula_iff {M : SetTheory.Structure.{u}} (he : Extensional M) {n : Nat} (e : Env M n)
    (C : ExpressionData (Project.Term n)) (m States Values Forests H Heights c p : Project.Term n) :
    Project.Formula.satisfies e (pseudoCandidateFormula C m States Values Forests H Heights c p) ↔
      PseudoCandidate M (C.eval e) (m.eval e) ⟨Values.eval e,Forests.eval e,States.eval e⟩ (H.eval e) (Heights.eval e) (c.eval e) (p.eval e) := by
  simp only [pseudoCandidateFormula,Project.Formula.satisfies_existsMem_iff,Project.Formula.satisfies_conj_iff,
    memPairFormula_iff he,previousLengthFormula_iff he,rowAtFormula_iff he,ancestorFormula_iff he,
    Project.Formula.satisfies_disj_iff,Project.Formula.satisfies_extensionalEq_iff_eq he,successorFormula_iff he,
    ExpressionData.eval_weaken,Term.eval_weaken]
  rfl

theorem PseudoCandidate.bounds {M : SetTheory.Structure.{u}} (he : Extensional M) {C : ExpressionData M.Domain}
    {m : M.Domain} {R : RowStateSpace M.Domain} {H Heights c p : M.Domain} (h : PseudoCandidate M C m R H Heights c p) :
    M.mem p m ∧ M.mem c m ∧ M.mem p c := by
  obtain ⟨_,_,_,_,_,_,_,_,_,_,_,_,_,_,hAnc,_⟩ := h
  exact ⟨(hAnc.bounds he).1,(hAnc.bounds he).2,hAnc.1⟩

def PseudoParent (M : SetTheory.Structure.{u}) (C : ExpressionData M.Domain) (m : M.Domain)
    (R : RowStateSpace M.Domain) (H Heights c p : M.Domain) : Prop :=
  (∃ hc, M.mem hc C.omega ∧ MemPair M Heights c hc ∧ M.mem C.zero hc) ∧
    PseudoCandidate M C m R H Heights c p ∧
      ∀ q, M.mem q c → PseudoCandidate M C m R H Heights c q → q=p ∨ M.mem q p

def pseudoParentFormula {n : Nat} (C : ExpressionData (Project.Term n))
    (m States Values Forests H Heights c p : Project.Term n) : Project.Formula 1 n :=
  .conj (Project.Formula.existsMem C.omega (.conj (memPairFormula Heights.weaken c.weaken (.bound 0)) (.mem C.zero.weaken (.bound 0))))
    (.conj (pseudoCandidateFormula C m States Values Forests H Heights c p)
      (Project.Formula.forallMem c (.imp
        (pseudoCandidateFormula C.weaken m.weaken States.weaken Values.weaken Forests.weaken H.weaken Heights.weaken c.weaken (.bound 0))
        (.disj (Project.Formula.extensionalEq (.bound 0) p.weaken) (.mem (.bound 0) p.weaken)))))

theorem pseudoParentFormula_delta0 {n : Nat} (C : ExpressionData (Project.Term n))
    (m States Values Forests H Heights c p : Project.Term n) : (pseudoParentFormula C m States Values Forests H Heights c p).IsDelta0 :=
  .conj (.existsMem _ (.conj (memPairFormula_delta0 _ _ _) (.mem _ _)))
    (.conj (pseudoCandidateFormula_delta0 _ _ _ _ _ _ _ _ _) (.forallMem _
      (.imp (pseudoCandidateFormula_delta0 _ _ _ _ _ _ _ _ _) (.disj (.atom _ _ _) (.mem _ _)))))

theorem pseudoParentFormula_freeClosed {n : Nat} {C : ExpressionData (Project.Term n)} (hC : C.Closed)
    (m States Values Forests H Heights c p : Project.Term n) (hm : m.freeSupport=[]) (hS : States.freeSupport=[])
    (hV : Values.freeSupport=[]) (hF : Forests.freeSupport=[]) (hH : H.freeSupport=[]) (hHs : Heights.freeSupport=[])
    (hc : c.freeSupport=[]) (hp : p.freeSupport=[]) : (pseudoParentFormula C m States Values Forests H Heights c p).FreeClosed := by
  have hCand := pseudoCandidateFormula_freeClosed hC m States Values Forests H Heights c p hm hS hV hF hH hHs hc hp
  have hOther := pseudoCandidateFormula_freeClosed hC.weaken m.weaken States.weaken Values.weaken Forests.weaken H.weaken Heights.weaken c.weaken
    (.bound 0) (by simpa using hm) (by simpa using hS) (by simpa using hV) (by simpa using hF)
    (by simpa using hH) (by simpa using hHs) (by simpa using hc) rfl
  simp [pseudoParentFormula,memPairFormula,codeFormula,pairFormula,Project.Formula.forallMem,Project.Formula.existsMem,
    Definitional.Formula.FreeClosed,hC.omega,hC.zero,hHs,hc,hp,hCand,hOther]

theorem pseudoParentFormula_iff {M : SetTheory.Structure.{u}} (he : Extensional M) {n : Nat} (e : Env M n)
    (C : ExpressionData (Project.Term n)) (m States Values Forests H Heights c p : Project.Term n) :
    Project.Formula.satisfies e (pseudoParentFormula C m States Values Forests H Heights c p) ↔
      PseudoParent M (C.eval e) (m.eval e) ⟨Values.eval e,Forests.eval e,States.eval e⟩ (H.eval e) (Heights.eval e) (c.eval e) (p.eval e) := by
  simp only [pseudoParentFormula,Project.Formula.satisfies_existsMem_iff,Project.Formula.satisfies_conj_iff,
    memPairFormula_iff he,Project.Formula.satisfies_mem_iff,pseudoCandidateFormula_iff he,Project.Formula.satisfies_forallMem_iff,
    Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_disj_iff,Project.Formula.satisfies_extensionalEq_iff_eq he,
    ExpressionData.eval_weaken,Term.eval_weaken]
  rfl

theorem pseudo_parent_unique_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory) {C : ExpressionData M.Domain} (hC : C.Valid M)
    {m : M.Domain} {R : RowStateSpace M.Domain} {H Heights c p q : M.Domain} (hm : M.mem m C.omega)
    (hp : PseudoParent M C m R H Heights c p) (hq : PseudoParent M C m R H Heights c q) : p=q := by
  rcases hq.2.2 p (hp.2.1.bounds hM.1).2.2 hp.2.1 with he | hpq
  · exact he
  · rcases hp.2.2 q (hq.2.1.bounds hM.1).2.2 hq.2.1 with he | hqp
    · exact he.symm
    · have hOrd := ((omega_isOrdinal_d hM hC.omega).mem hm).mem (hp.2.1.bounds hM.1).1
      exact False.elim (SetTheory.KP.mem_irrefl_d (KP1Y.models_weakKP hM) p (hOrd.transitive q hqp p hpq))

structure PseudoForest (M : SetTheory.Structure.{u}) (C : ExpressionData M.Domain) (m : M.Domain)
    (R : RowStateSpace M.Domain) (H Heights F : M.Domain) : Prop where
  forest : Forest M C.omega m F
  parents : ∀ c p, MemPair M F c p ↔ PseudoParent M C m R H Heights c p

private def pseudoForestSchema : Project.Delta0BinarySchema 11 where
  body := pseudoParentFormula ⟨.bound 12,.bound 11,.bound 10,.bound 9,.bound 8⟩
    (.bound 7) (.bound 6) (.bound 5) (.bound 4) (.bound 3) (.bound 2) (.bound 1) (.bound 0)
  freeClosed := pseudoParentFormula_freeClosed ⟨rfl,rfl,rfl,rfl,rfl⟩ _ _ _ _ _ _ _ _ rfl rfl rfl rfl rfl rfl rfl rfl
  delta0 := pseudoParentFormula_delta0 _ _ _ _ _ _ _ _ _

theorem pseudo_forest_exists_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory) {C : ExpressionData M.Domain} (hC : C.Valid M)
    {m : M.Domain} (hm : M.mem m C.omega) (R : RowStateSpace M.Domain) (H Heights : M.Domain) :
    ∃ F, PseudoForest M C m R H Heights F := by
  let e := ((((((((((oneEnv C.omega).push C.zero).push C.one).push C.sequences).push C.expressions).push m).push R.states).push R.values).push R.forests).push H).push Heights
  have hφ (c p : M.Domain) : Project.Formula.satisfies ((e.push c).push p) pseudoForestSchema.body ↔
      PseudoParent M C m R H Heights c p := pseudoParentFormula_iff hM.1 _ _ _ _ _ _ _ _ _ _
  obtain ⟨F,hSupport,hRaw⟩ := relation_comprehension_d hM pseudoForestSchema e m m
  have hRows (c p : M.Domain) : MemPair M F c p ↔ PseudoParent M C m R H Heights c p := by
    have hr := hRaw c p
    rw [hφ] at hr
    exact hr.trans ⟨fun h => h.2.2,fun h => ⟨(h.2.1.bounds hM.1).2.1,(h.2.1.bounds hM.1).1,h⟩⟩
  exact ⟨F,⟨hm,hSupport,fun c p q hp hq => pseudo_parent_unique_d hM hC hm ((hRows c p).mp hp) ((hRows c q).mp hq),
    fun c p hp => (((hRows c p).mp hp).2.1.bounds hM.1).2.2⟩,hRows⟩

theorem PseudoForest.unique {M : SetTheory.Structure.{u}} (he : Extensional M) {C : ExpressionData M.Domain}
    {m : M.Domain} {R : RowStateSpace M.Domain} {H Heights F G : M.Domain}
    (hF : PseudoForest M C m R H Heights F) (hG : PseudoForest M C m R H Heights G) : F=G :=
  hF.forest.ext he hG.forest (fun c p => (hF.parents c p).trans (hG.parents c p).symm)

def Extraction (M : SetTheory.Structure.{u}) (C : ExpressionData M.Domain) (m V P Top Q : M.Domain) : Prop :=
  ∃ (R : RowStateSpace M.Domain) (H Heights F : M.Domain), RowRun M C m R V P H ∧
    HeightGraph M C m R V H Heights ∧ TopValueGraph M C m R H Heights Top ∧
      PseudoForest M C m R H Heights F ∧ Selects true M C m F Top Q

theorem extraction_exists_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory) {C : ExpressionData M.Domain} (hC : C.Valid M)
    {m V P : M.Domain} (hBase : NumericRow M C m V P) : ∃ Top Q, Extraction M C m V P Top Q := by
  obtain ⟨R,H,hRun⟩ := mountain_rows_exists_d hM hC hBase
  obtain ⟨Heights,Top,hHeights,hTop⟩ := mountain_height_top_exists_d hM hC hRun
  obtain ⟨F,hF⟩ := pseudo_forest_exists_d hM hC hBase.forest.width R H Heights
  obtain ⟨Q,hQ⟩ := select_forest_exists_d hM true hC hF.forest hTop.graph
  exact ⟨Top,Q,⟨R,H,Heights,F,hRun,hHeights,hTop,hF,hQ⟩⟩

theorem Extraction.numeric_row {M : SetTheory.Structure.{u}} {C : ExpressionData M.Domain} {m V P Top Q : M.Domain}
    (h : Extraction M C m V P Top Q) : NumericRow M C m Top Q := by
  obtain ⟨_,_,_,_,_,_,_,_,hSelected⟩ := h
  exact hSelected.numeric_row

theorem Extraction.positive_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory) {C : ExpressionData M.Domain} (hC : C.Valid M)
    {m V P Top Q : M.Domain} (h : Extraction M C m V P Top Q)
    (hPositive : ∀ c a, MemPair M V c a → M.mem C.zero a) : ∀ c v, MemPair M Top c v → M.mem C.zero v := by
  obtain ⟨_,_,_,_,hRun,hHeights,hTop,_,_⟩ := h
  intro c v hAt
  obtain ⟨a,_,hA⟩ := hRun.base.values.total c (hTop.graph.bounds hM.1 hAt).1
  exact hTop.positive_d hM hC hRun hHeights hA (hPositive c a hA) hAt

theorem row_state_space_unique {M : SetTheory.Structure.{u}} (he : Extensional M) {C : ExpressionData M.Domain} {m : M.Domain}
    {R R' : RowStateSpace M.Domain} (hR : R.Valid M C m) (hR' : R'.Valid M C m) : R=R' := by
  have hValues : R.values=R'.values := he.eq_of_same_members _ _ (fun V => (hR.values V).trans (hR'.values V).symm)
  have hForests : R.forests=R'.forests := he.eq_of_same_members _ _ (fun P => (hR.forests P).trans (hR'.forests P).symm)
  have hStates : R.states=R'.states := by
    apply he.eq_of_same_members
    intro state
    rw [hR.states state,hR'.states state,hValues,hForests]
  cases R
  cases R'
  cases hValues
  cases hForests
  cases hStates
  rfl

theorem Extraction.unique_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory) {C : ExpressionData M.Domain} (hC : C.Valid M)
    {m V P Top Q Top' Q' : M.Domain} (h : Extraction M C m V P Top Q) (h' : Extraction M C m V P Top' Q') : Top=Top' ∧ Q=Q' := by
  obtain ⟨R,H,Heights,F,hRun,hHeights,hTop,hF,hQ⟩ := h
  obtain ⟨R',H',Heights',F',hRun',hHeights',hTop',hF',hQ'⟩ := h'
  have hRR := row_state_space_unique hM.1 hRun.space hRun'.space
  subst R'
  have hHH := hRun.unique_d hM hC hRun'
  subst H'
  have hHeightsEq := hHeights.unique hM.1 hHeights'
  subst Heights'
  have hTopEq := hTop.unique hM.1 hTop'
  subst Top'
  have hFEq := hF.unique hM.1 hF'
  subst F'
  exact ⟨rfl,hQ.unique hM.1 hQ'⟩

private def rootHeightSchema : Project.UnarySchema 9 where
  body := Project.Formula.forallMem (.bound 4) (Project.Formula.forallMem (.bound 10) (Project.Formula.forallMem (.bound 11)
    (.imp (rootFormula ⟨.bound 12,.bound 11,.bound 10,.bound 9,.bound 8⟩ (.bound 7) (.bound 6) (.bound 3) (.bound 2))
      (.imp (memPairFormula (.bound 5) (.bound 2) (.bound 1))
        (.imp (memPairFormula (.bound 5) (.bound 3) (.bound 0))
          (.imp (.disj (Project.Formula.extensionalEq (.bound 4) (.bound 0)) (.mem (.bound 4) (.bound 0)))
            (Project.Formula.extensionalEq (.bound 1) (.bound 4))))))))
  freeClosed := by
    have hRoot := rootFormula_freeClosed (n := 13) (C := ⟨.bound 12,.bound 11,.bound 10,.bound 9,.bound 8⟩)
      ⟨rfl,rfl,rfl,rfl,rfl⟩ (.bound 7) (.bound 6) (.bound 3) (.bound 2) rfl rfl rfl rfl
    simp [Project.Formula.forallMem,Definitional.Formula.FreeClosed,memPairFormula,codeFormula,pairFormula,Project.Formula.existsMem,hRoot]

private def rootHeightEnv {M : SetTheory.Structure.{u}} (C : ExpressionData M.Domain) (m Q Heights r : M.Domain) : Env M 9 :=
  ((((((((oneEnv C.omega).push C.zero).push C.one).push C.sequences).push C.expressions).push m).push Q).push Heights).push r

private theorem rootHeightSchema_iff {M : SetTheory.Structure.{u}} (he : Extensional M) (C : ExpressionData M.Domain)
    (m Q Heights r c : M.Domain) : Project.Formula.satisfies ((rootHeightEnv C m Q Heights r).push c) rootHeightSchema.body ↔
      ∀ q, M.mem q m → ∀ hq, M.mem hq C.omega → ∀ hc, M.mem hc C.omega → Root M C m Q c q →
        MemPair M Heights q hq → MemPair M Heights c hc → (r=hc ∨ M.mem r hc) → hq=r := by
  simp only [rootHeightSchema,Project.Formula.satisfies_forallMem_iff,Project.Formula.satisfies_imp_iff,
    rootFormula_iff he,memPairFormula_iff he,Project.Formula.satisfies_disj_iff,
    Project.Formula.satisfies_extensionalEq_iff_eq he,Project.Formula.satisfies_mem_iff]
  rfl

theorem HeightGraph.root_height_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory) {C : ExpressionData M.Domain} (hC : C.Valid M)
    {m : M.Domain} {R : RowStateSpace M.Domain} {V P H Heights r W Q c q hc hq : M.Domain}
    (hRun : RowRun M C m R V P H) (hHeights : HeightGraph M C m R V H Heights)
    (hPositive : ∀ j v, MemPair M V j v → M.mem C.zero v) (hAt : RowAt M R.states H r W Q)
    (hRoot : Root M C m Q c q) (hHC : MemPair M Heights c hc) (hHQ : MemPair M Heights q hq)
    (hLe : r=hc ∨ M.mem r hc) : hq=r := by
  have hRow := hRun.at_numeric_d hM hC hAt
  have hAll := KP1Y.ordinal_induction_d hM rootHeightSchema (rootHeightEnv C m Q Heights r) (by
    intro c _ ih
    apply (rootHeightSchema_iff hM.1 C m Q Heights r c).mpr
    intro q _ hq _ hc _ hRoot hHQ hHC hLe
    classical
    by_cases hNo : NoParent M m Q c
    · have hqc := root_of_no_parent_d hM hC hRow.forest hNo hRoot
      subst q
      have hh := hHeights.graph.unique c hq hc hHQ hHC
      obtain ⟨a,_,hA⟩ := hRun.base.values.total c (hHeights.graph.bounds hM.1 hHC).1
      have hNot : ¬M.mem r hc := by
        intro hlt
        obtain ⟨p,hParent⟩ := (hRun.parent_iff_lt_height_d hM hC hAt hA (hPositive c a hA) ((hHeights.rows c hc).mp hHC).2).mpr hlt
        exact hNo p (hRow.forest.bounds hM.1 hParent).2 hParent
      exact hh.trans (hLe.resolve_right hNot).symm
    · have hSome : ∃ p, M.mem p m ∧ MemPair M Q c p := by
        apply Classical.byContradiction
        intro hNot
        exact hNo (fun p hp hParent => hNot ⟨p,hp,hParent⟩)
      obtain ⟨p,hp,hParent⟩ := hSome
      obtain ⟨hpHeight,hpNat,hHP⟩ := hHeights.graph.total p hp
      have hRootP := (root_parent_iff_d hM hC hRow.forest hParent).mp hRoot
      have hLeP := (hHeights.parent_height_bounds_d hM hC hRun hPositive hAt hParent hHC hHP).2
      exact (rootHeightSchema_iff hM.1 C m Q Heights r p).mp (ih p (hRow.forest.left c p hParent))
        q hRootP.1 hq (hHeights.graph.bounds hM.1 hHQ).2 hpHeight hpNat hRootP hHQ hHP hLeP)
  have hcNat := (omega_isOrdinal_d hM hC.omega).transitive m hRun.space.width c (hHeights.graph.bounds hM.1 hHC).1
  exact (rootHeightSchema_iff hM.1 C m Q Heights r c).mp (hAll c ((omega_isOrdinal_d hM hC.omega).mem hcNat))
    q hRoot.1 hq (hHeights.graph.bounds hM.1 hHQ).2 hc (hHeights.graph.bounds hM.1 hHC).2 hRoot hHQ hHC hLe

theorem pseudo_candidate_exists_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory) {C : ExpressionData M.Domain} (hC : C.Valid M)
    {m : M.Domain} {R : RowStateSpace M.Domain} {V P H Heights c height : M.Domain} (hRun : RowRun M C m R V P H)
    (hHeights : HeightGraph M C m R V H Heights) (hPositive : ∀ j v, MemPair M V j v → M.mem C.zero v)
    (hHeight : MemPair M Heights c height) (hPos : M.mem C.zero height) : ∃ p, PseudoCandidate M C m R H Heights c p := by
  have hh := (hHeights.graph.bounds hM.1 hHeight).2
  rcases natural_cases hM hC.omega hh with hEmpty | ⟨r,hr,hs⟩
  · exact False.elim (hEmpty C.zero hPos)
  · obtain ⟨W,Q,hAt⟩ := hRun.at_exists_d hr
    have hRow := hRun.at_numeric_d hM hC hAt
    have hc := (hHeights.graph.bounds hM.1 hHeight).1
    obtain ⟨q,hRoot⟩ := root_exists_d hM hC hRow.forest hc
    obtain ⟨hq,hqNat,hHQ⟩ := hHeights.graph.total q hRoot.1
    have hqr := hHeights.root_height_d hM hC hRun hPositive hAt hRoot hHeight hHQ (Or.inr hs.predecessor_mem)
    have hAnc : Ancestor M C m Q q c := by
      rcases hRoot.2.2 with he | hAnc
      · subst q
        obtain ⟨a,_,hA⟩ := hRun.base.values.total c hc
        obtain ⟨p,hParent⟩ := (hRun.parent_iff_lt_height_d hM hC hAt hA (hPositive c a hA) ((hHeights.rows c height).mp hHeight).2).mpr hs.predecessor_mem
        exact False.elim (hRoot.2.1 p (hRow.forest.bounds hM.1 hParent).2 hParent)
      · exact hAnc
    exact ⟨q,height,hh,hq,hqNat,r,hr,hHeight,hHQ,⟨hr,Or.inr hs⟩,
      W,(hRun.space.values W).mpr hRow.values,Q,(hRun.space.forests Q).mpr hRow.forest,hAt,hAnc,Or.inr (hqr.symm ▸ hs)⟩

private def pseudoCandidateSetSchema : Project.Delta0UnarySchema 12 where
  body := pseudoCandidateFormula ⟨.bound 12,.bound 11,.bound 10,.bound 9,.bound 8⟩
    (.bound 7) (.bound 6) (.bound 5) (.bound 4) (.bound 3) (.bound 2) (.bound 1) (.bound 0)
  freeClosed := pseudoCandidateFormula_freeClosed ⟨rfl,rfl,rfl,rfl,rfl⟩ _ _ _ _ _ _ _ _ rfl rfl rfl rfl rfl rfl rfl rfl
  delta0 := pseudoCandidateFormula_delta0 _ _ _ _ _ _ _ _ _

theorem pseudo_parent_exists_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory) {C : ExpressionData M.Domain} (hC : C.Valid M)
    {m : M.Domain} {R : RowStateSpace M.Domain} {V P H Heights c height : M.Domain} (hRun : RowRun M C m R V P H)
    (hHeights : HeightGraph M C m R V H Heights) (hPositive : ∀ j v, MemPair M V j v → M.mem C.zero v)
    (hHeight : MemPair M Heights c height) (hPos : M.mem C.zero height) : ∃ p, PseudoParent M C m R H Heights c p := by
  let e := (((((((((((oneEnv C.omega).push C.zero).push C.one).push C.sequences).push C.expressions).push m).push R.states).push R.values).push R.forests).push H).push Heights).push c
  obtain ⟨L,hL⟩ := SetTheory.KP.separation_exists_d (KP1Y.models_weakKP hM) pseudoCandidateSetSchema e m
  have hφ (p : M.Domain) : Project.Formula.satisfies (e.push p) pseudoCandidateSetSchema.body ↔ PseudoCandidate M C m R H Heights c p :=
    pseudoCandidateFormula_iff hM.1 _ _ _ _ _ _ _ _ _ _
  have hRows (p : M.Domain) : M.mem p L ↔ PseudoCandidate M C m R H Heights c p := by
    have hr := hL p
    rw [hφ] at hr
    exact hr.trans ⟨And.right,fun h => ⟨(h.bounds hM.1).1,h⟩⟩
  obtain ⟨q,hQ⟩ := pseudo_candidate_exists_d hM hC hRun hHeights hPositive hHeight hPos
  have hcNat := (omega_isOrdinal_d hM hC.omega).transitive m hRun.space.width c (hHeights.graph.bounds hM.1 hHeight).1
  obtain ⟨p,hMax⟩ := greatest_below_exists_d (A := L) hM hC.omega hcNat ⟨q,(hQ.bounds hM.1).2.2,(hRows q).mpr hQ⟩
  exact ⟨p,⟨height,(hHeights.graph.bounds hM.1 hHeight).2,hHeight,hPos⟩,(hRows p).mp hMax.2.1,
    fun q hqc hQ => hMax.2.2 q hqc ((hRows q).mpr hQ)⟩

theorem PseudoForest.no_parent_iff_height_zero_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {m : M.Domain} {R : RowStateSpace M.Domain}
    {V P H Heights F c height : M.Domain} (hRun : RowRun M C m R V P H) (hHeights : HeightGraph M C m R V H Heights)
    (hPositive : ∀ j v, MemPair M V j v → M.mem C.zero v) (hF : PseudoForest M C m R H Heights F)
    (hHeight : MemPair M Heights c height) : NoParent M m F c ↔ height=C.zero := by
  constructor
  · intro hNone
    classical
    apply Classical.byContradiction
    intro hNe
    have hPos := (hC.zero_mem_iff hM (hHeights.graph.bounds hM.1 hHeight).2).mpr hNe
    obtain ⟨p,hParent⟩ := pseudo_parent_exists_d hM hC hRun hHeights hPositive hHeight hPos
    exact hNone p (hParent.2.1.bounds hM.1).1 ((hF.parents c p).mpr hParent)
  · intro hZero p _ hAt
    obtain ⟨height',_,hHeight',hPos⟩ := ((hF.parents c p).mp hAt).1
    have he := (hHeights.graph.unique c height' height hHeight' hHeight).trans hZero
    exact hC.zero_empty C.zero (he ▸ hPos)

theorem PseudoForest.parent_heights {M : SetTheory.Structure.{u}} {C : ExpressionData M.Domain}
    {m : M.Domain} {R : RowStateSpace M.Domain} {V H Heights F c p hc hp : M.Domain}
    (hHeights : HeightGraph M C m R V H Heights) (hF : PseudoForest M C m R H Heights F)
    (hParent : MemPair M F c p) (hHC : MemPair M Heights c hc) (hHP : MemPair M Heights p hp) : hp=hc ∨ M.SuccessorOf hc hp := by
  obtain ⟨hc',_,hp',_,_,_,hHC',hHP',_,_,_,_,_,_,_,hRel⟩ := ((hF.parents c p).mp hParent).2.1
  have hcc := hHeights.graph.unique c hc' hc hHC' hHC
  have hpp := hHeights.graph.unique p hp' hp hHP' hHP
  subst hc'
  subst hp'
  exact hRel

def RootsOne (M : SetTheory.Structure.{u}) (C : ExpressionData M.Domain) (m V P : M.Domain) : Prop :=
  ∀ c v, MemPair M V c v → NoParent M m P c → v=C.one

structure RootedRow (M : SetTheory.Structure.{u}) (C : ExpressionData M.Domain) (m V P : M.Domain) : Prop where
  row : NumericRow M C m V P
  positive : ∀ c v, MemPair M V c v → M.mem C.zero v
  rootsOne : RootsOne M C m V P

private theorem one_le_of_positive {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory) {C : ExpressionData M.Domain} (hC : C.Valid M)
    {v : M.Domain} (hv : M.mem v C.omega) (hPos : M.mem C.zero v) : C.one=v ∨ M.mem C.one v := by
  have hω := omega_isOrdinal_d hM hC.omega
  apply ordinal_subset_cases_d hM (hω.mem hC.one_nat) (hω.mem hv)
  intro x hx
  rcases (hC.one_succ x).mp hx with hEmpty | he
  · exact False.elim (hC.zero_empty x hEmpty)
  · exact (hM.1.eq_of_same_members x C.zero he).symm ▸ hPos

theorem Selects.roots_one_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory) {C : ExpressionData M.Domain} (hC : C.Valid M)
    {m F V P : M.Domain} (h : Selects true M C m F V P) (hPositive : ∀ c v, MemPair M V c v → M.mem C.zero v)
    (hRoots : RootsOne M C m V F) : RootsOne M C m V P := by
  intro c v hValue hNo
  classical
  by_cases hvOne : v=C.one
  · exact hvOne
  · have hvNat := (h.values.bounds hM.1 hValue).2
    have hOneLt := (one_le_of_positive hM hC hvNat (hPositive c v hValue)).resolve_left (fun he => hvOne he.symm)
    obtain ⟨q,hRoot⟩ := root_exists_d hM hC h.inherited (h.values.bounds hM.1 hValue).1
    obtain ⟨x,_,hQx⟩ := h.values.total q hRoot.1
    have hxOne := hRoots q x hQx hRoot.2.1
    have hQOne : MemPair M V q C.one := hxOne ▸ hQx
    have hAnc : Ancestor M C m F q c := by
      rcases hRoot.2.2 with he | hAnc
      · subst q
        exact False.elim (hvOne (h.values.unique c v C.one hValue hQOne))
      · exact hAnc
    exact False.elim ((h.no_parent_iff_d hM hC).mp hNo q
      ⟨hAnc,C.one,hC.one_nat,v,hvNat,hQOne,hValue,hOneLt,hC.one_succ.predecessor_mem⟩)

theorem Extraction.rooted_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory) {C : ExpressionData M.Domain} (hC : C.Valid M)
    {m V P Top Q : M.Domain} (hBase : RootedRow M C m V P) (h : Extraction M C m V P Top Q) : RootedRow M C m Top Q := by
  have hPositive := h.positive_d hM hC hBase.positive
  obtain ⟨R,H,Heights,F,hRun,hHeights,hTop,hF,hSelected⟩ := h
  have hRoots : RootsOne M C m Top F := by
    intro c v hTopAt hNo
    obtain ⟨height,hh,hHeight⟩ := hHeights.graph.total c (hTop.graph.bounds hM.1 hTopAt).1
    have hZero := (hF.no_parent_iff_height_zero_d hM hC hRun hHeights hBase.positive hHeight).mp hNo
    obtain ⟨height',_,hHeight',hValue⟩ := (hTop.rows c v).mp hTopAt
    have hHeightZero := (hHeights.graph.unique c height' height hHeight' hHeight).trans hZero
    subst height'
    have hOriginal := (hRun.value_initial_iff_d hM).mp hValue
    have hNoBase : NoParent M m P c := by
      intro p _ hParent
      have hLt := (hRun.parent_iff_lt_height_d hM hC (hRun.initial_row_at_d hM) hOriginal (hBase.positive c v hOriginal)
        ((hHeights.rows c height).mp hHeight).2).mp ⟨p,hParent⟩
      exact hC.zero_empty C.zero (hZero ▸ hLt)
    exact hBase.rootsOne c v hOriginal hNoBase
  exact ⟨hSelected.numeric_row,hPositive,hSelected.roots_one_d hM hC hPositive hRoots⟩

theorem Extraction.value_le_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory) {C : ExpressionData M.Domain} (hC : C.Valid M)
    {m V P Top Q c a v : M.Domain} (h : Extraction M C m V P Top Q) (hOriginal : MemPair M V c a) (hValue : MemPair M Top c v) :
    v=a ∨ M.mem v a := by
  obtain ⟨_,_,_,_,hRun,_,hTop,_,_⟩ := h
  exact hTop.le_initial_d hM hC hRun hOriginal hValue

theorem Extraction.value_lt_of_parent_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory) {C : ExpressionData M.Domain} (hC : C.Valid M)
    {m V P Top Q c p a v : M.Domain} (h : Extraction M C m V P Top Q)
    (hParent : MemPair M P c p) (hOriginal : MemPair M V c a) (hValue : MemPair M Top c v) : M.mem v a := by
  obtain ⟨R,H,Heights,F,hRun,hHeights,hTop,_,_⟩ := h
  obtain ⟨x,_,hX⟩ := hRun.base.values.total p (hRun.base.forest.bounds hM.1 hParent).2
  have hVals := hRun.base.parentValues c p x a hParent hX hOriginal
  have ha := (hRun.base.values.bounds hM.1 hOriginal).2
  have hPosA := ((omega_isOrdinal_d hM hC.omega).mem ha).transitive x hVals.2 C.zero hVals.1
  obtain ⟨height,hh,hHC,hAt⟩ := (hTop.rows c v).mp hValue
  have hHeight := ((hHeights.rows c height).mp hHC).2
  have hPosHeight := (hRun.parent_iff_lt_height_d hM hC (hRun.initial_row_at_d hM) hOriginal hPosA hHeight).mp ⟨p,hParent⟩
  have hSpec := hHeight.positive_spec hC hRun.base.values hOriginal hPosA
  obtain ⟨fuel,_,hDiff⟩ := truncated_difference_exists_d hM hC ha hh
  have hFuelLt := (truncated_difference_strict_d hM hC hDiff hPosHeight hSpec.1).2
  have hPosV := hTop.positive_d hM hC hRun hHeights hOriginal hPosA hValue
  rcases hRun.live_fuel_bound_d hM hC hh hAt hOriginal hDiff hPosV with he | hLess
  · exact he.symm ▸ hFuelLt
  · exact ((omega_isOrdinal_d hM hC.omega).mem ha).transitive fuel hFuelLt v hLess

theorem Extraction.value_lt_above_one_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory) {C : ExpressionData M.Domain} (hC : C.Valid M)
    {m V P Top Q c a v : M.Domain} (hBase : RootedRow M C m V P) (h : Extraction M C m V P Top Q)
    (hOriginal : MemPair M V c a) (hAbove : M.mem C.one a) (hValue : MemPair M Top c v) : M.mem v a := by
  classical
  by_cases hNone : NoParent M m P c
  · have he := hBase.rootsOne c a hOriginal hNone
    exact False.elim (SetTheory.KP.mem_irrefl_d (KP1Y.models_weakKP hM) C.one (he ▸ hAbove))
  · have hSome : ∃ p, MemPair M P c p := by
      apply Classical.byContradiction
      intro hNot
      exact hNone (fun p _ hp => hNot ⟨p,hp⟩)
    obtain ⟨p,hParent⟩ := hSome
    exact h.value_lt_of_parent_d hM hC hParent hOriginal hValue

theorem selected_legal_rooted_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory) {C : ExpressionData M.Domain} (hC : C.Valid M)
    {m V F P : M.Domain} (hLegal : LegalAt M C.omega C.zero C.one V m) (hLinear : LinearForest M C.omega m F)
    (hSelected : Selects true M C m F V P) : RootedRow M C m V P := by
  have hPositive : ∀ c v, MemPair M V c v → M.mem C.zero v := by
    intro c v hAt
    exact hLegal.2.1 c (hLegal.1.2.bounds hM.1 hAt).1 v (hLegal.1.2.bounds hM.1 hAt).2 hAt
  refine ⟨hSelected.numeric_row,hPositive,hSelected.roots_one_d hM hC hPositive ?_⟩
  intro c v hAt hNo
  have hc := (hLegal.1.2.bounds hM.1 hAt).1
  have hcNat := (omega_isOrdinal_d hM hC.omega).transitive m hLegal.1.1 c hc
  have hcZero : c=C.zero := by
    classical
    apply Classical.byContradiction
    intro hNe
    have hAnc := (linear_forest_ancestor_iff_d hM hC hLinear hc).mpr ((hC.zero_mem_iff hM hcNat).mpr hNe)
    exact no_ancestor_of_no_parent_d hM hC hLinear.1 hNo hAnc
  have hFirst : MemPair M V C.zero C.one := hLegal.2.2.resolve_left (fun hm => hC.zero_empty c (hm ▸ hc))
  subst c
  exact hLegal.1.2.unique C.zero v C.one hAt hFirst

theorem rooted_sequence_row_exists_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory) {C : ExpressionData M.Domain} (hC : C.Valid M)
    {m V : M.Domain} (hLegal : LegalAt M C.omega C.zero C.one V m) :
    ∃ F P, LinearForest M C.omega m F ∧ Selects true M C m F V P ∧ RootedRow M C m V P := by
  obtain ⟨F,hF⟩ := linear_forest_exists_d hM hC.omega hLegal.1.1
  obtain ⟨P,hP⟩ := select_forest_exists_d hM true hC hF.1 hLegal.1.2
  exact ⟨F,P,hF,hP,selected_legal_rooted_d hM hC hLegal hF hP⟩

theorem rooted_extraction_exists_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory) {C : ExpressionData M.Domain} (hC : C.Valid M)
    {m V P : M.Domain} (hBase : RootedRow M C m V P) : ∃ Top Q, Extraction M C m V P Top Q ∧ RootedRow M C m Top Q := by
  obtain ⟨Top,Q,h⟩ := extraction_exists_d hM hC hBase.row
  exact ⟨Top,Q,h,h.rooted_d hM hC hBase⟩

end KP1Y.OneYFinite
