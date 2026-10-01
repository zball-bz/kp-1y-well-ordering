import KP1Y.OneYAncestry
import KP1Y.OneYForestSpace
import KP1Y.OneYForestSelection
import KP1Y.OneYNaturalDifferenceFacts
import KP1Y.OneYLinearForest

/-! 内部 1-Y 数值山形。数值行与继承父森林共同构成状态；零表示缺失数值格。 -/
namespace KP1Y.OneYFinite
open YesMetaZFC YesMetaZFC.SetTheory YesMetaZFC.SetTheory.Definitional
open KP1Y.Kuratowski KP1Y.Functions KP1Y.Bounded
universe u

structure NumericRow (M : SetTheory.Structure.{u}) (C : ExpressionData M.Domain) (m V P : M.Domain) : Prop where
  values : Graph M V m C.omega
  forest : Forest M C.omega m P
  parentValues : ∀ c p x y, MemPair M P c p → MemPair M V p x → MemPair M V c y → M.mem C.zero x ∧ M.mem x y

def DifferenceAt (M : SetTheory.Structure.{u}) (C : ExpressionData M.Domain) (m V P c d : M.Domain) : Prop :=
  (NoParent M m P c ∧ d=C.zero) ∨ ∃ p, M.mem p m ∧ ∃ x, M.mem x C.omega ∧ ∃ y, M.mem y C.omega ∧
    MemPair M P c p ∧ MemPair M V c x ∧ MemPair M V p y ∧ TruncatedDifference M C.omega C.zero x y d

structure DifferenceGraph (M : SetTheory.Structure.{u}) (C : ExpressionData M.Domain) (m V P D : M.Domain) : Prop where
  graph : Graph M D m C.omega
  rows : ∀ c d, MemPair M D c d ↔ M.mem c m ∧ DifferenceAt M C m V P c d

theorem difference_at_exists_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {m V P c : M.Domain}
    (hV : Graph M V m C.omega) (hc : M.mem c m) :
    ∃ d, M.mem d C.omega ∧ DifferenceAt M C m V P c d := by
  classical
  by_cases hNone : NoParent M m P c
  · exact ⟨C.zero,hC.zero_nat,Or.inl ⟨hNone,rfl⟩⟩
  · have hSome : ∃ p, M.mem p m ∧ MemPair M P c p := by
      apply Classical.byContradiction
      intro hNot
      exact hNone (fun p hp hAt => hNot ⟨p,hp,hAt⟩)
    obtain ⟨p,hp,hAt⟩ := hSome
    obtain ⟨x,hx,hCx⟩ := hV.total c hc
    obtain ⟨y,hy,hPy⟩ := hV.total p hp
    obtain ⟨d,hd,hDiff⟩ := truncated_difference_exists_d hM hC hx hy
    exact ⟨d,hd,Or.inr ⟨p,hp,x,hx,y,hy,hAt,hCx,hPy,hDiff⟩⟩

theorem DifferenceAt.natural {M : SetTheory.Structure.{u}} (he : Extensional M) {C : ExpressionData M.Domain} (hC : C.Valid M)
    {m V P c d : M.Domain} (h : DifferenceAt M C m V P c d) : M.mem d C.omega := by
  rcases h with ⟨_,rfl⟩ | ⟨_,_,_,_,_,_,_,_,_,_,_,H,hH,hAt⟩
  · exact hC.zero_nat
  · exact (hH.1.bounds he hAt).2

theorem difference_at_unique_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {m V P c d e : M.Domain}
    (hV : Graph M V m C.omega) (hF : Forest M C.omega m P)
    (hd : DifferenceAt M C m V P c d) (he : DifferenceAt M C m V P c e) : d=e := by
  rcases hd with ⟨hNone,hd⟩ | ⟨p,hp,x,_,y,_,hPc,hCx,hPy,hDiff⟩
  · rcases he with ⟨_,he⟩ | ⟨p,hp,_,_,_,_,hPc,_⟩
    · exact hd.trans he.symm
    · exact False.elim (hNone p hp hPc)
  · rcases he with ⟨hNone,_⟩ | ⟨p',_,x',_,y',_,hPc',hCx',hPy',hDiff'⟩
    · exact False.elim (hNone p hp hPc)
    · have hpp := hF.unique c p p' hPc hPc'
      subst p'
      have hxx := hV.unique c x x' hCx hCx'
      have hyy := hV.unique p y y' hPy hPy'
      subst x'
      subst y'
      exact truncated_difference_unique_d hM hC hDiff hDiff'

private def differenceMatrix : KP1Y.WitnessMatrix 5 where
  body := .disj (.conj (noParentFormula (.bound 5) (.bound 3) (.bound 2)) (Project.Formula.extensionalEq (.bound 1) (.bound 6)))
    (Project.Formula.existsMem (.bound 5) (Project.Formula.existsMem (.bound 8) (Project.Formula.existsMem (.bound 9)
      (.conj (memPairFormula (.bound 6) (.bound 5) (.bound 2))
        (.conj (memPairFormula (.bound 7) (.bound 5) (.bound 1))
          (.conj (memPairFormula (.bound 7) (.bound 2) (.bound 0))
            (.conj (predecessorIteratorFormula (.bound 10) (.bound 9) (.bound 1) (.bound 3))
              (memPairFormula (.bound 3) (.bound 0) (.bound 4)))))))))
  freeClosed := by
    simp [noParentFormula,predecessorIteratorFormula,previousLengthFormula,successorFormula,
      graphFormula,memPairFormula,codeFormula,pairFormula,Project.Formula.forallMem,Project.Formula.existsMem,Definitional.Formula.FreeClosed]
  delta0 := .disj (.conj (noParentFormula_delta0 _ _ _) (.atom _ _ _))
    (.existsMem _ (.existsMem _ (.existsMem _ (.conj (memPairFormula_delta0 _ _ _)
      (.conj (memPairFormula_delta0 _ _ _) (.conj (memPairFormula_delta0 _ _ _)
        (.conj (predecessorIteratorFormula_delta0 _ _ _ _) (memPairFormula_delta0 _ _ _))))))))

private theorem differenceMatrix_iff {M : SetTheory.Structure.{u}} (he : Extensional M)
    (C : ExpressionData M.Domain) (m V P c d H : M.Domain) :
    Project.Formula.satisfies ((((((((oneEnv C.omega).push C.zero).push m).push V).push P).push c).push d).push H) differenceMatrix.body ↔
      (NoParent M m P c ∧ d=C.zero) ∨ ∃ p, M.mem p m ∧ ∃ x, M.mem x C.omega ∧ ∃ y, M.mem y C.omega ∧
        MemPair M P c p ∧ MemPair M V c x ∧ MemPair M V p y ∧ PredecessorIterator M C.omega C.zero x H ∧ MemPair M H y d := by
  simp only [differenceMatrix,Project.Formula.satisfies_disj_iff,Project.Formula.satisfies_conj_iff,
    Project.Formula.satisfies_existsMem_iff,Project.Formula.satisfies_extensionalEq_iff_eq he,
    noParentFormula_iff he,memPairFormula_iff he,predecessorIteratorFormula_iff he]
  rfl

private theorem differenceMatrix_exists_iff {M : SetTheory.Structure.{u}} (he : Extensional M)
    (C : ExpressionData M.Domain) (m V P c d : M.Domain) :
    (∃ H, Project.Formula.satisfies ((((((((oneEnv C.omega).push C.zero).push m).push V).push P).push c).push d).push H) differenceMatrix.body) ↔
      DifferenceAt M C m V P c d := by
  simp only [differenceMatrix_iff he]
  constructor
  · rintro ⟨H,h⟩
    rcases h with hNone | ⟨p,hp,x,hx,y,hy,hPc,hCx,hPy,hH,hAt⟩
    · exact Or.inl hNone
    · exact Or.inr ⟨p,hp,x,hx,y,hy,hPc,hCx,hPy,hx,hy,H,hH,hAt⟩
  · rintro (hNone | ⟨p,hp,x,hx,y,hy,hPc,hCx,hPy,_,_,H,hH,hAt⟩)
    · exact ⟨C.zero,Or.inl hNone⟩
    · exact ⟨H,Or.inr ⟨p,hp,x,hx,y,hy,hPc,hCx,hPy,hH,hAt⟩⟩

theorem difference_graph_exists_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {m V P : M.Domain}
    (hV : Graph M V m C.omega) (hF : Forest M C.omega m P) : ∃ D, DifferenceGraph M C m V P D := by
  let e := ((((oneEnv C.omega).push C.zero).push m).push V).push P
  obtain ⟨D,hGraph,hRows⟩ := sigma_function_graph_d hM differenceMatrix e m C.omega
    (by
      intro c hc
      obtain ⟨d,_,hDiff⟩ := difference_at_exists_d hM hC hV hc
      obtain ⟨H,hH⟩ := (differenceMatrix_exists_iff hM.1 C m V P c d).mpr hDiff
      exact ⟨d,H,hH⟩)
    (fun c _ d H hH => ((differenceMatrix_exists_iff hM.1 C m V P c d).mp ⟨H,hH⟩).natural hM.1 hC)
    (fun c _ d d' H H' hH hH' => difference_at_unique_d hM hC hV hF
      ((differenceMatrix_exists_iff hM.1 C m V P c d).mp ⟨H,hH⟩)
      ((differenceMatrix_exists_iff hM.1 C m V P c d').mp ⟨H',hH'⟩))
  refine ⟨D,hGraph,?_⟩
  intro c d
  have hr := hRows c d
  rw [differenceMatrix_exists_iff hM.1] at hr
  exact hr.trans ⟨fun h => ⟨h.1,h.2.2⟩,fun h => ⟨h.1,h.2.natural hM.1 hC,h.2⟩⟩

theorem DifferenceGraph.unique_d {M : SetTheory.Structure.{u}} (he : Extensional M)
    {C : ExpressionData M.Domain} {m V P D E : M.Domain}
    (hD : DifferenceGraph M C m V P D) (hE : DifferenceGraph M C m V P E) : D=E := by
  apply hD.graph.ext he hE.graph
  intro c _ d
  exact (hD.rows c d).trans (hE.rows c d).symm

theorem DifferenceGraph.at_parent_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} {m V P D c p x y d : M.Domain}
    (hV : Graph M V m C.omega) (hF : Forest M C.omega m P) (hD : DifferenceGraph M C m V P D)
    (hPc : MemPair M P c p) (hCx : MemPair M V c x) (hPy : MemPair M V p y) (hCd : MemPair M D c d) :
    TruncatedDifference M C.omega C.zero x y d := by
  rcases ((hD.rows c d).mp hCd).2 with ⟨hNone,_⟩ | ⟨p',_,x',_,y',_,hPc',hCx',hPy',hDiff⟩
  · exact False.elim (hNone p (hF.bounds hM.1 hPc).2 hPc)
  · have hpp := hF.unique c p p' hPc hPc'
    subst p'
    have hxx := hV.unique c x x' hCx hCx'
    have hyy := hV.unique p y y' hPy hPy'
    subst x'
    subst y'
    exact hDiff

theorem DifferenceGraph.at_no_parent {M : SetTheory.Structure.{u}} {C : ExpressionData M.Domain}
    {m V P D c d : M.Domain} (hD : DifferenceGraph M C m V P D) (hNone : NoParent M m P c)
    (hCd : MemPair M D c d) : d=C.zero := by
  rcases ((hD.rows c d).mp hCd).2 with ⟨_,hd⟩ | ⟨p,hp,_,_,_,_,hPc,_⟩
  · exact hd
  · exact False.elim (hNone p hp hPc)

theorem Selects.numeric_row {M : SetTheory.Structure.{u}} {C : ExpressionData M.Domain} {m F V P : M.Domain}
    (h : Selects true M C m F V P) : NumericRow M C m V P := by
  refine ⟨h.values,h.forest,?_⟩
  intro c p x y hParent hPx hCy
  obtain ⟨x',_,y',_,hPx',hCy',hLt,hPos⟩ := h.parent_values hParent
  have hxx := h.values.unique p x x' hPx hPx'
  have hyy := h.values.unique c y y' hCy hCy'
  subst x'
  subst y'
  exact ⟨hPos,hLt⟩

structure RowNext (M : SetTheory.Structure.{u}) (C : ExpressionData M.Domain) (m V P W Q : M.Domain) : Prop where
  difference : DifferenceGraph M C m V P W
  selection : Selects true M C m P W Q

theorem row_next_exists_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {m V P : M.Domain}
    (hV : Graph M V m C.omega) (hP : Forest M C.omega m P) :
    ∃ W Q, RowNext M C m V P W Q ∧ NumericRow M C m W Q := by
  obtain ⟨W,hW⟩ := difference_graph_exists_d hM hC hV hP
  obtain ⟨Q,hQ⟩ := select_forest_exists_d hM true hC hP hW.graph
  exact ⟨W,Q,⟨hW,hQ⟩,hQ.numeric_row⟩

theorem RowNext.unique {M : SetTheory.Structure.{u}} (he : Extensional M) {C : ExpressionData M.Domain}
    {m V P W Q W' Q' : M.Domain} (h : RowNext M C m V P W Q) (h' : RowNext M C m V P W' Q') : W=W' ∧ Q=Q' := by
  have hWW := h.difference.unique_d he h'.difference
  subst W'
  exact ⟨rfl,h.selection.unique he h'.selection⟩

structure RowStateSpace (α : Type u) where
  values : α
  forests : α
  states : α

structure RowStateSpace.Valid (M : SetTheory.Structure.{u}) (C : ExpressionData M.Domain) (m : M.Domain)
    (R : RowStateSpace M.Domain) : Prop where
  width : M.mem m C.omega
  values : ∀ V, M.mem V R.values ↔ Graph M V m C.omega
  forests : ∀ P, M.mem P R.forests ↔ Forest M C.omega m P
  states : IsProduct M R.states R.values R.forests

private def widthValuesSchema : Project.Delta0UnarySchema 2 where
  body := graphFormula (.bound 0) (.bound 1) (.bound 2)
  freeClosed := by
    simp [graphFormula,memPairFormula,codeFormula,pairFormula,Project.Formula.forallMem,Project.Formula.existsMem,Definitional.Formula.FreeClosed]
  delta0 := graphFormula_delta0 _ _ _

theorem row_state_space_exists_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {m : M.Domain} (hm : M.mem m C.omega) :
    ∃ R, RowStateSpace.Valid M C m R := by
  obtain ⟨Forests,hForests⟩ := forest_space_exists_d hM hC hm
  obtain ⟨Values,hValues⟩ := SetTheory.KP.separation_exists_d (KP1Y.models_weakKP hM) widthValuesSchema
    ((oneEnv C.omega).push m) C.sequences
  have hRows (V : M.Domain) : M.mem V Values ↔ Graph M V m C.omega := by
    have hφ : Project.Formula.satisfies (((oneEnv C.omega).push m).push V) widthValuesSchema.body ↔ Graph M V m C.omega :=
      graphFormula_iff hM.1 _ _ _ _
    exact ((hValues V).trans (and_congr Iff.rfl hφ)).trans
      ⟨And.right,fun hV => ⟨(hC.sequences V).mpr ⟨m,hm,hV⟩,hV⟩⟩
  obtain ⟨States,hStates⟩ := product_exists hM Values Forests
  exact ⟨⟨Values,Forests,States⟩,hm,hRows,hForests,hStates⟩

theorem RowStateSpace.Valid.encode_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} {m : M.Domain} {R : RowStateSpace M.Domain} (hR : R.Valid M C m)
    {V P : M.Domain} (hV : Graph M V m C.omega) (hP : Forest M C.omega m P) :
    ∃ state, M.mem state R.states ∧ Codes M state V P := by
  obtain ⟨state,hCode⟩ := codes_total hM V P
  exact ⟨state,(hR.states state).mpr ⟨V,(hR.values V).mpr hV,P,(hR.forests P).mpr hP,hCode⟩,hCode⟩

theorem RowStateSpace.Valid.decode {M : SetTheory.Structure.{u}} {C : ExpressionData M.Domain}
    {m : M.Domain} {R : RowStateSpace M.Domain} (hR : R.Valid M C m) {state : M.Domain} (hs : M.mem state R.states) :
    ∃ V P, Codes M state V P ∧ Graph M V m C.omega ∧ Forest M C.omega m P := by
  obtain ⟨V,hV,P,hP,hCode⟩ := (hR.states state).mp hs
  exact ⟨V,P,hCode,(hR.values V).mp hV,(hR.forests P).mp hP⟩

private def tableDifferenceFormula {n : Nat} (w Pairs Table x y d : Project.Term n) : Project.Formula 1 n :=
  .conj (.mem x w) (.conj (.mem y w) (Project.Formula.existsMem Pairs
    (.conj (codeFormula (.bound 0) x.weaken y.weaken) (memPairFormula Table.weaken (.bound 0) d.weaken))))

private theorem tableDifferenceFormula_delta0 {n : Nat} (w Pairs Table x y d : Project.Term n) :
    (tableDifferenceFormula w Pairs Table x y d).IsDelta0 :=
  .conj (.mem _ _) (.conj (.mem _ _) (.existsMem _ (.conj (codeFormula_delta0 _ _ _) (memPairFormula_delta0 _ _ _))))

private theorem tableDifferenceFormula_iff {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} {Pairs Table : M.Domain} (hTable : DifferenceTable M C Pairs Table)
    {n : Nat} (e : Env M n) (w ps tab x y d : Project.Term n)
    (hw : w.eval e=C.omega) (hps : ps.eval e=Pairs) (htab : tab.eval e=Table) :
    Project.Formula.satisfies e (tableDifferenceFormula w ps tab x y d) ↔
      TruncatedDifference M C.omega C.zero (x.eval e) (y.eval e) (d.eval e) := by
  simp only [tableDifferenceFormula,Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_mem_iff,
    Project.Formula.satisfies_existsMem_iff,codeFormula_iff hM.1,memPairFormula_iff hM.1,Term.eval_weaken,hw,hps,htab]
  constructor
  · rintro ⟨hx,hy,key,_,hCode,hAt⟩
    exact (hTable.rows _ hx _ hy key hCode _).mp hAt
  · intro hDiff
    obtain ⟨key,hCode⟩ := codes_total hM (x.eval e) (y.eval e)
    exact ⟨hDiff.1,hDiff.2.1,key,(hTable.pairs key).mpr ⟨_,hDiff.1,_,hDiff.2.1,hCode⟩,
      hCode,(hTable.rows _ hDiff.1 _ hDiff.2.1 key hCode _).mpr hDiff⟩

private def differenceAtTableFormula {n : Nat} (C : ExpressionData (Project.Term n))
    (Pairs Table m V P c d : Project.Term n) : Project.Formula 1 n :=
  .disj (.conj (noParentFormula m P c) (Project.Formula.extensionalEq d C.zero))
    (Project.Formula.existsMem m (Project.Formula.existsMem C.omega.weaken (Project.Formula.existsMem C.omega.weaken.weaken
      (.conj (memPairFormula P.weaken.weaken.weaken c.weaken.weaken.weaken (.bound 2))
        (.conj (memPairFormula V.weaken.weaken.weaken c.weaken.weaken.weaken (.bound 1))
          (.conj (memPairFormula V.weaken.weaken.weaken (.bound 2) (.bound 0))
            (tableDifferenceFormula C.omega.weaken.weaken.weaken Pairs.weaken.weaken.weaken Table.weaken.weaken.weaken
              (.bound 1) (.bound 0) d.weaken.weaken.weaken)))))))

private theorem differenceAtTableFormula_delta0 {n : Nat} (C : ExpressionData (Project.Term n))
    (Pairs Table m V P c d : Project.Term n) : (differenceAtTableFormula C Pairs Table m V P c d).IsDelta0 :=
  .disj (.conj (noParentFormula_delta0 _ _ _) (.atom _ _ _)) (.existsMem _ (.existsMem _ (.existsMem _
    (.conj (memPairFormula_delta0 _ _ _) (.conj (memPairFormula_delta0 _ _ _)
      (.conj (memPairFormula_delta0 _ _ _) (tableDifferenceFormula_delta0 _ _ _ _ _ _)))))))

private theorem differenceAtTableFormula_iff {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {n : Nat} (e : Env M n) (C : ExpressionData (Project.Term n)) (Pairs Table m V P c d : Project.Term n)
    (hTable : DifferenceTable M (C.eval e) (Pairs.eval e) (Table.eval e)) :
    Project.Formula.satisfies e (differenceAtTableFormula C Pairs Table m V P c d) ↔
      DifferenceAt M (C.eval e) (m.eval e) (V.eval e) (P.eval e) (c.eval e) (d.eval e) := by
  simp only [differenceAtTableFormula,Project.Formula.satisfies_disj_iff,Project.Formula.satisfies_conj_iff,
    noParentFormula_iff hM.1,Project.Formula.satisfies_extensionalEq_iff_eq hM.1,Project.Formula.satisfies_existsMem_iff,
    memPairFormula_iff hM.1,Term.eval_weaken]
  have hLookup (p x y : M.Domain) := tableDifferenceFormula_iff hM hTable (((e.push p).push x).push y)
    C.omega.weaken.weaken.weaken Pairs.weaken.weaken.weaken Table.weaken.weaken.weaken (.bound 1) (.bound 0) d.weaken.weaken.weaken (by simp [Term.eval_weaken,ExpressionData.eval,ExpressionData.map]) (by simp [Term.eval_weaken]) (by simp [Term.eval_weaken])
  simp only [hLookup,Term.eval_weaken]
  rfl

private def differenceGraphTableFormula {n : Nat} (C : ExpressionData (Project.Term n))
    (Pairs Table m V P W : Project.Term n) : Project.Formula 1 n :=
  .conj (graphFormula W m C.omega) (Project.Formula.forallMem m (Project.Formula.forallMem C.omega.weaken
    (.iff (memPairFormula W.weaken.weaken (.bound 1) (.bound 0))
      (differenceAtTableFormula C.weaken.weaken Pairs.weaken.weaken Table.weaken.weaken m.weaken.weaken
        V.weaken.weaken P.weaken.weaken (.bound 1) (.bound 0)))))

private theorem differenceGraphTableFormula_delta0 {n : Nat} (C : ExpressionData (Project.Term n))
    (Pairs Table m V P W : Project.Term n) : (differenceGraphTableFormula C Pairs Table m V P W).IsDelta0 :=
  .conj (graphFormula_delta0 _ _ _) (.forallMem _ (.forallMem _ (.iff (memPairFormula_delta0 _ _ _)
    (differenceAtTableFormula_delta0 _ _ _ _ _ _ _ _))))

private theorem differenceGraphTableFormula_freeClosed {n : Nat} {C : ExpressionData (Project.Term n)} (hC : C.Closed)
    (Pairs Table m V P W : Project.Term n) (hpairs : Pairs.freeSupport=[]) (htable : Table.freeSupport=[])
    (hm : m.freeSupport=[]) (hV : V.freeSupport=[]) (hP : P.freeSupport=[]) (hW : W.freeSupport=[]) :
    (differenceGraphTableFormula C Pairs Table m V P W).FreeClosed := by
  simp [differenceGraphTableFormula,differenceAtTableFormula,tableDifferenceFormula,noParentFormula,
    ExpressionData.weaken,ExpressionData.map,graphFormula,memPairFormula,codeFormula,pairFormula,
    Project.Formula.forallMem,Project.Formula.existsMem,Definitional.Formula.FreeClosed,
    hC.omega,hC.zero,hpairs,htable,hm,hV,hP,hW]

private theorem differenceGraphTableFormula_iff {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {n : Nat} (e : Env M n) (C : ExpressionData (Project.Term n)) (Pairs Table m V P W : Project.Term n)
    (hC : (C.eval e).Valid M) (hTable : DifferenceTable M (C.eval e) (Pairs.eval e) (Table.eval e)) :
    Project.Formula.satisfies e (differenceGraphTableFormula C Pairs Table m V P W) ↔
      DifferenceGraph M (C.eval e) (m.eval e) (V.eval e) (P.eval e) (W.eval e) := by
  have hAt (c d : M.Domain) := differenceAtTableFormula_iff hM ((e.push c).push d) C.weaken.weaken
    Pairs.weaken.weaken Table.weaken.weaken m.weaken.weaken V.weaken.weaken P.weaken.weaken (.bound 1) (.bound 0) (by simpa only [ExpressionData.eval_weaken,Term.eval_weaken] using hTable)
  simp only [ExpressionData.eval_weaken,Term.eval_weaken] at hAt
  simp only [differenceGraphTableFormula,Project.Formula.satisfies_conj_iff,graphFormula_iff hM.1,
    Project.Formula.satisfies_forallMem_iff,Project.Formula.satisfies_iff_iff,memPairFormula_iff hM.1,Term.eval_weaken,hAt]
  constructor
  · rintro ⟨hG,hRows⟩
    refine ⟨hG,?_⟩
    intro c d
    constructor
    · intro hcd
      obtain ⟨hc,hd⟩ := hG.bounds hM.1 hcd
      exact ⟨hc,(hRows c hc d hd).mp hcd⟩
    · rintro ⟨hc,hDiff⟩
      exact (hRows c hc d (hDiff.natural hM.1 hC)).mpr hDiff
  · intro hG
    exact ⟨hG.graph,fun c hc d _ => (hG.rows c d).trans ⟨And.right,fun h => ⟨hc,h⟩⟩⟩

private def rowStepTerms : ExpressionData (Project.Term 16) := ⟨.bound 15,.bound 14,.bound 13,.bound 12,.bound 11⟩

private theorem rowStepTerms_closed : rowStepTerms.Closed := ⟨rfl,rfl,rfl,rfl,rfl⟩

private def rowStepSchema : Project.Delta0BinarySchema 10 where
  body := Project.Formula.existsMem (.bound 5) (Project.Formula.existsMem (.bound 5)
    (Project.Formula.existsMem (.bound 7) (Project.Formula.existsMem (.bound 7)
      (.conj (codeFormula (.bound 5) (.bound 3) (.bound 2))
        (.conj (codeFormula (.bound 4) (.bound 1) (.bound 0))
          (.conj (differenceGraphTableFormula rowStepTerms (.bound 7) (.bound 6) (.bound 10) (.bound 3) (.bound 2) (.bound 1))
            (selectsFormula true rowStepTerms (.bound 10) (.bound 2) (.bound 1) (.bound 0))))))))
  freeClosed := by
    have hDiff := differenceGraphTableFormula_freeClosed rowStepTerms_closed
      (.bound 7) (.bound 6) (.bound 10) (.bound 3) (.bound 2) (.bound 1) rfl rfl rfl rfl rfl rfl
    have hSelect := selectsFormula_freeClosed true rowStepTerms_closed
      (.bound 10) (.bound 2) (.bound 1) (.bound 0) rfl rfl rfl rfl
    simp [Project.Formula.existsMem,Definitional.Formula.FreeClosed,codeFormula,pairFormula,
      Project.Formula.forallMem,hDiff,hSelect]
  delta0 := .existsMem _ (.existsMem _ (.existsMem _ (.existsMem _
    (.conj (codeFormula_delta0 _ _ _) (.conj (codeFormula_delta0 _ _ _)
      (.conj (differenceGraphTableFormula_delta0 _ _ _ _ _ _ _) (selectsFormula_delta0 _ _ _ _ _ _)))))))

private def rowStepEnv {M : SetTheory.Structure.{u}} (C : ExpressionData M.Domain) (m : M.Domain)
    (R : RowStateSpace M.Domain) (Pairs Table : M.Domain) : Env M 10 :=
  (((((((((oneEnv C.omega).push C.zero).push C.one).push C.sequences).push C.expressions).push m).push R.values).push R.forests).push Pairs).push Table

def RowTransition (M : SetTheory.Structure.{u}) (C : ExpressionData M.Domain) (m source target : M.Domain) : Prop :=
  ∃ V P W Q, Codes M source V P ∧ Codes M target W Q ∧ RowNext M C m V P W Q

private theorem rowStepSchema_iff {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {m : M.Domain} {R : RowStateSpace M.Domain} (hR : R.Valid M C m)
    {Pairs Table : M.Domain} (hTable : DifferenceTable M C Pairs Table) {source target : M.Domain}
    (hSource : M.mem source R.states) :
    KP1Y.Iteration.nextDenote rowStepSchema (rowStepEnv C m R Pairs Table) source target ↔ RowTransition M C m source target := by
  let e := rowStepEnv C m R Pairs Table
  have hDiff (V P W Q : M.Domain) := differenceGraphTableFormula_iff hM ((((((e.push source).push target).push V).push P).push W).push Q)
    rowStepTerms (.bound 7) (.bound 6) (.bound 10) (.bound 3) (.bound 2) (.bound 1) hC hTable
  simp only [KP1Y.Iteration.nextDenote,rowStepSchema,Project.Formula.satisfies_existsMem_iff,
    Project.Formula.satisfies_conj_iff,codeFormula_iff hM.1,selectsFormula_iff hM.1]
  change (∃ V, M.mem V R.values ∧ ∃ P, M.mem P R.forests ∧ ∃ W, M.mem W R.values ∧ ∃ Q, M.mem Q R.forests ∧
    Codes M source V P ∧ Codes M target W Q ∧
      Project.Formula.satisfies ((((((e.push source).push target).push V).push P).push W).push Q)
        (differenceGraphTableFormula rowStepTerms (.bound 7) (.bound 6) (.bound 10) (.bound 3) (.bound 2) (.bound 1)) ∧
      Selects true M C m P W Q) ↔ _
  simp only [hDiff]
  constructor
  · rintro ⟨V,_,P,_,W,_,Q,_,hIn,hOut,hDifference,hSelection⟩
    exact ⟨V,P,W,Q,hIn,hOut,hDifference,hSelection⟩
  · rintro ⟨V,P,W,Q,hIn,hOut,hNext⟩
    obtain ⟨V',hV',P',hP',hSourceCode⟩ := (hR.states source).mp hSource
    obtain ⟨hVV,hPP⟩ := codes_injective hM.1 hIn hSourceCode
    subst V'
    subst P'
    exact ⟨V,hV',P,hP',W,(hR.values W).mpr hNext.difference.graph,Q,(hR.forests Q).mpr hNext.selection.forest,
      hIn,hOut,hNext.difference,hNext.selection⟩

theorem row_transition_unique {M : SetTheory.Structure.{u}} (he : Extensional M) {C : ExpressionData M.Domain}
    {m source target target' : M.Domain} (h : RowTransition M C m source target) (h' : RowTransition M C m source target') : target=target' := by
  obtain ⟨V,P,W,Q,hIn,hOut,hNext⟩ := h
  obtain ⟨V',P',W',Q',hIn',hOut',hNext'⟩ := h'
  obtain ⟨hVV,hPP⟩ := codes_injective he hIn hIn'
  subst V'
  subst P'
  obtain ⟨hWW,hQQ⟩ := hNext.unique he hNext'
  subst W'
  subst Q'
  exact codes_unique he hOut hOut'

structure RowRun (M : SetTheory.Structure.{u}) (C : ExpressionData M.Domain) (m : M.Domain)
    (R : RowStateSpace M.Domain) (V P H : M.Domain) : Prop where
  space : R.Valid M C m
  base : NumericRow M C m V P
  graph : Graph M H C.omega R.states
  initial : ∀ state, Codes M state V P → MemPair M H C.zero state
  transition : ∀ i j source target, M.SuccessorOf j i → MemPair M H i source → MemPair M H j target → RowTransition M C m source target

theorem row_run_exists_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {m : M.Domain} {R : RowStateSpace M.Domain} (hR : R.Valid M C m)
    {V P : M.Domain} (hBase : NumericRow M C m V P) : ∃ H, RowRun M C m R V P H := by
  obtain ⟨Pairs,Table,hTable⟩ := difference_table_exists_d hM hC
  obtain ⟨base,hBaseMem,hBaseCode⟩ := hR.encode_d hM hBase.values hBase.forest
  obtain ⟨H,hH⟩ := KP1Y.Iteration.iterator_exists_d hM rowStepSchema (rowStepEnv C m R Pairs Table) hC.omega hBaseMem
    (by
      intro source hSource
      obtain ⟨X,Y,hCode,hX,hY⟩ := hR.decode hSource
      obtain ⟨W,Q,hNext,_⟩ := row_next_exists_d hM hC hX hY
      obtain ⟨target,hTarget,hTargetCode⟩ := hR.encode_d hM hNext.difference.graph hNext.selection.forest
      exact ⟨target,hTarget,(rowStepSchema_iff hM hC hR hTable hSource).mpr ⟨X,Y,W,Q,hCode,hTargetCode,hNext⟩⟩)
    (fun source hSource target _ target' _ hNext hNext' => row_transition_unique hM.1
      ((rowStepSchema_iff hM hC hR hTable hSource).mp hNext)
      ((rowStepSchema_iff hM hC hR hTable hSource).mp hNext'))
  refine ⟨H,hR,hBase,hH.graph,?_,?_⟩
  · intro state hCode
    have he := codes_unique hM.1 hCode hBaseCode
    exact he.symm ▸ hH.initial C.zero hC.zero_nat hC.zero_empty
  · intro i j source target hs hIn hOut
    exact (rowStepSchema_iff hM hC hR hTable (hH.graph.bounds hM.1 hIn).2).mp (hH.transition i j source target hs hIn hOut)

theorem RowRun.row_numeric_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {m : M.Domain} {R : RowStateSpace M.Domain} {V P H r state W Q : M.Domain}
    (h : RowRun M C m R V P H) (hAt : MemPair M H r state) (hCode : Codes M state W Q) : NumericRow M C m W Q := by
  have hr := (h.graph.bounds hM.1 hAt).1
  rcases KP1Y.Naturals.natural_cases hM hC.omega hr with hEmpty | ⟨i,hi,hs⟩
  · have hrz := hM.1.eq_of_same_members r C.zero (fun x => iff_of_false (hEmpty x) (hC.zero_empty x))
    subst r
    obtain ⟨base,hBaseCode⟩ := codes_total hM V P
    have hState := h.graph.unique C.zero state base hAt (h.initial base hBaseCode)
    subst state
    obtain ⟨hWV,hQP⟩ := codes_injective hM.1 hCode hBaseCode
    subst W
    subst Q
    exact h.base
  · obtain ⟨source,_,hSource⟩ := h.graph.total i hi
    obtain ⟨_,_,W',Q',_,hCode',hNext⟩ := h.transition i r source state hs hSource hAt
    obtain ⟨hWW,hQQ⟩ := codes_injective hM.1 hCode hCode'
    subst W'
    subst Q'
    exact hNext.selection.numeric_row

def RowAt (M : SetTheory.Structure.{u}) (States H r V P : M.Domain) : Prop :=
  ∃ state, M.mem state States ∧ MemPair M H r state ∧ Codes M state V P

def rowAtFormula {n : Nat} (States H r V P : Project.Term n) : Project.Formula 1 n :=
  Project.Formula.existsMem States (.conj (memPairFormula H.weaken r.weaken (.bound 0))
    (codeFormula (.bound 0) V.weaken P.weaken))

theorem rowAtFormula_delta0 {n : Nat} (States H r V P : Project.Term n) : (rowAtFormula States H r V P).IsDelta0 :=
  .existsMem _ (.conj (memPairFormula_delta0 _ _ _) (codeFormula_delta0 _ _ _))

theorem rowAtFormula_freeClosed {n : Nat} (States H r V P : Project.Term n)
    (hS : States.freeSupport=[]) (hH : H.freeSupport=[]) (hr : r.freeSupport=[]) (hV : V.freeSupport=[]) (hP : P.freeSupport=[]) :
    (rowAtFormula States H r V P).FreeClosed := by
  simp [rowAtFormula,memPairFormula,codeFormula,pairFormula,Project.Formula.forallMem,Project.Formula.existsMem,
    Definitional.Formula.FreeClosed,hS,hH,hr,hV,hP]

theorem rowAtFormula_iff {M : SetTheory.Structure.{u}} (he : Extensional M) {n : Nat}
    (e : Env M n) (States H r V P : Project.Term n) :
    Project.Formula.satisfies e (rowAtFormula States H r V P) ↔
      RowAt M (States.eval e) (H.eval e) (r.eval e) (V.eval e) (P.eval e) := by
  simp only [rowAtFormula,Project.Formula.satisfies_existsMem_iff,Project.Formula.satisfies_conj_iff,
    memPairFormula_iff he,codeFormula_iff he,Term.eval_weaken]
  rfl

theorem RowRun.at_exists_d {M : SetTheory.Structure.{u}} {C : ExpressionData M.Domain}
    {m : M.Domain} {R : RowStateSpace M.Domain} {V P H r : M.Domain} (h : RowRun M C m R V P H) (hr : M.mem r C.omega) :
    ∃ W Q, RowAt M R.states H r W Q := by
  obtain ⟨state,hs,hAt⟩ := h.graph.total r hr
  obtain ⟨W,Q,hCode,_,_⟩ := h.space.decode hs
  exact ⟨W,Q,state,hs,hAt,hCode⟩

theorem RowRun.at_unique {M : SetTheory.Structure.{u}} (he : Extensional M) {C : ExpressionData M.Domain}
    {m : M.Domain} {R : RowStateSpace M.Domain} {V P H r W Q W' Q' : M.Domain} (h : RowRun M C m R V P H)
    (hAt : RowAt M R.states H r W Q) (hAt' : RowAt M R.states H r W' Q') : W=W' ∧ Q=Q' := by
  obtain ⟨state,_,hs,hCode⟩ := hAt
  obtain ⟨state',_,hs',hCode'⟩ := hAt'
  have hss := h.graph.unique r state state' hs hs'
  subst state'
  exact codes_injective he hCode hCode'

theorem RowRun.at_numeric_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory) {C : ExpressionData M.Domain} (hC : C.Valid M)
    {m : M.Domain} {R : RowStateSpace M.Domain} {V P H r W Q : M.Domain} (h : RowRun M C m R V P H)
    (hAt : RowAt M R.states H r W Q) : NumericRow M C m W Q := by
  obtain ⟨_,_,hs,hCode⟩ := hAt
  exact h.row_numeric_d hM hC hs hCode

theorem RowRun.at_next {M : SetTheory.Structure.{u}} (he : Extensional M) {C : ExpressionData M.Domain}
    {m : M.Domain} {R : RowStateSpace M.Domain} {V P H r r' W Q W' Q' : M.Domain} (h : RowRun M C m R V P H)
    (hs : M.SuccessorOf r' r) (hAt : RowAt M R.states H r W Q) (hAt' : RowAt M R.states H r' W' Q') :
    RowNext M C m W Q W' Q' := by
  obtain ⟨source,_,hSource,hCode⟩ := hAt
  obtain ⟨target,_,hTarget,hCode'⟩ := hAt'
  obtain ⟨X,Y,X',Y',hIn,hOut,hNext⟩ := h.transition r r' source target hs hSource hTarget
  obtain ⟨hWX,hQY⟩ := codes_injective he hCode hIn
  obtain ⟨hWX',hQY'⟩ := codes_injective he hCode' hOut
  subst X
  subst Y
  subst X'
  subst Y'
  exact hNext

private def rowRunAgreementSchema : Project.UnarySchema 2 where
  body := .forallE (.forallE (.imp (.conj (memPairFormula (.bound 4) (.bound 2) (.bound 1))
    (memPairFormula (.bound 3) (.bound 2) (.bound 0))) (Project.Formula.extensionalEq (.bound 1) (.bound 0))))
  freeClosed := by
    simp [memPairFormula,codeFormula,pairFormula,Project.Formula.forallMem,Project.Formula.existsMem,Definitional.Formula.FreeClosed]

private theorem rowRunAgreementSchema_iff {M : SetTheory.Structure.{u}} (he : Extensional M) (H J r : M.Domain) :
    Project.Formula.satisfies (((oneEnv H).push J).push r) rowRunAgreementSchema.body ↔
      ∀ x y, MemPair M H r x → MemPair M J r y → x=y := by
  simp only [rowRunAgreementSchema,Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_imp_iff,
    Project.Formula.satisfies_conj_iff,memPairFormula_iff he,Project.Formula.satisfies_extensionalEq_iff_eq he]
  exact ⟨fun h x y hx hy => h x y ⟨hx,hy⟩,fun h x y hs => h x y hs.1 hs.2⟩

theorem RowRun.unique_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory) {C : ExpressionData M.Domain} (hC : C.Valid M)
    {m : M.Domain} {R R' : RowStateSpace M.Domain} {V P H J : M.Domain}
    (hH : RowRun M C m R V P H) (hJ : RowRun M C m R' V P J) : H=J := by
  have hAll := KP1Y.Naturals.natural_induction_d hM rowRunAgreementSchema ((oneEnv H).push J) hC.omega
    (fun z hz => (rowRunAgreementSchema_iff hM.1 H J z).mpr (by
      have hzz := hM.1.eq_of_same_members z C.zero (fun x => iff_of_false (hz x) (hC.zero_empty x))
      subst z
      obtain ⟨base,hCode⟩ := codes_total hM V P
      intro x y hx hy
      exact (hH.graph.unique C.zero x base hx (hH.initial base hCode)).trans
        (hJ.graph.unique C.zero y base hy (hJ.initial base hCode)).symm))
    (fun r hr ih r' hs => (rowRunAgreementSchema_iff hM.1 H J r').mpr (by
      obtain ⟨x,_,hX⟩ := hH.graph.total r hr
      obtain ⟨y,_,hY⟩ := hJ.graph.total r hr
      have hxy := (rowRunAgreementSchema_iff hM.1 H J r).mp ih x y hX hY
      subst y
      intro p q hp hq
      exact row_transition_unique hM.1 (hH.transition r r' x p hs hX hp) (hJ.transition r r' x q hs hY hq)))
  apply hH.graph.ext hM.1 hJ.graph
  intro r hr x
  have hAgree := (rowRunAgreementSchema_iff hM.1 H J r).mp (hAll r hr)
  constructor
  · intro hx
    obtain ⟨y,_,hy⟩ := hJ.graph.total r hr
    exact (hAgree x y hx hy).symm ▸ hy
  · intro hx
    obtain ⟨y,_,hy⟩ := hH.graph.total r hr
    exact hAgree y x hy hx ▸ hy

theorem RowRun.finite_trace_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory) {C : ExpressionData M.Domain} (hC : C.Valid M)
    {m : M.Domain} {R : RowStateSpace M.Domain} {V P H n : M.Domain} (h : RowRun M C m R V P H) (hn : M.mem n C.omega) :
    ∃ trace, Graph M trace n R.states ∧ ∀ r state, MemPair M trace r state ↔ M.mem r n ∧ MemPair M H r state :=
  restrict_graph_d hM h.graph ((KP1Y.Naturals.omega_isOrdinal_d hM hC.omega).transitive n hn)

theorem mountain_rows_exists_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {m V P : M.Domain} (hBase : NumericRow M C m V P) :
    ∃ R H, RowRun M C m R V P H := by
  obtain ⟨R,hR⟩ := row_state_space_exists_d hM hC hBase.forest.width
  obtain ⟨H,hH⟩ := row_run_exists_d hM hC hR hBase
  exact ⟨R,H,hH⟩

theorem sequence_rows_exists_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {m V : M.Domain} (hm : M.mem m C.omega) (hV : Graph M V m C.omega) :
    ∃ F P R H, LinearForest M C.omega m F ∧ Selects true M C m F V P ∧ RowRun M C m R V P H := by
  obtain ⟨F,hF⟩ := linear_forest_exists_d hM hC.omega hm
  obtain ⟨P,hP⟩ := select_forest_exists_d hM true hC hF.1 hV
  obtain ⟨R,H,hH⟩ := mountain_rows_exists_d hM hC hP.numeric_row
  exact ⟨F,P,R,H,hF,hP,hH⟩

/-- 公开别名保留原私有常量，以便提取层证书复用同一差分语法。 -/
abbrev differenceGraphTableFormula_public {n : Nat} (C : ExpressionData (Project.Term n))
    (Pairs Table m V P W : Project.Term n) : Project.Formula 1 n := differenceGraphTableFormula C Pairs Table m V P W

theorem differenceGraphTableFormula_public_delta0 {n : Nat} (C : ExpressionData (Project.Term n))
    (Pairs Table m V P W : Project.Term n) : (differenceGraphTableFormula_public C Pairs Table m V P W).IsDelta0 :=
  differenceGraphTableFormula_delta0 C Pairs Table m V P W

theorem differenceGraphTableFormula_public_freeClosed {n : Nat} {C : ExpressionData (Project.Term n)} (hC : C.Closed)
    (Pairs Table m V P W : Project.Term n) (hpairs : Pairs.freeSupport=[]) (htable : Table.freeSupport=[])
    (hm : m.freeSupport=[]) (hV : V.freeSupport=[]) (hP : P.freeSupport=[]) (hW : W.freeSupport=[]) :
    (differenceGraphTableFormula_public C Pairs Table m V P W).FreeClosed :=
  differenceGraphTableFormula_freeClosed hC Pairs Table m V P W hpairs htable hm hV hP hW

theorem differenceGraphTableFormula_public_iff {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {n : Nat} (e : Env M n) (C : ExpressionData (Project.Term n)) (Pairs Table m V P W : Project.Term n)
    (hC : (C.eval e).Valid M) (hTable : DifferenceTable M (C.eval e) (Pairs.eval e) (Table.eval e)) :
    Project.Formula.satisfies e (differenceGraphTableFormula_public C Pairs Table m V P W) ↔
      DifferenceGraph M (C.eval e) (m.eval e) (V.eval e) (P.eval e) (W.eval e) :=
  differenceGraphTableFormula_iff hM e C Pairs Table m V P W hC hTable

abbrev rowStepSchema_public : Project.Delta0BinarySchema 10 := rowStepSchema

abbrev rowStepEnv_public {M : SetTheory.Structure.{u}} (C : ExpressionData M.Domain) (m : M.Domain)
    (R : RowStateSpace M.Domain) (Pairs Table : M.Domain) : Env M 10 := rowStepEnv C m R Pairs Table

theorem rowStepSchema_public_iff {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {m : M.Domain} {R : RowStateSpace M.Domain} (hR : R.Valid M C m)
    {Pairs Table : M.Domain} (hTable : DifferenceTable M C Pairs Table) {source target : M.Domain}
    (hSource : M.mem source R.states) :
    KP1Y.Iteration.nextDenote rowStepSchema_public (rowStepEnv_public C m R Pairs Table) source target ↔ RowTransition M C m source target :=
  rowStepSchema_iff hM hC hR hTable hSource

end KP1Y.OneYFinite
