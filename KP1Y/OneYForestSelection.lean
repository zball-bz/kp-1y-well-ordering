import KP1Y.OneYForestPaths

/-! 继承祖先中的最右较小值选择。positive=false 允许深度0；true用于正值数值山形。 -/
namespace KP1Y.OneYFinite
open YesMetaZFC YesMetaZFC.SetTheory YesMetaZFC.SetTheory.Definitional
open KP1Y.Kuratowski KP1Y.Functions KP1Y.Naturals KP1Y.Bounded
universe u

def PositiveValue (positive : Bool) (M : SetTheory.Structure.{u}) (z a : M.Domain) : Prop :=
  if positive then M.mem z a else True

def positiveValueFormula {n : Nat} (positive : Bool) (z a : Project.Term n) : Project.Formula 1 n :=
  if positive then .mem z a else .truth

theorem positiveValueFormula_delta0 {n : Nat} (positive : Bool) (z a : Project.Term n) :
    (positiveValueFormula positive z a).IsDelta0 := by
  cases positive
  · exact .truth
  · exact .mem _ _

theorem positiveValueFormula_iff {M : SetTheory.Structure.{u}} {n : Nat}
    (e : Env M n) (positive : Bool) (z a : Project.Term n) :
    Project.Formula.satisfies e (positiveValueFormula positive z a) ↔ PositiveValue positive M (z.eval e) (a.eval e) := by
  cases positive <;> simp [positiveValueFormula,PositiveValue,Project.Formula.satisfies_truth_iff,Project.Formula.satisfies_mem_iff]

def ParentCandidate (positive : Bool) (M : SetTheory.Structure.{u}) (C : ExpressionData M.Domain)
    (m F V c p : M.Domain) : Prop :=
  Ancestor M C m F p c ∧ ∃ x, M.mem x C.omega ∧ ∃ y, M.mem y C.omega ∧
    MemPair M V p x ∧ MemPair M V c y ∧ M.mem x y ∧ PositiveValue positive M C.zero x

def parentCandidateFormula {n : Nat} (positive : Bool) (C : ExpressionData (Project.Term n))
    (m F V c p : Project.Term n) : Project.Formula 1 n :=
  .conj (ancestorFormula C m F p c)
    (Project.Formula.existsMem C.omega (Project.Formula.existsMem C.omega.weaken
      (.conj (memPairFormula V.weaken.weaken p.weaken.weaken (.bound 1))
        (.conj (memPairFormula V.weaken.weaken c.weaken.weaken (.bound 0))
          (.conj (.mem (.bound 1) (.bound 0))
            (positiveValueFormula positive C.zero.weaken.weaken (.bound 1)))))))

theorem parentCandidateFormula_delta0 {n : Nat} (positive : Bool) (C : ExpressionData (Project.Term n))
    (m F V c p : Project.Term n) : (parentCandidateFormula positive C m F V c p).IsDelta0 :=
  .conj (ancestorFormula_delta0 _ _ _ _ _) (.existsMem _ (.existsMem _
    (.conj (memPairFormula_delta0 _ _ _) (.conj (memPairFormula_delta0 _ _ _)
      (.conj (.mem _ _) (positiveValueFormula_delta0 _ _ _))))))

theorem parentCandidateFormula_freeClosed {n : Nat} (positive : Bool)
    {C : ExpressionData (Project.Term n)} (hC : C.Closed) (m F V c p : Project.Term n)
    (hm : m.freeSupport=[]) (hF : F.freeSupport=[]) (hV : V.freeSupport=[])
    (hc : c.freeSupport=[]) (hp : p.freeSupport=[]) : (parentCandidateFormula positive C m F V c p).FreeClosed := by
  have hAnc := ancestorFormula_freeClosed hC m F p c hm hF hp hc
  cases positive <;> simp [parentCandidateFormula,positiveValueFormula,memPairFormula,codeFormula,pairFormula,
    Project.Formula.forallMem,Project.Formula.existsMem,Definitional.Formula.FreeClosed,hAnc,hC.omega,hC.zero,hV,hc,hp]

theorem parentCandidateFormula_iff {M : SetTheory.Structure.{u}} (he : Extensional M) {n : Nat}
    (e : Env M n) (positive : Bool) (C : ExpressionData (Project.Term n)) (m F V c p : Project.Term n) :
    Project.Formula.satisfies e (parentCandidateFormula positive C m F V c p) ↔
      ParentCandidate positive M (C.eval e) (m.eval e) (F.eval e) (V.eval e) (c.eval e) (p.eval e) := by
  simp only [parentCandidateFormula,Project.Formula.satisfies_conj_iff,ancestorFormula_iff he,
    Project.Formula.satisfies_existsMem_iff,memPairFormula_iff he,
    Project.Formula.satisfies_mem_iff,positiveValueFormula_iff,Term.eval_weaken]
  rfl

def RestrictedParent (positive : Bool) (M : SetTheory.Structure.{u}) (C : ExpressionData M.Domain)
    (m F V c p : M.Domain) : Prop :=
  ParentCandidate positive M C m F V c p ∧ ∀ q, M.mem q c →
    ParentCandidate positive M C m F V c q → q=p ∨ M.mem q p

def restrictedParentFormula {n : Nat} (positive : Bool) (C : ExpressionData (Project.Term n))
    (m F V c p : Project.Term n) : Project.Formula 1 n :=
  .conj (parentCandidateFormula positive C m F V c p)
    (Project.Formula.forallMem c (.imp
      (parentCandidateFormula positive C.weaken m.weaken F.weaken V.weaken c.weaken (.bound 0))
      (.disj (Project.Formula.extensionalEq (.bound 0) p.weaken) (.mem (.bound 0) p.weaken))))

theorem restrictedParentFormula_delta0 {n : Nat} (positive : Bool) (C : ExpressionData (Project.Term n))
    (m F V c p : Project.Term n) : (restrictedParentFormula positive C m F V c p).IsDelta0 :=
  .conj (parentCandidateFormula_delta0 _ _ _ _ _ _ _) (.forallMem _
    (.imp (parentCandidateFormula_delta0 _ _ _ _ _ _ _) (.disj (.atom _ _ _) (.mem _ _))))

theorem restrictedParentFormula_freeClosed {n : Nat} (positive : Bool)
    {C : ExpressionData (Project.Term n)} (hC : C.Closed) (m F V c p : Project.Term n)
    (hm : m.freeSupport=[]) (hF : F.freeSupport=[]) (hV : V.freeSupport=[])
    (hc : c.freeSupport=[]) (hp : p.freeSupport=[]) : (restrictedParentFormula positive C m F V c p).FreeClosed := by
  have hFirst := parentCandidateFormula_freeClosed positive hC m F V c p hm hF hV hc hp
  have hAll := parentCandidateFormula_freeClosed positive hC.weaken m.weaken F.weaken V.weaken c.weaken (.bound 0)
    (by simpa using hm) (by simpa using hF) (by simpa using hV) (by simpa using hc) rfl
  simp [restrictedParentFormula,Project.Formula.forallMem,Definitional.Formula.FreeClosed,hFirst,hAll,hc,hp]

theorem restrictedParentFormula_iff {M : SetTheory.Structure.{u}} (he : Extensional M) {n : Nat}
    (e : Env M n) (positive : Bool) (C : ExpressionData (Project.Term n)) (m F V c p : Project.Term n) :
    Project.Formula.satisfies e (restrictedParentFormula positive C m F V c p) ↔
      RestrictedParent positive M (C.eval e) (m.eval e) (F.eval e) (V.eval e) (c.eval e) (p.eval e) := by
  simp only [restrictedParentFormula,Project.Formula.satisfies_conj_iff,parentCandidateFormula_iff he,
    Project.Formula.satisfies_forallMem_iff,Project.Formula.satisfies_imp_iff,
    Project.Formula.satisfies_disj_iff,Project.Formula.satisfies_extensionalEq_iff_eq he,
    Project.Formula.satisfies_mem_iff,ExpressionData.eval_weaken,Term.eval_weaken]
  rfl

private def selectionEnv {M : SetTheory.Structure.{u}} (C : ExpressionData M.Domain) (m F V : M.Domain) : Env M 8 :=
  (((((((oneEnv C.omega).push C.zero).push C.one).push C.sequences).push C.expressions).push m).push F).push V

private def candidateSchema (positive : Bool) : Project.Delta0UnarySchema 9 where
  body := parentCandidateFormula positive ⟨.bound 9,.bound 8,.bound 7,.bound 6,.bound 5⟩
    (.bound 4) (.bound 3) (.bound 2) (.bound 1) (.bound 0)
  freeClosed := parentCandidateFormula_freeClosed positive ⟨rfl,rfl,rfl,rfl,rfl⟩ _ _ _ _ _ rfl rfl rfl rfl rfl
  delta0 := parentCandidateFormula_delta0 _ _ _ _ _ _ _

private theorem candidateSchema_iff {M : SetTheory.Structure.{u}} (he : Extensional M) (positive : Bool)
    (C : ExpressionData M.Domain) (m F V c p : M.Domain) :
    Project.Formula.satisfies (((selectionEnv C m F V).push c).push p) (candidateSchema positive).body ↔
      ParentCandidate positive M C m F V c p := by
  rw [candidateSchema,parentCandidateFormula_iff he]
  rfl

theorem parent_candidate_set_exists_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    (positive : Bool) (C : ExpressionData M.Domain) (m F V c : M.Domain) :
    ∃ A, ∀ p, M.mem p A ↔ ParentCandidate positive M C m F V c p := by
  obtain ⟨A,hA⟩ := SetTheory.KP.separation_exists_d (KP1Y.models_weakKP hM)
    (candidateSchema positive) ((selectionEnv C m F V).push c) c
  refine ⟨A,fun p => ?_⟩
  rw [hA p,candidateSchema_iff hM.1]
  exact ⟨And.right,fun h => ⟨h.1.1,h⟩⟩

theorem restricted_parent_exists_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    (positive : Bool) {C : ExpressionData M.Domain} (hC : C.Valid M) {m F V c : M.Domain}
    (hF : Forest M C.omega m F) (hSome : ∃ p, ParentCandidate positive M C m F V c p) :
    ∃ p, RestrictedParent positive M C m F V c p := by
  obtain ⟨A,hA⟩ := parent_candidate_set_exists_d hM positive C m F V c
  obtain ⟨p,hp⟩ := hSome
  have hcw := (omega_isOrdinal_d hM hC.omega).transitive m hF.width c (hp.1.bounds hM.1).2
  obtain ⟨q,hq,hMax⟩ := bounded_nat_max_d hM hC.omega hcw (fun q hq => ((hA q).mp hq).1.1)
    ⟨p,(hA p).mpr hp⟩
  exact ⟨q,(hA q).mp hq,fun r _ hr => hMax r ((hA r).mpr hr)⟩

theorem restricted_parent_unique_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    (positive : Bool) {C : ExpressionData M.Domain} (hC : C.Valid M) {m F V c p q : M.Domain}
    (hF : Forest M C.omega m F) (hp : RestrictedParent positive M C m F V c p)
    (hq : RestrictedParent positive M C m F V c q) : p=q := by
  rcases hq.2 p hp.1.1.1 hp.1 with he | hpq
  · exact he
  · rcases hp.2 q hq.1.1.1 hq.1 with he | hqp
    · exact he.symm
    · have hpω := (omega_isOrdinal_d hM hC.omega).transitive m hF.width p (hp.1.1.bounds hM.1).1
      exact False.elim (SetTheory.KP.mem_irrefl_d (KP1Y.models_weakKP hM) p
        (((omega_isOrdinal_d hM hC.omega).mem hpω).transitive q hqp p hpq))

/-- 搜索的失败值是列 c 本身；成功值严格小于 c，允许其为 0。 -/
theorem parent_search_exists_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    (positive : Bool) {C : ExpressionData M.Domain} (hC : C.Valid M) {m F V c : M.Domain}
    (hF : Forest M C.omega m F) (hc : M.mem c m) :
    ∃ p, M.mem p C.omega ∧
      ((p=c ∧ ∀ q, ¬ParentCandidate positive M C m F V c q) ∨ RestrictedParent positive M C m F V c p) := by
  obtain ⟨A,hA⟩ := parent_candidate_set_exists_d hM positive C m F V c
  have hcw := (omega_isOrdinal_d hM hC.omega).transitive m hF.width c hc
  obtain ⟨p,hp,hSearch⟩ := bounded_search_exists_d (A := A) hM hC.omega hcw
  refine ⟨p,hp,?_⟩
  rcases hSearch with ⟨he,hNone⟩ | ⟨hpc,hpA,hMax⟩
  · exact Or.inl ⟨he,fun q hq => hNone q hq.1.1 ((hA q).mpr hq)⟩
  · exact Or.inr ⟨(hA p).mp hpA,fun q hqc hq => hMax q hqc ((hA q).mpr hq)⟩

structure Selects (positive : Bool) (M : SetTheory.Structure.{u}) (C : ExpressionData M.Domain)
    (m F V P : M.Domain) : Prop where
  inherited : Forest M C.omega m F
  values : Graph M V m C.omega
  forest : Forest M C.omega m P
  parents : ∀ c p, MemPair M P c p ↔ RestrictedParent positive M C m F V c p

def selectsFormula {n : Nat} (positive : Bool) (C : ExpressionData (Project.Term n))
    (m F V P : Project.Term n) : Project.Formula 1 n :=
  .conj (forestFormula C.omega m F) (.conj (graphFormula V m C.omega)
    (.conj (forestFormula C.omega m P)
      (Project.Formula.forallMem m (Project.Formula.forallMem m.weaken
        (.iff (memPairFormula P.weaken.weaken (.bound 1) (.bound 0))
          (restrictedParentFormula positive C.weaken.weaken m.weaken.weaken F.weaken.weaken V.weaken.weaken (.bound 1) (.bound 0)))))))

theorem selectsFormula_delta0 {n : Nat} (positive : Bool) (C : ExpressionData (Project.Term n))
    (m F V P : Project.Term n) : (selectsFormula positive C m F V P).IsDelta0 :=
  .conj (forestFormula_delta0 _ _ _) (.conj (graphFormula_delta0 _ _ _)
    (.conj (forestFormula_delta0 _ _ _) (.forallMem _ (.forallMem _
      (.iff (memPairFormula_delta0 _ _ _) (restrictedParentFormula_delta0 _ _ _ _ _ _ _))))))

theorem selectsFormula_freeClosed {n : Nat} (positive : Bool)
    {C : ExpressionData (Project.Term n)} (hC : C.Closed) (m F V P : Project.Term n)
    (hm : m.freeSupport=[]) (hF : F.freeSupport=[]) (hV : V.freeSupport=[])
    (hP : P.freeSupport=[]) : (selectsFormula positive C m F V P).FreeClosed := by
  have hInherited := forestFormula_freeClosed C.omega m F hC.omega hm hF
  have hOutput := forestFormula_freeClosed C.omega m P hC.omega hm hP
  have hRows := restrictedParentFormula_freeClosed positive hC.weaken.weaken m.weaken.weaken F.weaken.weaken
    V.weaken.weaken (.bound 1) (.bound 0) (by simpa using hm) (by simpa using hF) (by simpa using hV) rfl rfl
  simp [selectsFormula,graphFormula,memPairFormula,codeFormula,pairFormula,Project.Formula.forallMem,
    Project.Formula.existsMem,Definitional.Formula.FreeClosed,hInherited,hOutput,hRows,hm,hP,hV,hC.omega]

theorem selectsFormula_iff {M : SetTheory.Structure.{u}} (he : Extensional M) {n : Nat}
    (e : Env M n) (positive : Bool) (C : ExpressionData (Project.Term n)) (m F V P : Project.Term n) :
    Project.Formula.satisfies e (selectsFormula positive C m F V P) ↔
      Selects positive M (C.eval e) (m.eval e) (F.eval e) (V.eval e) (P.eval e) := by
  simp only [selectsFormula,Project.Formula.satisfies_conj_iff,forestFormula_iff he,graphFormula_iff he,
    Project.Formula.satisfies_forallMem_iff,Project.Formula.satisfies_iff_iff,
    memPairFormula_iff he,restrictedParentFormula_iff he,ExpressionData.eval_weaken,Term.eval_weaken]
  constructor
  · rintro ⟨hF,hV,hP,hRows⟩
    refine ⟨hF,hV,hP,fun c p => ⟨?_,?_⟩⟩
    · intro hcp
      exact (hRows c (hP.bounds he hcp).1 p (hP.bounds he hcp).2).mp hcp
    · intro hcp
      exact (hRows c (hcp.1.1.bounds he).2 p (hcp.1.1.bounds he).1).mpr hcp
  · intro h
    exact ⟨h.inherited,h.values,h.forest,fun c _ p _ => h.parents c p⟩

private def selectionSchema (positive : Bool) : Project.Delta0BinarySchema 8 where
  body := restrictedParentFormula positive ⟨.bound 9,.bound 8,.bound 7,.bound 6,.bound 5⟩
    (.bound 4) (.bound 3) (.bound 2) (.bound 1) (.bound 0)
  freeClosed := restrictedParentFormula_freeClosed positive ⟨rfl,rfl,rfl,rfl,rfl⟩ _ _ _ _ _ rfl rfl rfl rfl rfl
  delta0 := restrictedParentFormula_delta0 _ _ _ _ _ _ _

private theorem selectionSchema_iff {M : SetTheory.Structure.{u}} (he : Extensional M) (positive : Bool)
    (C : ExpressionData M.Domain) (m F V c p : M.Domain) :
    Project.Formula.satisfies (((selectionEnv C m F V).push c).push p) (selectionSchema positive).body ↔
      RestrictedParent positive M C m F V c p := by
  rw [selectionSchema,restrictedParentFormula_iff he]
  rfl

theorem select_forest_exists_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    (positive : Bool) {C : ExpressionData M.Domain} (hC : C.Valid M) {m F V : M.Domain}
    (hF : Forest M C.omega m F) (hV : Graph M V m C.omega) : ∃ P, Selects positive M C m F V P := by
  obtain ⟨P,hSupport,hP⟩ := relation_comprehension_d hM (selectionSchema positive) (selectionEnv C m F V) m m
  have hRows : ∀ c p, MemPair M P c p ↔ RestrictedParent positive M C m F V c p := by
    intro c p
    rw [hP c p,selectionSchema_iff hM.1]
    exact ⟨fun h => h.2.2,fun h => ⟨(h.1.1.bounds hM.1).2,(h.1.1.bounds hM.1).1,h⟩⟩
  refine ⟨P,hF,hV,⟨hF.width,hSupport,?_,?_⟩,hRows⟩
  · intro c p q hcp hcq
    exact restricted_parent_unique_d hM positive hC hF ((hRows c p).mp hcp) ((hRows c q).mp hcq)
  · intro c p hcp
    exact ((hRows c p).mp hcp).1.1.1

theorem Forest.ext {M : SetTheory.Structure.{u}} (he : Extensional M) {w m n P Q : M.Domain}
    (hP : Forest M w m P) (hQ : Forest M w n Q)
    (hRows : ∀ c p, MemPair M P c p ↔ MemPair M Q c p) : P=Q := by
  apply he.eq_of_same_members
  intro e
  constructor
  · intro heP
    obtain ⟨c,_,p,_,hcp⟩ := hP.support e heP
    obtain ⟨e',heQ,hcp'⟩ := (hRows c p).mp ⟨e,heP,hcp⟩
    exact codes_unique he hcp hcp' ▸ heQ
  · intro heQ
    obtain ⟨c,_,p,_,hcp⟩ := hQ.support e heQ
    obtain ⟨e',heP,hcp'⟩ := (hRows c p).mpr ⟨e,heQ,hcp⟩
    exact codes_unique he hcp hcp' ▸ heP

theorem Selects.unique {M : SetTheory.Structure.{u}} (he : Extensional M) {positive : Bool}
    {C : ExpressionData M.Domain} {m F V P Q : M.Domain}
    (hP : Selects positive M C m F V P) (hQ : Selects positive M C m F V Q) : P=Q :=
  hP.forest.ext he hQ.forest (fun c p => (hP.parents c p).trans (hQ.parents c p).symm)

theorem Selects.parent_values {M : SetTheory.Structure.{u}} {positive : Bool}
    {C : ExpressionData M.Domain} {m F V P c p : M.Domain}
    (h : Selects positive M C m F V P) (hParent : MemPair M P c p) :
    ∃ x, M.mem x C.omega ∧ ∃ y, M.mem y C.omega ∧ MemPair M V p x ∧ MemPair M V c y ∧
      M.mem x y ∧ PositiveValue positive M C.zero x := ((h.parents c p).mp hParent).1.2

theorem Selects.parent_ancestor {M : SetTheory.Structure.{u}} {positive : Bool}
    {C : ExpressionData M.Domain} {m F V P c p : M.Domain}
    (h : Selects positive M C m F V P) (hParent : MemPair M P c p) : Ancestor M C m F p c :=
  ((h.parents c p).mp hParent).1.1

theorem Selects.no_parent_iff_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {positive : Bool} {C : ExpressionData M.Domain} (hC : C.Valid M) {m F V P c : M.Domain}
    (h : Selects positive M C m F V P) :
    NoParent M m P c ↔ ∀ p, ¬ParentCandidate positive M C m F V c p := by
  constructor
  · intro hNo p hp
    obtain ⟨q,hq⟩ := restricted_parent_exists_d hM positive hC h.inherited ⟨p,hp⟩
    exact hNo q (hq.1.1.bounds hM.1).1 ((h.parents c q).mpr hq)
  · intro hNone p _ hParent
    exact hNone p ((h.parents c p).mp hParent).1

def RowsAgreeOn (M : SetTheory.Structure.{u}) (P Q n : M.Domain) : Prop :=
  ∀ c, M.mem c n → ∀ p, MemPair M P c p ↔ MemPair M Q c p

theorem Forest.restrict_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {w m P n : M.Domain} (hw : M.IsOmega w) (hF : Forest M w m P)
    (hn : M.mem n w) : ∃ Q, Forest M w n Q ∧ RowsAgreeOn M P Q n := by
  obtain ⟨Q,hSupport,hQ⟩ := relation_comprehension_d hM KP1Y.Recursion.memberSchema (oneEnv P) n n
  have hRows : ∀ c p, MemPair M Q c p ↔ M.mem c n ∧ MemPair M P c p := by
    intro c p
    have h := hQ c p
    rw [KP1Y.Recursion.memberSchema_iff hM.1] at h
    exact h.trans ⟨fun h => ⟨h.1,h.2.2⟩,fun h => ⟨h.1,
      ((omega_isOrdinal_d hM hw).mem hn).transitive c h.1 p (hF.left c p h.2),h.2⟩⟩
  refine ⟨Q,⟨hn,hSupport,?_,?_⟩,?_⟩
  · intro c p q hcp hcq
    exact hF.unique c p q ((hRows c p).mp hcp).2 ((hRows c q).mp hcq).2
  · intro c p hcp
    exact hF.left c p ((hRows c p).mp hcp).2
  · intro c hc p
    exact ((hRows c p).trans ⟨And.right,fun h => ⟨hc,h⟩⟩).symm

theorem ParentPath.restrict_rows_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {m P Q n f len a c : M.Domain}
    (hF : Forest M C.omega m P) (hn : M.mem n C.omega) (hc : M.mem c n)
    (hRows : RowsAgreeOn M P Q n) (h : ParentPath M C m P f len a c) : ParentPath M C n Q f len a c := by
  have hValues : ∀ i x, MemPair M f i x → M.mem x n := by
    intro i x hix
    rcases h.values_below_last_d hM hC hF i x hix with he | hxc
    · exact he ▸ hc
    · exact ((omega_isOrdinal_d hM hC.omega).mem hn).transitive c hc x hxc
  have hGraph := KP1Y.Assignments.graph_tighten_values h.graph hValues
  refine ⟨h.length,hGraph,h.endpoints,?_⟩
  intro i j x y hi hj hix hjy hs
  exact (hRows y (hValues j y hjy) x).mp (h.edges i j x y hi hj hix hjy hs)

theorem ParentPath.enlarge_rows {M : SetTheory.Structure.{u}} (he : Extensional M)
    {C : ExpressionData M.Domain} {m P Q n f len a c : M.Domain}
    (hSub : M.MemberSubset n m) (hRows : RowsAgreeOn M P Q n)
    (h : ParentPath M C n Q f len a c) : ParentPath M C m P f len a c := by
  refine ⟨h.length,h.graph.mono_values hSub,h.endpoints,?_⟩
  intro i j x y hi hj hix hjy hs
  exact (hRows y (h.graph.bounds he hjy).2 x).mpr (h.edges i j x y hi hj hix hjy hs)

theorem ancestor_prefix_iff_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {m P Q n a c : M.Domain}
    (hF : Forest M C.omega m P) (hn : M.mem n C.omega) (hSub : M.MemberSubset n m)
    (hc : M.mem c n) (hRows : RowsAgreeOn M P Q n) :
    Ancestor M C m P a c ↔ Ancestor M C n Q a c := by
  constructor
  · rintro ⟨hac,len,hlen,f,hf,hPath⟩
    exact ⟨hac,len,hlen,f,hf,hPath.restrict_rows_d hM hC hF hn hc hRows⟩
  · rintro ⟨hac,len,hlen,f,hf,hPath⟩
    exact ⟨hac,len,hlen,f,hf,hPath.enlarge_rows hM.1 hSub hRows⟩

theorem no_parent_prefix_iff_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {m P Q n c : M.Domain}
    (hF : Forest M C.omega m P) (hn : M.mem n C.omega) (hc : M.mem c n)
    (hRows : RowsAgreeOn M P Q n) : NoParent M m P c ↔ NoParent M n Q c := by
  constructor
  · intro hNo p _ hcp
    have hOld := (hRows c hc p).mpr hcp
    exact hNo p (hF.bounds hM.1 hOld).2 hOld
  · intro hNo p _ hcp
    have hp := ((omega_isOrdinal_d hM hC.omega).mem hn).transitive c hc p (hF.left c p hcp)
    exact hNo p hp ((hRows c hc p).mp hcp)

theorem root_prefix_iff_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {m P Q n c q : M.Domain}
    (hF : Forest M C.omega m P) (hn : M.mem n C.omega) (hSub : M.MemberSubset n m)
    (hc : M.mem c n) (hRows : RowsAgreeOn M P Q n) : Root M C m P c q ↔ Root M C n Q c q := by
  constructor
  · rintro ⟨_,hNo,hReach⟩
    have hqn : M.mem q n := by
      rcases hReach with he | hAnc
      · exact he ▸ hc
      · exact ((omega_isOrdinal_d hM hC.omega).mem hn).transitive c hc q hAnc.1
    refine ⟨hqn,(no_parent_prefix_iff_d hM hC hF hn hqn hRows).mp hNo,?_⟩
    exact hReach.imp id ((ancestor_prefix_iff_d hM hC hF hn hSub hc hRows).mp)
  · rintro ⟨hqn,hNo,hReach⟩
    refine ⟨hSub q hqn,(no_parent_prefix_iff_d hM hC hF hn hqn hRows).mpr hNo,?_⟩
    exact hReach.imp id ((ancestor_prefix_iff_d hM hC hF hn hSub hc hRows).mpr)

theorem depth_prefix_iff_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {m P Q n c d : M.Domain}
    (hF : Forest M C.omega m P) (hn : M.mem n C.omega) (hSub : M.MemberSubset n m)
    (hc : M.mem c n) (hRows : RowsAgreeOn M P Q n) : Depth M C m P c d ↔ Depth M C n Q c d := by
  constructor
  · rintro ⟨hd,q,_,len,hlen,f,hf,hNo,hPath,hs⟩
    have hNew := hPath.restrict_rows_d hM hC hF hn hc hRows
    have hqn := hNew.start_bound hM.1
    exact ⟨hd,q,hqn,len,hlen,f,hf,(no_parent_prefix_iff_d hM hC hF hn hqn hRows).mp hNo,hNew,hs⟩
  · rintro ⟨hd,q,hq,len,hlen,f,hf,hNo,hPath,hs⟩
    exact ⟨hd,q,hSub q hq,len,hlen,f,hf,(no_parent_prefix_iff_d hM hC hF hn hq hRows).mpr hNo,
      hPath.enlarge_rows hM.1 hSub hRows,hs⟩

theorem parent_candidate_prefix_iff_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    (positive : Bool) {C : ExpressionData M.Domain} (hC : C.Valid M) {m F G V W n c p : M.Domain}
    (hF : Forest M C.omega m F) (hn : M.mem n C.omega) (hSub : M.MemberSubset n m)
    (hc : M.mem c n) (hParents : RowsAgreeOn M F G n) (hValues : RowsAgreeOn M V W n) :
    ParentCandidate positive M C m F V c p ↔ ParentCandidate positive M C n G W c p := by
  have hAnc := ancestor_prefix_iff_d (a := p) hM hC hF hn hSub hc hParents
  constructor
  · rintro ⟨hOld,x,hx,y,hy,hpx,hcy,hxy,hPos⟩
    have hNew := hAnc.mp hOld
    exact ⟨hNew,x,hx,y,hy,(hValues p (hNew.bounds hM.1).1 x).mp hpx,(hValues c hc y).mp hcy,hxy,hPos⟩
  · rintro ⟨hNew,x,hx,y,hy,hpx,hcy,hxy,hPos⟩
    exact ⟨hAnc.mpr hNew,x,hx,y,hy,(hValues p (hNew.bounds hM.1).1 x).mpr hpx,(hValues c hc y).mpr hcy,hxy,hPos⟩

theorem restricted_parent_prefix_iff_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    (positive : Bool) {C : ExpressionData M.Domain} (hC : C.Valid M) {m F G V W n c p : M.Domain}
    (hF : Forest M C.omega m F) (hn : M.mem n C.omega) (hSub : M.MemberSubset n m)
    (hc : M.mem c n) (hParents : RowsAgreeOn M F G n) (hValues : RowsAgreeOn M V W n) :
    RestrictedParent positive M C m F V c p ↔ RestrictedParent positive M C n G W c p := by
  have hCandidates := fun p => parent_candidate_prefix_iff_d (p := p) hM positive hC hF hn hSub hc hParents hValues
  exact ⟨fun ⟨hp,hMax⟩ => ⟨(hCandidates p).mp hp,fun q hqc hq => hMax q hqc ((hCandidates q).mpr hq)⟩,
    fun ⟨hp,hMax⟩ => ⟨(hCandidates p).mpr hp,fun q hqc hq => hMax q hqc ((hCandidates q).mp hq)⟩⟩

theorem Selects.prefix_rows_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {positive : Bool} {C : ExpressionData M.Domain} (hC : C.Valid M) {m F G V W P Q n : M.Domain}
    (hOld : Selects positive M C m F V P) (hNew : Selects positive M C n G W Q)
    (hSub : M.MemberSubset n m) (hParents : RowsAgreeOn M F G n) (hValues : RowsAgreeOn M V W n) :
    RowsAgreeOn M P Q n := by
  intro c hc p
  exact (hOld.parents c p).trans ((restricted_parent_prefix_iff_d hM positive hC hOld.inherited
    hNew.inherited.width hSub hc hParents hValues).trans (hNew.parents c p).symm)

end KP1Y.OneYFinite
