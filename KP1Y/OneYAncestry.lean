import KP1Y.OneYFiniteComputation

/-! 内部有限父森林与有限路径的公共编码。父 0 是实际边；无父由该列无边表示。 -/
namespace KP1Y.OneYFinite
open YesMetaZFC YesMetaZFC.SetTheory YesMetaZFC.SetTheory.Definitional
open KP1Y.Kuratowski KP1Y.Functions KP1Y.Naturals KP1Y.Bounded
universe u

structure Forest (M : SetTheory.Structure.{u}) (w m P : M.Domain) : Prop where
  width : M.mem m w
  support : ∀ e, M.mem e P → ∃ c, M.mem c m ∧ ∃ p, M.mem p m ∧ Codes M e c p
  unique : ∀ c p q, MemPair M P c p → MemPair M P c q → p=q
  left : ∀ c p, MemPair M P c p → M.mem p c

theorem Forest.bounds {M : SetTheory.Structure.{u}} (he : Extensional M) {w m P c p : M.Domain}
    (hF : Forest M w m P) (h : MemPair M P c p) : M.mem c m ∧ M.mem p m := by
  obtain ⟨e,heP,hecp⟩ := h
  obtain ⟨c',hc',p',hp',hecp'⟩ := hF.support e heP
  obtain ⟨hcc',hpp'⟩ := codes_injective he hecp hecp'
  subst c'
  subst p'
  exact ⟨hc',hp'⟩

def forestFormula {n : Nat} (w m P : Project.Term n) : Project.Formula 1 n :=
  .conj (.mem m w) (.conj
    (Project.Formula.forallMem P (Project.Formula.existsMem m.weaken
      (Project.Formula.existsMem m.weaken.weaken (codeFormula (.bound 2) (.bound 1) (.bound 0)))))
    (.conj (Project.Formula.forallMem m (Project.Formula.forallMem m.weaken
      (Project.Formula.forallMem m.weaken.weaken
        (.imp (.conj (memPairFormula P.weaken.weaken.weaken (.bound 2) (.bound 1))
          (memPairFormula P.weaken.weaken.weaken (.bound 2) (.bound 0)))
          (Project.Formula.extensionalEq (.bound 1) (.bound 0))))))
      (Project.Formula.forallMem m (Project.Formula.forallMem m.weaken
        (.imp (memPairFormula P.weaken.weaken (.bound 1) (.bound 0)) (.mem (.bound 0) (.bound 1)))))))

theorem forestFormula_delta0 {n : Nat} (w m P : Project.Term n) : (forestFormula w m P).IsDelta0 :=
  .conj (.mem _ _) (.conj (.forallMem _ (.existsMem _ (.existsMem _ (codeFormula_delta0 _ _ _))))
    (.conj (.forallMem _ (.forallMem _ (.forallMem _ (.imp
      (.conj (memPairFormula_delta0 _ _ _) (memPairFormula_delta0 _ _ _)) (.atom _ _ _)))))
      (.forallMem _ (.forallMem _ (.imp (memPairFormula_delta0 _ _ _) (.mem _ _))))))

theorem forestFormula_freeClosed {n : Nat} (w m P : Project.Term n)
    (hw : w.freeSupport=[]) (hm : m.freeSupport=[]) (hP : P.freeSupport=[]) : (forestFormula w m P).FreeClosed := by
  simp [forestFormula,memPairFormula,codeFormula,pairFormula,Project.Formula.forallMem,
    Project.Formula.existsMem,Definitional.Formula.FreeClosed,hw,hm,hP]

theorem forestFormula_iff {M : SetTheory.Structure.{u}} (he : Extensional M) {n : Nat}
    (e : Env M n) (w m P : Project.Term n) : Project.Formula.satisfies e (forestFormula w m P) ↔
      Forest M (w.eval e) (m.eval e) (P.eval e) := by
  simp only [forestFormula,Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_mem_iff,
    Project.Formula.satisfies_forallMem_iff,Project.Formula.satisfies_existsMem_iff,
    Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_extensionalEq_iff_eq he,
    codeFormula_iff he,memPairFormula_iff he,Term.eval_weaken]
  constructor
  · rintro ⟨hm,hSupport,hUnique,hLeft⟩
    have hBounds : ∀ c p, MemPair M (P.eval e) c p → M.mem c (m.eval e) ∧ M.mem p (m.eval e) := by
      rintro c p ⟨v,hv,hcp⟩
      obtain ⟨c',hc',p',hp',hcp'⟩ := hSupport v hv
      change Codes M v c' p' at hcp'
      obtain ⟨hcc',hpp'⟩ := codes_injective he hcp hcp'
      subst c'
      subst p'
      exact ⟨hc',hp'⟩
    exact ⟨hm,hSupport,
      fun c p q hcp hcq => hUnique c (hBounds c p hcp).1 p (hBounds c p hcp).2 q (hBounds c q hcq).2 ⟨hcp,hcq⟩,
      fun c p hcp => hLeft c (hBounds c p hcp).1 p (hBounds c p hcp).2 hcp⟩
  · intro hF
    exact ⟨hF.width,hF.support,fun c _ p _ q _ h => hF.unique c p q h.1 h.2,fun c _ p _ h => hF.left c p h⟩

def NoParent (M : SetTheory.Structure.{u}) (m P c : M.Domain) : Prop :=
  ∀ p, M.mem p m → ¬MemPair M P c p

def noParentFormula {n : Nat} (m P c : Project.Term n) : Project.Formula 1 n :=
  Project.Formula.forallMem m (.neg (memPairFormula P.weaken c.weaken (.bound 0)))

theorem noParentFormula_delta0 {n : Nat} (m P c : Project.Term n) : (noParentFormula m P c).IsDelta0 :=
  .forallMem _ (.neg (memPairFormula_delta0 _ _ _))

theorem noParentFormula_iff {M : SetTheory.Structure.{u}} (he : Extensional M) {n : Nat}
    (e : Env M n) (m P c : Project.Term n) :
    Project.Formula.satisfies e (noParentFormula m P c) ↔ NoParent M (m.eval e) (P.eval e) (c.eval e) := by
  simp only [noParentFormula,Project.Formula.satisfies_forallMem_iff,
    Project.Formula.satisfies_neg_iff,memPairFormula_iff he,Term.eval_weaken]
  rfl

theorem Forest.noParent_iff {M : SetTheory.Structure.{u}} (he : Extensional M) {w m P c : M.Domain}
    (hF : Forest M w m P) : NoParent M m P c ↔ ∀ p, ¬MemPair M P c p :=
  ⟨fun h p hp => h p (hF.bounds he hp).2 hp,fun h p _ => h p⟩

theorem empty_forest {M : SetTheory.Structure.{u}} {w m z : M.Domain}
    (hm : M.mem m w) (hz : ∀ x, ¬M.mem x z) : Forest M w m z := by
  refine ⟨hm,fun p hp => False.elim (hz p hp),?_,?_⟩
  · rintro c p q ⟨e,he,_⟩ _
    exact False.elim (hz e he)
  · rintro c p ⟨e,he,_⟩
    exact False.elim (hz e he)

/-- 路径按祖先到后代的顺序存储，相邻后项的父为前项。n 是含端点的内部长度。 -/
structure ParentPath (M : SetTheory.Structure.{u}) (C : ExpressionData M.Domain)
    (m P f n a c : M.Domain) : Prop where
  length : M.mem n C.omega
  graph : Graph M f n m
  endpoints : ∃ last, M.mem last n ∧ M.SuccessorOf n last ∧ MemPair M f C.zero a ∧ MemPair M f last c
  edges : ∀ i j x y, M.mem i n → M.mem j n → MemPair M f i x → MemPair M f j y →
    M.SuccessorOf j i → MemPair M P y x

def parentPathFormula {n : Nat} (C : ExpressionData (Project.Term n))
    (m P f len a c : Project.Term n) : Project.Formula 1 n :=
  .conj (.mem len C.omega) (.conj (graphFormula f len m)
    (.conj (Project.Formula.existsMem len
      (.conj (successorFormula len.weaken (.bound 0))
        (.conj (memPairFormula f.weaken C.zero.weaken a.weaken)
          (memPairFormula f.weaken (.bound 0) c.weaken))))
      (Project.Formula.forallMem len (Project.Formula.forallMem len.weaken
        (Project.Formula.forallMem m.weaken.weaken (Project.Formula.forallMem m.weaken.weaken.weaken
          (.imp (memPairFormula f.weaken.weaken.weaken.weaken (.bound 3) (.bound 1))
            (.imp (memPairFormula f.weaken.weaken.weaken.weaken (.bound 2) (.bound 0))
              (.imp (successorFormula (.bound 2) (.bound 3))
                (memPairFormula P.weaken.weaken.weaken.weaken (.bound 0) (.bound 1)))))))))))

theorem parentPathFormula_delta0 {n : Nat} (C : ExpressionData (Project.Term n)) (m P f len a c : Project.Term n) :
    (parentPathFormula C m P f len a c).IsDelta0 :=
  .conj (.mem _ _) (.conj (graphFormula_delta0 _ _ _)
    (.conj (.existsMem _ (.conj (successorFormula_delta0 _ _)
      (.conj (memPairFormula_delta0 _ _ _) (memPairFormula_delta0 _ _ _))))
      (.forallMem _ (.forallMem _ (.forallMem _ (.forallMem _
        (.imp (memPairFormula_delta0 _ _ _) (.imp (memPairFormula_delta0 _ _ _)
          (.imp (successorFormula_delta0 _ _) (memPairFormula_delta0 _ _ _))))))))))

theorem parentPathFormula_freeClosed {n : Nat} {C : ExpressionData (Project.Term n)} (hC : C.Closed)
    (m P f len a c : Project.Term n) (hm : m.freeSupport=[]) (hP : P.freeSupport=[])
    (hf : f.freeSupport=[]) (hl : len.freeSupport=[]) (ha : a.freeSupport=[])
    (hc : c.freeSupport=[]) : (parentPathFormula C m P f len a c).FreeClosed := by
  simp [parentPathFormula,graphFormula,memPairFormula,codeFormula,pairFormula,successorFormula,
    Project.Formula.forallMem,Project.Formula.existsMem,Definitional.Formula.FreeClosed,
    hC.omega,hC.zero,hm,hP,hf,hl,ha,hc]

theorem parentPathFormula_iff {M : SetTheory.Structure.{u}} (he : Extensional M) {n : Nat}
    (e : Env M n) (C : ExpressionData (Project.Term n)) (m P f len a c : Project.Term n) :
    Project.Formula.satisfies e (parentPathFormula C m P f len a c) ↔
      ParentPath M (C.eval e) (m.eval e) (P.eval e) (f.eval e) (len.eval e) (a.eval e) (c.eval e) := by
  simp only [parentPathFormula,Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_mem_iff,
    graphFormula_iff he,Project.Formula.satisfies_existsMem_iff,successorFormula_iff he,
    memPairFormula_iff he,Project.Formula.satisfies_forallMem_iff,Project.Formula.satisfies_imp_iff,Term.eval_weaken]
  constructor
  · rintro ⟨hlen,hGraph,hEnds,hEdges⟩
    exact ⟨hlen,hGraph,hEnds,fun i j x y hi hj hix hjy hs =>
      hEdges i hi j hj x (hGraph.bounds he hix).2 y (hGraph.bounds he hjy).2 hix hjy hs⟩
  · intro hP
    exact ⟨hP.length,hP.graph,hP.endpoints,fun i hi j hj x _ y _ hix hjy hs => hP.edges i j x y hi hj hix hjy hs⟩

/-- 严格祖先关系只量化实际集合中的内部有限路径，不使用宿主传递闭包。 -/
def Ancestor (M : SetTheory.Structure.{u}) (C : ExpressionData M.Domain) (m P a c : M.Domain) : Prop :=
  M.mem a c ∧ ∃ n, M.mem n C.omega ∧ ∃ f, M.mem f C.sequences ∧ ParentPath M C m P f n a c

def ancestorFormula {n : Nat} (C : ExpressionData (Project.Term n)) (m P a c : Project.Term n) : Project.Formula 1 n :=
  .conj (.mem a c) (Project.Formula.existsMem C.omega (Project.Formula.existsMem C.sequences.weaken
    (parentPathFormula C.weaken.weaken m.weaken.weaken P.weaken.weaken (.bound 0) (.bound 1) a.weaken.weaken c.weaken.weaken)))

theorem ancestorFormula_delta0 {n : Nat} (C : ExpressionData (Project.Term n)) (m P a c : Project.Term n) :
    (ancestorFormula C m P a c).IsDelta0 :=
  .conj (.mem _ _) (.existsMem _ (.existsMem _ (parentPathFormula_delta0 _ _ _ _ _ _ _)))

theorem ancestorFormula_freeClosed {n : Nat} {C : ExpressionData (Project.Term n)} (hC : C.Closed)
    (m P a c : Project.Term n) (hm : m.freeSupport=[]) (hP : P.freeSupport=[])
    (ha : a.freeSupport=[]) (hc : c.freeSupport=[]) : (ancestorFormula C m P a c).FreeClosed := by
  have hPath := parentPathFormula_freeClosed hC.weaken.weaken m.weaken.weaken P.weaken.weaken
    (.bound 0) (.bound 1) a.weaken.weaken c.weaken.weaken
    (by simpa using hm) (by simpa using hP) rfl rfl (by simpa using ha) (by simpa using hc)
  simp [ancestorFormula,Project.Formula.existsMem,Definitional.Formula.FreeClosed,hC.omega,hC.sequences,ha,hc,hPath]

theorem ancestorFormula_iff {M : SetTheory.Structure.{u}} (he : Extensional M) {n : Nat}
    (e : Env M n) (C : ExpressionData (Project.Term n)) (m P a c : Project.Term n) :
    Project.Formula.satisfies e (ancestorFormula C m P a c) ↔
      Ancestor M (C.eval e) (m.eval e) (P.eval e) (a.eval e) (c.eval e) := by
  simp only [ancestorFormula,Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_mem_iff,
    Project.Formula.satisfies_existsMem_iff,parentPathFormula_iff he,ExpressionData.eval_weaken,Term.eval_weaken]
  rfl

def Root (M : SetTheory.Structure.{u}) (C : ExpressionData M.Domain) (m P c q : M.Domain) : Prop :=
  M.mem q m ∧ NoParent M m P q ∧ (q=c ∨ Ancestor M C m P q c)

def rootFormula {n : Nat} (C : ExpressionData (Project.Term n)) (m P c q : Project.Term n) : Project.Formula 1 n :=
  .conj (.mem q m) (.conj (noParentFormula m P q)
    (.disj (Project.Formula.extensionalEq q c) (ancestorFormula C m P q c)))

theorem rootFormula_delta0 {n : Nat} (C : ExpressionData (Project.Term n)) (m P c q : Project.Term n) :
    (rootFormula C m P c q).IsDelta0 :=
  .conj (.mem _ _) (.conj (noParentFormula_delta0 _ _ _) (.disj (.atom _ _ _) (ancestorFormula_delta0 _ _ _ _ _)))

theorem rootFormula_freeClosed {n : Nat} {C : ExpressionData (Project.Term n)} (hC : C.Closed)
    (m P c q : Project.Term n) (hm : m.freeSupport=[]) (hP : P.freeSupport=[])
    (hc : c.freeSupport=[]) (hq : q.freeSupport=[]) : (rootFormula C m P c q).FreeClosed := by
  have hA := ancestorFormula_freeClosed hC m P q c hm hP hq hc
  simp [rootFormula,noParentFormula,memPairFormula,codeFormula,pairFormula,Project.Formula.forallMem,
    Project.Formula.existsMem,Definitional.Formula.FreeClosed,hm,hP,hc,hq,hA]

theorem rootFormula_iff {M : SetTheory.Structure.{u}} (he : Extensional M) {n : Nat}
    (e : Env M n) (C : ExpressionData (Project.Term n)) (m P c q : Project.Term n) :
    Project.Formula.satisfies e (rootFormula C m P c q) ↔
      Root M (C.eval e) (m.eval e) (P.eval e) (c.eval e) (q.eval e) := by
  simp only [rootFormula,Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_mem_iff,
    noParentFormula_iff he,Project.Formula.satisfies_disj_iff,Project.Formula.satisfies_extensionalEq_iff_eq he,
    ancestorFormula_iff he]
  rfl

end KP1Y.OneYFinite
