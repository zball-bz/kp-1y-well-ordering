import KP1Y.OneYCopiedMountainSyntax

/-! 待重建图层的实际伪父定义。这里只定义有界最大候选，不假定存在性。 -/
namespace KP1Y.OneYFinite.CopiedMountain
open YesMetaZFC YesMetaZFC.SetTheory YesMetaZFC.SetTheory.Definitional
open KP1Y.Kuratowski KP1Y.Functions KP1Y.Naturals KP1Y.Bounded
universe u

/-- 子列高度hc=succ r；候选是第r行祖先，且候选高度恰为hc或r。 -/
def GraphPseudoCandidate (M : SetTheory.Structure.{u}) (C : ExpressionData M.Domain) (X : Data M.Domain) (c p : M.Domain) : Prop :=
  ∃ hc, M.mem hc C.omega ∧ ∃ hp, M.mem hp C.omega ∧ ∃ r, M.mem r C.omega ∧
    MemPair M X.heights c hc ∧ MemPair M X.heights p hp ∧ M.SuccessorOf hc r ∧
      ∃ F, M.mem F X.forests ∧ MemPair M X.parents r F ∧ Ancestor M C X.width F p c ∧ (hp=hc ∨ hp=r)

def graphPseudoCandidateFormula {n : Nat} (C : ExpressionData (Project.Term n)) (X : Data (Project.Term n))
    (c p : Project.Term n) : Project.Formula 1 n :=
  Project.Formula.existsMem C.omega (Project.Formula.existsMem C.omega.weaken
    (Project.Formula.existsMem C.omega.weaken.weaken
      (.conj (memPairFormula X.heights.weaken.weaken.weaken c.weaken.weaken.weaken (.bound 2))
        (.conj (memPairFormula X.heights.weaken.weaken.weaken p.weaken.weaken.weaken (.bound 1))
          (.conj (successorFormula (.bound 2) (.bound 0))
            (Project.Formula.existsMem X.forests.weaken.weaken.weaken
              (.conj (memPairFormula X.parents.weaken.weaken.weaken.weaken (.bound 1) (.bound 0))
                (.conj (ancestorFormula C.weaken.weaken.weaken.weaken X.width.weaken.weaken.weaken.weaken (.bound 0)
                  p.weaken.weaken.weaken.weaken c.weaken.weaken.weaken.weaken)
                  (.disj (Project.Formula.extensionalEq (.bound 2) (.bound 3))
                    (Project.Formula.extensionalEq (.bound 2) (.bound 1)))))))))))

theorem graphPseudoCandidateFormula_delta0 {n : Nat} (C : ExpressionData (Project.Term n)) (X : Data (Project.Term n))
    (c p : Project.Term n) : (graphPseudoCandidateFormula C X c p).IsDelta0 :=
  .existsMem _ (.existsMem _ (.existsMem _ (.conj (memPairFormula_delta0 _ _ _) (.conj (memPairFormula_delta0 _ _ _)
    (.conj (successorFormula_delta0 _ _) (.existsMem _ (.conj (memPairFormula_delta0 _ _ _)
      (.conj (ancestorFormula_delta0 _ _ _ _ _) (.disj (.atom _ _ _) (.atom _ _ _))))))))))

theorem graphPseudoCandidateFormula_freeClosed {n : Nat} {C : ExpressionData (Project.Term n)} (hC : C.Closed)
    {X : Data (Project.Term n)} (hX : X.Closed) (c p : Project.Term n)
    (hc : c.freeSupport=[]) (hp : p.freeSupport=[]) : (graphPseudoCandidateFormula C X c p).FreeClosed := by
  have hAnc := ancestorFormula_freeClosed hC.weaken.weaken.weaken.weaken X.width.weaken.weaken.weaken.weaken
    (.bound 0) p.weaken.weaken.weaken.weaken c.weaken.weaken.weaken.weaken
    (by simpa using hX.width) rfl (by simpa using hp) (by simpa using hc)
  simp [graphPseudoCandidateFormula,successorFormula,memPairFormula,codeFormula,pairFormula,
    Project.Formula.existsMem,Project.Formula.forallMem,Definitional.Formula.FreeClosed,hC.omega,hX.heights,hX.forests,hX.parents,hc,hp,hAnc]

theorem graphPseudoCandidateFormula_iff {M : SetTheory.Structure.{u}} (he : Extensional M) {n : Nat}
    (e : Env M n) (C : ExpressionData (Project.Term n)) (X : Data (Project.Term n)) (c p : Project.Term n) :
    Project.Formula.satisfies e (graphPseudoCandidateFormula C X c p) ↔
      GraphPseudoCandidate M (C.eval e) (X.eval e) (c.eval e) (p.eval e) := by
  simp only [graphPseudoCandidateFormula,GraphPseudoCandidate,Project.Formula.satisfies_existsMem_iff,
    Project.Formula.satisfies_conj_iff,memPairFormula_iff he,successorFormula_iff he,ancestorFormula_iff he,
    Project.Formula.satisfies_disj_iff,Project.Formula.satisfies_extensionalEq_iff_eq he,ExpressionData.eval_weaken,Term.eval_weaken]
  rfl

theorem GraphPseudoCandidate.bounds {M : SetTheory.Structure.{u}} (he : Extensional M)
    {C : ExpressionData M.Domain} {X : Data M.Domain} {c p : M.Domain} (h : GraphPseudoCandidate M C X c p) :
    M.mem p X.width ∧ M.mem c X.width ∧ M.mem p c := by
  obtain ⟨_,_,_,_,_,_,_,_,_,_,_,_,hAnc,_⟩ := h
  exact ⟨(hAnc.bounds he).1,(hAnc.bounds he).2,hAnc.1⟩

def GraphPseudoParent (M : SetTheory.Structure.{u}) (C : ExpressionData M.Domain) (X : Data M.Domain) (c p : M.Domain) : Prop :=
  GraphPseudoCandidate M C X c p ∧ ∀ q, M.mem q c → GraphPseudoCandidate M C X c q → q=p ∨ M.mem q p

def graphPseudoParentFormula {n : Nat} (C : ExpressionData (Project.Term n)) (X : Data (Project.Term n))
    (c p : Project.Term n) : Project.Formula 1 n :=
  .conj (graphPseudoCandidateFormula C X c p)
    (Project.Formula.forallMem c (.imp (graphPseudoCandidateFormula C.weaken X.weaken c.weaken (.bound 0))
      (.disj (Project.Formula.extensionalEq (.bound 0) p.weaken) (.mem (.bound 0) p.weaken))))

theorem graphPseudoParentFormula_delta0 {n : Nat} (C : ExpressionData (Project.Term n)) (X : Data (Project.Term n))
    (c p : Project.Term n) : (graphPseudoParentFormula C X c p).IsDelta0 :=
  .conj (graphPseudoCandidateFormula_delta0 _ _ _ _) (.forallMem _ (.imp
    (graphPseudoCandidateFormula_delta0 _ _ _ _) (.disj (.atom _ _ _) (.mem _ _))))

theorem graphPseudoParentFormula_freeClosed {n : Nat} {C : ExpressionData (Project.Term n)} (hC : C.Closed)
    {X : Data (Project.Term n)} (hX : X.Closed) (c p : Project.Term n)
    (hc : c.freeSupport=[]) (hp : p.freeSupport=[]) : (graphPseudoParentFormula C X c p).FreeClosed := by
  have hCand := graphPseudoCandidateFormula_freeClosed hC hX c p hc hp
  have hOther := graphPseudoCandidateFormula_freeClosed hC.weaken hX.weaken c.weaken (.bound 0) (by simpa using hc) rfl
  simp [graphPseudoParentFormula,Project.Formula.forallMem,Definitional.Formula.FreeClosed,hc,hp,hCand,hOther]

theorem graphPseudoParentFormula_iff {M : SetTheory.Structure.{u}} (he : Extensional M) {n : Nat}
    (e : Env M n) (C : ExpressionData (Project.Term n)) (X : Data (Project.Term n)) (c p : Project.Term n) :
    Project.Formula.satisfies e (graphPseudoParentFormula C X c p) ↔ GraphPseudoParent M (C.eval e) (X.eval e) (c.eval e) (p.eval e) := by
  simp only [graphPseudoParentFormula,GraphPseudoParent,Project.Formula.satisfies_conj_iff,graphPseudoCandidateFormula_iff he,
    Project.Formula.satisfies_forallMem_iff,Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_disj_iff,
    Project.Formula.satisfies_extensionalEq_iff_eq he,Project.Formula.satisfies_mem_iff,ExpressionData.eval_weaken,Data.eval_weaken,Term.eval_weaken]
  rfl

theorem GraphPseudoParent.unique_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {X : Data M.Domain} (hX : X.Valid M C) {c p q : M.Domain}
    (hP : GraphPseudoParent M C X c p) (hQ : GraphPseudoParent M C X c q) : p=q := by
  rcases hQ.2 p (hP.1.bounds hM.1).2.2 hP.1 with he | hpq
  · exact he
  · rcases hP.2 q (hQ.1.bounds hM.1).2.2 hQ.1 with he | hqp
    · exact he.symm
    · have hp := (omega_isOrdinal_d hM hC.omega).transitive X.width hX.width p (hP.1.bounds hM.1).1
      exact False.elim (SetTheory.KP.mem_irrefl_d (KP1Y.models_weakKP hM) p
        (((omega_isOrdinal_d hM hC.omega).mem hp).transitive q hqp p hpq))

end KP1Y.OneYFinite.CopiedMountain
