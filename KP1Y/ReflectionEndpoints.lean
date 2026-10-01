import KP1Y.ReflectionRepresentation

/-! 端点模板在指定上端点的真值。模板合法性由反射需求单独验证。 -/
namespace KP1Y.Reflection
open YesMetaZFC YesMetaZFC.SetTheory YesMetaZFC.SetTheory.Definitional
open KP1Y.Kuratowski KP1Y.Functions
universe u

def NeedTruth (M : SetTheory.Structure.{u}) (C : Data M.Domain) (H f b k q p : M.Domain) : Prop :=
  ∀ η, M.mem η C.cap → ∀ a, M.mem a C.cap → MemPair M f q η → MemPair M f p a → Query M C.toIndexData H k η a b

def needTruthFormula {n : Nat} (C : Data (Project.Term n)) (H f b k q p : Project.Term n) : Project.Formula 1 n :=
  Project.Formula.forallMem C.cap (Project.Formula.forallMem C.cap.weaken
    (.imp (.conj (memPairFormula f.weaken.weaken q.weaken.weaken (.bound 1))
        (memPairFormula f.weaken.weaken p.weaken.weaken (.bound 0)))
      (queryFormula C.toIndexData.weaken.weaken H.weaken.weaken k.weaken.weaken (.bound 1) (.bound 0) b.weaken.weaken)))

theorem needTruthFormula_delta0 {n : Nat} (C : Data (Project.Term n)) (H f b k q p : Project.Term n) :
    (needTruthFormula C H f b k q p).IsDelta0 := .forallMem _ (.forallMem _
      (.imp (.conj (memPairFormula_delta0 _ _ _) (memPairFormula_delta0 _ _ _)) (queryFormula_delta0 _ _ _ _ _ _)))

theorem needTruthFormula_freeClosed {n : Nat} {C : Data (Project.Term n)} (hC : C.Closed) (H f b k q p : Project.Term n)
    (hH : H.freeSupport=[]) (hf : f.freeSupport=[]) (hb : b.freeSupport=[]) (hk : k.freeSupport=[])
    (hq : q.freeSupport=[]) (hp : p.freeSupport=[]) : (needTruthFormula C H f b k q p).FreeClosed := by
  have hQuery := queryFormula_freeClosed C.toIndexData.weaken.weaken H.weaken.weaken k.weaken.weaken
    (.bound 1) (.bound 0) b.weaken.weaken
    (by simpa [IndexData.weaken,IndexData.map] using hC.omega) (by simpa [IndexData.weaken,IndexData.map] using hC.cap)
    (by simpa [IndexData.weaken,IndexData.map] using hC.keys) (by simpa [IndexData.weaken,IndexData.map] using hC.index)
    (by simpa [IndexData.weaken,IndexData.map] using hC.bound) (by simpa using hH) (by simpa using hk) rfl rfl (by simpa using hb)
  simp [needTruthFormula,memPairFormula,codeFormula,pairFormula,Project.Formula.forallMem,Project.Formula.existsMem,
    Definitional.Formula.FreeClosed,hC.cap,hf,hq,hp,hQuery]

theorem needTruthFormula_iff {M : SetTheory.Structure.{u}} (he : Extensional M) {n : Nat} (e : Env M n)
    (C : Data (Project.Term n)) (H f b k q p : Project.Term n) : Project.Formula.satisfies e (needTruthFormula C H f b k q p) ↔
      NeedTruth M (C.eval e) (H.eval e) (f.eval e) (b.eval e) (k.eval e) (q.eval e) (p.eval e) := by
  simp only [needTruthFormula,Project.Formula.satisfies_forallMem_iff,Project.Formula.satisfies_imp_iff,
    Project.Formula.satisfies_conj_iff,memPairFormula_iff he,queryFormula_iff he,IndexData.eval_weaken,Data.eval_index,Term.eval_weaken]
  exact ⟨fun h η hη a ha hq hp => h η hη a ha ⟨hq,hp⟩,fun h η hη a ha hRows => h η hη a ha hRows.1 hRows.2⟩

def End (M : SetTheory.Structure.{u}) (C : Data M.Domain) (H N f b : M.Domain) : Prop :=
  ∀ k, M.mem k C.omega → ∀ q, M.mem q C.omega → ∀ p, M.mem p C.omega → NeedAt M C N k q p → NeedTruth M C H f b k q p

def endFormula {n : Nat} (C : Data (Project.Term n)) (H N f b : Project.Term n) : Project.Formula 1 n :=
  Project.Formula.forallMem C.omega (Project.Formula.forallMem C.omega.weaken (Project.Formula.forallMem C.omega.weaken.weaken
    (.imp (needAtFormula C.weaken.weaken.weaken N.weaken.weaken.weaken (.bound 2) (.bound 1) (.bound 0))
      (needTruthFormula C.weaken.weaken.weaken H.weaken.weaken.weaken f.weaken.weaken.weaken b.weaken.weaken.weaken (.bound 2) (.bound 1) (.bound 0)))))

theorem endFormula_delta0 {n : Nat} (C : Data (Project.Term n)) (H N f b : Project.Term n) : (endFormula C H N f b).IsDelta0 :=
  .forallMem _ (.forallMem _ (.forallMem _ (.imp (needAtFormula_delta0 _ _ _ _ _) (needTruthFormula_delta0 _ _ _ _ _ _ _))))

theorem endFormula_freeClosed {n : Nat} {C : Data (Project.Term n)} (hC : C.Closed) (H N f b : Project.Term n)
    (hH : H.freeSupport=[]) (hN : N.freeSupport=[]) (hf : f.freeSupport=[]) (hb : b.freeSupport=[]) : (endFormula C H N f b).FreeClosed := by
  have hNeed := needAtFormula_freeClosed hC.weaken.weaken.weaken N.weaken.weaken.weaken (.bound 2) (.bound 1) (.bound 0)
    (by simpa using hN) rfl rfl rfl
  have hTruth := needTruthFormula_freeClosed hC.weaken.weaken.weaken H.weaken.weaken.weaken f.weaken.weaken.weaken b.weaken.weaken.weaken
    (.bound 2) (.bound 1) (.bound 0) (by simpa using hH) (by simpa using hf) (by simpa using hb) rfl rfl rfl
  simp [endFormula,Project.Formula.forallMem,Definitional.Formula.FreeClosed,hC.omega,hNeed,hTruth]

theorem endFormula_iff {M : SetTheory.Structure.{u}} (he : Extensional M) {n : Nat} (e : Env M n)
    (C : Data (Project.Term n)) (H N f b : Project.Term n) : Project.Formula.satisfies e (endFormula C H N f b) ↔
      End M (C.eval e) (H.eval e) (N.eval e) (f.eval e) (b.eval e) := by
  simp only [endFormula,Project.Formula.satisfies_forallMem_iff,Project.Formula.satisfies_imp_iff,
    needAtFormula_iff he,needTruthFormula_iff he,Data.eval_weaken,Term.eval_weaken]
  rfl

theorem End.transport {M : SetTheory.Structure.{u}} {C : Data M.Domain} {H J N f b : M.Domain}
    (hQueries : ∀ k η a, Query M C.toIndexData H k η a b ↔ Query M C.toIndexData J k η a b)
    (h : End M C H N f b) : End M C J N f b :=
  fun k hk q hq p hp hNeed η hη a ha hfq hfp => (hQueries k η a).mp (h k hk q hq p hp hNeed η hη a ha hfq hfp)

theorem end_agrees_below_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory) {C : Data M.Domain} (hC : C.Valid M)
    {H J N f a b K θ σ : M.Domain} (hCursor : Cursor M C.keys C.index b K θ σ) (hab : M.mem a b)
    (hAgree : ∀ τ, M.mem τ σ → ∀ x, M.mem x C.cap → (MemPair M H τ x ↔ MemPair M J τ x)) :
    End M C H N f a ↔ End M C J N f a := by
  have hQueries (k η x : M.Domain) : Query M C.toIndexData H k η x a ↔ Query M C.toIndexData J k η x a :=
    query_agrees_of_earlier_d hM hC.toValid hCursor (Or.inl hab) hAgree
  exact ⟨End.transport hQueries,End.transport (fun k η x => (hQueries k η x).symm)⟩

end KP1Y.Reflection
