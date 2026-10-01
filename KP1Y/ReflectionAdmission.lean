import KP1Y.ReflectionEndpoints

/-! 端点需求只允许较小层，或同层且cut以前、根标签更小的条目。 -/
namespace KP1Y.Reflection
open YesMetaZFC YesMetaZFC.SetTheory YesMetaZFC.SetTheory.Definitional
open KP1Y.Kuratowski KP1Y.Functions
universe u

def Admissible (M : SetTheory.Structure.{u}) (C : Data M.Domain) (K θ N f c : M.Domain) : Prop :=
  ∀ k, M.mem k C.omega → ∀ q, M.mem q C.omega → ∀ p, M.mem p C.omega → NeedAt M C N k q p →
    ∀ η, M.mem η C.cap → MemPair M f q η → M.mem k K ∨ k=K ∧ M.mem q c ∧ M.mem η θ

def admissibleFormula {n : Nat} (C : Data (Project.Term n)) (K θ N f c : Project.Term n) : Project.Formula 1 n :=
  Project.Formula.forallMem C.omega (Project.Formula.forallMem C.omega.weaken (Project.Formula.forallMem C.omega.weaken.weaken
    (.imp (needAtFormula C.weaken.weaken.weaken N.weaken.weaken.weaken (.bound 2) (.bound 1) (.bound 0))
      (Project.Formula.forallMem C.cap.weaken.weaken.weaken
        (.imp (memPairFormula f.weaken.weaken.weaken.weaken (.bound 2) (.bound 0))
          (.disj (.mem (.bound 3) K.weaken.weaken.weaken.weaken)
            (.conj (Project.Formula.extensionalEq (.bound 3) K.weaken.weaken.weaken.weaken)
              (.conj (.mem (.bound 2) c.weaken.weaken.weaken.weaken) (.mem (.bound 0) θ.weaken.weaken.weaken.weaken)))))))))

theorem admissibleFormula_delta0 {n : Nat} (C : Data (Project.Term n)) (K θ N f c : Project.Term n) :
    (admissibleFormula C K θ N f c).IsDelta0 := .forallMem _ (.forallMem _ (.forallMem _
      (.imp (needAtFormula_delta0 _ _ _ _ _) (.forallMem _ (.imp (memPairFormula_delta0 _ _ _)
        (.disj (.mem _ _) (.conj (.atom _ _ _) (.conj (.mem _ _) (.mem _ _)))))))))

theorem admissibleFormula_freeClosed {n : Nat} {C : Data (Project.Term n)} (hC : C.Closed) (K θ N f c : Project.Term n)
    (hK : K.freeSupport=[]) (hθ : θ.freeSupport=[]) (hN : N.freeSupport=[]) (hf : f.freeSupport=[]) (hc : c.freeSupport=[]) :
    (admissibleFormula C K θ N f c).FreeClosed := by
  have hNeed := needAtFormula_freeClosed hC.weaken.weaken.weaken N.weaken.weaken.weaken (.bound 2) (.bound 1) (.bound 0)
    (by simpa using hN) rfl rfl rfl
  simp [admissibleFormula,memPairFormula,codeFormula,pairFormula,Project.Formula.forallMem,Project.Formula.existsMem,
    Definitional.Formula.FreeClosed,hC.omega,hC.cap,hK,hθ,hf,hc,hNeed]

theorem admissibleFormula_iff {M : SetTheory.Structure.{u}} (he : Extensional M) {n : Nat} (e : Env M n)
    (C : Data (Project.Term n)) (K θ N f c : Project.Term n) : Project.Formula.satisfies e (admissibleFormula C K θ N f c) ↔
      Admissible M (C.eval e) (K.eval e) (θ.eval e) (N.eval e) (f.eval e) (c.eval e) := by
  simp only [admissibleFormula,Project.Formula.satisfies_forallMem_iff,Project.Formula.satisfies_imp_iff,
    needAtFormula_iff he,memPairFormula_iff he,Project.Formula.satisfies_disj_iff,Project.Formula.satisfies_conj_iff,
    Project.Formula.satisfies_mem_iff,Project.Formula.satisfies_extensionalEq_iff_eq he,Data.eval_weaken,Term.eval_weaken]
  rfl

theorem admissible_mono_root {M : SetTheory.Structure.{u}} {C : Data M.Domain} {K ξ θ N f c : M.Domain}
    (hθ : M.IsOrdinal θ) (hξθ : ξ=θ ∨ M.mem ξ θ) (h : Admissible M C K ξ N f c) : Admissible M C K θ N f c := by
  intro k hk q hq p hp hNeed η hη hFq
  rcases h k hk q hq p hp hNeed η hη hFq with hkK | ⟨he,hqc,hηξ⟩
  · exact Or.inl hkK
  · refine Or.inr ⟨he,hqc,?_⟩
    rcases hξθ with he | hξθ
    · exact he ▸ hηξ
    · exact hθ.transitive ξ hξθ η hηξ

theorem end_transport_admitted_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory) {C : Data M.Domain} (hC : C.Valid M)
    {H J N f c b K θ σ : M.Domain} (hCursor : Cursor M C.keys C.index b K θ σ) (hAdm : Admissible M C K θ N f c)
    (hAgree : ∀ τ, M.mem τ σ → ∀ a, M.mem a C.cap → (MemPair M H τ a ↔ MemPair M J τ a))
    (h : End M C H N f b) : End M C J N f b := by
  intro k hk q hq p hp hNeed η hη a ha hFq hFp
  have hEarlier : Earlier M b k η b K θ := by
    refine Or.inr ⟨rfl,?_⟩
    rcases hAdm k hk q hq p hp hNeed η hη hFq with hkK | ⟨he,_,hηθ⟩
    · exact Or.inl hkK
    · exact Or.inr ⟨he,hηθ⟩
  exact (query_agrees_of_earlier_d hM hC.toValid hCursor hEarlier hAgree).mp
    (h k hk q hq p hp hNeed η hη a ha hFq hFp)

theorem end_agrees_admitted_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory) {C : Data M.Domain} (hC : C.Valid M)
    {H J N f c b K θ σ : M.Domain} (hCursor : Cursor M C.keys C.index b K θ σ) (hAdm : Admissible M C K θ N f c)
    (hAgree : ∀ τ, M.mem τ σ → ∀ a, M.mem a C.cap → (MemPair M H τ a ↔ MemPair M J τ a)) :
    End M C H N f b ↔ End M C J N f b :=
  ⟨end_transport_admitted_d hM hC hCursor hAdm hAgree,
    end_transport_admitted_d hM hC hCursor hAdm (fun τ hτ a ha => (hAgree τ hτ a ha).symm)⟩

end KP1Y.Reflection
