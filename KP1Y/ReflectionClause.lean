import KP1Y.ReflectionDemand

/-! 文稿Definition2的完整有界FR公式，以及对较早行的局部性和根阈值单调性。 -/
namespace KP1Y.Reflection
open YesMetaZFC YesMetaZFC.SetTheory YesMetaZFC.SetTheory.Definitional
open KP1Y.Kuratowski KP1Y.Functions
universe u

def Reflect (M : SetTheory.Structure.{u}) (C : Data M.Domain) (H K θ a b : M.Domain) : Prop :=
  ∀ m, M.mem m C.omega → ∀ A, M.mem A C.edgeLists → ∀ N, M.mem N C.needLists →
    ∀ c, M.mem c m → ∀ f, M.mem f C.labels → Demand M C H K θ a b m A N c f →
      ∃ g, M.mem g C.labels ∧ Response M C H a m A N c f g

def reflectionFormula {n : Nat} (C : Data (Project.Term n)) (H K θ a b : Project.Term n) : Project.Formula 1 n :=
  Project.Formula.forallMem C.omega (Project.Formula.forallMem C.edgeLists.weaken
    (Project.Formula.forallMem C.needLists.weaken.weaken (Project.Formula.forallMem (.bound 2)
      (Project.Formula.forallMem C.labels.weaken.weaken.weaken.weaken
        (.imp (demandFormula C.weaken.weaken.weaken.weaken.weaken H.weaken.weaken.weaken.weaken.weaken
          K.weaken.weaken.weaken.weaken.weaken θ.weaken.weaken.weaken.weaken.weaken
          a.weaken.weaken.weaken.weaken.weaken b.weaken.weaken.weaken.weaken.weaken (.bound 4) (.bound 3) (.bound 2) (.bound 1) (.bound 0))
          (Project.Formula.existsMem C.labels.weaken.weaken.weaken.weaken.weaken
            (responseFormula C.weaken.weaken.weaken.weaken.weaken.weaken H.weaken.weaken.weaken.weaken.weaken.weaken
              a.weaken.weaken.weaken.weaken.weaken.weaken (.bound 5) (.bound 4) (.bound 3) (.bound 2) (.bound 1) (.bound 0))))))))

theorem reflectionFormula_delta0 {n : Nat} (C : Data (Project.Term n)) (H K θ a b : Project.Term n) :
    (reflectionFormula C H K θ a b).IsDelta0 := .forallMem _ (.forallMem _ (.forallMem _ (.forallMem _ (.forallMem _
      (.imp (demandFormula_delta0 _ _ _ _ _ _ _ _ _ _ _) (.existsMem _ (responseFormula_delta0 _ _ _ _ _ _ _ _ _)))))))

theorem reflectionFormula_freeClosed {n : Nat} {C : Data (Project.Term n)} (hC : C.Closed) (H K θ a b : Project.Term n)
    (hH : H.freeSupport=[]) (hK : K.freeSupport=[]) (hθ : θ.freeSupport=[]) (ha : a.freeSupport=[]) (hb : b.freeSupport=[]) :
    (reflectionFormula C H K θ a b).FreeClosed := by
  have hDemand := demandFormula_freeClosed hC.weaken.weaken.weaken.weaken.weaken H.weaken.weaken.weaken.weaken.weaken
    K.weaken.weaken.weaken.weaken.weaken θ.weaken.weaken.weaken.weaken.weaken a.weaken.weaken.weaken.weaken.weaken
    b.weaken.weaken.weaken.weaken.weaken (.bound 4) (.bound 3) (.bound 2) (.bound 1) (.bound 0)
    (by simpa using hH) (by simpa using hK) (by simpa using hθ) (by simpa using ha) (by simpa using hb) rfl rfl rfl rfl rfl
  have hResponse := responseFormula_freeClosed hC.weaken.weaken.weaken.weaken.weaken.weaken H.weaken.weaken.weaken.weaken.weaken.weaken
    a.weaken.weaken.weaken.weaken.weaken.weaken (.bound 5) (.bound 4) (.bound 3) (.bound 2) (.bound 1) (.bound 0)
    (by simpa using hH) (by simpa using ha) rfl rfl rfl rfl rfl rfl
  simp [reflectionFormula,Project.Formula.forallMem,Project.Formula.existsMem,Definitional.Formula.FreeClosed,
    hC.omega,hC.edgeLists,hC.needLists,hC.labels,hDemand,hResponse]

theorem reflectionFormula_iff {M : SetTheory.Structure.{u}} (he : Extensional M) {n : Nat} (e : Env M n)
    (C : Data (Project.Term n)) (H K θ a b : Project.Term n) : Project.Formula.satisfies e (reflectionFormula C H K θ a b) ↔
      Reflect M (C.eval e) (H.eval e) (K.eval e) (θ.eval e) (a.eval e) (b.eval e) := by
  simp only [reflectionFormula,Project.Formula.satisfies_forallMem_iff,Project.Formula.satisfies_existsMem_iff,
    Project.Formula.satisfies_imp_iff,demandFormula_iff he,responseFormula_iff he,Data.eval_weaken,Term.eval_weaken]
  rfl

theorem reflection_transport_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory) {C : Data M.Domain} (hC : C.Valid M)
    {H J K θ a b σ : M.Domain} (hCursor : Cursor M C.keys C.index b K θ σ) (hab : M.mem a b)
    (hAgree : ∀ τ, M.mem τ σ → ∀ x, M.mem x C.cap → (MemPair M H τ x ↔ MemPair M J τ x))
    (h : Reflect M C H K θ a b) : Reflect M C J K θ a b := by
  intro m hm A hA N hN c hc f hf hDemand
  have hInput := hDemand.transport_d hM hC hCursor (fun τ hτ x hx => (hAgree τ hτ x hx).symm)
  obtain ⟨g,hg,hResponse⟩ := h m hm A hA N hN c hc f hf hInput
  exact ⟨g,hg,hResponse.transport_d hM hC hCursor hab hAgree⟩

theorem reflection_agrees_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory) {C : Data M.Domain} (hC : C.Valid M)
    {H J K θ a b σ : M.Domain} (hCursor : Cursor M C.keys C.index b K θ σ) (hab : M.mem a b)
    (hAgree : ∀ τ, M.mem τ σ → ∀ x, M.mem x C.cap → (MemPair M H τ x ↔ MemPair M J τ x)) :
    Reflect M C H K θ a b ↔ Reflect M C J K θ a b :=
  ⟨reflection_transport_d hM hC hCursor hab hAgree,
    reflection_transport_d hM hC hCursor hab (fun τ hτ x hx => (hAgree τ hτ x hx).symm)⟩

theorem reflect_mono_root {M : SetTheory.Structure.{u}} {C : Data M.Domain} {H K ξ θ a b : M.Domain}
    (hθ : M.IsOrdinal θ) (hξθ : ξ=θ ∨ M.mem ξ θ) (h : Reflect M C H K θ a b) : Reflect M C H K ξ a b := by
  intro m hm A hA N hN c hc f hf hDemand
  exact h m hm A hA N hN c hc f hf ⟨hDemand.template,hDemand.representation,hDemand.cut,hDemand.below,
    admissible_mono_root hθ hξθ hDemand.admissible,hDemand.endpoint⟩

end KP1Y.Reflection
