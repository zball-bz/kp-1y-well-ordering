import KP1Y.ReflectionAdmission

/-! 文稿FR的具体输入需求与输出证书：同宽度同内部图、保留cut前缀、改换端点。 -/
namespace KP1Y.Reflection
open YesMetaZFC YesMetaZFC.SetTheory YesMetaZFC.SetTheory.Definitional
open KP1Y.Kuratowski KP1Y.Functions
universe u

structure Demand (M : SetTheory.Structure.{u}) (C : Data M.Domain) (H K θ a b m A N c f : M.Domain) : Prop where
  template : Template M C m N
  representation : Representation M C H m A f
  cut : MemPair M f c a
  below : Below M C m f b
  admissible : Admissible M C K θ N f c
  endpoint : End M C H N f b

structure Response (M : SetTheory.Structure.{u}) (C : Data M.Domain) (H a m A N c f g : M.Domain) : Prop where
  representation : Representation M C H m A g
  below : Below M C m g a
  prefix_eq : PrefixAgree M C f g c
  endpoint : End M C H N g a

def demandFormula {n : Nat} (C : Data (Project.Term n)) (H K θ a b m A N c f : Project.Term n) : Project.Formula 1 n :=
  .conj (templateFormula C m N) (.conj (representationFormula C H m A f) (.conj (memPairFormula f c a)
    (.conj (belowFormula C m f b) (.conj (admissibleFormula C K θ N f c) (endFormula C H N f b)))))

def responseFormula {n : Nat} (C : Data (Project.Term n)) (H a m A N c f g : Project.Term n) : Project.Formula 1 n :=
  .conj (representationFormula C H m A g) (.conj (belowFormula C m g a)
    (.conj (prefixAgreeFormula C f g c) (endFormula C H N g a)))

theorem demandFormula_delta0 {n : Nat} (C : Data (Project.Term n)) (H K θ a b m A N c f : Project.Term n) :
    (demandFormula C H K θ a b m A N c f).IsDelta0 := .conj (templateFormula_delta0 _ _ _)
      (.conj (representationFormula_delta0 _ _ _ _ _) (.conj (memPairFormula_delta0 _ _ _)
        (.conj (belowFormula_delta0 _ _ _ _) (.conj (admissibleFormula_delta0 _ _ _ _ _ _) (endFormula_delta0 _ _ _ _ _)))))

theorem responseFormula_delta0 {n : Nat} (C : Data (Project.Term n)) (H a m A N c f g : Project.Term n) :
    (responseFormula C H a m A N c f g).IsDelta0 := .conj (representationFormula_delta0 _ _ _ _ _)
      (.conj (belowFormula_delta0 _ _ _ _) (.conj (prefixAgreeFormula_delta0 _ _ _ _) (endFormula_delta0 _ _ _ _ _)))

theorem demandFormula_freeClosed {n : Nat} {C : Data (Project.Term n)} (hC : C.Closed) (H K θ a b m A N c f : Project.Term n)
    (hH : H.freeSupport=[]) (hK : K.freeSupport=[]) (hθ : θ.freeSupport=[]) (ha : a.freeSupport=[]) (hb : b.freeSupport=[])
    (hm : m.freeSupport=[]) (hA : A.freeSupport=[]) (hN : N.freeSupport=[]) (hc : c.freeSupport=[]) (hf : f.freeSupport=[]) :
    (demandFormula C H K θ a b m A N c f).FreeClosed := by
  simp only [demandFormula,Definitional.Formula.FreeClosed]
  refine ⟨templateFormula_freeClosed hC m N hm hN,representationFormula_freeClosed hC H m A f hH hm hA hf,?_,
    belowFormula_freeClosed hC m f b hm hf hb,admissibleFormula_freeClosed hC K θ N f c hK hθ hN hf hc,
    endFormula_freeClosed hC H N f b hH hN hf hb⟩
  simp [memPairFormula,codeFormula,pairFormula,Project.Formula.existsMem,Project.Formula.forallMem,Definitional.Formula.FreeClosed,hf,hc,ha]

theorem responseFormula_freeClosed {n : Nat} {C : Data (Project.Term n)} (hC : C.Closed) (H a m A N c f g : Project.Term n)
    (hH : H.freeSupport=[]) (ha : a.freeSupport=[]) (hm : m.freeSupport=[]) (hA : A.freeSupport=[])
    (hN : N.freeSupport=[]) (hc : c.freeSupport=[]) (hf : f.freeSupport=[]) (hg : g.freeSupport=[]) :
    (responseFormula C H a m A N c f g).FreeClosed := by
  simp only [responseFormula,Definitional.Formula.FreeClosed]
  exact ⟨representationFormula_freeClosed hC H m A g hH hm hA hg,belowFormula_freeClosed hC m g a hm hg ha,
    prefixAgreeFormula_freeClosed hC f g c hf hg hc,endFormula_freeClosed hC H N g a hH hN hg ha⟩

theorem demandFormula_iff {M : SetTheory.Structure.{u}} (he : Extensional M) {n : Nat} (e : Env M n)
    (C : Data (Project.Term n)) (H K θ a b m A N c f : Project.Term n) :
    Project.Formula.satisfies e (demandFormula C H K θ a b m A N c f) ↔
      Demand M (C.eval e) (H.eval e) (K.eval e) (θ.eval e) (a.eval e) (b.eval e) (m.eval e) (A.eval e) (N.eval e) (c.eval e) (f.eval e) := by
  simp only [demandFormula,Project.Formula.satisfies_conj_iff,templateFormula_iff he,representationFormula_iff he,
    memPairFormula_iff he,belowFormula_iff he,admissibleFormula_iff he,endFormula_iff he]
  exact ⟨fun h => ⟨h.1,h.2.1,h.2.2.1,h.2.2.2.1,h.2.2.2.2.1,h.2.2.2.2.2⟩,
    fun h => ⟨h.template,h.representation,h.cut,h.below,h.admissible,h.endpoint⟩⟩

theorem responseFormula_iff {M : SetTheory.Structure.{u}} (he : Extensional M) {n : Nat} (e : Env M n)
    (C : Data (Project.Term n)) (H a m A N c f g : Project.Term n) :
    Project.Formula.satisfies e (responseFormula C H a m A N c f g) ↔
      Response M (C.eval e) (H.eval e) (a.eval e) (m.eval e) (A.eval e) (N.eval e) (c.eval e) (f.eval e) (g.eval e) := by
  simp only [responseFormula,Project.Formula.satisfies_conj_iff,representationFormula_iff he,
    belowFormula_iff he,prefixAgreeFormula_iff he,endFormula_iff he]
  exact ⟨fun h => ⟨h.1,h.2.1,h.2.2.1,h.2.2.2⟩,fun h => ⟨h.representation,h.below,h.prefix_eq,h.endpoint⟩⟩

theorem Demand.transport_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory) {C : Data M.Domain} (hC : C.Valid M)
    {H J K θ a b m A N c f σ : M.Domain} (hCursor : Cursor M C.keys C.index b K θ σ)
    (hAgree : ∀ τ, M.mem τ σ → ∀ x, M.mem x C.cap → (MemPair M H τ x ↔ MemPair M J τ x))
    (h : Demand M C H K θ a b m A N c f) : Demand M C J K θ a b m A N c f :=
  ⟨h.template,(representation_agrees_below_d hM hC hCursor h.below hAgree).mp h.representation,h.cut,h.below,h.admissible,
    (end_agrees_admitted_d hM hC hCursor h.admissible hAgree).mp h.endpoint⟩

theorem Response.transport_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory) {C : Data M.Domain} (hC : C.Valid M)
    {H J K θ a b m A N c f g σ : M.Domain} (hCursor : Cursor M C.keys C.index b K θ σ) (hab : M.mem a b)
    (hAgree : ∀ τ, M.mem τ σ → ∀ x, M.mem x C.cap → (MemPair M H τ x ↔ MemPair M J τ x))
    (h : Response M C H a m A N c f g) : Response M C J a m A N c f g := by
  have hb := ((hC.toValid.cursor_iff_d hM b K θ σ).mp hCursor).1
  exact ⟨(representation_agrees_below_d hM hC hCursor (h.below.trans (hC.cap.mem hb) hab) hAgree).mp h.representation,
    h.below,h.prefix_eq,(end_agrees_below_d hM hC hCursor hab hAgree).mp h.endpoint⟩

end KP1Y.Reflection
