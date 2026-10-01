import KP1Y.ReflectionAtoms

/-! 有限根图和端点模板的合法性。内部图不依赖当前反射层K，绝不限制其边层号。 -/
namespace KP1Y.Reflection
open YesMetaZFC YesMetaZFC.SetTheory YesMetaZFC.SetTheory.Definitional
open KP1Y.Kuratowski KP1Y.Functions
universe u

def Diagram (M : SetTheory.Structure.{u}) (C : Data M.Domain) (m A : M.Domain) : Prop :=
  M.mem m C.omega ∧ M.mem A C.edgeLists ∧ ∀ k, M.mem k C.omega → ∀ q, M.mem q C.omega →
    ∀ p, M.mem p C.omega → ∀ j, M.mem j C.omega → EdgeAt M C A k q p j → (q=p ∨ M.mem q p) ∧ M.mem p j ∧ M.mem j m

def Template (M : SetTheory.Structure.{u}) (C : Data M.Domain) (m N : M.Domain) : Prop :=
  M.mem m C.omega ∧ M.mem N C.needLists ∧ ∀ k, M.mem k C.omega → ∀ q, M.mem q C.omega →
    ∀ p, M.mem p C.omega → NeedAt M C N k q p → (q=p ∨ M.mem q p) ∧ M.mem p m

def diagramFormula {n : Nat} (C : Data (Project.Term n)) (m A : Project.Term n) : Project.Formula 1 n :=
  .conj (.mem m C.omega) (.conj (.mem A C.edgeLists)
    (Project.Formula.forallMem C.omega (Project.Formula.forallMem C.omega.weaken
      (Project.Formula.forallMem C.omega.weaken.weaken (Project.Formula.forallMem C.omega.weaken.weaken.weaken
        (.imp (edgeAtFormula C.weaken.weaken.weaken.weaken A.weaken.weaken.weaken.weaken (.bound 3) (.bound 2) (.bound 1) (.bound 0))
          (.conj (.disj (Project.Formula.extensionalEq (.bound 2) (.bound 1)) (.mem (.bound 2) (.bound 1)))
            (.conj (.mem (.bound 1) (.bound 0)) (.mem (.bound 0) m.weaken.weaken.weaken.weaken)))))))))

def templateFormula {n : Nat} (C : Data (Project.Term n)) (m N : Project.Term n) : Project.Formula 1 n :=
  .conj (.mem m C.omega) (.conj (.mem N C.needLists)
    (Project.Formula.forallMem C.omega (Project.Formula.forallMem C.omega.weaken
      (Project.Formula.forallMem C.omega.weaken.weaken
        (.imp (needAtFormula C.weaken.weaken.weaken N.weaken.weaken.weaken (.bound 2) (.bound 1) (.bound 0))
          (.conj (.disj (Project.Formula.extensionalEq (.bound 1) (.bound 0)) (.mem (.bound 1) (.bound 0)))
            (.mem (.bound 0) m.weaken.weaken.weaken)))))))

theorem diagramFormula_delta0 {n : Nat} (C : Data (Project.Term n)) (m A : Project.Term n) : (diagramFormula C m A).IsDelta0 :=
  .conj (.mem _ _) (.conj (.mem _ _) (.forallMem _ (.forallMem _ (.forallMem _ (.forallMem _
    (.imp (edgeAtFormula_delta0 _ _ _ _ _ _) (.conj (.disj (.atom _ _ _) (.mem _ _)) (.conj (.mem _ _) (.mem _ _)))))))))

theorem templateFormula_delta0 {n : Nat} (C : Data (Project.Term n)) (m N : Project.Term n) : (templateFormula C m N).IsDelta0 :=
  .conj (.mem _ _) (.conj (.mem _ _) (.forallMem _ (.forallMem _ (.forallMem _
    (.imp (needAtFormula_delta0 _ _ _ _ _) (.conj (.disj (.atom _ _ _) (.mem _ _)) (.mem _ _)))))))

theorem diagramFormula_freeClosed {n : Nat} {C : Data (Project.Term n)} (hC : C.Closed) (m A : Project.Term n)
    (hm : m.freeSupport=[]) (hA : A.freeSupport=[]) : (diagramFormula C m A).FreeClosed := by
  have hEdges := edgeAtFormula_freeClosed hC.weaken.weaken.weaken.weaken A.weaken.weaken.weaken.weaken
    (.bound 3) (.bound 2) (.bound 1) (.bound 0) (by simpa using hA) rfl rfl rfl rfl
  simp [diagramFormula,Project.Formula.forallMem,Definitional.Formula.FreeClosed,hC.omega,hC.edgeLists,hm,hA,hEdges]

theorem templateFormula_freeClosed {n : Nat} {C : Data (Project.Term n)} (hC : C.Closed) (m N : Project.Term n)
    (hm : m.freeSupport=[]) (hN : N.freeSupport=[]) : (templateFormula C m N).FreeClosed := by
  have hNeeds := needAtFormula_freeClosed hC.weaken.weaken.weaken N.weaken.weaken.weaken
    (.bound 2) (.bound 1) (.bound 0) (by simpa using hN) rfl rfl rfl
  simp [templateFormula,Project.Formula.forallMem,Definitional.Formula.FreeClosed,hC.omega,hC.needLists,hm,hN,hNeeds]

theorem diagramFormula_iff {M : SetTheory.Structure.{u}} (he : Extensional M) {n : Nat} (e : Env M n)
    (C : Data (Project.Term n)) (m A : Project.Term n) : Project.Formula.satisfies e (diagramFormula C m A) ↔
      Diagram M (C.eval e) (m.eval e) (A.eval e) := by
  simp only [diagramFormula,Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_mem_iff,
    Project.Formula.satisfies_forallMem_iff,Project.Formula.satisfies_imp_iff,edgeAtFormula_iff he,
    Project.Formula.satisfies_disj_iff,Project.Formula.satisfies_extensionalEq_iff_eq he,Data.eval_weaken,Term.eval_weaken]
  rfl

theorem templateFormula_iff {M : SetTheory.Structure.{u}} (he : Extensional M) {n : Nat} (e : Env M n)
    (C : Data (Project.Term n)) (m N : Project.Term n) : Project.Formula.satisfies e (templateFormula C m N) ↔
      Template M (C.eval e) (m.eval e) (N.eval e) := by
  simp only [templateFormula,Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_mem_iff,
    Project.Formula.satisfies_forallMem_iff,Project.Formula.satisfies_imp_iff,needAtFormula_iff he,
    Project.Formula.satisfies_disj_iff,Project.Formula.satisfies_extensionalEq_iff_eq he,Data.eval_weaken,Term.eval_weaken]
  rfl

theorem Diagram.edge_columns_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory) {C : Data M.Domain} (hC : C.Valid M)
    {m A k q p j : M.Domain} (h : Diagram M C m A) (hEdge : EdgeAt M C A k q p j) :
    M.mem q m ∧ M.mem p m ∧ M.mem j m ∧ (q=p ∨ M.mem q p) ∧ M.mem p j := by
  obtain ⟨hk,hq,hp,hj⟩ := hEdge.bounds hM.1 hC
  obtain ⟨hqp,hpj,hjm⟩ := h.2.2 k hk q hq p hp j hj hEdge
  have hm := (KP1Y.Naturals.omega_isOrdinal_d hM hC.omega).mem h.1
  have hpm := hm.transitive j hjm p hpj
  refine ⟨?_,hpm,hjm,hqp,hpj⟩
  rcases hqp with he | hqp
  · exact he ▸ hpm
  · exact hm.transitive p hpm q hqp

theorem Template.need_columns_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory) {C : Data M.Domain} (hC : C.Valid M)
    {m N k q p : M.Domain} (h : Template M C m N) (hNeed : NeedAt M C N k q p) :
    M.mem q m ∧ M.mem p m ∧ (q=p ∨ M.mem q p) := by
  obtain ⟨hk,hq,hp⟩ := hNeed.bounds hM.1 hC
  obtain ⟨hqp,hpm⟩ := h.2.2 k hk q hq p hp hNeed
  refine ⟨?_,hpm,hqp⟩
  rcases hqp with he | hqp
  · exact he ▸ hpm
  · exact ((KP1Y.Naturals.omega_isOrdinal_d hM hC.omega).mem h.1).transitive p hpm q hqp

end KP1Y.Reflection
