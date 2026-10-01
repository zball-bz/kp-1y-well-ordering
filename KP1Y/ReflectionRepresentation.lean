import KP1Y.ReflectionLabels

/-! 实际根图的表示及其对较早历史的依赖，边层号不作当前层限制。 -/
namespace KP1Y.Reflection
open YesMetaZFC YesMetaZFC.SetTheory YesMetaZFC.SetTheory.Definitional
open KP1Y.Kuratowski KP1Y.Functions
universe u

def EdgeTruth (M : SetTheory.Structure.{u}) (C : Data M.Domain) (H f k q p j : M.Domain) : Prop :=
  ∀ η, M.mem η C.cap → ∀ a, M.mem a C.cap → ∀ b, M.mem b C.cap →
    MemPair M f q η → MemPair M f p a → MemPair M f j b → Query M C.toIndexData H k η a b

def edgeTruthFormula {n : Nat} (C : Data (Project.Term n)) (H f k q p j : Project.Term n) : Project.Formula 1 n :=
  Project.Formula.forallMem C.cap (Project.Formula.forallMem C.cap.weaken (Project.Formula.forallMem C.cap.weaken.weaken
    (.imp (.conj (memPairFormula f.weaken.weaken.weaken q.weaken.weaken.weaken (.bound 2))
      (.conj (memPairFormula f.weaken.weaken.weaken p.weaken.weaken.weaken (.bound 1))
        (memPairFormula f.weaken.weaken.weaken j.weaken.weaken.weaken (.bound 0))))
      (queryFormula C.toIndexData.weaken.weaken.weaken H.weaken.weaken.weaken k.weaken.weaken.weaken (.bound 2) (.bound 1) (.bound 0)))))

theorem edgeTruthFormula_delta0 {n : Nat} (C : Data (Project.Term n)) (H f k q p j : Project.Term n) :
    (edgeTruthFormula C H f k q p j).IsDelta0 := .forallMem _ (.forallMem _ (.forallMem _
      (.imp (.conj (memPairFormula_delta0 _ _ _) (.conj (memPairFormula_delta0 _ _ _) (memPairFormula_delta0 _ _ _)))
        (queryFormula_delta0 _ _ _ _ _ _))))

theorem edgeTruthFormula_freeClosed {n : Nat} {C : Data (Project.Term n)} (hC : C.Closed) (H f k q p j : Project.Term n)
    (hH : H.freeSupport=[]) (hf : f.freeSupport=[]) (hk : k.freeSupport=[]) (hq : q.freeSupport=[])
    (hp : p.freeSupport=[]) (hj : j.freeSupport=[]) : (edgeTruthFormula C H f k q p j).FreeClosed := by
  have hQuery := queryFormula_freeClosed C.toIndexData.weaken.weaken.weaken H.weaken.weaken.weaken k.weaken.weaken.weaken
    (.bound 2) (.bound 1) (.bound 0)
    (by simpa [IndexData.weaken,IndexData.map] using hC.omega) (by simpa [IndexData.weaken,IndexData.map] using hC.cap)
    (by simpa [IndexData.weaken,IndexData.map] using hC.keys) (by simpa [IndexData.weaken,IndexData.map] using hC.index)
    (by simpa [IndexData.weaken,IndexData.map] using hC.bound) (by simpa using hH) (by simpa using hk) rfl rfl rfl
  simp [edgeTruthFormula,memPairFormula,codeFormula,pairFormula,Project.Formula.forallMem,Project.Formula.existsMem,
    Definitional.Formula.FreeClosed,hC.cap,hf,hq,hp,hj,hQuery]

theorem edgeTruthFormula_iff {M : SetTheory.Structure.{u}} (he : Extensional M) {n : Nat} (e : Env M n)
    (C : Data (Project.Term n)) (H f k q p j : Project.Term n) :
    Project.Formula.satisfies e (edgeTruthFormula C H f k q p j) ↔
      EdgeTruth M (C.eval e) (H.eval e) (f.eval e) (k.eval e) (q.eval e) (p.eval e) (j.eval e) := by
  simp only [edgeTruthFormula,Project.Formula.satisfies_forallMem_iff,Project.Formula.satisfies_imp_iff,
    Project.Formula.satisfies_conj_iff,memPairFormula_iff he,queryFormula_iff he,IndexData.eval_weaken,Data.eval_index,Term.eval_weaken]
  exact ⟨fun h η hη a ha b hb hq hp hj => h η hη a ha b hb ⟨hq,hp,hj⟩,
    fun h η hη a ha b hb hRows => h η hη a ha b hb hRows.1 hRows.2.1 hRows.2.2⟩

structure Representation (M : SetTheory.Structure.{u}) (C : Data M.Domain) (H m A f : M.Domain) : Prop where
  diagram : Diagram M C m A
  labeling : Labeling M C m f
  edges : ∀ k, M.mem k C.omega → ∀ q, M.mem q C.omega → ∀ p, M.mem p C.omega → ∀ j, M.mem j C.omega →
    EdgeAt M C A k q p j → EdgeTruth M C H f k q p j

def representationFormula {n : Nat} (C : Data (Project.Term n)) (H m A f : Project.Term n) : Project.Formula 1 n :=
  .conj (diagramFormula C m A) (.conj (labelingFormula C m f)
    (Project.Formula.forallMem C.omega (Project.Formula.forallMem C.omega.weaken
      (Project.Formula.forallMem C.omega.weaken.weaken (Project.Formula.forallMem C.omega.weaken.weaken.weaken
        (.imp (edgeAtFormula C.weaken.weaken.weaken.weaken A.weaken.weaken.weaken.weaken (.bound 3) (.bound 2) (.bound 1) (.bound 0))
          (edgeTruthFormula C.weaken.weaken.weaken.weaken H.weaken.weaken.weaken.weaken f.weaken.weaken.weaken.weaken
            (.bound 3) (.bound 2) (.bound 1) (.bound 0))))))))

theorem representationFormula_delta0 {n : Nat} (C : Data (Project.Term n)) (H m A f : Project.Term n) :
    (representationFormula C H m A f).IsDelta0 := .conj (diagramFormula_delta0 _ _ _) (.conj (labelingFormula_delta0 _ _ _)
      (.forallMem _ (.forallMem _ (.forallMem _ (.forallMem _
        (.imp (edgeAtFormula_delta0 _ _ _ _ _ _) (edgeTruthFormula_delta0 _ _ _ _ _ _ _)))))))

theorem representationFormula_freeClosed {n : Nat} {C : Data (Project.Term n)} (hC : C.Closed) (H m A f : Project.Term n)
    (hH : H.freeSupport=[]) (hm : m.freeSupport=[]) (hA : A.freeSupport=[]) (hf : f.freeSupport=[]) :
    (representationFormula C H m A f).FreeClosed := by
  have hEdge := edgeAtFormula_freeClosed hC.weaken.weaken.weaken.weaken A.weaken.weaken.weaken.weaken
    (.bound 3) (.bound 2) (.bound 1) (.bound 0) (by simpa using hA) rfl rfl rfl rfl
  have hTruth := edgeTruthFormula_freeClosed hC.weaken.weaken.weaken.weaken H.weaken.weaken.weaken.weaken f.weaken.weaken.weaken.weaken
    (.bound 3) (.bound 2) (.bound 1) (.bound 0) (by simpa using hH) (by simpa using hf) rfl rfl rfl rfl
  have hDiagram := diagramFormula_freeClosed hC m A hm hA
  have hLabel := labelingFormula_freeClosed hC m f hm hf
  simp [representationFormula,Project.Formula.forallMem,Definitional.Formula.FreeClosed,hC.omega,hEdge,hTruth,hDiagram,hLabel]

theorem representationFormula_iff {M : SetTheory.Structure.{u}} (he : Extensional M) {n : Nat} (e : Env M n)
    (C : Data (Project.Term n)) (H m A f : Project.Term n) : Project.Formula.satisfies e (representationFormula C H m A f) ↔
      Representation M (C.eval e) (H.eval e) (m.eval e) (A.eval e) (f.eval e) := by
  simp only [representationFormula,Project.Formula.satisfies_conj_iff,diagramFormula_iff he,labelingFormula_iff he,
    Project.Formula.satisfies_forallMem_iff,Project.Formula.satisfies_imp_iff,edgeAtFormula_iff he,edgeTruthFormula_iff he,Data.eval_weaken,Term.eval_weaken]
  exact ⟨fun h => ⟨h.1,h.2.1,h.2.2⟩,fun h => ⟨h.diagram,h.labeling,h.edges⟩⟩

theorem Representation.transport {M : SetTheory.Structure.{u}} (he : Extensional M) {C : Data M.Domain} {H J m A f b : M.Domain}
    (hBelow : Below M C m f b)
    (hQueries : ∀ k η a d, M.mem d b → (Query M C.toIndexData H k η a d ↔ Query M C.toIndexData J k η a d))
    (h : Representation M C H m A f) : Representation M C J m A f := by
  refine ⟨h.diagram,h.labeling,?_⟩
  intro k hk q hq p hp j hj hEdge η hη a ha d hd hfq hfp hfj
  exact (hQueries k η a d (hBelow.at he h.labeling.graph hfj)).mp (h.edges k hk q hq p hp j hj hEdge η hη a ha d hd hfq hfp hfj)

theorem representation_agrees_below_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory) {C : Data M.Domain} (hC : C.Valid M)
    {H J m A f b K θ σ : M.Domain} (hCursor : Cursor M C.keys C.index b K θ σ) (hBelow : Below M C m f b)
    (hAgree : ∀ τ, M.mem τ σ → ∀ a, M.mem a C.cap → (MemPair M H τ a ↔ MemPair M J τ a)) :
    Representation M C H m A f ↔ Representation M C J m A f := by
  have hQueries (k η a d : M.Domain) (hd : M.mem d b) : Query M C.toIndexData H k η a d ↔ Query M C.toIndexData J k η a d :=
    query_agrees_of_earlier_d hM hC.toValid hCursor (Or.inl hd) hAgree
  exact ⟨Representation.transport hM.1 hBelow hQueries,
    Representation.transport hM.1 hBelow (fun k η a d hd => (hQueries k η a d hd).symm)⟩

end KP1Y.Reflection
