import KP1Y.ReflectionHeightTop
import KP1Y.ReflectionHeightIteration

/-! 任意内部有限根图由实际递增高度序列表示；空图宽度也包含在同一构造中。 -/
namespace KP1Y.ReflectionModel
open YesMetaZFC YesMetaZFC.SetTheory
open KP1Y.Kuratowski KP1Y.Functions KP1Y.Reflection KP1Y.Cardinal
universe u

theorem HeightSequence.labeling_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ArticleData M.Domain} (hC : C.Valid M) {S : ArticleStructure M.Domain} {γ m f : M.Domain}
    (h : HeightSequence M C S γ m f) (hm : M.mem m C.reflection.omega) : Labeling M C.reflection m f := by
  have hSub : M.MemberSubset C.top C.reflection.cap := hC.reflection.cap.transitive C.top hC.cap.predecessor_mem
  refine ⟨hm,h.graph.mono_values hSub,?_,increasing_enlarge hM.1 h.graph h.increasing⟩
  intro i _ δ _ hAt
  obtain ⟨small,hδ⟩ := h.heights i δ hAt
  exact hδ.omega

theorem HeightSequence.representation_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ArticleData M.Domain} (hC : C.Valid M) {S : ArticleStructure M.Domain} (hS : S.Valid M C)
    {γ m f diagram : M.Domain} (h : HeightSequence M C S γ m f) (hDiagram : Diagram M C.reflection m diagram) :
    Representation M C.reflection C.table m diagram f := by
  refine ⟨hDiagram,h.labeling_d hM hC hDiagram.1,?_⟩
  intro k hk q _ p _ j _ hEdge η _ a _ b _ hFq hFp hFj
  obtain ⟨hqM,hpM,hjM,hqp,hpj⟩ := hDiagram.edge_columns_d hM hC.reflection hEdge
  have hηTop := (h.graph.bounds hM.1 hFq).2
  have haTop := (h.graph.bounds hM.1 hFp).2
  have hbTop := (h.graph.bounds hM.1 hFj).2
  have hηa : η=a ∨ M.mem η a := by
    rcases hqp with he | hqp
    · subst p
      exact Or.inl (h.graph.unique q η a hFq hFp)
    · exact Or.inr (h.increasing q hqM p hpM hqp η hηTop a haTop hFq hFp)
  have hab := h.increasing p hpM j hjM hpj a haTop b hbTop hFp hFj
  obtain ⟨smallA,hA⟩ := h.heights p a hFp
  obtain ⟨smallB,hB⟩ := h.heights j b hFj
  exact (hB.query_agreement_d hM hC hS hk hab hηa).mp (hA.top_query_d hM hC hS hk hηa)

theorem initial_representation_above_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ArticleData M.Domain} (hC : C.Valid M) {S : ArticleStructure M.Domain} (hS : S.Valid M C)
    (hκ : UncountableOrdinal M C.reflection.omega C.top) {γ m diagram : M.Domain}
    (hγ : M.mem γ C.top) (hDiagram : Diagram M C.reflection m diagram) :
    ∃ f, HeightSequence M C S γ m f ∧ Representation M C.reflection C.table m diagram f := by
  obtain ⟨f,hSeq⟩ := height_sequence_exists_d hM hC hS hκ hγ hDiagram.1
  exact ⟨f,hSeq,hSeq.representation_d hM hC hS hDiagram⟩

theorem initial_representation_exists_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ArticleData M.Domain} (hC : C.Valid M) {S : ArticleStructure M.Domain} (hS : S.Valid M C)
    (hκ : UncountableOrdinal M C.reflection.omega C.top) {m diagram : M.Domain}
    (hDiagram : Diagram M C.reflection m diagram) :
    ∃ f, M.mem f C.reflection.labels ∧ Representation M C.reflection C.table m diagram f ∧ Below M C.reflection m f C.top := by
  obtain ⟨f,hSeq,hRep⟩ := initial_representation_above_d hM hC hS hκ hC.omega_top hDiagram
  exact ⟨f,hRep.labeling.sequence hC.reflection,hRep,fun _ _ _ _ hAt => (hSeq.graph.bounds hM.1 hAt).2⟩

end KP1Y.ReflectionModel
