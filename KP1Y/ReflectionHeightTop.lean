import KP1Y.ReflectionHeightAgreement
import KP1Y.ReflectionPrefixExistence

/-! 第6引理(8)：每个初等高度 δ 都满足全部 θ≤δ 的顶端查询，包括 θ=δ。 -/
namespace KP1Y.ReflectionModel
open YesMetaZFC YesMetaZFC.SetTheory
open KP1Y.Kuratowski KP1Y.Functions KP1Y.Reflection
universe u

theorem Height.end_top_iff_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ArticleData M.Domain} (hC : C.Valid M) {S : ArticleStructure M.Domain} (hS : S.Valid M C)
    {δ : M.Domain} {small : KP1Y.Satisfaction.EvaluationData M.Domain} (h : Height M C S δ small)
    {m N f : M.Domain} (hF : Graph M f m δ) :
    End M C.reflection C.table N f C.top ↔ End M C.reflection C.table N f δ := by
  constructor
  · intro hEnd k hk q hq p hp hNeed η hη a ha hFq hFp
    have hQ := hEnd k hk q hq p hp hNeed η hη a ha hFq hFp
    exact (h.query_agreement_d hM hC hS hk (hF.bounds hM.1 hFp).2 hQ.1.2.2.2.2.1).mp hQ
  · intro hEnd k hk q hq p hp hNeed η hη a ha hFq hFp
    have hQ := hEnd k hk q hq p hp hNeed η hη a ha hFq hFp
    exact (h.query_agreement_d hM hC hS hk (hF.bounds hM.1 hFp).2 hQ.1.2.2.2.2.1).mpr hQ

theorem Height.top_query_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ArticleData M.Domain} (hC : C.Valid M) {S : ArticleStructure M.Domain} (hS : S.Valid M C)
    {δ : M.Domain} {small : KP1Y.Satisfaction.EvaluationData M.Domain} (h : Height M C S δ small)
    {K θ : M.Domain} (hK : M.mem K C.reflection.omega) (hθδ : θ=δ ∨ M.mem θ δ) :
    Query M C.reflection.toIndexData C.table K θ δ C.top := by
  have hδCap := hC.reflection.cap.transitive C.top hC.cap.predecessor_mem δ h.below
  have hθCap : M.mem θ C.reflection.cap := by
    rcases hθδ with he | hθ
    · exact he ▸ hδCap
    · exact hC.reflection.cap.transitive δ hδCap θ hθ
  apply (hC.table.equation_d hM hC.reflection K θ δ C.top).mpr
  refine ⟨⟨hK,hθCap,hδCap,hC.cap.predecessor_mem,hθδ,h.below,h.omega⟩,?_⟩
  intro m _ diagram _ template _ cut hCut f _ hDemand
  obtain ⟨NI,NN,hShape⟩ := template_shape_exists hC hDemand.representation.diagram hDemand.template hCut
  let T : TemplateShape M.Domain := ⟨m,diagram,template,cut,NI,NN⟩
  have hT : T.Valid M C := hShape
  obtain ⟨F,_,V,hV,B,hB⟩ := template_environment_exists_d hM hC hS.interpretation hT K
  obtain ⟨g,hG,hRep,hPrefix,hEnd⟩ := h.reflect_prefix_witness_d hM hC hS hT hV hB
    (demand_graph_below hM.1 hDemand) hDemand.representation hDemand.cut hDemand.endpoint
  exact ⟨g,hRep.labeling.sequence hC.reflection,hRep,
    (fun _ _ _ _ hAt => (hG.bounds hM.1 hAt).2),hPrefix,(h.end_top_iff_d hM hC hS hG).mp hEnd⟩

end KP1Y.ReflectionModel
