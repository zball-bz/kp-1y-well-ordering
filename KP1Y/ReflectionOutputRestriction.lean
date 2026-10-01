import KP1Y.ReflectionGroundParameters
import KP1Y.AssignmentCarriers

/-! 输出变量都落在小域时，整个量词块赋值也落在小域；处理反例反射中的候选输出绝对性。 -/
namespace KP1Y.ReflectionModel
open YesMetaZFC YesMetaZFC.SetTheory
open KP1Y.Kuratowski KP1Y.Functions KP1Y.Assignments KP1Y.Satisfaction
universe u

theorem frame_restrict_by_tuple {M : SetTheory.Structure.{u}} (he : Extensional M) {vars n scope A B s t g : M.Domain}
    (hAB : M.MemberSubset A B) (hS : Graph M s scope A) (hFrame : AgreeOutside M vars n s t scope B)
    (hTuple : TupleValue M g vars t n scope B) (hValues : ∀ i x, MemPair M g i x → M.mem x A) :
    AgreeOutside M vars n s t scope A ∧ TupleValue M g vars t n scope A := by
  have hT : Graph M t scope A := graph_tighten_values hFrame.target (by
    intro v x hAt
    have hb := hFrame.target.bounds he hAt
    classical
    by_cases hTouched : Touched M vars n v
    · obtain ⟨i,hi,hName⟩ := hTouched
      exact hValues i x ((hTuple.rows i hi v hb.1 x hb.2 hName).mpr hAt)
    · exact (hS.bounds he ((hFrame.rows v hb.1 hTouched x hb.2).mpr hAt)).2)
  have hG : Graph M g n A := graph_tighten_values hTuple.values hValues
  exact ⟨⟨hS,hT,fun v hv hNot x hx => hFrame.rows v hv hNot x (hAB x hx)⟩,
    ⟨hTuple.variables,hT,hG,fun i hi v hv x hx hName => hTuple.rows i hi v hv x (hAB x hx) hName⟩⟩

theorem frame_restrict_below_cut {M : SetTheory.Structure.{u}} (he : Extensional M) {vars n scope δ κ a s t g : M.Domain}
    (hSub : M.MemberSubset δ κ) (hδ : M.IsOrdinal δ) (ha : M.mem a δ) (hS : Graph M s scope δ)
    (hFrame : AgreeOutside M vars n s t scope κ) (hTuple : TupleValue M g vars t n scope κ)
    (hBelow : ∀ i x, MemPair M g i x → M.mem x a) :
    AgreeOutside M vars n s t scope δ ∧ TupleValue M g vars t n scope δ :=
  frame_restrict_by_tuple he hSub hS hFrame hTuple (fun i x hAt => hδ.transitive a ha x (hBelow i x hAt))

theorem GroundParameters.enlarge {M : SetTheory.Structure.{u}} {C : ArticleData M.Domain} {T : TemplateShape M.Domain}
    {V : NameFrame M.Domain} {a θ A B s : M.Domain} (hSub : M.MemberSubset A B) (h : GroundParameters M C T V a θ A s) :
    GroundParameters M C T V a θ B s := ⟨h.graph.mono_values hSub,h.omega,h.point,h.root,h.edges,h.needs⟩

theorem frame_enlarge {M : SetTheory.Structure.{u}} (he : Extensional M) {vars n scope A B s t : M.Domain}
    (hSub : M.MemberSubset A B) (h : AgreeOutside M vars n s t scope A) : AgreeOutside M vars n s t scope B := by
  refine ⟨h.source.mono_values hSub,h.target.mono_values hSub,?_⟩
  intro v hv hNot x _
  classical
  by_cases hx : M.mem x A
  · exact h.rows v hv hNot x hx
  · exact iff_of_false (fun hAt => hx (h.source.bounds he hAt).2) (fun hAt => hx (h.target.bounds he hAt).2)

end KP1Y.ReflectionModel
