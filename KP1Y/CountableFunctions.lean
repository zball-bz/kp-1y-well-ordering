import KP1Y.WordEnumerationCoverage
import KP1Y.SequenceCertificate

/-! 对象模型中的满射复合和可数像；所有函数均为实际集合图。 -/
namespace KP1Y.Cardinal
open YesMetaZFC YesMetaZFC.SetTheory
open KP1Y.Kuratowski KP1Y.Functions
universe u

theorem Onto.bounds {M : SetTheory.Structure.{u}} (he : Extensional M) {f X Y x y : M.Domain}
    (hf : Onto M f X Y) (hxy : MemPair M f x y) : M.mem x X ∧ M.mem y Y := by
  obtain ⟨p,hp,hCode⟩ := hxy
  obtain ⟨a,ha,b,hb,hCode'⟩ := hf.1 p hp
  obtain ⟨hxa,hyb⟩ := codes_injective he hCode hCode'
  subst a
  subst b
  exact ⟨ha,hb⟩

theorem Onto.toGraph {M : SetTheory.Structure.{u}} (he : Extensional M) {f X Y : M.Domain}
    (hf : Onto M f X Y) : Graph M f X Y :=
  ⟨hf.1,hf.2.1,fun x y z hxy hxz => hf.2.2.1 x (hf.bounds he hxy).1 y (hf.bounds he hxy).2
    z (hf.bounds he hxz).2 hxy hxz⟩

theorem onto_compose_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {f g X Y Z : M.Domain} (hf : Onto M f X Y) (hg : Onto M g Y Z) : ∃ h, Onto M h X Z := by
  obtain ⟨h,hValue⟩ := KP1Y.Assignments.tuple_value_exists_d hM (hf.toGraph hM.1) (hg.toGraph hM.1)
  refine ⟨h,hValue.values.support,hValue.values.total,
    fun x _ y _ z _ hxy hxz => hValue.values.unique x y z hxy hxz,?_⟩
  intro z hz
  obtain ⟨y,hy,hgAt⟩ := hg.2.2.2 z hz
  obtain ⟨x,hx,hfAt⟩ := hf.2.2.2 y hy
  exact ⟨x,hx,(hValue.rows x hx y hy z hz hfAt).mpr hgAt⟩

theorem function_range_countable_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {ω f Y : M.Domain} (hf : Graph M f ω Y) :
    ∃ X, (∀ y, M.mem y X ↔ ∃ n, M.mem n ω ∧ MemPair M f n y) ∧ Onto M f ω X := by
  obtain ⟨X,hX⟩ := KP1Y.Sequences.range_bound_exists_d hM Y f ω
  have hRange := hX.exact hM.1 hf
  have hGraph : Graph M f ω X := KP1Y.Assignments.graph_tighten_values hf
    (fun n y hAt => (hRange y).mpr ⟨n,(hf.bounds hM.1 hAt).1,hAt⟩)
  exact ⟨X,hRange,hGraph.support,hGraph.total,fun n _ a _ b _ ha hb => hGraph.unique n a b ha hb,
    fun y hy => (hRange y).mp hy⟩

theorem countable_function_image_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {ω E X f Y : M.Domain} (hE : Onto M E ω X) (hf : Graph M f X Y) :
    ∃ image enumerator, (∀ y, M.mem y image ↔ ∃ x, M.mem x X ∧ MemPair M f x y) ∧ Onto M enumerator ω image := by
  obtain ⟨enumerator,hCompose⟩ := KP1Y.Assignments.tuple_value_exists_d hM (hE.toGraph hM.1) hf
  obtain ⟨image,hRange,hOnto⟩ := function_range_countable_d hM hCompose.values
  refine ⟨image,enumerator,?_,hOnto⟩
  intro y
  rw [hRange y]
  constructor
  · rintro ⟨n,hn,hAt⟩
    obtain ⟨x,hx,hEx⟩ := hE.2.1 n hn
    have hy := (hCompose.values.bounds hM.1 hAt).2
    exact ⟨x,hx,(hCompose.rows n hn x hx y hy hEx).mp hAt⟩
  · rintro ⟨x,hx,hfy⟩
    obtain ⟨n,hn,hEx⟩ := hE.2.2.2 x hx
    exact ⟨n,hn,(hCompose.rows n hn x hx y (hf.bounds hM.1 hfy).2 hEx).mpr hfy⟩

end KP1Y.Cardinal
