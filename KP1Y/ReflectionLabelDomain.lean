import KP1Y.ReflectionSemantics

/-! 实际标签集合D={x∈cap:ω∈x}，并证明标签公式等价于到D的严格递增有限函数。 -/
namespace KP1Y.Reflection
open YesMetaZFC YesMetaZFC.SetTheory YesMetaZFC.SetTheory.Definitional
open KP1Y.Kuratowski KP1Y.Functions
universe u

private def aboveSchema : Project.Delta0UnarySchema 1 where
  body := .mem (.bound 1) (.bound 0)
  freeClosed := by simp [Definitional.Formula.FreeClosed]
  delta0 := .mem _ _

theorem label_domain_exists_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory) (C : Data M.Domain) :
    ∃ D, ∀ x, M.mem x D ↔ M.mem x C.cap ∧ M.mem C.omega x := by
  obtain ⟨D,hD⟩ := SetTheory.KP.separation_exists_d (KP1Y.models_weakKP hM) aboveSchema (oneEnv C.omega) C.cap
  refine ⟨D,?_⟩
  intro x
  have hAbove : Project.Formula.satisfies ((oneEnv C.omega).push x) aboveSchema.body ↔ M.mem C.omega x := by
    rw [aboveSchema,Project.Formula.satisfies_mem_iff]
    rfl
  simpa only [hAbove] using hD x

theorem Labeling.graph_domain {M : SetTheory.Structure.{u}} {C : Data M.Domain} {D m f : M.Domain}
    (hD : ∀ x, M.mem x D ↔ M.mem x C.cap ∧ M.mem C.omega x) (h : Labeling M C m f) : Graph M f m D := by
  refine ⟨?_,?_,h.graph.unique⟩
  · intro p hp
    obtain ⟨i,hi,x,hx,hCode⟩ := h.graph.support p hp
    exact ⟨i,hi,x,(hD x).mpr ⟨hx,h.above i hi x hx ⟨p,hp,hCode⟩⟩,hCode⟩
  · intro i hi
    obtain ⟨x,hx,hAt⟩ := h.graph.total i hi
    exact ⟨x,(hD x).mpr ⟨hx,h.above i hi x hx hAt⟩,hAt⟩

theorem labeling_domain_iff {M : SetTheory.Structure.{u}} (he : Extensional M) {C : Data M.Domain} {D m f : M.Domain}
    (hD : ∀ x, M.mem x D ↔ M.mem x C.cap ∧ M.mem C.omega x) :
    Labeling M C m f ↔ M.mem m C.omega ∧ Graph M f m D ∧
      ∀ i, M.mem i m → ∀ j, M.mem j m → M.mem i j → ∀ x, M.mem x D → ∀ y, M.mem y D →
        MemPair M f i x → MemPair M f j y → M.mem x y := by
  constructor
  · intro h
    exact ⟨h.length,h.graph_domain hD,fun i hi j hj hij x hx y hy hix hjy =>
      h.increasing i hi j hj hij x ((hD x).mp hx).1 y ((hD y).mp hy).1 hix hjy⟩
  · rintro ⟨hm,hGraph,hInc⟩
    refine ⟨hm,hGraph.mono_values (fun x hx => ((hD x).mp hx).1),?_,?_⟩
    · intro i _ x _ hAt
      exact ((hD x).mp (hGraph.bounds he hAt).2).2
    · intro i hi j hj hij x _ y _ hix hjy
      exact hInc i hi j hj hij x (hGraph.bounds he hix).2 y (hGraph.bounds he hjy).2 hix hjy

theorem label_domain_paper_iff {M : SetTheory.Structure.{u}} (he : Extensional M) {C : Data M.Domain} {D κ : M.Domain}
    (hs : M.SuccessorOf C.cap κ) (hD : ∀ x, M.mem x D ↔ M.mem x C.cap ∧ M.mem C.omega x) (x : M.Domain) :
    M.mem x D ↔ M.mem C.omega x ∧ (x=κ ∨ M.mem x κ) :=
  (hD x).trans ⟨fun h => ⟨h.2,(cap_member_iff he hs x).mp h.1⟩,fun h => ⟨(cap_member_iff he hs x).mpr h.2,h.1⟩⟩

end KP1Y.Reflection
