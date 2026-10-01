import KP1Y.ReflectionSemantics

/-! 第6引理(7)的归纳前向步骤：较早顶端查询可替换后，κ处反射给出δ处反射。 -/
namespace KP1Y.Reflection
open YesMetaZFC YesMetaZFC.SetTheory YesMetaZFC.SetTheory.Definitional
open KP1Y.Kuratowski KP1Y.Functions
universe u

def TopAgreementBefore (M : SetTheory.Structure.{u}) (C : Data M.Domain) (H κ δ K θ : M.Domain) : Prop :=
  ∀ k, M.mem k C.omega → ∀ η, M.mem η C.cap → ∀ x, M.mem x C.cap →
    (M.mem k K ∨ k=K ∧ M.mem η θ) → (η=x ∨ M.mem η x) → M.mem x δ →
      (Query M C.toIndexData H k η x κ ↔ Query M C.toIndexData H k η x δ)

theorem end_top_height_agree {M : SetTheory.Structure.{u}} (he : Extensional M) {C : Data M.Domain}
    {H κ δ K θ m N f c : M.Domain} (hIH : TopAgreementBefore M C H κ δ K θ)
    (hGraph : Graph M f m C.cap) (hBelow : Below M C m f δ) (hAdm : Admissible M C K θ N f c) :
    End M C H N f κ ↔ End M C H N f δ := by
  have hEarlier (k q p η : M.Domain) (hk : M.mem k C.omega) (hq : M.mem q C.omega) (hp : M.mem p C.omega)
      (hNeed : NeedAt M C N k q p) (hη : M.mem η C.cap) (hFq : MemPair M f q η) : M.mem k K ∨ k=K ∧ M.mem η θ := by
    rcases hAdm k hk q hq p hp hNeed η hη hFq with hkK | ⟨he,_,hηθ⟩
    · exact Or.inl hkK
    · exact Or.inr ⟨he,hηθ⟩
  constructor
  · intro hEnd k hk q hq p hp hNeed η hη x hx hFq hFp
    have hQ := hEnd k hk q hq p hp hNeed η hη x hx hFq hFp
    exact (hIH k hk η hη x hx (hEarlier k q p η hk hq hp hNeed hη hFq) hQ.1.2.2.2.2.1 (hBelow.at he hGraph hFp)).mp hQ
  · intro hEnd k hk q hq p hp hNeed η hη x hx hFq hFp
    have hQ := hEnd k hk q hq p hp hNeed η hη x hx hFq hFp
    exact (hIH k hk η hη x hx (hEarlier k q p η hk hq hp hNeed hη hFq) hQ.1.2.2.2.2.1 (hBelow.at he hGraph hFp)).mpr hQ

theorem top_to_height_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory) {C : Data M.Domain} (hC : C.Valid M)
    {H κ δ K θ a : M.Domain} (hTable : Table M C H) (hδκ : M.mem δ κ) (haδ : M.mem a δ)
    (hIH : TopAgreementBefore M C H κ δ K θ) (hTop : Query M C.toIndexData H K θ a κ) :
    Query M C.toIndexData H K θ a δ := by
  obtain ⟨hValid,hFR⟩ := (hTable.equation_d hM hC K θ a κ).mp hTop
  have hκ := hC.cap.mem hValid.2.2.2.1
  have hδCap := hC.cap.transitive κ hValid.2.2.2.1 δ hδκ
  apply (hTable.equation_d hM hC K θ a δ).mpr
  refine ⟨⟨hValid.1,hValid.2.1,hValid.2.2.1,hδCap,hValid.2.2.2.2.1,haδ,hValid.2.2.2.2.2.2⟩,?_⟩
  intro m hm A hA N hN c hc f hf hDemand
  have hEndκ := (end_top_height_agree hM.1 hIH hDemand.representation.labeling.graph hDemand.below hDemand.admissible).mpr hDemand.endpoint
  exact hFR m hm A hA N hN c hc f hf ⟨hDemand.template,hDemand.representation,hDemand.cut,
    hDemand.below.trans hκ hδκ,hDemand.admissible,hEndκ⟩

theorem Table.counterexample_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory) {C : Data M.Domain} (hC : C.Valid M)
    {H K θ a b : M.Domain} (hTable : Table M C H) (hValid : ValidQuery M C.toIndexData K θ a b)
    (hNot : ¬Query M C.toIndexData H K θ a b) :
    ∃ m, M.mem m C.omega ∧ ∃ A, M.mem A C.edgeLists ∧ ∃ N, M.mem N C.needLists ∧
      ∃ c, M.mem c m ∧ ∃ f, M.mem f C.labels ∧ Demand M C H K θ a b m A N c f ∧
        ∀ g, M.mem g C.labels → ¬Response M C H a m A N c f g := by
  classical
  apply Classical.byContradiction
  intro hNone
  apply hNot
  apply (hTable.equation_d hM hC K θ a b).mpr
  refine ⟨hValid,?_⟩
  intro m hm A hA N hN c hc f hf hDemand
  apply Classical.byContradiction
  intro hNoResponse
  exact hNone ⟨m,hm,A,hA,N,hN,c,hc,f,hf,hDemand,fun g hg hResponse => hNoResponse ⟨g,hg,hResponse⟩⟩

end KP1Y.Reflection
