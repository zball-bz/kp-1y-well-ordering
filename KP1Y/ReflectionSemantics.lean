import KP1Y.ReflectionTable
import KP1Y.CountableFunctions
import KP1Y.SequenceCertificate

/-! 将代码定义与文稿的标签域、有效元组及有限原子集合接口对照。 -/
namespace KP1Y.Reflection
open YesMetaZFC YesMetaZFC.SetTheory YesMetaZFC.SetTheory.Definitional
open KP1Y.Kuratowski KP1Y.Functions KP1Y.Cardinal
universe u

theorem cap_member_iff {M : SetTheory.Structure.{u}} (he : Extensional M) {cap κ : M.Domain}
    (hs : M.SuccessorOf cap κ) (x : M.Domain) : M.mem x cap ↔ x=κ ∨ M.mem x κ := by
  constructor
  · intro hx
    rcases (hs x).mp hx with hx | hx
    · exact Or.inr hx
    · exact Or.inl (he.eq_of_same_members x κ hx)
  · rintro (hx | hx)
    · subst x
      exact hs.predecessor_mem
    · exact (hs x).mpr (Or.inl hx)

theorem valid_query_paper_iff {M : SetTheory.Structure.{u}} (he : Extensional M) {C : IndexData M.Domain}
    (hCap : M.IsOrdinal C.cap) {κ : M.Domain} (hs : M.SuccessorOf C.cap κ) (K θ a b : M.Domain) :
    ValidQuery M C K θ a b ↔
      M.mem K C.omega ∧ (θ=a ∨ M.mem θ a) ∧ M.mem a b ∧ (b=κ ∨ M.mem b κ) ∧ M.mem C.omega a := by
  constructor
  · intro h
    exact ⟨h.1,h.2.2.2.2.1,h.2.2.2.2.2.1,(cap_member_iff he hs b).mp h.2.2.2.1,h.2.2.2.2.2.2⟩
  · rintro ⟨hK,hθa,hab,hb,hωa⟩
    have hbCap := (cap_member_iff he hs b).mpr hb
    have haCap := hCap.transitive b hbCap a hab
    have hθCap : M.mem θ C.cap := by
      rcases hθa with he | hθa
      · exact he ▸ haCap
      · exact hCap.transitive a haCap θ hθa
    exact ⟨hK,hθCap,haCap,hbCap,hθa,hab,hωa⟩

theorem Labeling.paper_labels {M : SetTheory.Structure.{u}} (he : Extensional M) {C : Data M.Domain}
    {κ m f i x : M.Domain} (hs : M.SuccessorOf C.cap κ) (h : Labeling M C m f) (hAt : MemPair M f i x) :
    M.mem C.omega x ∧ (x=κ ∨ M.mem x κ) := by
  have hb := h.graph.bounds he hAt
  exact ⟨h.above i hb.1 x hb.2 hAt,(cap_member_iff he hs x).mp hb.2⟩

theorem finite_code_range_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory) {A n Codes : M.Domain}
    (hA : Graph M A n Codes) : ∃ S, M.MemberSubset S Codes ∧ Onto M A n S := by
  obtain ⟨S,hS⟩ := KP1Y.Sequences.range_bound_exists_d hM Codes A n
  have hRows := hS.exact hM.1 hA
  refine ⟨S,hS.1,?_,?_,?_,?_⟩
  · intro p hp
    obtain ⟨i,hi,x,_,hCode⟩ := hA.support p hp
    exact ⟨i,hi,x,(hRows x).mpr ⟨i,hi,p,hp,hCode⟩,hCode⟩
  · intro i hi
    obtain ⟨x,_,hAt⟩ := hA.total i hi
    exact ⟨x,(hRows x).mpr ⟨i,hi,hAt⟩,hAt⟩
  · intro i _ x _ y _ hix hiy
    exact hA.unique i x y hix hiy
  · intro x hx
    exact (hRows x).mp hx

theorem edge_list_from_enumerator_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory) {C : Data M.Domain} (hC : C.Valid M)
    {A n S : M.Domain} (hn : M.mem n C.omega) (hA : Onto M A n S) (hSub : M.MemberSubset S C.edgeCodes) :
    M.mem A C.edgeLists ∧ ∀ k q p j, EdgeAt M C A k q p j ↔ ∃ e, M.mem e S ∧ Quad M C.pairs e k q p j := by
  have hGraph := hA.toGraph hM.1
  refine ⟨(hC.edgeLists A).mpr ⟨n,hn,hGraph.mono_values hSub⟩,?_⟩
  intro k q p j
  constructor
  · rintro ⟨_,_,e,_,hAt,hQuad⟩
    exact ⟨e,(hGraph.bounds hM.1 hAt).2,hQuad⟩
  · rintro ⟨e,he,hQuad⟩
    obtain ⟨i,hi,hAt⟩ := hA.2.2.2 e he
    exact ⟨i,(KP1Y.Naturals.omega_isOrdinal_d hM hC.omega).transitive n hn i hi,e,hSub e he,hAt,hQuad⟩

theorem need_list_from_enumerator_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory) {C : Data M.Domain} (hC : C.Valid M)
    {N n S : M.Domain} (hn : M.mem n C.omega) (hN : Onto M N n S) (hSub : M.MemberSubset S C.needCodes) :
    M.mem N C.needLists ∧ ∀ k q p, NeedAt M C N k q p ↔ ∃ e, M.mem e S ∧ KP1Y.Ranking.Packet M e k q p := by
  have hGraph := hN.toGraph hM.1
  refine ⟨(hC.needLists N).mpr ⟨n,hn,hGraph.mono_values hSub⟩,?_⟩
  intro k q p
  constructor
  · rintro ⟨_,_,e,_,hAt,hPacket⟩
    exact ⟨e,(hGraph.bounds hM.1 hAt).2,hPacket⟩
  · rintro ⟨e,he,hPacket⟩
    obtain ⟨i,hi,hAt⟩ := hN.2.2.2 e he
    exact ⟨i,(KP1Y.Naturals.omega_isOrdinal_d hM hC.omega).transitive n hn i hi,e,hSub e he,hAt,hPacket⟩

theorem Table.paper_equation_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory) {C : Data M.Domain} (hC : C.Valid M)
    {H κ : M.Domain} (hs : M.SuccessorOf C.cap κ) (h : Table M C H) (K θ a b : M.Domain) :
    Query M C.toIndexData H K θ a b ↔
      (M.mem K C.omega ∧ (θ=a ∨ M.mem θ a) ∧ M.mem a b ∧ (b=κ ∨ M.mem b κ) ∧ M.mem C.omega a) ∧ Reflect M C H K θ a b :=
  (h.equation_d hM hC K θ a b).trans (and_congr (valid_query_paper_iff hM.1 hC.cap hs K θ a b) Iff.rfl)

end KP1Y.Reflection
