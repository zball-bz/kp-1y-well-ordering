import KP1Y.SetRelationExtensions
import KP1Y.CompileDisjunction
import KP1Y.ThreeTuples

/-! 实际编译x=a∨x=b，并证明相应无序对属于纯集合语言Def后继。 -/
namespace KP1Y.SetLanguage
open YesMetaZFC YesMetaZFC.SetTheory
open KP1Y.Kuratowski KP1Y.Functions KP1Y.Sequences KP1Y.Assignments KP1Y.Satisfaction KP1Y.Definability
universe u

theorem pairing_program_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : Context M.Domain} {D : RelationalData M.Domain} {zero one two three H Raw Sat Def : M.Domain}
    (h : DefStage M C D zero one two H Raw Sat Def) (hThree : M.SuccessorOf three two) (hThreeNat : M.mem three C.omega) :
    ∃ p length head, FormulaResult M C D p length head three ∧
      ∀ s x a b, Graph M s three C.carrier → MemPair M s zero x → MemPair M s one a → MemPair M s two b →
        (NodeTrue M C H p head s ↔ x=a ∨ x=b) := by
  have h0 := (hThree zero).mpr (Or.inl h.naturals.zero_mem_two)
  have h1 := (hThree one).mpr (Or.inl h.naturals.two_succ.predecessor_mem)
  have h2 := hThree.predecessor_mem
  have hEmpty : WellFormedProgram M C D zero zero three :=
    ⟨empty_graph h.naturals.zero_empty,h.naturals.zero_nat,hThreeNat,fun i hi => False.elim (h.naturals.zero_empty i hi)⟩
  obtain ⟨p1,n1,hP1,truth1⟩ := compile_equality_extension_d hM h hEmpty h0 h1
  obtain ⟨p2,n2,hP2,truth2⟩ := compile_equality_extension_d hM h hP1.wellFormed h0 h2
  obtain ⟨p,length,head,hP,truth⟩ := compile_disjunction_d hM h.spaces h.evaluation hP2.wellFormed
    ((hP2.successor zero).mpr (Or.inl hP1.successor.predecessor_mem)) hP2.successor.predecessor_mem
  refine ⟨p,length,head,hP.result,?_⟩
  intro s x a b hS hS0 hS1 hS2
  have hs := (h.spaces.assignments s).mpr ⟨three,hThreeNat,hS⟩
  have hOld := (hP2.old_node hM h.spaces h.evaluation hP1.wellFormed.length_nat hP1.successor.predecessor_mem hs).symm
  exact (truth s hs).trans (or_congr (hOld.trans (truth1 s x a hS hS0 hS1)) (truth2 s x b hS hS0 hS2))

theorem DefStage.pair_exists_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : Context M.Domain} {D : RelationalData M.Domain} {zero one two H Raw Sat Def a b : M.Domain}
    (h : DefStage M C D zero one two H Raw Sat Def) (ha : M.mem a C.carrier) (hb : M.mem b C.carrier) :
    ∃ S, M.mem S Def ∧ PairSet M S a b := by
  obtain ⟨three,hThree,hThreeNat⟩ := h.naturals.three_exists h.spaces.omega
  have h0 := (hThree zero).mpr (Or.inl h.naturals.zero_mem_two)
  have h1 := (hThree one).mpr (Or.inl h.naturals.two_succ.predecessor_mem)
  have h2 := hThree.predecessor_mem
  obtain ⟨s,hS,_,hS1,hS2⟩ := triple_tuple_exists_d hM h.naturals hThree ha ha hb
  obtain ⟨p,length,head,hP,hTruth⟩ := pairing_program_d hM h hThree hThreeNat
  have hMeaning (x : M.Domain) (hx : M.mem x C.carrier) (t : M.Domain)
      (hU : Updated M t s three C.carrier zero x) : NodeTrue M C H p head t ↔ x=a ∨ x=b := by
    have ht0 := (hU.rows zero h0 x hx).mpr (Or.inl ⟨rfl,rfl⟩)
    have ht1 := (hU.rows one h1 a ha).mpr (Or.inr ⟨(h.naturals.zero_ne_one hM).symm,hS1⟩)
    have ht2 := (hU.rows two h2 b hb).mpr (Or.inr ⟨(h.naturals.zero_ne_two hM).symm,hS2⟩)
    exact hTruth t x a b hU.graph ht0 ht1 ht2
  obtain ⟨S,hSDef,hMembers⟩ := def_set_covers_program_d hM h.spaces h.raw h.typed h.subsets hP hS h0
  refine ⟨S,hSDef,?_⟩
  intro x
  constructor
  · intro hx
    obtain ⟨hxC,t,hU,hTrue⟩ := (hMembers x).mp hx
    exact (hMeaning x hxC t hU).mp hTrue
  · intro hx
    have hxC : M.mem x C.carrier := by
      rcases hx with he | he
      · exact he ▸ ha
      · exact he ▸ hb
    obtain ⟨t,hU⟩ := update_exists_d hM hS hxC
    exact (hMembers x).mpr ⟨hxC,t,hU,(hMeaning x hxC t hU).mpr hx⟩

end KP1Y.SetLanguage
