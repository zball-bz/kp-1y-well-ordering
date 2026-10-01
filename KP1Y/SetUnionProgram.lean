import KP1Y.SetRelationExtensions
import KP1Y.CompileDerived
import KP1Y.ThreeTuples

/-! 实际编译并集谓词∃y(x∈y∧y∈a)，量化第三变量且保留输出和参数变量。 -/
namespace KP1Y.SetLanguage
open YesMetaZFC YesMetaZFC.SetTheory
open KP1Y.Kuratowski KP1Y.Functions KP1Y.Assignments KP1Y.Satisfaction
universe u

theorem union_program_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : Context M.Domain} {D : RelationalData M.Domain} {zero one two three H Raw Sat Def : M.Domain}
    (h : DefStage M C D zero one two H Raw Sat Def) (hThree : M.SuccessorOf three two) (hThreeNat : M.mem three C.omega) :
    ∃ p length head, FormulaResult M C D p length head three ∧
      ∀ s x a, Graph M s three C.carrier → MemPair M s zero x → MemPair M s one a →
        (NodeTrue M C H p head s ↔ ∃ y, M.mem y C.carrier ∧ M.mem x y ∧ M.mem y a) := by
  have h0 := (hThree zero).mpr (Or.inl h.naturals.zero_mem_two)
  have h1 := (hThree one).mpr (Or.inl h.naturals.two_succ.predecessor_mem)
  have h2 := hThree.predecessor_mem
  have hEmpty : WellFormedProgram M C D zero zero three :=
    ⟨empty_graph h.naturals.zero_empty,h.naturals.zero_nat,hThreeNat,fun i hi => False.elim (h.naturals.zero_empty i hi)⟩
  obtain ⟨p1,n1,hP1,truth1⟩ := compile_membership_extension_d hM h hEmpty h0 h2
  obtain ⟨p2,n2,hP2,truth2⟩ := compile_membership_extension_d hM h hP1.wellFormed h2 h1
  obtain ⟨p3,n3,j3,hP3,truth3⟩ := compile_conjunction_d hM h.spaces h.evaluation hP2.wellFormed
    ((hP2.successor zero).mpr (Or.inl hP1.successor.predecessor_mem)) hP2.successor.predecessor_mem
  have hConj (t x y a : M.Domain) (hT : Graph M t three C.carrier)
      (ht0 : MemPair M t zero x) (ht1 : MemPair M t one a) (ht2 : MemPair M t two y) :
      NodeTrue M C H p3 j3 t ↔ M.mem x y ∧ M.mem y a := by
    have ht := (h.spaces.assignments t).mpr ⟨three,hThreeNat,hT⟩
    have hOld := (hP2.old_node hM h.spaces h.evaluation hP1.wellFormed.length_nat hP1.successor.predecessor_mem ht).symm
    exact (truth3 t ht).trans (and_congr (hOld.trans (truth1 t x y hT ht0 ht2)) (truth2 t y a hT ht2 ht1))
  obtain ⟨p,length,head,hP,truth⟩ := compile_existential_d hM h.spaces h.evaluation hP3.wellFormed hP3.successor.predecessor_mem h2
  refine ⟨p,length,head,hP.result,?_⟩
  intro s x a hS hs0 hs1
  have hx := (hS.bounds hM.1 hs0).2
  have ha := (hS.bounds hM.1 hs1).2
  have hUpdated (y : M.Domain) (hy : M.mem y C.carrier) (t : M.Domain)
      (hU : Updated M t s three C.carrier two y) : NodeTrue M C H p3 j3 t ↔ M.mem x y ∧ M.mem y a := by
    have ht0 := (hU.rows zero h0 x hx).mpr (Or.inr ⟨h.naturals.zero_ne_two hM,hs0⟩)
    have ht1 := (hU.rows one h1 a ha).mpr (Or.inr ⟨h.naturals.one_ne_two hM,hs1⟩)
    have ht2 := (hU.rows two h2 y hy).mpr (Or.inl ⟨rfl,rfl⟩)
    exact hConj t x y a hU.graph ht0 ht1 ht2
  apply (truth s hS).trans
  constructor
  · rintro ⟨y,hy,t,hU,hTrue⟩
    exact ⟨y,hy,(hUpdated y hy t hU).mp hTrue⟩
  · rintro ⟨y,hy,hxy,hya⟩
    obtain ⟨t,hU⟩ := update_exists_d hM (i := two) hS hy
    exact ⟨y,hy,t,hU,(hUpdated y hy t hU).mpr ⟨hxy,hya⟩⟩

end KP1Y.SetLanguage
