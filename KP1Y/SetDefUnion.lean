import KP1Y.SetUnionProgram

/-! 传递载域中参数a的实际并集属于Def后继。 -/
namespace KP1Y.SetLanguage
open YesMetaZFC YesMetaZFC.SetTheory
open KP1Y.Kuratowski KP1Y.Functions KP1Y.Sequences KP1Y.Assignments KP1Y.Satisfaction KP1Y.Definability
universe u

theorem DefStage.union_exists_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : Context M.Domain} {D : RelationalData M.Domain} {zero one two H Raw Sat Def a : M.Domain}
    (h : DefStage M C D zero one two H Raw Sat Def) (hTrans : M.TransitiveSet C.carrier) (ha : M.mem a C.carrier) :
    ∃ U, M.mem U Def ∧ M.IsUnionOf U a := by
  obtain ⟨three,hThree,hThreeNat⟩ := h.naturals.three_exists h.spaces.omega
  have h0 := (hThree zero).mpr (Or.inl h.naturals.zero_mem_two)
  have h1 := (hThree one).mpr (Or.inl h.naturals.two_succ.predecessor_mem)
  obtain ⟨s,hS,_,hS1,_⟩ := triple_tuple_exists_d hM h.naturals hThree ha ha ha
  obtain ⟨p,length,head,hP,hTruth⟩ := union_program_d hM h hThree hThreeNat
  have hMeaning (x : M.Domain) (hx : M.mem x C.carrier) (t : M.Domain)
      (hU : Updated M t s three C.carrier zero x) :
      NodeTrue M C H p head t ↔ ∃ y, M.mem y C.carrier ∧ M.mem x y ∧ M.mem y a := by
    have ht0 := (hU.rows zero h0 x hx).mpr (Or.inl ⟨rfl,rfl⟩)
    have ht1 := (hU.rows one h1 a ha).mpr (Or.inr ⟨(h.naturals.zero_ne_one hM).symm,hS1⟩)
    exact hTruth t x a hU.graph ht0 ht1
  obtain ⟨U,hUDef,hMembers⟩ := def_set_covers_program_d hM h.spaces h.raw h.typed h.subsets hP hS h0
  refine ⟨U,hUDef,?_⟩
  intro x
  constructor
  · intro hx
    obtain ⟨hxC,t,hUpdate,hTrue⟩ := (hMembers x).mp hx
    obtain ⟨y,_,hxy,hya⟩ := (hMeaning x hxC t hUpdate).mp hTrue
    exact ⟨y,hya,hxy⟩
  · rintro ⟨y,hya,hxy⟩
    have hyC := hTrans a ha y hya
    have hxC := hTrans y hyC x hxy
    obtain ⟨t,hUpdate⟩ := update_exists_d hM hS hxC
    exact (hMembers x).mpr ⟨hxC,t,hUpdate,(hMeaning x hxC t hUpdate).mpr ⟨y,hyC,hxy,hya⟩⟩

end KP1Y.SetLanguage
