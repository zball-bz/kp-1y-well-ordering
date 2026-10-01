import KP1Y.SetFormulaMeaning

/-! 纯集合语言 Def 后继的包含性与传递性，含空载域分支。 -/
namespace KP1Y.SetLanguage
open YesMetaZFC YesMetaZFC.SetTheory
open KP1Y.Kuratowski KP1Y.Functions KP1Y.Sequences KP1Y.Assignments KP1Y.Satisfaction KP1Y.Definability
universe u

theorem DefStage.carrier_member_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : Context M.Domain} {D : RelationalData M.Domain} {zero one two H Raw Sat Def : M.Domain}
    (h : DefStage M C D zero one two H Raw Sat Def) : M.mem C.carrier Def := by
  classical
  by_cases hNonempty : ∃ a, M.mem a C.carrier
  · obtain ⟨a,ha⟩ := hNonempty
    obtain ⟨s,hS,_,_⟩ := binary_tuple_exists_d hM h.naturals ha ha
    obtain ⟨p,length,hP,hTrue⟩ := self_equality_program_d hM h
    obtain ⟨S,hSDef,hMembers⟩ := def_set_covers_program_d hM h.spaces h.raw h.typed h.subsets hP hS h.naturals.zero_mem_two
    have hEq : S=C.carrier := by
      apply hM.1.eq_of_same_members
      intro x
      constructor
      · intro hx
        exact ((hMembers x).mp hx).1
      · intro hx
        obtain ⟨t,hUpdate⟩ := update_exists_d hM hS hx
        exact (hMembers x).mpr ⟨hx,t,hUpdate,hTrue t hUpdate.graph⟩
    exact hEq ▸ hSDef
  · exact empty_member_def_set_d hM h.spaces h.subsets (fun x hx => hNonempty ⟨x,hx⟩)

theorem DefStage.element_member_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : Context M.Domain} {D : RelationalData M.Domain} {zero one two H Raw Sat Def a : M.Domain}
    (h : DefStage M C D zero one two H Raw Sat Def) (hTrans : M.TransitiveSet C.carrier)
    (ha : M.mem a C.carrier) : M.mem a Def := by
  obtain ⟨s,hS,_,hS1⟩ := binary_tuple_exists_d hM h.naturals ha ha
  obtain ⟨p,length,hP,hTruth⟩ := membership_program_d hM h
  have hMeaning (x : M.Domain) (hx : M.mem x C.carrier) (t : M.Domain)
      (hU : Updated M t s two C.carrier zero x) : NodeTrue M C H p zero t ↔ M.mem x a := by
    have h0 : MemPair M t zero x := (hU.rows zero h.naturals.zero_mem_two x hx).mpr (Or.inl ⟨rfl,rfl⟩)
    have h1 : MemPair M t one a := (hU.rows one h.naturals.two_succ.predecessor_mem a ha).mpr
      (Or.inr ⟨(h.naturals.zero_ne_one hM).symm,hS1⟩)
    exact hTruth t x a hU.graph h0 h1
  obtain ⟨S,hSDef,hMembers⟩ := def_set_covers_program_d hM h.spaces h.raw h.typed h.subsets hP hS h.naturals.zero_mem_two
  have hEq : S=a := by
    apply hM.1.eq_of_same_members
    intro x
    constructor
    · intro hx
      obtain ⟨hxA,t,hUpdate,hTrue⟩ := (hMembers x).mp hx
      exact (hMeaning x hxA t hUpdate).mp hTrue
    · intro hx
      have hxA := hTrans a ha x hx
      obtain ⟨t,hUpdate⟩ := update_exists_d hM hS hxA
      exact (hMembers x).mpr ⟨hxA,t,hUpdate,(hMeaning x hxA t hUpdate).mpr hx⟩
  exact hEq ▸ hSDef

theorem DefStage.carrier_subset_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : Context M.Domain} {D : RelationalData M.Domain} {zero one two H Raw Sat Def : M.Domain}
    (h : DefStage M C D zero one two H Raw Sat Def) (hTrans : M.TransitiveSet C.carrier) :
    M.MemberSubset C.carrier Def := fun _ ha => h.element_member_d hM hTrans ha

theorem DefStage.transitive_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : Context M.Domain} {D : RelationalData M.Domain} {zero one two H Raw Sat Def : M.Domain}
    (h : DefStage M C D zero one two H Raw Sat Def) (hTrans : M.TransitiveSet C.carrier) : M.TransitiveSet Def := by
  intro S hS x hx
  exact h.carrier_subset_d hM hTrans x (h.subsets.member_subset hS x hx)

theorem transitive_set_def_stage_exists_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {ω A : M.Domain} (hω : M.IsOmega ω) (hTrans : M.TransitiveSet A) :
    ∃ C D zero one two H Raw Sat Def, C.omega=ω ∧ C.carrier=A ∧
      DefStage M C D zero one two H Raw Sat Def ∧ M.mem A Def ∧ M.MemberSubset A Def ∧ M.TransitiveSet Def := by
  obtain ⟨C,D,zero,one,two,H,Raw,Sat,Def,hOmega,hCarrier,h⟩ := set_def_stage_exists_d hM hω A
  have hTransC : M.TransitiveSet C.carrier := hCarrier.symm ▸ hTrans
  exact ⟨C,D,zero,one,two,H,Raw,Sat,Def,hOmega,hCarrier,h,
    hCarrier ▸ h.carrier_member_d hM,hCarrier ▸ h.carrier_subset_d hM hTransC,h.transitive_d hM hTransC⟩

end KP1Y.SetLanguage
