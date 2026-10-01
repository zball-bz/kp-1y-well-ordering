import KP1Y.SetFormulaMeaning

/-! 在任意合法前缀后追加实际等号／隶属原子，供一般定义公式组合使用。 -/
namespace KP1Y.SetLanguage
open YesMetaZFC YesMetaZFC.SetTheory
open KP1Y.Kuratowski KP1Y.Functions KP1Y.Satisfaction
universe u

theorem compile_relation_extension_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : Context M.Domain} {D : RelationalData M.Domain} {zero one two H Raw Sat Def r bound i j p n : M.Domain}
    (h : DefStage M C D zero one two H Raw Sat Def) (hP : WellFormedProgram M C D p n bound)
    (hr : M.mem r D.symbols) (hi : M.mem i bound) (hj : M.mem j bound) :
    ∃ q length, CompiledExtension M C D p n bound q length n ∧
      ∀ s x y, Graph M s bound C.carrier → MemPair M s i x → MemPair M s j y →
        (NodeTrue M C H q n s ↔ (r=zero ∧ x=y) ∨ (r=one ∧ M.mem x y)) := by
  have hbD : M.mem bound D.omega := h.link.omega_eq ▸ hP.bound_nat
  obtain ⟨a,vars,hScope,hCode,hVars,hV0,hV1⟩ := binary_atom_code_exists_d hM h.interpretation hr hbD hi hj
  have ha := hScope.code_mem h.interpretation.spaces
  obtain ⟨q,length,hQ,hTruth⟩ := compile_atom_d hM h.spaces h.evaluation hP ha (h.link.codes_bound a ha) hScope
  refine ⟨q,length,hQ,?_⟩
  intro s x y hS hS0 hS1
  have hs := (h.spaces.assignments s).mpr ⟨bound,hP.bound_nat,hS⟩
  have hSD : Graph M s bound D.carrier := h.link.carrier_eq ▸ hS
  exact (hTruth s hs).trans (binary_code_meaning hM h.interpretation h.atomic hr hbD hCode hVars hV0 hV1 hSD hS0 hS1)

theorem compile_equality_extension_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : Context M.Domain} {D : RelationalData M.Domain} {zero one two H Raw Sat Def bound i j p n : M.Domain}
    (h : DefStage M C D zero one two H Raw Sat Def) (hP : WellFormedProgram M C D p n bound)
    (hi : M.mem i bound) (hj : M.mem j bound) :
    ∃ q length, CompiledExtension M C D p n bound q length n ∧
      ∀ s x y, Graph M s bound C.carrier → MemPair M s i x → MemPair M s j y → (NodeTrue M C H q n s ↔ x=y) := by
  obtain ⟨q,length,hQ,hTruth⟩ := compile_relation_extension_d hM h hP
    ((h.interpretation.symbols zero).mpr (Or.inl rfl)) hi hj
  refine ⟨q,length,hQ,?_⟩
  intro s x y hS hS0 hS1
  simpa only [h.naturals.zero_ne_one hM,false_and,or_false,eq_self_iff_true,true_and] using hTruth s x y hS hS0 hS1

theorem compile_membership_extension_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : Context M.Domain} {D : RelationalData M.Domain} {zero one two H Raw Sat Def bound i j p n : M.Domain}
    (h : DefStage M C D zero one two H Raw Sat Def) (hP : WellFormedProgram M C D p n bound)
    (hi : M.mem i bound) (hj : M.mem j bound) :
    ∃ q length, CompiledExtension M C D p n bound q length n ∧
      ∀ s x y, Graph M s bound C.carrier → MemPair M s i x → MemPair M s j y → (NodeTrue M C H q n s ↔ M.mem x y) := by
  obtain ⟨q,length,hQ,hTruth⟩ := compile_relation_extension_d hM h hP
    ((h.interpretation.symbols one).mpr (Or.inr rfl)) hi hj
  refine ⟨q,length,hQ,?_⟩
  intro s x y hS hS0 hS1
  simpa only [(h.naturals.zero_ne_one hM).symm,false_and,false_or,eq_self_iff_true,true_and] using hTruth s x y hS hS0 hS1

end KP1Y.SetLanguage
