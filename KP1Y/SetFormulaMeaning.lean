import KP1Y.SetDefStage
import KP1Y.SetAtomicMeaning
import KP1Y.CompileConnectives

/-! 实际编译纯集合语言原子，证明整个程序在所有界内赋值上的语义。 -/
namespace KP1Y.SetLanguage
open YesMetaZFC YesMetaZFC.SetTheory
open KP1Y.Kuratowski KP1Y.Functions KP1Y.Naturals KP1Y.Satisfaction
universe u

theorem DefStage.naturals {M : SetTheory.Structure.{u}} {C : Context M.Domain} {D : RelationalData M.Domain}
    {zero one two H Raw Sat Def : M.Domain} (h : DefStage M C D zero one two H Raw Sat Def) :
    SmallNaturals M C.omega zero one two := h.link.omega_eq.symm ▸ h.interpretation.naturals

theorem binary_relation_program_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : Context M.Domain} {D : RelationalData M.Domain} {zero one two H Raw Sat Def r bound i j : M.Domain}
    (h : DefStage M C D zero one two H Raw Sat Def) (hr : M.mem r D.symbols) (hb : M.mem bound D.omega)
    (hi : M.mem i bound) (hj : M.mem j bound) :
    ∃ p length, FormulaResult M C D p length zero bound ∧
      ∀ s x y, Graph M s bound C.carrier → MemPair M s i x → MemPair M s j y →
        (NodeTrue M C H p zero s ↔ (r=zero ∧ x=y) ∨ (r=one ∧ M.mem x y)) := by
  obtain ⟨a,vars,hScope,hCode,hVars,hV0,hV1⟩ := binary_atom_code_exists_d hM h.interpretation hr hb hi hj
  have hbC : M.mem bound C.omega := h.link.omega_eq.symm ▸ hb
  have hEmpty : WellFormedProgram M C D zero zero bound :=
    ⟨empty_graph h.naturals.zero_empty,h.naturals.zero_nat,hbC,fun k hk => False.elim (h.naturals.zero_empty k hk)⟩
  have ha := hScope.code_mem h.interpretation.spaces
  obtain ⟨p,length,hP,hTruth⟩ := compile_atom_d hM h.spaces h.evaluation hEmpty ha (h.link.codes_bound a ha) hScope
  refine ⟨p,length,hP.result,?_⟩
  intro s x y hS hS0 hS1
  have hs := (h.spaces.assignments s).mpr ⟨bound,hbC,hS⟩
  have hSD : Graph M s bound D.carrier := h.link.carrier_eq ▸ hS
  exact (hTruth s hs).trans (binary_code_meaning hM h.interpretation h.atomic hr hb hCode hVars hV0 hV1 hSD hS0 hS1)

theorem membership_program_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : Context M.Domain} {D : RelationalData M.Domain} {zero one two H Raw Sat Def : M.Domain}
    (h : DefStage M C D zero one two H Raw Sat Def) :
    ∃ p length, FormulaResult M C D p length zero two ∧
      ∀ s x y, Graph M s two C.carrier → MemPair M s zero x → MemPair M s one y →
        (NodeTrue M C H p zero s ↔ M.mem x y) := by
  obtain ⟨p,length,hP,hTruth⟩ := binary_relation_program_d hM h
    ((h.interpretation.symbols one).mpr (Or.inr rfl)) h.interpretation.naturals.two_nat
    h.naturals.zero_mem_two h.naturals.two_succ.predecessor_mem
  refine ⟨p,length,hP,?_⟩
  intro s x y hS hS0 hS1
  have hAt := hTruth s x y hS hS0 hS1
  simpa only [(h.naturals.zero_ne_one hM).symm, false_and, false_or, eq_self_iff_true, true_and] using hAt

theorem self_equality_program_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : Context M.Domain} {D : RelationalData M.Domain} {zero one two H Raw Sat Def : M.Domain}
    (h : DefStage M C D zero one two H Raw Sat Def) :
    ∃ p length, FormulaResult M C D p length zero two ∧
      ∀ s, Graph M s two C.carrier → NodeTrue M C H p zero s := by
  obtain ⟨p,length,hP,hTruth⟩ := binary_relation_program_d hM h
    ((h.interpretation.symbols zero).mpr (Or.inl rfl)) h.interpretation.naturals.two_nat
    h.naturals.zero_mem_two h.naturals.zero_mem_two
  refine ⟨p,length,hP,?_⟩
  intro s hS
  obtain ⟨x,_,hS0⟩ := hS.total zero h.naturals.zero_mem_two
  exact (hTruth s x x hS hS0 hS0).mpr (Or.inl ⟨rfl,rfl⟩)

end KP1Y.SetLanguage
