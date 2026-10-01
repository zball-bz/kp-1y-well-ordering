import KP1Y.SetLanguageInterpretation
import KP1Y.ScopedAtoms

/-! 等号、隶属的实际原子代码；变量替换后的真值等于对象模型中的关系。 -/
namespace KP1Y.SetLanguage
open YesMetaZFC YesMetaZFC.SetTheory
open KP1Y.Kuratowski KP1Y.Functions KP1Y.Naturals KP1Y.Sequences KP1Y.Assignments KP1Y.Satisfaction
universe u

theorem binary_atom_code_exists_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {D : RelationalData M.Domain} {zero one two r bound i j : M.Domain}
    (hI : Interpretation M D zero one two) (hr : M.mem r D.symbols) (hb : M.mem bound D.omega)
    (hi : M.mem i bound) (hj : M.mem j bound) :
    ∃ a vars, ScopedAtom M D a bound ∧ Codes M a r vars ∧ Graph M vars two bound ∧
      MemPair M vars zero i ∧ MemPair M vars one j := by
  obtain ⟨vars,hVars,h0,h1⟩ := binary_tuple_exists_d hM hI.naturals hi hj
  have hVariables := (hI.spaces.variables vars).mpr
    ⟨two,hI.naturals.two_nat,hVars.mono_values ((omega_isOrdinal_d hM hI.spaces.omega).transitive bound hb)⟩
  have hArity := (hI.arity_rows r two).mpr ⟨hr,rfl⟩
  obtain ⟨a,hCode⟩ := codes_total hM r vars
  exact ⟨a,vars,⟨r,hr,vars,hVariables,hCode,two,hI.naturals.two_nat,hArity,hVars⟩,hCode,hVars,h0,h1⟩

theorem binary_code_meaning {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {D : RelationalData M.Domain} {zero one two Atom r a vars bound i j s x y : M.Domain}
    (hI : Interpretation M D zero one two) (hAtom : AtomicTable M D Atom)
    (hr : M.mem r D.symbols) (hb : M.mem bound D.omega) (hCode : Codes M a r vars)
    (hVars : Graph M vars two bound) (hV0 : MemPair M vars zero i) (hV1 : MemPair M vars one j)
    (hS : Graph M s bound D.carrier) (hS0 : MemPair M s i x) (hS1 : MemPair M s j y) :
    MemPair M Atom a s ↔ (r=zero ∧ x=y) ∨ (r=one ∧ M.mem x y) := by
  obtain ⟨t,hValue⟩ := tuple_value_exists_d hM hVars hS
  have h0 : MemPair M t zero x :=
    (hValue.rows zero hI.naturals.zero_mem_two i (hVars.bounds hM.1 hV0).2
      x (hS.bounds hM.1 hS0).2 hV0).mpr hS0
  have h1 : MemPair M t one y :=
    (hValue.rows one hI.naturals.two_succ.predecessor_mem j (hVars.bounds hM.1 hV1).2
      y (hS.bounds hM.1 hS1).2 hV1).mpr hS1
  have hTable := atomic_table_correct hM hI.spaces hAtom hr hCode hI.naturals.two_nat hb
    ((hI.arity_rows r two).mpr ⟨hr,rfl⟩) hValue
  have hRel : MemPair M D.interpretation r t ↔ SetAtom M D.carrier zero one two r t := by
    rw [hI.relation_rows r t]
    exact ⟨fun h => h.2.2,fun h => ⟨hr,(hI.spaces.values t).mpr ⟨two,hI.naturals.two_nat,hValue.values⟩,h⟩⟩
  exact hTable.trans (hRel.trans (set_atom_iff hM.1 hValue.values h0 h1))

theorem membership_code_meaning {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {D : RelationalData M.Domain} {zero one two Atom a vars bound i j s x y : M.Domain}
    (hI : Interpretation M D zero one two) (hAtom : AtomicTable M D Atom)
    (hb : M.mem bound D.omega) (hCode : Codes M a one vars)
    (hVars : Graph M vars two bound) (hV0 : MemPair M vars zero i) (hV1 : MemPair M vars one j)
    (hS : Graph M s bound D.carrier) (hS0 : MemPair M s i x) (hS1 : MemPair M s j y) :
    MemPair M Atom a s ↔ M.mem x y := by
  rw [binary_code_meaning hM hI hAtom ((hI.symbols one).mpr (Or.inr rfl)) hb hCode hVars hV0 hV1 hS hS0 hS1]
  simp only [(hI.naturals.zero_ne_one hM).symm, false_and, false_or, true_and]

theorem equality_code_meaning {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {D : RelationalData M.Domain} {zero one two Atom a vars bound i j s x y : M.Domain}
    (hI : Interpretation M D zero one two) (hAtom : AtomicTable M D Atom)
    (hb : M.mem bound D.omega) (hCode : Codes M a zero vars)
    (hVars : Graph M vars two bound) (hV0 : MemPair M vars zero i) (hV1 : MemPair M vars one j)
    (hS : Graph M s bound D.carrier) (hS0 : MemPair M s i x) (hS1 : MemPair M s j y) :
    MemPair M Atom a s ↔ x=y := by
  rw [binary_code_meaning hM hI hAtom ((hI.symbols zero).mpr (Or.inl rfl)) hb hCode hVars hV0 hV1 hS hS0 hS1]
  simp only [hI.naturals.zero_ne_one hM, false_and, or_false, true_and]

end KP1Y.SetLanguage
