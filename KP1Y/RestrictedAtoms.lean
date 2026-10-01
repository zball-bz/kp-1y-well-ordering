import KP1Y.SkolemClosure

/-! 将给定关系解释限制到任意较小载域，原子满意度在小域赋值上保持。 -/
namespace KP1Y.Satisfaction
open YesMetaZFC YesMetaZFC.SetTheory YesMetaZFC.SetTheory.Definitional
open KP1Y.Kuratowski KP1Y.Functions KP1Y.Assignments
universe u

def RelationalData.withInterpretation {α : Type u} (D : RelationalData α) (A values interpretation : α) : RelationalData α :=
  { D with carrier := A, values := values, interpretation := interpretation }

theorem restricted_atomic_table_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {D : RelationalData M.Domain} (hD : DataSpaces M D) (X : M.Domain) :
    ∃ S R Atom, DataSpaces M (D.withInterpretation X S R) ∧ AtomicTable M (D.withInterpretation X S R) Atom ∧
      ∀ r t, MemPair M R r t ↔ M.mem r D.symbols ∧ M.mem t S ∧ MemPair M D.interpretation r t := by
  obtain ⟨S,hS⟩ := KP1Y.Sequences.finite_sequences_exist_d hM hD.omega X
  obtain ⟨R,_,hR⟩ := relation_comprehension_d hM KP1Y.Recursion.memberSchema (oneEnv D.interpretation) D.symbols S
  have hSmall : DataSpaces M (D.withInterpretation X S R) := ⟨hD.omega,hD.variables,hS,hD.codes⟩
  obtain ⟨Atom,hAtom⟩ := atomic_table_exists_d hM (D.withInterpretation X S R)
  refine ⟨S,R,Atom,hSmall,hAtom,?_⟩
  intro r t
  simpa only [KP1Y.Recursion.memberSchema_iff hM.1] using hR r t

theorem atomic_restriction_correct {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {D : RelationalData M.Domain} (hD : DataSpaces M D) {BigAtom X S R SmallAtom : M.Domain}
    (hBigAtom : AtomicTable M D BigAtom) (hSmall : DataSpaces M (D.withInterpretation X S R))
    (hSmallAtom : AtomicTable M (D.withInterpretation X S R) SmallAtom)
    (hR : ∀ r t, MemPair M R r t ↔ M.mem r D.symbols ∧ M.mem t S ∧ MemPair M D.interpretation r t)
    (hSub : M.MemberSubset X D.carrier) {a bound s : M.Domain}
    (hScope : ScopedAtom M D a bound) (hb : M.mem bound D.omega) (hS : Graph M s bound X) :
    MemPair M SmallAtom a s ↔ MemPair M BigAtom a s := by
  have hScopeSmall : ScopedAtom M (D.withInterpretation X S R) a bound := hScope
  obtain ⟨r,vars,n,t,hr,hCode,hn,hArity,hValue⟩ := scoped_atom_evaluable_d hM hScopeSmall hS
  have htS := (hSmall.values t).mpr ⟨n,hn,hValue.values⟩
  have hRestricted : MemPair M R r t ↔ MemPair M D.interpretation r t :=
    (hR r t).trans ⟨fun h => h.2.2,fun h => ⟨hr,htS,h⟩⟩
  exact (atomic_table_correct hM hSmall hSmallAtom hr hCode hn hb hArity hValue).trans
    (hRestricted.trans (atomic_table_correct hM hD hBigAtom hr hCode hn hb hArity (tuple_value_enlarge hM.1 hSub hValue)).symm)

theorem restricted_evaluation_exists_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : Context M.Domain} (hC : ContextSpaces M C) {D : RelationalData M.Domain} (hD : DataSpaces M D)
    {large : EvaluationData M.Domain} (hCarrier : large.carrier=D.carrier) (hBigAtom : AtomicTable M D large.atomic)
    (X : M.Domain) (hSub : M.MemberSubset X large.carrier) :
    ∃ small, small.carrier=X ∧ small.Valid C ∧ AtomicAgreement M C D small large := by
  obtain ⟨S,R,Atom,hSmallData,hSmallAtom,hR⟩ := restricted_atomic_table_d hM hD X
  have hωeq := KP1Y.Naturals.omega_unique hM.1 hC.omega hD.omega
  have hAssignments : ∀ s, M.mem s S ↔ ∃ n, M.mem n C.omega ∧ Graph M s n X := by
    intro s
    simpa only [RelationalData.withInterpretation,hωeq] using hSmallData.values s
  obtain ⟨B,hB⟩ := product_exists hM C.programs S
  obtain ⟨H,hH⟩ := evaluation_exists_d hM (C.withInterpretation X S B Atom) hC.omega
  let small : EvaluationData M.Domain := ⟨X,S,B,Atom,H⟩
  refine ⟨small,rfl,⟨hAssignments,hB,hH⟩,?_⟩
  intro a bound hScope hb s hS
  have hSubD : M.MemberSubset X D.carrier := hCarrier ▸ hSub
  have hbD : M.mem bound D.omega := hωeq ▸ hb
  exact atomic_restriction_correct hM hD hBigAtom hSmallData hSmallAtom hR hSubD hScope hbD hS

theorem closed_substructure_exists_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : Context M.Domain} (hC : ContextSpaces M C) {D : RelationalData M.Domain} (hD : DataSpaces M D)
    {large : EvaluationData M.Domain} (hLarge : large.Valid C) (hCarrier : large.carrier=D.carrier)
    (hBigAtom : AtomicTable M D large.atomic) {K : SkolemBounds M.Domain} (hK : SkolemBoundsValid M C large K)
    {zero F X : M.Domain} (hF : SkolemFunction M C large K zero F) (hSub : M.MemberSubset X large.carrier)
    (hClosed : SkolemClosed M C K F X) :
    ∃ small, small.carrier=X ∧ small.Valid C ∧ ProgramElementary M C D small large := by
  obtain ⟨small,hX,hSmall,hAtomic⟩ := restricted_evaluation_exists_d hM hC hD hCarrier hBigAtom X hSub
  have hSub' : M.MemberSubset small.carrier large.carrier := hX ▸ hSub
  have hClosed' : SkolemClosed M C K F small.carrier := hX ▸ hClosed
  exact ⟨small,hX,hSmall,skolem_function_closed_elementary_d hM hC hSmall hLarge hSub' hAtomic hK hF hClosed'⟩

end KP1Y.Satisfaction
