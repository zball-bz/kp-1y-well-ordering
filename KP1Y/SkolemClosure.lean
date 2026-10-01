import KP1Y.SkolemFunction

/-! 对实际最小见证函数封闭，足以供应 Tarski–Vaught 所需的全部反例见证。 -/
namespace KP1Y.Satisfaction
open YesMetaZFC YesMetaZFC.SetTheory
open KP1Y.Kuratowski KP1Y.Functions KP1Y.Assignments
universe u

def SkolemClosed (M : SetTheory.Structure.{u}) (C : Context M.Domain) (K : SkolemBounds M.Domain) (F X : M.Domain) : Prop :=
  ∀ p, M.mem p C.programs → ∀ j, M.mem j C.omega → ∀ bound, M.mem bound C.omega →
    ∀ v, M.mem v C.omega → ∀ s, Graph M s bound X → ∀ key, KeyCode M K key p j s bound v →
      ∀ x, MemPair M F key x → M.mem x X

theorem skolem_closed_witnesses_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : Context M.Domain} (hC : ContextSpaces M C) {D : RelationalData M.Domain}
    {small large : EvaluationData M.Domain} (hLarge : large.Valid C)
    (hSub : M.MemberSubset small.carrier large.carrier) {K : SkolemBounds M.Domain}
    (hK : SkolemBoundsValid M C large K) {zero F : M.Domain}
    (hF : SkolemFunction M C large K zero F) (hClosed : SkolemClosed M C K F small.carrier) :
    CounterWitnessClosed M C D small large := by
  intro p length bound hP j hj s hS v hv hExists
  have hω := KP1Y.Naturals.omega_isOrdinal_d hM hC.omega
  have hp := (hC.programs p).mpr ⟨length,hP.length_nat,hP.graph⟩
  have hjω := hω.transitive length hP.length_nat j hj
  have hvω := hω.transitive bound hP.bound_nat v hv
  have hsLarge := (hLarge.assignments_exact s).mpr ⟨bound,hP.bound_nat,hS.mono_values hSub⟩
  obtain ⟨key,hkey,hCode⟩ := skolem_key_exists_d hM hK hp hjω hsLarge hP.bound_nat hvω
  obtain ⟨x,_,hFx⟩ := hF.graph.total key hkey
  have hxSmall := hClosed p hp j hjω bound hP.bound_nat v hvω s hS key hCode x hFx
  have hChosen := (hF.rows p hp j hjω s hsLarge bound hP.bound_nat v hvω key hCode x).mp hFx
  have hExists' : ∃ y, M.mem y large.carrier ∧ FalseWitness M C large p j s bound v y := by
    obtain ⟨y,hy,t,ht,hNot⟩ := hExists
    exact ⟨y,hy,t,(hLarge.assignments_exact t).mpr ⟨bound,hP.bound_nat,ht.graph⟩,ht,hNot⟩
  obtain ⟨t,_,ht,hNot⟩ := chosen_witness_is_real hChosen hExists'
  exact ⟨x,hxSmall,t,updated_restrict hM.1 hSub hS hxSmall ht,hNot⟩

theorem skolem_function_closed_elementary_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : Context M.Domain} (hC : ContextSpaces M C) {D : RelationalData M.Domain}
    {small large : EvaluationData M.Domain} (hSmall : small.Valid C) (hLarge : large.Valid C)
    (hSub : M.MemberSubset small.carrier large.carrier) (hAtomic : AtomicAgreement M C D small large)
    {K : SkolemBounds M.Domain} (hK : SkolemBoundsValid M C large K) {zero F : M.Domain}
    (hF : SkolemFunction M C large K zero F) (hClosed : SkolemClosed M C K F small.carrier) :
    ProgramElementary M C D small large :=
  skolem_closed_elementary_d hM hC hSmall hLarge hSub hAtomic
    (skolem_closed_witnesses_d hM hC hLarge hSub hK hF hClosed)

end KP1Y.Satisfaction
