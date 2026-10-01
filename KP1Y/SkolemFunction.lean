import KP1Y.SkolemFunctionSyntax

/-! 把所有最小见证选择装成一个实际集合函数图，不额外假设选择函数存在。 -/
namespace KP1Y.Satisfaction
open YesMetaZFC YesMetaZFC.SetTheory
open KP1Y.Kuratowski KP1Y.Functions
universe u

theorem skolem_key_exists_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : Context M.Domain} {I : EvaluationData M.Domain} {K : SkolemBounds M.Domain}
    (hK : SkolemBoundsValid M C I K) {p j s bound v : M.Domain}
    (hp : M.mem p C.programs) (hj : M.mem j C.omega) (hs : M.mem s I.assignments)
    (hb : M.mem bound C.omega) (hv : M.mem v C.omega) :
    ∃ key, M.mem key K.keys ∧ KeyCode M K key p j s bound v := by
  obtain ⟨pj,hPJ⟩ := codes_total hM p j
  have hpj := (hK.programNodes pj).mpr ⟨p,hp,j,hj,hPJ⟩
  obtain ⟨bv,hBV⟩ := codes_total hM bound v
  have hbv := (hK.variableSlots bv).mpr ⟨bound,hb,v,hv,hBV⟩
  obtain ⟨sbv,hSBV⟩ := codes_total hM s bv
  have hsbv := (hK.assignmentSlots sbv).mpr ⟨s,hs,bv,hbv,hSBV⟩
  obtain ⟨key,hKey⟩ := codes_total hM pj sbv
  exact ⟨key,(hK.keys key).mpr ⟨pj,hpj,sbv,hsbv,hKey⟩,pj,hpj,bv,hbv,sbv,hsbv,hKey,hPJ,hSBV,hBV⟩

structure SkolemFunction (M : SetTheory.Structure.{u}) (C : Context M.Domain) (I : EvaluationData M.Domain)
    (K : SkolemBounds M.Domain) (zero F : M.Domain) : Prop where
  graph : Graph M F K.keys I.carrier
  rows : ∀ p, M.mem p C.programs → ∀ j, M.mem j C.omega → ∀ s, M.mem s I.assignments →
    ∀ bound, M.mem bound C.omega → ∀ v, M.mem v C.omega → ∀ key, KeyCode M K key p j s bound v →
      ∀ x, MemPair M F key x ↔ ChosenWitness M C I zero p j s bound v x

theorem skolem_function_exists_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    (C : Context M.Domain) (I : EvaluationData M.Domain) {K : SkolemBounds M.Domain}
    (hK : SkolemBoundsValid M C I K) (hOrd : M.IsOrdinal I.carrier)
    {zero : M.Domain} (hZero : M.mem zero I.carrier) : ∃ F, SkolemFunction M C I K zero F := by
  obtain ⟨F,hSupport,hRows⟩ := relation_comprehension_d hM skolemRowSchema (skolemEnv C I K zero) K.keys I.carrier
  have hRaw (key x : M.Domain) : MemPair M F key x ↔
      M.mem key K.keys ∧ M.mem x I.carrier ∧ SkolemRow M C I K zero key x := by
    simpa only [skolemRowSchema_iff hM.1] using hRows key x
  have hSpec : ∀ p, M.mem p C.programs → ∀ j, M.mem j C.omega → ∀ s, M.mem s I.assignments →
      ∀ bound, M.mem bound C.omega → ∀ v, M.mem v C.omega → ∀ key, KeyCode M K key p j s bound v →
        ∀ x, MemPair M F key x ↔ ChosenWitness M C I zero p j s bound v x := by
    intro p hp j hj s hs bound hb v hv key hKey x
    constructor
    · intro hFx
      obtain ⟨_,_,p',_,j',_,s',_,bound',_,v',_,hKey',hChosen⟩ := (hRaw key x).mp hFx
      obtain ⟨hpp',hjj',hss',hbb',hvv'⟩ := key_code_unique hM.1 hKey hKey'
      subst p'
      subst j'
      subst s'
      subst bound'
      subst v'
      exact hChosen
    · intro hChosen
      exact (hRaw key x).mpr ⟨(key_members hK key).mpr ⟨p,hp,j,hj,s,hs,bound,hb,v,hv,hKey⟩,hChosen.1,
        p,hp,j,hj,s,hs,bound,hb,v,hv,hKey,hChosen⟩
  refine ⟨F,⟨hSupport,?_,?_⟩,hSpec⟩
  · intro key hkey
    obtain ⟨p,hp,j,hj,s,hs,bound,hb,v,hv,hKey⟩ := (key_members hK key).mp hkey
    obtain ⟨x,hChosen⟩ := chosen_witness_exists_d hM C I hOrd hZero p j s bound v
    exact ⟨x,hChosen.1,(hSpec p hp j hj s hs bound hb v hv key hKey x).mpr hChosen⟩
  · intro key x y hFx hFy
    obtain ⟨p,hp,j,hj,s,hs,bound,hb,v,hv,hKey⟩ := (key_members hK key).mp ((hRaw key x).mp hFx).1
    exact chosen_witness_unique hM.1 hOrd
      ((hSpec p hp j hj s hs bound hb v hv key hKey x).mp hFx)
      ((hSpec p hp j hj s hs bound hb v hv key hKey y).mp hFy)

theorem chosen_witness_is_real {M : SetTheory.Structure.{u}} {C : Context M.Domain} {I : EvaluationData M.Domain}
    {zero p j s bound v x : M.Domain} (hChosen : ChosenWitness M C I zero p j s bound v x)
    (hExists : ∃ y, M.mem y I.carrier ∧ FalseWitness M C I p j s bound v y) : FalseWitness M C I p j s bound v x := by
  rcases hChosen.2 with hReal | ⟨_,hNone⟩
  · exact hReal.1
  · obtain ⟨y,hy,hWitness⟩ := hExists
    exact False.elim (hNone y hy hWitness)

end KP1Y.Satisfaction
