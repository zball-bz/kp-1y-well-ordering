import KP1Y.RelationalAtoms

/-! 关系结构的所有内部原子和赋值均有集合界；原子表确实读取给定关系解释。 -/
namespace KP1Y.Satisfaction
open YesMetaZFC YesMetaZFC.SetTheory YesMetaZFC.SetTheory.Definitional
open KP1Y.Kuratowski KP1Y.Functions KP1Y.Assignments KP1Y.Naturals
universe u

structure DataSpaces (M : SetTheory.Structure.{u}) (D : RelationalData M.Domain) : Prop where
  omega : M.IsOmega D.omega
  variables : ∀ vars, M.mem vars D.variables ↔ ∃ n, M.mem n D.omega ∧ Graph M vars n D.omega
  values : ∀ t, M.mem t D.values ↔ ∃ n, M.mem n D.omega ∧ Graph M t n D.carrier
  codes : ∀ a, M.mem a D.codes ↔ ∃ r, M.mem r D.symbols ∧ ∃ vars, M.mem vars D.variables ∧ Codes M a r vars

theorem data_spaces_exists_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {ω : M.Domain} (hω : M.IsOmega ω) (A symbols arity interpretation : M.Domain) :
    ∃ variables values codes, DataSpaces M ⟨ω,A,symbols,arity,interpretation,variables,values,codes⟩ := by
  obtain ⟨variables,hV⟩ := KP1Y.Sequences.finite_sequences_exist_d hM hω ω
  obtain ⟨values,hA⟩ := KP1Y.Sequences.finite_sequences_exist_d hM hω A
  obtain ⟨codes,hC⟩ := product_exists hM symbols variables
  exact ⟨variables,values,codes,hω,hV,hA,hC⟩

theorem atomic_table_correct {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {D : RelationalData M.Domain} (hD : DataSpaces M D) {Atom : M.Domain} (hAtom : AtomicTable M D Atom)
    {a r vars s n m t : M.Domain} (hr : M.mem r D.symbols) (hCode : Codes M a r vars)
    (hn : M.mem n D.omega) (hm : M.mem m D.omega) (hArity : MemPair M D.arity r n)
    (hValue : TupleValue M t vars s n m D.carrier) :
    MemPair M Atom a s ↔ MemPair M D.interpretation r t := by
  constructor
  · intro hTrue
    obtain ⟨_,_,r',_,vars',_,hCode',n',_,m',_,_,t',_,hValue',hRel⟩ := (hAtom.rows a s).mp hTrue
    obtain ⟨hrr',hvars⟩ := codes_injective hM.1 hCode hCode'
    subst r'
    subst vars'
    have hnn' := domain_unique hM.1 hValue'.variables hValue.variables
    subst n'
    have hmm' := domain_unique hM.1 hValue'.source hValue.source
    subst m'
    exact (tuple_value_unique hM.1 hValue' hValue) ▸ hRel
  · intro hRel
    have hVariables : M.mem vars D.variables := (hD.variables vars).mpr
      ⟨n,hn,hValue.variables.mono_values ((omega_isOrdinal_d hM hD.omega).transitive m hm)⟩
    have hAssignments : M.mem s D.values := (hD.values s).mpr ⟨m,hm,hValue.source⟩
    have hTuple : M.mem t D.values := (hD.values t).mpr ⟨n,hn,hValue.values⟩
    exact (hAtom.rows a s).mpr ⟨(hD.codes a).mpr ⟨r,hr,vars,hVariables,hCode⟩,hAssignments,
      r,hr,vars,hVariables,hCode,n,hn,m,hm,hArity,t,hTuple,hValue,hRel⟩

end KP1Y.Satisfaction
