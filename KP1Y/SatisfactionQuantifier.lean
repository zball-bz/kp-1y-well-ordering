import KP1Y.SatisfactionConnectives

/-! 全称节点量化所有实际赋值更新；更新的存在唯一性已在 KPω 内证明。 -/
namespace KP1Y.Satisfaction
open YesMetaZFC YesMetaZFC.SetTheory
open KP1Y.Kuratowski KP1Y.Functions KP1Y.Assignments
universe u

def QuantifiesAt (M : SetTheory.Structure.{u}) (C : Context M.Domain) (H p s n v j : M.Domain) : Prop :=
  ∀ x, M.mem x C.carrier → ∀ t, Updated M t s n C.carrier v x →
    ∃ c, M.mem c C.columns ∧ Codes M c p t ∧ MemPair M H j c

theorem universal_clauses_iff {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : Context M.Domain} (hC : ContextSpaces M C) {p s i c H v j n m V : M.Domain}
    (hP : Graph M p m V) (hS : Graph M s n C.carrier) (hn : M.mem n C.omega)
    (hInstr : InstructionAt M C.instructions C.pairs p i C.allTag v j)
    (hv : M.mem v n) (hj : M.mem j i) :
    Clauses M C p s i c H ↔ QuantifiesAt M C H p s n v j := by
  constructor
  · intro h
    rcases h with ⟨a,_,r,_,hInstr',_⟩ | ⟨j',_,r,_,hInstr',_⟩ |
      ⟨j',_,k,_,hInstr',_⟩ | ⟨j',_,v',_,n',_,hInstr',hS',_,hAll⟩
    · exact False.elim (hC.distinct.atom_all (instruction_unique hM.1 hP hInstr hInstr').1.symm)
    · exact False.elim (hC.distinct.neg_all (instruction_unique hM.1 hP hInstr hInstr').1.symm)
    · exact False.elim (hC.distinct.imp_all (instruction_unique hM.1 hP hInstr hInstr').1.symm)
    · obtain ⟨_,hvv',hjj'⟩ := instruction_unique hM.1 hP hInstr hInstr'
      subst v'
      subst j'
      have hnn' := domain_unique hM.1 hS' hS
      subst n'
      intro x hx t ht
      obtain ⟨t',_,ht',b,hb,hCode,hTrue⟩ := hAll x hx
      have htt' := update_unique hM.1 ht' ht
      subst t'
      exact ⟨b,hb,hCode,hTrue⟩
  · intro hAll
    have hvω := (KP1Y.Naturals.omega_isOrdinal_d hM hC.omega).transitive n hn v hv
    refine Or.inr (Or.inr (Or.inr ⟨j,hj,v,hvω,n,hn,hInstr,hS,hv,?_⟩))
    intro x hx
    obtain ⟨t,ht⟩ := update_exists_d hM hS hx
    obtain ⟨b,hb,hCode,hTrue⟩ := hAll x hx t ht
    exact ⟨t,(hC.assignments t).mpr ⟨n,hn,ht.graph⟩,ht,b,hb,hCode,hTrue⟩

theorem evaluation_universal {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : Context M.Domain} (hC : ContextSpaces M C) {p s i c H v j n : M.Domain}
    (hH : Evaluation M C H) (hp : M.mem p C.programs)
    (hS : Graph M s n C.carrier) (hn : M.mem n C.omega) (hi : M.mem i C.omega)
    (hCode : Codes M c p s) (hInstr : InstructionAt M C.instructions C.pairs p i C.allTag v j)
    (hv : M.mem v n) (hj : M.mem j i) :
    MemPair M H i c ↔ QuantifiesAt M C H p s n v j := by
  obtain ⟨m,_,hP⟩ := (hC.programs p).mp hp
  have hs := (hC.assignments s).mpr ⟨n,hn,hS⟩
  exact (evaluation_node hM.1 hC hH hp hs hi hCode).trans
    (universal_clauses_iff hM hC hP hS hn hInstr hv hj)

/-- 从给定关系解释构造全部语法空间、原子表和唯一求值表，而非假设这些集合存在。 -/
theorem relational_evaluation_exists_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {ω : M.Domain} (hω : M.IsOmega ω) (A symbols arity interpretation : M.Domain) :
    ∃ variables values codes Atom C H,
      let D : RelationalData M.Domain := ⟨ω,A,symbols,arity,interpretation,variables,values,codes⟩
      DataSpaces M D ∧ AtomicTable M D Atom ∧ RelationalContext M D Atom C ∧
        ContextSpaces M C ∧ Evaluation M C H := by
  obtain ⟨variables,values,codes,hD⟩ := data_spaces_exists_d hM hω A symbols arity interpretation
  let D : RelationalData M.Domain := ⟨ω,A,symbols,arity,interpretation,variables,values,codes⟩
  obtain ⟨Atom,hAtom⟩ := atomic_table_exists_d hM D
  obtain ⟨C,hRel,hC⟩ := context_spaces_exists_d hM hD Atom
  obtain ⟨H,hH⟩ := evaluation_exists_d hM C hC.omega
  exact ⟨variables,values,codes,Atom,C,H,hD,hAtom,hRel,hC,hH⟩

end KP1Y.Satisfaction
