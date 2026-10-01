import KP1Y.CompileFiniteConjunction
import KP1Y.CompileConjunctionExtension
import KP1Y.CompileFiniteQuantifiers

/-! 有限图所需的存在约束和反例公式模板，长度均可为模型内部的任意自然数。 -/
namespace KP1Y.Satisfaction
open YesMetaZFC YesMetaZFC.SetTheory
open KP1Y.Kuratowski KP1Y.Functions
universe u

def ExistsConstraints (M : SetTheory.Structure.{u}) (C : Context M.Domain) (D : RelationalData M.Domain)
    (seq N vars NV s bound : M.Domain) : Prop :=
  ∃ t, M.mem t C.assignments ∧ AgreeOutside M vars NV s t bound C.carrier ∧ AllAtoms M C D seq N t

def Counterexample (M : SetTheory.Structure.{u}) (C : Context M.Domain) (D : RelationalData M.Domain)
    (input NI output NO inputVars NVI outputVars NVO s bound : M.Domain) : Prop :=
  ∃ t, M.mem t C.assignments ∧ AgreeOutside M inputVars NVI s t bound C.carrier ∧
    AllAtoms M C D input NI t ∧ ¬ExistsConstraints M C D output NO outputVars NVO t bound

theorem compile_exists_constraints_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : Context M.Domain} (hC : ContextSpaces M C) {D : RelationalData M.Domain}
    {H seq N vars NV bound seed : M.Domain} (hH : Evaluation M C H)
    (hSeq : Graph M seq N D.codes) (hN : M.mem N C.omega) (hb : M.mem bound C.omega)
    (hVars : Graph M vars NV bound) (hNV : M.mem NV C.omega)
    (hCodes : M.MemberSubset D.codes C.operands)
    (hScoped : ∀ i, M.mem i N → ∀ a, MemPair M seq i a → ScopedAtom M D a bound)
    (hSeed : M.mem seed D.codes) (hSeedScope : ScopedAtom M D seed bound) :
    ∃ q length head, FormulaResult M C D q length head bound ∧ ∀ s, Graph M s bound C.carrier →
      (NodeTrue M C H q head s ↔ ExistsConstraints M C D seq N vars NV s bound) := by
  obtain ⟨p,_,n,_,j,_,hP,truth⟩ := compile_atom_sequence_d hM hC hH hSeq hN hb hCodes hScoped hSeed hSeedScope
  obtain ⟨q,length,head,hQ,hMeaning⟩ := compile_existential_block_d hM hC hH hP hVars hNV
  refine ⟨q,length,head,hQ.result,?_⟩
  intro s hS
  apply (hMeaning s hS).trans
  exact ⟨fun ⟨t,ht,hFrame,hTrue⟩ => ⟨t,ht,hFrame,(truth t ht).mp hTrue⟩,
    fun ⟨t,ht,hFrame,hTrue⟩ => ⟨t,ht,hFrame,(truth t ht).mpr hTrue⟩⟩

theorem compile_counterexample_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : Context M.Domain} (hC : ContextSpaces M C) {D : RelationalData M.Domain}
    {H input NI output NO inputVars NVI outputVars NVO bound seed : M.Domain} (hH : Evaluation M C H)
    (hInput : Graph M input NI D.codes) (hNI : M.mem NI C.omega)
    (hOutput : Graph M output NO D.codes) (hNO : M.mem NO C.omega) (hb : M.mem bound C.omega)
    (hInputVars : Graph M inputVars NVI bound) (hNVI : M.mem NVI C.omega)
    (hOutputVars : Graph M outputVars NVO bound) (hNVO : M.mem NVO C.omega)
    (hCodes : M.MemberSubset D.codes C.operands)
    (hScopedInput : ∀ i, M.mem i NI → ∀ a, MemPair M input i a → ScopedAtom M D a bound)
    (hScopedOutput : ∀ i, M.mem i NO → ∀ a, MemPair M output i a → ScopedAtom M D a bound)
    (hSeed : M.mem seed D.codes) (hSeedScope : ScopedAtom M D seed bound) :
    ∃ q length head, FormulaResult M C D q length head bound ∧ ∀ s, Graph M s bound C.carrier →
      (NodeTrue M C H q head s ↔ Counterexample M C D input NI output NO inputVars NVI outputVars NVO s bound) := by
  obtain ⟨p0,_,n0,_,j0,_,h0,truth0⟩ := compile_atom_sequence_d hM hC hH hInput hNI hb hCodes hScopedInput hSeed hSeedScope
  obtain ⟨p1,n1,j1,h1,truth1⟩ := compile_atom_sequence_extended_d hM hC hH h0 hOutput hNO hCodes hScopedOutput
  obtain ⟨p2,n2,j2,h2,truth2⟩ := compile_existential_block_d hM hC hH h1.result hOutputVars hNVO
  obtain ⟨p3,n3,h3,truth3⟩ := compile_negation_d hM hC hH h2.wellFormed h2.successor.predecessor_mem
  have hBefore := (h1.trans hM.1 h2).trans hM.1 h3
  have hj0 := prefix_domain_subset hM.1 hBefore.prefixGraph hBefore.wellFormed.graph j0 h0.successor.predecessor_mem
  obtain ⟨p4,n4,j4,h4,truth4⟩ := compile_conjunction_d hM hC hH h3.wellFormed hj0 h3.successor.predecessor_mem
  have hBody (s : M.Domain) (hS : Graph M s bound C.carrier) :
      NodeTrue M C H p4 j4 s ↔ AllAtoms M C D input NI s ∧ ¬ExistsConstraints M C D output NO outputVars NVO s bound := by
    have hs := (hC.assignments s).mpr ⟨bound,hb,hS⟩
    have hIn := (hBefore.old_node hM hC hH h0.wellFormed.length_nat h0.successor.predecessor_mem hs).symm.trans (truth0 s hs)
    have hOut : NodeTrue M C H p2 j2 s ↔ ExistsConstraints M C D output NO outputVars NVO s bound := by
      apply (truth2 s hS).trans
      exact ⟨fun ⟨t,ht,hFrame,hTrue⟩ => ⟨t,ht,hFrame,(truth1 t ht).mp hTrue⟩,
        fun ⟨t,ht,hFrame,hTrue⟩ => ⟨t,ht,hFrame,(truth1 t ht).mpr hTrue⟩⟩
    exact (truth4 s hs).trans (and_congr hIn ((truth3 s hs).trans (not_congr hOut)))
  obtain ⟨p5,n5,j5,h5,truth5⟩ := compile_existential_block_d hM hC hH h4.result hInputVars hNVI
  refine ⟨p5,n5,j5,h5.result,?_⟩
  intro s hS
  apply (truth5 s hS).trans
  exact ⟨fun ⟨t,ht,hFrame,hTrue⟩ => ⟨t,ht,hFrame,(hBody t hFrame.target).mp hTrue⟩,
    fun ⟨t,ht,hFrame,hTrue⟩ => ⟨t,ht,hFrame,(hBody t hFrame.target).mpr hTrue⟩⟩

end KP1Y.Satisfaction
