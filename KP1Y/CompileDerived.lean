import KP1Y.CompileBoolean
import KP1Y.CompileQuantifier

/-! 存在量词与追加原子合取：使用有限个已核验编译步骤，不引入新逻辑公理。 -/
namespace KP1Y.Satisfaction
open YesMetaZFC YesMetaZFC.SetTheory
open KP1Y.Kuratowski KP1Y.Functions KP1Y.Assignments
universe u

theorem compile_existential_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : Context M.Domain} (hC : ContextSpaces M C) {D : RelationalData M.Domain}
    {H p n bound j v : M.Domain} (hH : Evaluation M C H) (hP : WellFormedProgram M C D p n bound)
    (hj : M.mem j n) (hv : M.mem v bound) :
    ∃ q length head, CompiledExtension M C D p n bound q length head ∧
      ∀ s, Graph M s bound C.carrier →
        (NodeTrue M C H q head s ↔ ∃ x, M.mem x C.carrier ∧ ∃ t,
          Updated M t s bound C.carrier v x ∧ NodeTrue M C H p j t) := by
  classical
  obtain ⟨p1,n1,h1,truth1⟩ := compile_negation_d hM hC hH hP hj
  obtain ⟨p2,n2,h2,truth2⟩ := compile_universal_d hM hC hH h1.wellFormed h1.successor.predecessor_mem hv
  obtain ⟨p3,n3,h3,truth3⟩ := compile_negation_d hM hC hH h2.wellFormed h2.successor.predecessor_mem
  refine ⟨p3,n3,n2,(h1.trans hM.1 h2).trans hM.1 h3,?_⟩
  intro s hS
  have hAll : NodeTrue M C H p2 n1 s ↔
      ∀ x, M.mem x C.carrier → ∀ t, Updated M t s bound C.carrier v x → ¬NodeTrue M C H p j t := by
    apply (truth2 s hS).trans
    constructor
    · intro h x hx t ht
      exact (truth1 t ((hC.assignments t).mpr ⟨bound,hP.bound_nat,ht.graph⟩)).mp (h x hx t ht)
    · intro h x hx t ht
      exact (truth1 t ((hC.assignments t).mpr ⟨bound,hP.bound_nat,ht.graph⟩)).mpr (h x hx t ht)
  apply (truth3 s ((hC.assignments s).mpr ⟨bound,hP.bound_nat,hS⟩)).trans
  apply (not_congr hAll).trans
  constructor
  · intro hNot
    apply Classical.byContradiction
    intro hNone
    exact hNot (fun x hx t ht hTrue => hNone ⟨x,hx,t,ht,hTrue⟩)
  · rintro ⟨x,hx,t,ht,hTrue⟩ hAll
    exact hAll x hx t ht hTrue

theorem compile_conjoin_atom_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : Context M.Domain} (hC : ContextSpaces M C) {D : RelationalData M.Domain}
    {H p n bound j a : M.Domain} (hH : Evaluation M C H) (hP : WellFormedProgram M C D p n bound)
    (hj : M.mem j n) (ha : M.mem a D.codes) (haC : M.mem a C.operands) (hScope : ScopedAtom M D a bound) :
    ∃ q length head, CompiledExtension M C D p n bound q length head ∧
      ∀ s, M.mem s C.assignments →
        (NodeTrue M C H q head s ↔ NodeTrue M C H p j s ∧ MemPair M C.atomic a s) := by
  obtain ⟨p1,n1,h1,truth1⟩ := compile_atom_d hM hC hH hP ha haC hScope
  obtain ⟨p2,n2,j2,h2,truth2⟩ := compile_conjunction_d hM hC hH h1.wellFormed
    ((h1.successor j).mpr (Or.inl hj)) h1.successor.predecessor_mem
  refine ⟨p2,n2,j2,h1.trans hM.1 h2,?_⟩
  intro s hs
  exact (truth2 s hs).trans (and_congr (h1.old_node hM hC hH hP.length_nat hj hs).symm (truth1 s hs))

end KP1Y.Satisfaction
