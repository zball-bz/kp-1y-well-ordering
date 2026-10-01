import KP1Y.CompileConnectives

/-! 全称量词编译：新节点量化真实更新后的赋值，子程序引用保持原义。 -/
namespace KP1Y.Satisfaction
open YesMetaZFC YesMetaZFC.SetTheory
open KP1Y.Kuratowski KP1Y.Functions KP1Y.Assignments
universe u

theorem compile_universal_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : Context M.Domain} (hC : ContextSpaces M C) {D : RelationalData M.Domain}
    {H p n bound j v : M.Domain} (hH : Evaluation M C H) (hP : WellFormedProgram M C D p n bound)
    (hj : M.mem j n) (hv : M.mem v bound) :
    ∃ q length, CompiledExtension M C D p n bound q length n ∧
      ∀ s, Graph M s bound C.carrier →
        (NodeTrue M C H q n s ↔ ∀ x, M.mem x C.carrier → ∀ t, Updated M t s bound C.carrier v x → NodeTrue M C H p j t) := by
  have hω := KP1Y.Naturals.omega_isOrdinal_d hM hC.omega
  have hjC := hC.omega_operands j (hω.transitive n hP.length_nat j hj)
  have hvC := hC.omega_operands v (hω.transitive bound hP.bound_nat v hv)
  obtain ⟨q,length,hSucc,hLength,hQ,hq,hPrefix,hInstr⟩ := append_instruction_d hM hC hP.graph hP.length_nat
    (Or.inr (Or.inr (Or.inr rfl))) hvC hjC
  have hNode : WellFormedAt M C D q n bound := Or.inr (Or.inr (Or.inr ⟨j,hj,v,hv,hInstr⟩))
  refine ⟨q,length,⟨hSucc,hP.length_nat,wellFormed_extend hM.1 hP hQ hLength hSucc hPrefix hNode,hPrefix⟩,?_⟩
  intro s hS
  apply (nodeTrue_universal_d hM hC hH hq hS hP.bound_nat hP.length_nat hInstr hv hj).trans
  constructor
  · intro h x hx t ht
    exact (nodeTrue_prefix_d hM hC hH hP.length_nat hq hPrefix hj
      ((hC.assignments t).mpr ⟨bound,hP.bound_nat,ht.graph⟩)).mpr (h x hx t ht)
  · intro h x hx t ht
    exact (nodeTrue_prefix_d hM hC hH hP.length_nat hq hPrefix hj
      ((hC.assignments t).mpr ⟨bound,hP.bound_nat,ht.graph⟩)).mp (h x hx t ht)

end KP1Y.Satisfaction
