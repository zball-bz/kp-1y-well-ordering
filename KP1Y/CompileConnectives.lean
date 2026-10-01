import KP1Y.CompiledExtension

/-! 原子、否定、蕴涵的实际程序编译，附合法性和逐赋值真值证明。 -/
namespace KP1Y.Satisfaction
open YesMetaZFC YesMetaZFC.SetTheory
open KP1Y.Kuratowski KP1Y.Functions
universe u

theorem compile_atom_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : Context M.Domain} (hC : ContextSpaces M C) {D : RelationalData M.Domain}
    {H p n bound a : M.Domain} (hH : Evaluation M C H) (hP : WellFormedProgram M C D p n bound)
    (ha : M.mem a D.codes) (haC : M.mem a C.operands) (hScope : ScopedAtom M D a bound) :
    ∃ q length, CompiledExtension M C D p n bound q length n ∧
      ∀ s, M.mem s C.assignments → (NodeTrue M C H q n s ↔ MemPair M C.atomic a s) := by
  have hPad := hC.omega_operands C.atomTag hC.tag_naturals.1
  obtain ⟨q,length,hSucc,hLength,hQ,hq,hPrefix,hInstr⟩ := append_instruction_d hM hC hP.graph hP.length_nat
    (Or.inl rfl) haC hPad
  have hNode : WellFormedAt M C D q n bound := Or.inl ⟨a,ha,C.atomTag,hPad,hInstr,hScope⟩
  exact ⟨q,length,⟨hSucc,hP.length_nat,wellFormed_extend hM.1 hP hQ hLength hSucc hPrefix hNode,hPrefix⟩,
    fun s hs => nodeTrue_atomic_d hM hC hH hq hs hP.length_nat hInstr⟩

theorem compile_negation_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : Context M.Domain} (hC : ContextSpaces M C) {D : RelationalData M.Domain}
    {H p n bound j : M.Domain} (hH : Evaluation M C H) (hP : WellFormedProgram M C D p n bound) (hj : M.mem j n) :
    ∃ q length, CompiledExtension M C D p n bound q length n ∧
      ∀ s, M.mem s C.assignments → (NodeTrue M C H q n s ↔ ¬NodeTrue M C H p j s) := by
  have hPad := hC.omega_operands C.atomTag hC.tag_naturals.1
  have hjC := hC.omega_operands j ((KP1Y.Naturals.omega_isOrdinal_d hM hC.omega).transitive n hP.length_nat j hj)
  obtain ⟨q,length,hSucc,hLength,hQ,hq,hPrefix,hInstr⟩ := append_instruction_d hM hC hP.graph hP.length_nat
    (Or.inr (Or.inl rfl)) hjC hPad
  have hNode : WellFormedAt M C D q n bound := Or.inr (Or.inl ⟨j,hj,C.atomTag,hPad,hInstr⟩)
  refine ⟨q,length,⟨hSucc,hP.length_nat,wellFormed_extend hM.1 hP hQ hLength hSucc hPrefix hNode,hPrefix⟩,?_⟩
  intro s hs
  exact (nodeTrue_negation_d hM hC hH hq hs hP.length_nat hInstr hj).trans
    (not_congr (nodeTrue_prefix_d hM hC hH hP.length_nat hq hPrefix hj hs).symm)

theorem compile_implication_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : Context M.Domain} (hC : ContextSpaces M C) {D : RelationalData M.Domain}
    {H p n bound j k : M.Domain} (hH : Evaluation M C H) (hP : WellFormedProgram M C D p n bound)
    (hj : M.mem j n) (hk : M.mem k n) :
    ∃ q length, CompiledExtension M C D p n bound q length n ∧
      ∀ s, M.mem s C.assignments →
        (NodeTrue M C H q n s ↔ (NodeTrue M C H p j s → NodeTrue M C H p k s)) := by
  have hω := KP1Y.Naturals.omega_isOrdinal_d hM hC.omega
  have hjC := hC.omega_operands j (hω.transitive n hP.length_nat j hj)
  have hkC := hC.omega_operands k (hω.transitive n hP.length_nat k hk)
  obtain ⟨q,length,hSucc,hLength,hQ,hq,hPrefix,hInstr⟩ := append_instruction_d hM hC hP.graph hP.length_nat
    (Or.inr (Or.inr (Or.inl rfl))) hjC hkC
  have hNode : WellFormedAt M C D q n bound := Or.inr (Or.inr (Or.inl ⟨j,hj,k,hk,hInstr⟩))
  refine ⟨q,length,⟨hSucc,hP.length_nat,wellFormed_extend hM.1 hP hQ hLength hSucc hPrefix hNode,hPrefix⟩,?_⟩
  intro s hs
  exact (nodeTrue_implication_d hM hC hH hq hs hP.length_nat hInstr hj hk).trans
    (imp_congr (nodeTrue_prefix_d hM hC hH hP.length_nat hq hPrefix hj hs).symm
      (nodeTrue_prefix_d hM hC hH hP.length_nat hq hPrefix hk hs).symm)

end KP1Y.Satisfaction
