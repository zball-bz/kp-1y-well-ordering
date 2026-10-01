import KP1Y.SatisfactionInterpretations
import KP1Y.ProgramRelations

/-! 先构造一份语法，再证明它对所有共享语法的解释同时正确。 -/
namespace KP1Y.Satisfaction
open YesMetaZFC YesMetaZFC.SetTheory
open KP1Y.Kuratowski KP1Y.Functions KP1Y.Assignments
universe u

theorem uniform_compile_atom_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : Context M.Domain} (hC : ContextSpaces M C) {D : RelationalData M.Domain}
    {p n bound a : M.Domain} (hP : WellFormedProgram M C D p n bound)
    (ha : M.mem a D.codes) (haC : M.mem a C.operands) (hScope : ScopedAtom M D a bound) :
    ∃ q length, CompiledExtension M C D p n bound q length n ∧
      ∀ A assignments columns atomic H, EvaluationInstance M C A assignments columns atomic H →
        ∀ s, M.mem s assignments →
          (NodeTrue M (C.withInterpretation A assignments columns atomic) H q n s ↔ MemPair M atomic a s) := by
  have hPad := hC.omega_operands C.atomTag hC.tag_naturals.1
  obtain ⟨q,length,hSucc,hLength,hQ,hq,hPrefix,hInstr⟩ := append_instruction_d hM hC hP.graph hP.length_nat
    (Or.inl rfl) haC hPad
  have hNode : WellFormedAt M C D q n bound := Or.inl ⟨a,ha,C.atomTag,hPad,hInstr,hScope⟩
  refine ⟨q,length,⟨hSucc,hP.length_nat,wellFormed_extend hM.1 hP hQ hLength hSucc hPrefix hNode,hPrefix⟩,?_⟩
  intro A assignments columns atomic H hI s hs
  exact nodeTrue_atomic_d hM (hI.contextSpaces hC) hI.table hq hs hP.length_nat hInstr

theorem uniform_compile_negation_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : Context M.Domain} (hC : ContextSpaces M C) {D : RelationalData M.Domain}
    {p n bound j : M.Domain} (hP : WellFormedProgram M C D p n bound) (hj : M.mem j n) :
    ∃ q length, CompiledExtension M C D p n bound q length n ∧
      ∀ A assignments columns atomic H, EvaluationInstance M C A assignments columns atomic H →
        ∀ s, M.mem s assignments →
          (NodeTrue M (C.withInterpretation A assignments columns atomic) H q n s ↔
            ¬NodeTrue M (C.withInterpretation A assignments columns atomic) H p j s) := by
  have hPad := hC.omega_operands C.atomTag hC.tag_naturals.1
  have hjC := hC.omega_operands j ((KP1Y.Naturals.omega_isOrdinal_d hM hC.omega).transitive n hP.length_nat j hj)
  obtain ⟨q,length,hSucc,hLength,hQ,hq,hPrefix,hInstr⟩ := append_instruction_d hM hC hP.graph hP.length_nat
    (Or.inr (Or.inl rfl)) hjC hPad
  have hNode : WellFormedAt M C D q n bound := Or.inr (Or.inl ⟨j,hj,C.atomTag,hPad,hInstr⟩)
  refine ⟨q,length,⟨hSucc,hP.length_nat,wellFormed_extend hM.1 hP hQ hLength hSucc hPrefix hNode,hPrefix⟩,?_⟩
  intro A assignments columns atomic H hI s hs
  have hCI := hI.contextSpaces hC
  exact (nodeTrue_negation_d hM hCI hI.table hq hs hP.length_nat hInstr hj).trans
    (not_congr (nodeTrue_prefix_d hM hCI hI.table hP.length_nat hq hPrefix hj hs).symm)

theorem uniform_compile_implication_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : Context M.Domain} (hC : ContextSpaces M C) {D : RelationalData M.Domain}
    {p n bound j k : M.Domain} (hP : WellFormedProgram M C D p n bound) (hj : M.mem j n) (hk : M.mem k n) :
    ∃ q length, CompiledExtension M C D p n bound q length n ∧
      ∀ A assignments columns atomic H, EvaluationInstance M C A assignments columns atomic H →
        ∀ s, M.mem s assignments →
          (NodeTrue M (C.withInterpretation A assignments columns atomic) H q n s ↔
            (NodeTrue M (C.withInterpretation A assignments columns atomic) H p j s →
              NodeTrue M (C.withInterpretation A assignments columns atomic) H p k s)) := by
  have hω := KP1Y.Naturals.omega_isOrdinal_d hM hC.omega
  have hjC := hC.omega_operands j (hω.transitive n hP.length_nat j hj)
  have hkC := hC.omega_operands k (hω.transitive n hP.length_nat k hk)
  obtain ⟨q,length,hSucc,hLength,hQ,hq,hPrefix,hInstr⟩ := append_instruction_d hM hC hP.graph hP.length_nat
    (Or.inr (Or.inr (Or.inl rfl))) hjC hkC
  have hNode : WellFormedAt M C D q n bound := Or.inr (Or.inr (Or.inl ⟨j,hj,k,hk,hInstr⟩))
  refine ⟨q,length,⟨hSucc,hP.length_nat,wellFormed_extend hM.1 hP hQ hLength hSucc hPrefix hNode,hPrefix⟩,?_⟩
  intro A assignments columns atomic H hI s hs
  have hCI := hI.contextSpaces hC
  exact (nodeTrue_implication_d hM hCI hI.table hq hs hP.length_nat hInstr hj hk).trans
    (imp_congr (nodeTrue_prefix_d hM hCI hI.table hP.length_nat hq hPrefix hj hs).symm
      (nodeTrue_prefix_d hM hCI hI.table hP.length_nat hq hPrefix hk hs).symm)

theorem uniform_compile_universal_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : Context M.Domain} (hC : ContextSpaces M C) {D : RelationalData M.Domain}
    {p n bound j v : M.Domain} (hP : WellFormedProgram M C D p n bound) (hj : M.mem j n) (hv : M.mem v bound) :
    ∃ q length, CompiledExtension M C D p n bound q length n ∧
      ∀ A assignments columns atomic H, EvaluationInstance M C A assignments columns atomic H →
        ∀ s, Graph M s bound A →
          (NodeTrue M (C.withInterpretation A assignments columns atomic) H q n s ↔
            ∀ x, M.mem x A → ∀ t, Updated M t s bound A v x →
              NodeTrue M (C.withInterpretation A assignments columns atomic) H p j t) := by
  have hω := KP1Y.Naturals.omega_isOrdinal_d hM hC.omega
  have hjC := hC.omega_operands j (hω.transitive n hP.length_nat j hj)
  have hvC := hC.omega_operands v (hω.transitive bound hP.bound_nat v hv)
  obtain ⟨q,length,hSucc,hLength,hQ,hq,hPrefix,hInstr⟩ := append_instruction_d hM hC hP.graph hP.length_nat
    (Or.inr (Or.inr (Or.inr rfl))) hvC hjC
  have hNode : WellFormedAt M C D q n bound := Or.inr (Or.inr (Or.inr ⟨j,hj,v,hv,hInstr⟩))
  refine ⟨q,length,⟨hSucc,hP.length_nat,wellFormed_extend hM.1 hP hQ hLength hSucc hPrefix hNode,hPrefix⟩,?_⟩
  intro A assignments columns atomic H hI s hS
  have hCI := hI.contextSpaces hC
  apply (nodeTrue_universal_d hM hCI hI.table hq hS hP.bound_nat hP.length_nat hInstr hv hj).trans
  constructor
  · intro h x hx t ht
    exact (nodeTrue_prefix_d hM hCI hI.table hP.length_nat hq hPrefix hj
      ((hI.assignments_exact t).mpr ⟨bound,hP.bound_nat,ht.graph⟩)).mpr (h x hx t ht)
  · intro h x hx t ht
    exact (nodeTrue_prefix_d hM hCI hI.table hP.length_nat hq hPrefix hj
      ((hI.assignments_exact t).mpr ⟨bound,hP.bound_nat,ht.graph⟩)).mp (h x hx t ht)

end KP1Y.Satisfaction
