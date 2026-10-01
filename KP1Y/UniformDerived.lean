import KP1Y.UniformCompile
import KP1Y.CompileDerived
import KP1Y.ProgramInclusion

/-! 组合统一编译原语。代码在所有解释参数之前选择，故可用于跨结构反射。 -/
namespace KP1Y.Satisfaction
open YesMetaZFC YesMetaZFC.SetTheory
open KP1Y.Kuratowski KP1Y.Functions KP1Y.Assignments
universe u

private theorem not_imp_not_iff (P Q : Prop) : (¬(P → ¬Q)) ↔ P ∧ Q := by
  classical
  constructor
  · intro h
    exact ⟨Classical.byContradiction (fun hn => h (fun hp => False.elim (hn hp))),
      Classical.byContradiction (fun hn => h (fun _ => hn))⟩
  · rintro ⟨hp,hq⟩ h
    exact h hp hq

theorem uniform_compile_conjunction_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : Context M.Domain} (hC : ContextSpaces M C) {D : RelationalData M.Domain}
    {p n bound j k : M.Domain} (hP : WellFormedProgram M C D p n bound) (hj : M.mem j n) (hk : M.mem k n) :
    ∃ q length head, CompiledExtension M C D p n bound q length head ∧
      ∀ A S B At H, EvaluationInstance M C A S B At H → ∀ s, M.mem s S →
        (NodeTrue M (C.withInterpretation A S B At) H q head s ↔
          NodeTrue M (C.withInterpretation A S B At) H p j s ∧ NodeTrue M (C.withInterpretation A S B At) H p k s) := by
  obtain ⟨p1,n1,h1,truth1⟩ := uniform_compile_negation_d hM hC hP hk
  obtain ⟨p2,n2,h2,truth2⟩ := uniform_compile_implication_d hM hC h1.wellFormed
    ((h1.successor j).mpr (Or.inl hj)) h1.successor.predecessor_mem
  obtain ⟨p3,n3,h3,truth3⟩ := uniform_compile_negation_d hM hC h2.wellFormed h2.successor.predecessor_mem
  refine ⟨p3,n3,n2,(h1.trans hM.1 h2).trans hM.1 h3,?_⟩
  intro A S B At H hI s hs
  have hCI := hI.contextSpaces hC
  have h2' : NodeTrue M (C.withInterpretation A S B At) H p2 n1 s ↔
      (NodeTrue M (C.withInterpretation A S B At) H p j s → ¬NodeTrue M (C.withInterpretation A S B At) H p k s) :=
    (truth2 A S B At H hI s hs).trans (imp_congr
      ((h1.withInterpretation A S B At).old_node hM hCI hI.table hP.length_nat hj hs).symm
      (truth1 A S B At H hI s hs))
  exact (truth3 A S B At H hI s hs).trans ((not_congr h2').trans (not_imp_not_iff _ _))

theorem uniform_compile_tautology_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : Context M.Domain} (hC : ContextSpaces M C) {D : RelationalData M.Domain}
    {p n bound j : M.Domain} (hP : WellFormedProgram M C D p n bound) (hj : M.mem j n) :
    ∃ q length, CompiledExtension M C D p n bound q length n ∧
      ∀ A S B At H, EvaluationInstance M C A S B At H → ∀ s, M.mem s S →
        NodeTrue M (C.withInterpretation A S B At) H q n s := by
  obtain ⟨q,length,hQ,truth⟩ := uniform_compile_implication_d hM hC hP hj hj
  exact ⟨q,length,hQ,fun A S B At H hI s hs => (truth A S B At H hI s hs).mpr id⟩

theorem uniform_compile_conjoin_atom_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : Context M.Domain} (hC : ContextSpaces M C) {D : RelationalData M.Domain}
    {p n bound j a : M.Domain} (hP : WellFormedProgram M C D p n bound) (hj : M.mem j n)
    (ha : M.mem a D.codes) (haC : M.mem a C.operands) (hScope : ScopedAtom M D a bound) :
    ∃ q length head, CompiledExtension M C D p n bound q length head ∧
      ∀ A S B At H, EvaluationInstance M C A S B At H → ∀ s, M.mem s S →
        (NodeTrue M (C.withInterpretation A S B At) H q head s ↔
          NodeTrue M (C.withInterpretation A S B At) H p j s ∧ MemPair M At a s) := by
  obtain ⟨p1,n1,h1,truth1⟩ := uniform_compile_atom_d hM hC hP ha haC hScope
  obtain ⟨p2,n2,j2,h2,truth2⟩ := uniform_compile_conjunction_d hM hC h1.wellFormed
    ((h1.successor j).mpr (Or.inl hj)) h1.successor.predecessor_mem
  refine ⟨p2,n2,j2,h1.trans hM.1 h2,?_⟩
  intro A S B At H hI s hs
  exact (truth2 A S B At H hI s hs).trans (and_congr
    ((h1.withInterpretation A S B At).old_node hM (hI.contextSpaces hC) hI.table hP.length_nat hj hs).symm
    (truth1 A S B At H hI s hs))

theorem uniform_compile_existential_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : Context M.Domain} (hC : ContextSpaces M C) {D : RelationalData M.Domain}
    {p n bound j v : M.Domain} (hP : WellFormedProgram M C D p n bound) (hj : M.mem j n) (hv : M.mem v bound) :
    ∃ q length head, CompiledExtension M C D p n bound q length head ∧
      ∀ A S B At H, EvaluationInstance M C A S B At H → ∀ s, Graph M s bound A →
        (NodeTrue M (C.withInterpretation A S B At) H q head s ↔
          ∃ x, M.mem x A ∧ ∃ t, Updated M t s bound A v x ∧ NodeTrue M (C.withInterpretation A S B At) H p j t) := by
  classical
  obtain ⟨p1,n1,h1,truth1⟩ := uniform_compile_negation_d hM hC hP hj
  obtain ⟨p2,n2,h2,truth2⟩ := uniform_compile_universal_d hM hC h1.wellFormed h1.successor.predecessor_mem hv
  obtain ⟨p3,n3,h3,truth3⟩ := uniform_compile_negation_d hM hC h2.wellFormed h2.successor.predecessor_mem
  refine ⟨p3,n3,n2,(h1.trans hM.1 h2).trans hM.1 h3,?_⟩
  intro A S B At H hI s hS
  have hAll : NodeTrue M (C.withInterpretation A S B At) H p2 n1 s ↔
      ∀ x, M.mem x A → ∀ t, Updated M t s bound A v x → ¬NodeTrue M (C.withInterpretation A S B At) H p j t := by
    apply (truth2 A S B At H hI s hS).trans
    constructor
    · intro h x hx t ht
      exact (truth1 A S B At H hI t ((hI.assignments_exact t).mpr ⟨bound,hP.bound_nat,ht.graph⟩)).mp (h x hx t ht)
    · intro h x hx t ht
      exact (truth1 A S B At H hI t ((hI.assignments_exact t).mpr ⟨bound,hP.bound_nat,ht.graph⟩)).mpr (h x hx t ht)
  apply (truth3 A S B At H hI s ((hI.assignments_exact s).mpr ⟨bound,hP.bound_nat,hS⟩)).trans
  apply (not_congr hAll).trans
  constructor
  · intro hNot
    apply Classical.byContradiction
    intro hNone
    exact hNot (fun x hx t ht hTrue => hNone ⟨x,hx,t,ht,hTrue⟩)
  · rintro ⟨x,hx,t,ht,hTrue⟩ h
    exact h x hx t ht hTrue

end KP1Y.Satisfaction
