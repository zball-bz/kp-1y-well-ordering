import KP1Y.CompileConnectives
import KP1Y.FormulaResult

/-! 从三个已核验的编译原语构造合取和恒真公式；程序前缀和变量作用域保持。 -/
namespace KP1Y.Satisfaction
open YesMetaZFC YesMetaZFC.SetTheory
open KP1Y.Kuratowski KP1Y.Functions
universe u

private theorem not_imp_not_iff (P Q : Prop) : (¬(P → ¬Q)) ↔ P ∧ Q := by
  classical
  constructor
  · intro h
    exact ⟨Classical.byContradiction (fun hn => h (fun hp => False.elim (hn hp))),
      Classical.byContradiction (fun hn => h (fun _ => hn))⟩
  · rintro ⟨hp,hq⟩ h
    exact h hp hq

theorem compile_conjunction_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : Context M.Domain} (hC : ContextSpaces M C) {D : RelationalData M.Domain}
    {H p n bound j k : M.Domain} (hH : Evaluation M C H) (hP : WellFormedProgram M C D p n bound)
    (hj : M.mem j n) (hk : M.mem k n) :
    ∃ q length head, CompiledExtension M C D p n bound q length head ∧
      ∀ s, M.mem s C.assignments → (NodeTrue M C H q head s ↔ NodeTrue M C H p j s ∧ NodeTrue M C H p k s) := by
  obtain ⟨p1,n1,h1,truth1⟩ := compile_negation_d hM hC hH hP hk
  obtain ⟨p2,n2,h2,truth2⟩ := compile_implication_d hM hC hH h1.wellFormed
    ((h1.successor j).mpr (Or.inl hj)) h1.successor.predecessor_mem
  obtain ⟨p3,n3,h3,truth3⟩ := compile_negation_d hM hC hH h2.wellFormed h2.successor.predecessor_mem
  refine ⟨p3,n3,n2,(h1.trans hM.1 h2).trans hM.1 h3,?_⟩
  intro s hs
  have h2' : NodeTrue M C H p2 n1 s ↔ (NodeTrue M C H p j s → ¬NodeTrue M C H p k s) :=
    (truth2 s hs).trans (imp_congr (h1.old_node hM hC hH hP.length_nat hj hs).symm (truth1 s hs))
  exact (truth3 s hs).trans ((not_congr h2').trans (not_imp_not_iff _ _))

theorem compile_tautology_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : Context M.Domain} (hC : ContextSpaces M C) {D : RelationalData M.Domain}
    {H p n bound j : M.Domain} (hH : Evaluation M C H) (hP : WellFormedProgram M C D p n bound) (hj : M.mem j n) :
    ∃ q length, CompiledExtension M C D p n bound q length n ∧ ∀ s, M.mem s C.assignments → NodeTrue M C H q n s := by
  obtain ⟨q,length,hQ,hTruth⟩ := compile_implication_d hM hC hH hP hj hj
  exact ⟨q,length,hQ,fun s hs => (hTruth s hs).mpr id⟩

theorem compile_true_from_atom_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : Context M.Domain} (hC : ContextSpaces M C) {D : RelationalData M.Domain}
    {H bound a : M.Domain} (hH : Evaluation M C H) (hb : M.mem bound C.omega)
    (ha : M.mem a D.codes) (haC : M.mem a C.operands) (hScope : ScopedAtom M D a bound) :
    ∃ p length head, FormulaResult M C D p length head bound ∧ ∀ s, M.mem s C.assignments → NodeTrue M C H p head s := by
  obtain ⟨e,he,heω,_,hE⟩ := empty_program_d hC
  have hEmpty : WellFormedProgram M C D e e bound := ⟨hE,heω,hb,fun i hi => False.elim (he i hi)⟩
  obtain ⟨p,n,hP,_⟩ := compile_atom_d hM hC hH hEmpty ha haC hScope
  obtain ⟨q,m,hQ,hTrue⟩ := compile_tautology_d hM hC hH hP.wellFormed hP.successor.predecessor_mem
  exact ⟨q,m,n,hQ.result,hTrue⟩

end KP1Y.Satisfaction
