import KP1Y.CompileConnectives

/-! 用已核验否定和蕴涵编译析取，保持前缀并给逐赋值语义。 -/
namespace KP1Y.Satisfaction
open YesMetaZFC YesMetaZFC.SetTheory
universe u

private theorem neg_imp_iff_or (P Q : Prop) : (¬P → Q) ↔ P ∨ Q := by
  classical
  constructor
  · intro h
    by_cases hp : P
    · exact Or.inl hp
    · exact Or.inr (h hp)
  · rintro (hp | hq) hn
    · exact False.elim (hn hp)
    · exact hq

theorem compile_disjunction_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : Context M.Domain} (hC : ContextSpaces M C) {D : RelationalData M.Domain}
    {H p n bound j k : M.Domain} (hH : Evaluation M C H) (hP : WellFormedProgram M C D p n bound)
    (hj : M.mem j n) (hk : M.mem k n) :
    ∃ q length head, CompiledExtension M C D p n bound q length head ∧
      ∀ s, M.mem s C.assignments → (NodeTrue M C H q head s ↔ NodeTrue M C H p j s ∨ NodeTrue M C H p k s) := by
  obtain ⟨p1,n1,h1,truth1⟩ := compile_negation_d hM hC hH hP hj
  obtain ⟨p2,n2,h2,truth2⟩ := compile_implication_d hM hC hH h1.wellFormed h1.successor.predecessor_mem
    ((h1.successor k).mpr (Or.inl hk))
  refine ⟨p2,n2,n1,h1.trans hM.1 h2,?_⟩
  intro s hs
  exact (truth2 s hs).trans ((imp_congr (truth1 s hs)
    (h1.old_node hM hC hH hP.length_nat hk hs).symm).trans (neg_imp_iff_or _ _))

end KP1Y.Satisfaction
