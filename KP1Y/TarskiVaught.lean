import KP1Y.ElementarySyntax

/-! 由原子相容和反例见证闭包推出全部内部公式程序的初等性。 -/
namespace KP1Y.Satisfaction
open YesMetaZFC YesMetaZFC.SetTheory YesMetaZFC.SetTheory.Definitional
open KP1Y.Kuratowski KP1Y.Functions KP1Y.Assignments
universe u

theorem skolem_closed_nodes_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : Context M.Domain} (hC : ContextSpaces M C) {D : RelationalData M.Domain}
    {small large : EvaluationData M.Domain} (hSmall : small.Valid C) (hLarge : large.Valid C)
    (hSub : M.MemberSubset small.carrier large.carrier) (hAtomic : AtomicAgreement M C D small large)
    (hClosed : CounterWitnessClosed M C D small large)
    {p length bound : M.Domain} (hP : WellFormedProgram M C D p length bound) :
    ∀ i, M.mem i length → NodeElementary M C small large p i bound := by
  classical
  have hCS := hSmall.contextSpaces hC
  have hCL := hLarge.contextSpaces hC
  have hω := KP1Y.Naturals.omega_isOrdinal_d hM hC.omega
  have hLength := hω.mem hP.length_nat
  have hp := (hC.programs p).mpr ⟨length,hP.length_nat,hP.graph⟩
  have hAll := KP1Y.ordinal_induction_d hM elementaryGuard
    ((((elementaryEnv C small large).push p).push length).push bound)
    (fun i _ ih => (elementaryGuard_iff hM.1 C small large p length bound i).mpr (by
      intro hi s hs hS
      have hiω := hω.transitive length hP.length_nat i hi
      have hSL := hS.mono_values hSub
      have hsL := (hLarge.assignments_exact s).mpr ⟨bound,hP.bound_nat,hSL⟩
      have hPast : ∀ j, M.mem j i → NodeElementary M C small large p j bound := by
        intro j hj
        exact (elementaryGuard_iff hM.1 C small large p length bound j).mp (ih j hj)
          (hLength.transitive i hi j hj)
      rcases hP.nodes i hi with ⟨a,_,r,_,hInstr,hScope⟩ | ⟨j,hj,r,_,hInstr⟩ |
        ⟨j,hj,k,hk,hInstr⟩ | ⟨j,hj,v,hv,hInstr⟩
      · exact (nodeTrue_atomic_d hM hCS hSmall.table hp hs hiω hInstr).trans
          ((hAtomic a bound hScope hP.bound_nat s hS).trans
            (nodeTrue_atomic_d hM hCL hLarge.table hp hsL hiω hInstr).symm)
      · exact (nodeTrue_negation_d hM hCS hSmall.table hp hs hiω hInstr hj).trans
          ((not_congr (hPast j hj s hs hS)).trans
            (nodeTrue_negation_d hM hCL hLarge.table hp hsL hiω hInstr hj).symm)
      · exact (nodeTrue_implication_d hM hCS hSmall.table hp hs hiω hInstr hj hk).trans
          ((imp_congr (hPast j hj s hs hS) (hPast k hk s hs hS)).trans
            (nodeTrue_implication_d hM hCL hLarge.table hp hsL hiω hInstr hj hk).symm)
      · apply (nodeTrue_universal_d hM hCS hSmall.table hp hS hP.bound_nat hiω hInstr hv hj).trans
        apply Iff.trans ?_ (nodeTrue_universal_d hM hCL hLarge.table hp hSL hP.bound_nat hiω hInstr hv hj).symm
        constructor
        · intro hAllSmall x hx t ht
          apply Classical.byContradiction
          intro hNot
          obtain ⟨y,hy,u,hu,hNotU⟩ := hClosed p length bound hP j (hLength.transitive i hi j hj)
            s hS v hv ⟨x,hx,t,ht,hNot⟩
          have huS := (hSmall.assignments_exact u).mpr ⟨bound,hP.bound_nat,hu.graph⟩
          exact hNotU ((hPast j hj u huS hu.graph).mp (hAllSmall y hy u hu))
        · intro hAllLarge x hx t ht
          have htS := (hSmall.assignments_exact t).mpr ⟨bound,hP.bound_nat,ht.graph⟩
          exact (hPast j hj t htS ht.graph).mpr
            (hAllLarge x (hSub x hx) t (updated_enlarge hM.1 hSub hS hx ht))))
  exact fun i hi => (elementaryGuard_iff hM.1 C small large p length bound i).mp (hAll i (hLength.mem hi)) hi

theorem skolem_closed_elementary_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : Context M.Domain} (hC : ContextSpaces M C) {D : RelationalData M.Domain}
    {small large : EvaluationData M.Domain} (hSmall : small.Valid C) (hLarge : large.Valid C)
    (hSub : M.MemberSubset small.carrier large.carrier) (hAtomic : AtomicAgreement M C D small large)
    (hClosed : CounterWitnessClosed M C D small large) : ProgramElementary M C D small large := by
  refine ⟨hSub,?_⟩
  intro p length head bound hP s hS
  exact skolem_closed_nodes_d hM hC hSmall hLarge hSub hAtomic hClosed hP.wellFormed head
    hP.successor.predecessor_mem s ((hSmall.assignments_exact s).mpr ⟨bound,hP.wellFormed.bound_nat,hS⟩) hS

end KP1Y.Satisfaction
