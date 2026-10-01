import KP1Y.SatisfactionTransport

/-! 用实际对象归纳证明：相同程序前缀对全部内部有限赋值有相同真值。 -/
namespace KP1Y.Satisfaction
open YesMetaZFC YesMetaZFC.SetTheory YesMetaZFC.SetTheory.Definitional
open KP1Y.Kuratowski KP1Y.Functions
universe u

def agreementFormula {n : Nat} (C : Context (Project.Term n)) (H p q i : Project.Term n) : Project.Formula 1 n :=
  Project.Formula.forallMem C.assignments (Project.Formula.forallMem C.columns.weaken
    (Project.Formula.forallMem C.columns.weaken.weaken
      (.imp (.conj (codeFormula (.bound 1) p.weaken.weaken.weaken (.bound 2))
          (codeFormula (.bound 0) q.weaken.weaken.weaken (.bound 2)))
        (.iff (memPairFormula H.weaken.weaken.weaken i.weaken.weaken.weaken (.bound 1))
          (memPairFormula H.weaken.weaken.weaken i.weaken.weaken.weaken (.bound 0))))))

theorem agreementFormula_delta0 {n : Nat} (C : Context (Project.Term n)) (H p q i : Project.Term n) :
    (agreementFormula C H p q i).IsDelta0 :=
  .forallMem _ (.forallMem _ (.forallMem _ (.imp
    (.conj (codeFormula_delta0 _ _ _) (codeFormula_delta0 _ _ _))
    (.iff (memPairFormula_delta0 _ _ _) (memPairFormula_delta0 _ _ _)))))

theorem agreementFormula_iff {M : SetTheory.Structure.{u}} (he : Extensional M) {n : Nat}
    (env : Env M n) (C : Context (Project.Term n)) (H p q i : Project.Term n) :
    Project.Formula.satisfies env (agreementFormula C H p q i) ↔
      NodeAgreement M (C.eval env) (H.eval env) (p.eval env) (q.eval env) (i.eval env) := by
  simp only [agreementFormula, Project.Formula.satisfies_forallMem_iff,
    Project.Formula.satisfies_imp_iff, Project.Formula.satisfies_conj_iff,
    Project.Formula.satisfies_iff_iff, codeFormula_iff he, memPairFormula_iff he,
    Definitional.Term.eval_weaken]
  rfl

private def agreementParameters : Context (Project.Term 18) :=
  ⟨.bound 5,.bound 6,.bound 7,.bound 8,.bound 9,.bound 10,.bound 11,
    .bound 12,.bound 13,.bound 14,.bound 15,.bound 16,.bound 17⟩

private def agreementGuard : Project.UnarySchema 17 where
  body := .imp (.mem (.bound 0) (.bound 1))
    (agreementFormula agreementParameters (.bound 4) (.bound 3) (.bound 2) (.bound 0))
  freeClosed := by
    simp [agreementFormula, agreementParameters, memPairFormula, codeFormula, pairFormula,
      Project.Formula.existsMem, Project.Formula.forallMem, Definitional.Formula.FreeClosed]

private theorem agreementGuard_iff {M : SetTheory.Structure.{u}} (he : Extensional M)
    (C : Context M.Domain) (H p q δ i : M.Domain) :
    Project.Formula.satisfies ((((((contextEnv C).push H).push p).push q).push δ).push i) agreementGuard.body ↔
      (M.mem i δ → NodeAgreement M C H p q i) := by
  simp only [agreementGuard, Project.Formula.satisfies_imp_iff,
    Project.Formula.satisfies_mem_iff, agreementFormula_iff he]
  rfl

theorem program_rows_agree_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : Context M.Domain} (hC : ContextSpaces M C) {H p q δ : M.Domain} (hH : Evaluation M C H)
    (hp : M.mem p C.programs) (hq : M.mem q C.programs)
    (hδ : M.IsOrdinal δ) (hδω : M.MemberSubset δ C.omega)
    (hRows : ∀ i, M.mem i δ → ∀ instr, M.mem instr C.instructions →
      (MemPair M p i instr ↔ MemPair M q i instr)) :
    ∀ i, M.mem i δ → NodeAgreement M C H p q i := by
  have hAll := KP1Y.ordinal_induction_d hM agreementGuard ((((contextEnv C).push H).push p).push q |>.push δ)
    (fun i _ ih => (agreementGuard_iff hM.1 C H p q δ i).mpr (by
      intro hi s hs c hc d hd hCodes
      have hPast : ∀ j, M.mem j i → NodeAgreement M C H p q j := by
        intro j hj
        exact (agreementGuard_iff hM.1 C H p q δ j).mp (ih j hj) (hδ.transitive i hi j hj)
      exact (evaluation_node hM.1 hC hH hp hs (hδω i hi) hCodes.1).trans
        ((clauses_program_congr hM hC hp hq hs hc hd hCodes.1 hCodes.2 (hRows i hi) hPast).trans
          (evaluation_node hM.1 hC hH hq hs (hδω i hi) hCodes.2).symm)))
  exact fun i hi => (agreementGuard_iff hM.1 C H p q δ i).mp (hAll i (hδ.mem hi)) hi

theorem evaluation_prefix_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : Context M.Domain} (hC : ContextSpaces M C) {H p q n : M.Domain} (hH : Evaluation M C H)
    (hn : M.mem n C.omega) (hq : M.mem q C.programs) (hPrefix : Prefix M p q n C.instructions) :
    ∀ i, M.mem i n → NodeAgreement M C H p q i := by
  have hω := KP1Y.Naturals.omega_isOrdinal_d hM hC.omega
  exact program_rows_agree_d hM hC hH ((hC.programs p).mpr ⟨n,hn,hPrefix.graph⟩) hq
    (hω.mem hn) (hω.transitive n hn) hPrefix.rows

end KP1Y.Satisfaction
