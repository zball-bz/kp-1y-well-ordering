import KP1Y.ProgramRelations

/-! 将程序节点真值写成有界列查询，便于对象公式编译和内部有限迭代。 -/
namespace KP1Y.Satisfaction
open YesMetaZFC YesMetaZFC.SetTheory YesMetaZFC.SetTheory.Definitional
open KP1Y.Kuratowski KP1Y.Functions KP1Y.Assignments
universe u

def NodeTrue (M : SetTheory.Structure.{u}) (C : Context M.Domain) (H p i s : M.Domain) : Prop :=
  ∃ c, M.mem c C.columns ∧ Codes M c p s ∧ MemPair M H i c

def nodeTrueFormula {n : Nat} (C : Context (Project.Term n)) (H p i s : Project.Term n) : Project.Formula 1 n :=
  Project.Formula.existsMem C.columns (.conj (codeFormula (.bound 0) p.weaken s.weaken)
    (memPairFormula H.weaken i.weaken (.bound 0)))

theorem nodeTrueFormula_delta0 {n : Nat} (C : Context (Project.Term n)) (H p i s : Project.Term n) :
    (nodeTrueFormula C H p i s).IsDelta0 :=
  .existsMem _ (.conj (codeFormula_delta0 _ _ _) (memPairFormula_delta0 _ _ _))

theorem nodeTrueFormula_iff {M : SetTheory.Structure.{u}} (he : Extensional M) {n : Nat}
    (env : Env M n) (C : Context (Project.Term n)) (H p i s : Project.Term n) :
    Project.Formula.satisfies env (nodeTrueFormula C H p i s) ↔
      NodeTrue M (C.eval env) (H.eval env) (p.eval env) (i.eval env) (s.eval env) := by
  simp only [nodeTrueFormula, Project.Formula.satisfies_existsMem_iff,
    Project.Formula.satisfies_conj_iff, codeFormula_iff he, memPairFormula_iff he,
    Definitional.Term.eval_weaken]
  rfl

theorem nodeTrue_at {M : SetTheory.Structure.{u}} (he : Extensional M)
    {C : Context M.Domain} {H p i s c : M.Domain} (hc : M.mem c C.columns) (hCode : Codes M c p s) :
    NodeTrue M C H p i s ↔ MemPair M H i c := by
  constructor
  · rintro ⟨d,_,hCode',hTrue⟩
    have heq := codes_unique he hCode' hCode
    subst d
    exact hTrue
  · exact fun h => ⟨c,hc,hCode,h⟩

theorem nodeTrue_agreement_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : Context M.Domain} (hC : ContextSpaces M C) {H p q i s : M.Domain}
    (hp : M.mem p C.programs) (hq : M.mem q C.programs) (hs : M.mem s C.assignments)
    (h : NodeAgreement M C H p q i) : NodeTrue M C H p i s ↔ NodeTrue M C H q i s := by
  obtain ⟨c,hc,hcp⟩ := column_exists_d hM hC hp hs
  obtain ⟨d,hd,hdq⟩ := column_exists_d hM hC hq hs
  exact (nodeTrue_at hM.1 hc hcp).trans ((h s hs c hc d hd ⟨hcp,hdq⟩).trans (nodeTrue_at hM.1 hd hdq).symm)

theorem nodeTrue_prefix_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : Context M.Domain} (hC : ContextSpaces M C) {H p q n i s : M.Domain} (hH : Evaluation M C H)
    (hn : M.mem n C.omega) (hq : M.mem q C.programs) (hPrefix : Prefix M p q n C.instructions)
    (hi : M.mem i n) (hs : M.mem s C.assignments) : NodeTrue M C H p i s ↔ NodeTrue M C H q i s :=
  nodeTrue_agreement_d hM hC ((hC.programs p).mpr ⟨n,hn,hPrefix.graph⟩) hq hs
    (evaluation_prefix_d hM hC hH hn hq hPrefix i hi)

theorem nodeTrue_atomic_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : Context M.Domain} (hC : ContextSpaces M C) {H p i s a r : M.Domain} (hH : Evaluation M C H)
    (hp : M.mem p C.programs) (hs : M.mem s C.assignments) (hi : M.mem i C.omega)
    (hInstr : InstructionAt M C.instructions C.pairs p i C.atomTag a r) :
    NodeTrue M C H p i s ↔ MemPair M C.atomic a s := by
  obtain ⟨c,hc,hCode⟩ := column_exists_d hM hC hp hs
  exact (nodeTrue_at hM.1 hc hCode).trans (evaluation_atomic hM.1 hC hH hp hs hi hCode hInstr)

theorem nodeTrue_negation_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : Context M.Domain} (hC : ContextSpaces M C) {H p i s j r : M.Domain} (hH : Evaluation M C H)
    (hp : M.mem p C.programs) (hs : M.mem s C.assignments) (hi : M.mem i C.omega)
    (hInstr : InstructionAt M C.instructions C.pairs p i C.negTag j r) (hj : M.mem j i) :
    NodeTrue M C H p i s ↔ ¬NodeTrue M C H p j s := by
  obtain ⟨c,hc,hCode⟩ := column_exists_d hM hC hp hs
  exact (nodeTrue_at hM.1 hc hCode).trans
    ((evaluation_negation hM.1 hC hH hp hs hi hCode hInstr hj).trans (not_congr (nodeTrue_at hM.1 hc hCode).symm))

theorem nodeTrue_implication_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : Context M.Domain} (hC : ContextSpaces M C) {H p i s j k : M.Domain} (hH : Evaluation M C H)
    (hp : M.mem p C.programs) (hs : M.mem s C.assignments) (hi : M.mem i C.omega)
    (hInstr : InstructionAt M C.instructions C.pairs p i C.impTag j k) (hj : M.mem j i) (hk : M.mem k i) :
    NodeTrue M C H p i s ↔ (NodeTrue M C H p j s → NodeTrue M C H p k s) := by
  obtain ⟨c,hc,hCode⟩ := column_exists_d hM hC hp hs
  exact (nodeTrue_at hM.1 hc hCode).trans ((evaluation_implication hM.1 hC hH hp hs hi hCode hInstr hj hk).trans
    (imp_congr (nodeTrue_at hM.1 hc hCode).symm (nodeTrue_at hM.1 hc hCode).symm))

theorem nodeTrue_universal_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : Context M.Domain} (hC : ContextSpaces M C) {H p i s j v bound : M.Domain} (hH : Evaluation M C H)
    (hp : M.mem p C.programs) (hS : Graph M s bound C.carrier) (hb : M.mem bound C.omega) (hi : M.mem i C.omega)
    (hInstr : InstructionAt M C.instructions C.pairs p i C.allTag v j) (hv : M.mem v bound) (hj : M.mem j i) :
    NodeTrue M C H p i s ↔ ∀ x, M.mem x C.carrier → ∀ t, Updated M t s bound C.carrier v x → NodeTrue M C H p j t := by
  obtain ⟨c,hc,hCode⟩ := column_exists_d hM hC hp ((hC.assignments s).mpr ⟨bound,hb,hS⟩)
  exact (nodeTrue_at hM.1 hc hCode).trans (evaluation_universal hM hC hH hp hS hb hi hCode hInstr hv hj)

end KP1Y.Satisfaction
