import KP1Y.OneYSelectionOrder

/-! 根为0、每条父边加1的实际数值图必为真实父路径深度。 -/
namespace KP1Y.OneYFinite
open YesMetaZFC YesMetaZFC.SetTheory YesMetaZFC.SetTheory.Definitional
open KP1Y.Kuratowski KP1Y.Functions KP1Y.Naturals
universe u

def DepthValueEquations (M : SetTheory.Structure.{u}) (C : ExpressionData M.Domain) (m P V : M.Domain) : Prop :=
  ∀ c v, MemPair M V c v → (NoParent M m P c → v=C.zero) ∧
    ∀ p w, MemPair M P c p → MemPair M V p w → M.SuccessorOf v w

private def depthValueEnv {M : SetTheory.Structure.{u}} (C : ExpressionData M.Domain) (m P V : M.Domain) : Env M 8 :=
  (((((((oneEnv C.omega).push C.zero).push C.one).push C.sequences).push C.expressions).push m).push P).push V

private def depthValueSchema : Project.UnarySchema 8 where
  body := .forallE (.forallE (.imp (.conj (memPairFormula (.bound 3) (.bound 2) (.bound 1))
    (depthFormula ⟨.bound 10,.bound 9,.bound 8,.bound 7,.bound 6⟩ (.bound 5) (.bound 4) (.bound 2) (.bound 0)))
    (Project.Formula.extensionalEq (.bound 1) (.bound 0))))
  freeClosed := by
    have hD := depthFormula_freeClosed (n := 11)
      (C := ⟨.bound 10,.bound 9,.bound 8,.bound 7,.bound 6⟩)
      ⟨rfl,rfl,rfl,rfl,rfl⟩ (.bound 5) (.bound 4) (.bound 2) (.bound 0) rfl rfl rfl rfl
    simp [memPairFormula,codeFormula,pairFormula,Project.Formula.forallMem,Project.Formula.existsMem,Definitional.Formula.FreeClosed,hD]

private theorem depthValueSchema_iff {M : SetTheory.Structure.{u}} (he : Extensional M)
    (C : ExpressionData M.Domain) (m P V c : M.Domain) :
    Project.Formula.satisfies ((depthValueEnv C m P V).push c) depthValueSchema.body ↔
      ∀ v d, MemPair M V c v → Depth M C m P c d → v=d := by
  simp only [depthValueSchema,Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_imp_iff,
    Project.Formula.satisfies_conj_iff,memPairFormula_iff he,depthFormula_iff he,
    Project.Formula.satisfies_extensionalEq_iff_eq he,and_imp]
  rfl

theorem depth_value_eq_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {m P V c v d : M.Domain}
    (hP : Forest M C.omega m P) (hV : Graph M V m C.omega) (hEq : DepthValueEquations M C m P V)
    (hAt : MemPair M V c v) (hD : Depth M C m P c d) : v=d := by
  have hAll := KP1Y.induction_d hM depthValueSchema (depthValueEnv C m P V) (by
    intro c ih
    apply (depthValueSchema_iff hM.1 C m P V c).mpr
    intro v d hAt hD
    classical
    by_cases hNo : NoParent M m P c
    · exact ((hEq c v hAt).1 hNo).trans (depth_of_no_parent_d hM hC hP hNo hD).symm
    · have hSome : ∃ p, M.mem p m ∧ MemPair M P c p := by
        apply Classical.byContradiction
        intro hNone
        exact hNo (fun p hp hcp => hNone ⟨p,hp,hcp⟩)
      obtain ⟨p,hp,hParent⟩ := hSome
      obtain ⟨w,_,hW⟩ := hV.total p hp
      obtain ⟨dp,hDP,hSucc⟩ := depth_parent_predecessor_d hM hC hP hParent hD
      have hwd := (depthValueSchema_iff hM.1 C m P V p).mp (ih p (hP.left c p hParent)) w dp hW hDP
      subst w
      exact Structure.SuccessorOf.eq hM.1 ((hEq c v hAt).2 p dp hParent hW) hSucc)
  exact (depthValueSchema_iff hM.1 C m P V c).mp (hAll c) v d hAt hD

theorem depth_values_iff_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {m P V : M.Domain}
    (hP : Forest M C.omega m P) (hV : Graph M V m C.omega) (hEq : DepthValueEquations M C m P V) (c d : M.Domain) :
    MemPair M V c d ↔ Depth M C m P c d := by
  constructor
  · intro hAt
    obtain ⟨e,hE⟩ := depth_exists_d hM hC hP (hV.bounds hM.1 hAt).1
    exact (depth_value_eq_d hM hC hP hV hEq hAt hE).symm ▸ hE
  · intro hD
    obtain ⟨v,_,hAt⟩ := hV.total c (hD.column_bound hM.1)
    exact depth_value_eq_d hM hC hP hV hEq hAt hD ▸ hAt

end KP1Y.OneYFinite
