import KP1Y.OneYMountainRelations
import KP1Y.OneYCopiedMountainSyntax

/-! 复制高度山形的独立相邻行嵌套条件；Data.Valid没有隐含此条件。 -/
namespace KP1Y.OneYFinite.CopiedMountain
open YesMetaZFC YesMetaZFC.SetTheory YesMetaZFC.SetTheory.Definitional
open KP1Y.Kuratowski KP1Y.Functions KP1Y.Naturals KP1Y.Bounded
universe u

def Nested (M : SetTheory.Structure.{u}) (C : ExpressionData M.Domain) (X : Data M.Domain) : Prop :=
  ∀r s F G, M.SuccessorOf s r → MemPair M X.parents r F → MemPair M X.parents s G →
    ForestRefines M C X.width G F

theorem FromRun.nested_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {m : M.Domain} {R : RowStateSpace M.Domain}
    {V P H : M.Domain} (hRun : RowRun M C m R V P H) {X : Data M.Domain} (_hX : X.Valid M C)
    (h : FromRun M C m R V H X) : Nested M C X := by
  intro r s F G hSucc hF hG c p hParent
  obtain ⟨U,hAtF⟩ := (h.parents r F).mp hF
  obtain ⟨W,hAtG⟩ := (h.parents s G).mp hG
  have hAnc := hRun.ancestor_lower_d hM hC hAtF hAtG (Or.inr hSucc.predecessor_mem)
    (ancestor_direct_d hM hC (hRun.at_numeric_d hM hC hAtG).forest hParent)
  exact h.width.symm ▸ hAnc

theorem Nested.parent_lower_d {M : SetTheory.Structure.{u}} {C : ExpressionData M.Domain}
    {X : Data M.Domain} (_hX : X.Valid M C) (h : Nested M C X)
    {r s F c p : M.Domain} (hSucc : M.SuccessorOf s r) (hF : MemPair M X.parents r F)
    (hParent : ParentAt M X s c p) : Ancestor M C X.width F p c := by
  obtain ⟨G,_,hG,hParent⟩ := hParent
  exact h r s F G hSucc hF hG c p hParent

def nestedFormula {n : Nat} (C : ExpressionData (Project.Term n)) (X : Data (Project.Term n)) : Project.Formula 1 n :=
  Project.Formula.forallMem C.omega (Project.Formula.forallMem C.omega.weaken
    (Project.Formula.forallMem X.forests.weaken.weaken (Project.Formula.forallMem X.forests.weaken.weaken.weaken
      (.imp (successorFormula (.bound 2) (.bound 3))
        (.imp (memPairFormula X.parents.weaken.weaken.weaken.weaken (.bound 3) (.bound 1))
          (.imp (memPairFormula X.parents.weaken.weaken.weaken.weaken (.bound 2) (.bound 0))
            (Project.Formula.forallMem X.width.weaken.weaken.weaken.weaken
              (Project.Formula.forallMem X.width.weaken.weaken.weaken.weaken.weaken
                (.imp (memPairFormula (.bound 2) (.bound 1) (.bound 0))
                  (ancestorFormula C.weaken.weaken.weaken.weaken.weaken.weaken X.width.weaken.weaken.weaken.weaken.weaken.weaken
                    (.bound 3) (.bound 0) (.bound 1)))))))))))

theorem nestedFormula_delta0 {n : Nat} (C : ExpressionData (Project.Term n)) (X : Data (Project.Term n)) :
    (nestedFormula C X).IsDelta0 :=
  .forallMem _ (.forallMem _ (.forallMem _ (.forallMem _ (.imp (successorFormula_delta0 _ _)
    (.imp (memPairFormula_delta0 _ _ _) (.imp (memPairFormula_delta0 _ _ _) (.forallMem _ (.forallMem _
      (.imp (memPairFormula_delta0 _ _ _) (ancestorFormula_delta0 _ _ _ _ _))))))))))

theorem nestedFormula_freeClosed {n : Nat} {C : ExpressionData (Project.Term n)} (hC : C.Closed)
    {X : Data (Project.Term n)} (hX : X.Closed) : (nestedFormula C X).FreeClosed := by
  have hAnc := ancestorFormula_freeClosed hC.weaken.weaken.weaken.weaken.weaken.weaken
    X.width.weaken.weaken.weaken.weaken.weaken.weaken (Project.Term.bound 3) (Project.Term.bound 0) (Project.Term.bound 1)
    (by simp [hX.width]) rfl rfl rfl
  simp [nestedFormula,Project.Formula.forallMem,Definitional.Formula.FreeClosed,successorFormula,memPairFormula,
    codeFormula,pairFormula,Project.Formula.existsMem,hC.omega,hX.forests,hX.parents,hX.width,hAnc]

theorem nestedFormula_iff {M : SetTheory.Structure.{u}} (he : Extensional M) {n : Nat} (e : Env M n)
    (C : ExpressionData (Project.Term n)) (X : Data (Project.Term n)) (hX : (X.eval e).Valid M (C.eval e)) :
    Project.Formula.satisfies e (nestedFormula C X) ↔ Nested M (C.eval e) (X.eval e) := by
  simp only [nestedFormula,Project.Formula.satisfies_forallMem_iff,Project.Formula.satisfies_imp_iff,
    successorFormula_iff he,memPairFormula_iff he,ancestorFormula_iff he,ExpressionData.eval_weaken,Term.eval_weaken]
  constructor
  · intro h r s F G hSucc hF hG c p hParent
    exact h r (hX.parents.bounds he hF).1 s (hX.parents.bounds he hG).1 F (hX.parents.bounds he hF).2
      G (hX.parents.bounds he hG).2 hSucc hF hG c ((hX.forest s G hG).bounds he hParent).1
      p ((hX.forest s G hG).bounds he hParent).2 hParent
  · intro h r _ s _ F _ G _ hSucc hF hG c _ p _ hParent
    exact h r s F G hSucc hF hG c p hParent

end KP1Y.OneYFinite.CopiedMountain
