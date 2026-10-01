import KP1Y.FunctionIteration

/-! 沿有限方形边界枚举 ω² 的一步关系，不依赖尚未实现的内部加乘运算。 -/
namespace KP1Y.Naturals
open YesMetaZFC YesMetaZFC.SetTheory YesMetaZFC.SetTheory.Definitional
open KP1Y.Kuratowski KP1Y.Functions KP1Y.Bounded
universe u

def SquareMove (M : SetTheory.Structure.{u}) (zero x y u v : M.Domain) : Prop :=
  (M.mem y x ∧ u=x ∧ M.SuccessorOf v y) ∨
    (¬M.mem y x ∧ (((∀ z, ¬M.mem z x) ∧ M.SuccessorOf u y ∧ v=zero) ∨
      ∃ p, M.mem p x ∧ M.SuccessorOf x p ∧ u=p ∧ v=y))

def squareMoveFormula {n : Nat} (zero x y u v : Project.Term n) : Project.Formula 1 n :=
  .disj (.conj (.mem y x) (.conj (Project.Formula.extensionalEq u x) (successorFormula v y)))
    (.conj (.neg (.mem y x))
      (.disj (.conj (emptyFormula x) (.conj (successorFormula u y) (Project.Formula.extensionalEq v zero)))
        (Project.Formula.existsMem x (.conj (successorFormula x.weaken (.bound 0))
          (.conj (Project.Formula.extensionalEq u.weaken (.bound 0)) (Project.Formula.extensionalEq v.weaken y.weaken))))))

theorem squareMoveFormula_delta0 {n : Nat} (zero x y u v : Project.Term n) : (squareMoveFormula zero x y u v).IsDelta0 :=
  .disj (.conj (.mem _ _) (.conj (.atom _ _ _) (successorFormula_delta0 _ _)))
    (.conj (.neg (.mem _ _)) (.disj (.conj (emptyFormula_delta0 _) (.conj (successorFormula_delta0 _ _) (.atom _ _ _)))
      (.existsMem _ (.conj (successorFormula_delta0 _ _) (.conj (.atom _ _ _) (.atom _ _ _))))))

theorem squareMoveFormula_iff {M : SetTheory.Structure.{u}} (he : Extensional M) {n : Nat}
    (env : Env M n) (zero x y u v : Project.Term n) :
    Project.Formula.satisfies env (squareMoveFormula zero x y u v) ↔
      SquareMove M (zero.eval env) (x.eval env) (y.eval env) (u.eval env) (v.eval env) := by
  simp only [squareMoveFormula, Project.Formula.satisfies_disj_iff, Project.Formula.satisfies_conj_iff,
    Project.Formula.satisfies_neg_iff, Project.Formula.satisfies_mem_iff,
    Project.Formula.satisfies_extensionalEq_iff_eq he, successorFormula_iff he, emptyFormula_iff,
    Project.Formula.satisfies_existsMem_iff, Definitional.Term.eval_weaken]
  rfl

theorem square_move_total_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {ω zero x y : M.Domain} (hω : M.IsOmega ω) (hZero : M.mem zero ω) (hx : M.mem x ω) (hy : M.mem y ω) :
    ∃ u, M.mem u ω ∧ ∃ v, M.mem v ω ∧ SquareMove M zero x y u v := by
  classical
  by_cases hyx : M.mem y x
  · obtain ⟨v,hvSucc,hv⟩ := hω.1.2 y hy
    exact ⟨x,hx,v,hv,Or.inl ⟨hyx,rfl,hvSucc⟩⟩
  · rcases natural_cases hM hω hx with he | ⟨p,hp,hs⟩
    · obtain ⟨u,huSucc,hu⟩ := hω.1.2 y hy
      exact ⟨u,hu,zero,hZero,Or.inr ⟨hyx,Or.inl ⟨he,huSucc,rfl⟩⟩⟩
    · exact ⟨p,hp,y,hy,Or.inr ⟨hyx,Or.inr ⟨p,hs.predecessor_mem,hs,rfl,rfl⟩⟩⟩

theorem square_move_unique {M : SetTheory.Structure.{u}} (he : Extensional M)
    {zero x y u v u' v' : M.Domain} (hx : M.IsOrdinal x)
    (h : SquareMove M zero x y u v) (h' : SquareMove M zero x y u' v') : u=u' ∧ v=v' := by
  rcases h with ⟨hyx,hu,hv⟩ | ⟨hyx,hRest⟩
  · rcases h' with ⟨_,hu',hv'⟩ | ⟨hyx',_⟩
    · exact ⟨hu.trans hu'.symm,Structure.SuccessorOf.eq he hv hv'⟩
    · exact False.elim (hyx' hyx)
  · rcases h' with ⟨hyx',_,_⟩ | ⟨_,hRest'⟩
    · exact False.elim (hyx hyx')
    · rcases hRest with ⟨hEmpty,hu,hv⟩ | ⟨p,hp,hs,hu,hv⟩
      · rcases hRest' with ⟨_,hu',hv'⟩ | ⟨p,hp,_⟩
        · exact ⟨Structure.SuccessorOf.eq he hu hu',hv.trans hv'.symm⟩
        · exact False.elim (hEmpty p hp)
      · rcases hRest' with ⟨hEmpty,_⟩ | ⟨p',_,hs',hu',hv'⟩
        · exact False.elim (hEmpty p hp)
        · have hpp' := Structure.SuccessorOf.predecessor_eq he (hx.mem hp) hs hs'
          exact ⟨hu.trans (hpp'.trans hu'.symm),hv.trans hv'.symm⟩

def SquareStep (M : SetTheory.Structure.{u}) (ω zero p q : M.Domain) : Prop :=
  ∃ x, M.mem x ω ∧ ∃ y, M.mem y ω ∧ ∃ u, M.mem u ω ∧ ∃ v, M.mem v ω ∧
    Codes M p x y ∧ Codes M q u v ∧ SquareMove M zero x y u v

def squareSchema : Project.Delta0BinarySchema 2 where
  body := Project.Formula.existsMem (.bound 3) (Project.Formula.existsMem (.bound 4)
    (Project.Formula.existsMem (.bound 5) (Project.Formula.existsMem (.bound 6)
      (.conj (codeFormula (.bound 5) (.bound 3) (.bound 2))
        (.conj (codeFormula (.bound 4) (.bound 1) (.bound 0))
          (squareMoveFormula (.bound 6) (.bound 3) (.bound 2) (.bound 1) (.bound 0)))))))
  freeClosed := by
    simp [squareMoveFormula, successorFormula, emptyFormula, codeFormula, pairFormula,
      Project.Formula.existsMem, Project.Formula.forallMem, Definitional.Formula.FreeClosed]
  delta0 := .existsMem _ (.existsMem _ (.existsMem _ (.existsMem _
    (.conj (codeFormula_delta0 _ _ _) (.conj (codeFormula_delta0 _ _ _) (squareMoveFormula_delta0 _ _ _ _ _))))))

theorem squareSchema_iff {M : SetTheory.Structure.{u}} (he : Extensional M) (ω zero p q : M.Domain) :
    KP1Y.Iteration.nextDenote squareSchema ((oneEnv ω).push zero) p q ↔ SquareStep M ω zero p q := by
  simp only [KP1Y.Iteration.nextDenote, squareSchema, Project.Formula.satisfies_existsMem_iff,
    Project.Formula.satisfies_conj_iff, codeFormula_iff he, squareMoveFormula_iff he]
  rfl

theorem square_step_unique_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {ω zero p q q' : M.Domain} (hω : M.IsOmega ω)
    (h : SquareStep M ω zero p q) (h' : SquareStep M ω zero p q') : q=q' := by
  obtain ⟨x,hx,y,_,u,_,v,_,hP,hQ,hMove⟩ := h
  obtain ⟨x',_,y',_,u',_,v',_,hP',hQ',hMove'⟩ := h'
  obtain ⟨hxx',hyy'⟩ := codes_injective hM.1 hP hP'
  subst x'
  subst y'
  obtain ⟨huu',hvv'⟩ := square_move_unique hM.1 ((omega_isOrdinal_d hM hω).mem hx) hMove hMove'
  subst u'
  subst v'
  exact codes_unique hM.1 hQ hQ'

end KP1Y.Naturals
