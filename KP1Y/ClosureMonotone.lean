import KP1Y.ClosureFamily

/-! 用对象自然数归纳证明任意较早枚举器的像包含于较晚枚举器的像。 -/
namespace KP1Y.Closure
open YesMetaZFC YesMetaZFC.SetTheory YesMetaZFC.SetTheory.Definitional
open KP1Y.Kuratowski KP1Y.Iteration
universe u

def RangeIncluded (M : SetTheory.Structure.{u}) (ω A E F : M.Domain) : Prop :=
  ∀ x, M.mem x A → Reached M ω E x → Reached M ω F x

def rangeIncludedFormula {n : Nat} (ω A E F : Project.Term n) : Project.Formula 1 n :=
  Project.Formula.forallMem A (.imp (reachedFormula ω.weaken E.weaken (.bound 0))
    (reachedFormula ω.weaken F.weaken (.bound 0)))

theorem rangeIncludedFormula_iff {M : SetTheory.Structure.{u}} (he : Extensional M) {n : Nat}
    (env : Env M n) (ω A E F : Project.Term n) :
    Project.Formula.satisfies env (rangeIncludedFormula ω A E F) ↔ RangeIncluded M (ω.eval env) (A.eval env) (E.eval env) (F.eval env) := by
  simp only [rangeIncludedFormula, Project.Formula.satisfies_forallMem_iff,
    Project.Formula.satisfies_imp_iff, reachedFormula_iff he, Definitional.Term.eval_weaken]
  rfl

private def monotoneSchema : Project.UnarySchema 4 where
  body := Project.Formula.forallMem (.bound 4) (.imp
    (.disj (Project.Formula.extensionalEq (.bound 0) (.bound 1)) (.mem (.bound 0) (.bound 1)))
    (Project.Formula.forallMem (.bound 2) (.imp (memPairFormula (.bound 4) (.bound 1) (.bound 0))
      (Project.Formula.forallMem (.bound 3) (.imp (memPairFormula (.bound 5) (.bound 3) (.bound 0))
        (rangeIncludedFormula (.bound 7) (.bound 6) (.bound 1) (.bound 0)))))))
  freeClosed := by
    simp [rangeIncludedFormula, reachedFormula, memPairFormula, codeFormula, pairFormula,
      Project.Formula.existsMem, Project.Formula.forallMem, Definitional.Formula.FreeClosed]

private def monotoneEnv {M : SetTheory.Structure.{u}} (ω A R V : M.Domain) : Env M 4 :=
  (((oneEnv ω).push A).push R).push V

private theorem monotoneSchema_iff {M : SetTheory.Structure.{u}} (he : Extensional M) (ω A R V top : M.Domain) :
    Project.Formula.satisfies ((monotoneEnv ω A R V).push top) monotoneSchema.body ↔
      ∀ i, M.mem i ω → (i=top ∨ M.mem i top) → ∀ E, M.mem E V → MemPair M R i E →
        ∀ F, M.mem F V → MemPair M R top F → RangeIncluded M ω A E F := by
  simp only [monotoneSchema, Project.Formula.satisfies_forallMem_iff, Project.Formula.satisfies_imp_iff,
    Project.Formula.satisfies_disj_iff, Project.Formula.satisfies_mem_iff,
    Project.Formula.satisfies_extensionalEq_iff_eq he, memPairFormula_iff he, rangeIncludedFormula_iff he]
  rfl

theorem family_monotone_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : Data M.Domain} (hC : Valid M C) {base R V : M.Domain} (hF : EnumeratorFamily M C base R V) :
    ∀ top, M.mem top C.omega → ∀ i, M.mem i C.omega → (i=top ∨ M.mem i top) →
      ∀ E F, MemPair M R i E → MemPair M R top F → RangeIncluded M C.omega C.carrier E F := by
  have hAll := KP1Y.Naturals.natural_induction_d hM monotoneSchema (monotoneEnv C.omega C.carrier R V) hC.omega
    (fun zero hEmpty => (monotoneSchema_iff hM.1 C.omega C.carrier R V zero).mpr (by
      intro i _ hi E _ hE F _ hTop
      rcases hi with he | hi
      · subst i
        have hEF := hF.graph.unique zero E F hE hTop
        subst E
        exact fun _ _ h => h
      · exact False.elim (hEmpty i hi)))
    (fun n hn ih next hSucc => (monotoneSchema_iff hM.1 C.omega C.carrier R V next).mpr (by
      intro i hiω hi E hEV hE F _ hTop
      rcases hi with he | hi
      · subst i
        have hEF := hF.graph.unique next E F hE hTop
        subst E
        exact fun _ _ h => h
      · have hLe : i=n ∨ M.mem i n := by
          rcases (hSucc i).mp hi with hin | he
          · exact Or.inr hin
          · exact Or.inl (hM.1.eq_of_same_members i n he)
        obtain ⟨G,hGV,hG⟩ := hF.graph.total n hn
        have hOld := (monotoneSchema_iff hM.1 C.omega C.carrier R V n).mp ih i hiω hLe E hEV hE G hGV hG
        have hNext := hF.step n next G F hSucc hG hTop
        intro x hx hReach
        exact next_enumerator_preserves_d hM hC (hF.values n hn G hG) hNext x (hOld x hx hReach)))
  intro top hTop i hi hLe E F hE hF'
  exact (monotoneSchema_iff hM.1 C.omega C.carrier R V top).mp (hAll top hTop) i hi hLe
    E (hF.graph.bounds hM.1 hE).2 hE F (hF.graph.bounds hM.1 hF').2 hF'

end KP1Y.Closure
