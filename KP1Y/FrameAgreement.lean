import KP1Y.CompileQuantifier

/-! 有限量词块的赋值语义：恰好允许改变给定变量序列中已经出现的位置。 -/
namespace KP1Y.Satisfaction
open YesMetaZFC YesMetaZFC.SetTheory YesMetaZFC.SetTheory.Definitional
open KP1Y.Kuratowski KP1Y.Functions KP1Y.Assignments
universe u

def Touched (M : SetTheory.Structure.{u}) (vars stage j : M.Domain) : Prop :=
  ∃ k, M.mem k stage ∧ MemPair M vars k j

def touchedFormula {n : Nat} (vars stage j : Project.Term n) : Project.Formula 1 n :=
  Project.Formula.existsMem stage (memPairFormula vars.weaken (.bound 0) j.weaken)

theorem touchedFormula_delta0 {n : Nat} (vars stage j : Project.Term n) : (touchedFormula vars stage j).IsDelta0 :=
  .existsMem _ (memPairFormula_delta0 _ _ _)

theorem touchedFormula_iff {M : SetTheory.Structure.{u}} (he : Extensional M) {n : Nat}
    (env : Env M n) (vars stage j : Project.Term n) :
    Project.Formula.satisfies env (touchedFormula vars stage j) ↔ Touched M (vars.eval env) (stage.eval env) (j.eval env) := by
  simp only [touchedFormula, Project.Formula.satisfies_existsMem_iff, memPairFormula_iff he, Definitional.Term.eval_weaken]
  rfl

structure AgreeOutside (M : SetTheory.Structure.{u}) (vars stage s t bound A : M.Domain) : Prop where
  source : Graph M s bound A
  target : Graph M t bound A
  rows : ∀ j, M.mem j bound → ¬Touched M vars stage j → ∀ a, M.mem a A → (MemPair M s j a ↔ MemPair M t j a)

def agreeOutsideFormula {n : Nat} (vars stage s t bound A : Project.Term n) : Project.Formula 1 n :=
  .conj (graphFormula s bound A) (.conj (graphFormula t bound A)
    (Project.Formula.forallMem bound (.imp (.neg (touchedFormula vars.weaken stage.weaken (.bound 0)))
      (Project.Formula.forallMem A.weaken (.iff (memPairFormula s.weaken.weaken (.bound 1) (.bound 0))
        (memPairFormula t.weaken.weaken (.bound 1) (.bound 0)))))))

theorem agreeOutsideFormula_delta0 {n : Nat} (vars stage s t bound A : Project.Term n) :
    (agreeOutsideFormula vars stage s t bound A).IsDelta0 :=
  .conj (graphFormula_delta0 _ _ _) (.conj (graphFormula_delta0 _ _ _)
    (.forallMem _ (.imp (.neg (touchedFormula_delta0 _ _ _))
      (.forallMem _ (.iff (memPairFormula_delta0 _ _ _) (memPairFormula_delta0 _ _ _))))))

theorem agreeOutsideFormula_iff {M : SetTheory.Structure.{u}} (he : Extensional M) {n : Nat}
    (env : Env M n) (vars stage s t bound A : Project.Term n) :
    Project.Formula.satisfies env (agreeOutsideFormula vars stage s t bound A) ↔
      AgreeOutside M (vars.eval env) (stage.eval env) (s.eval env) (t.eval env) (bound.eval env) (A.eval env) := by
  simp only [agreeOutsideFormula, Project.Formula.satisfies_conj_iff, graphFormula_iff he,
    Project.Formula.satisfies_forallMem_iff, Project.Formula.satisfies_imp_iff,
    Project.Formula.satisfies_neg_iff, Project.Formula.satisfies_iff_iff,
    touchedFormula_iff he, memPairFormula_iff he, Definitional.Term.eval_weaken]
  exact ⟨fun h => ⟨h.1,h.2.1,h.2.2⟩,fun h => ⟨h.source,h.target,h.rows⟩⟩

theorem touched_successor {M : SetTheory.Structure.{u}} (he : Extensional M)
    {vars N bound stage next v j : M.Domain} (hVars : Graph M vars N bound)
    (hAt : MemPair M vars stage v) (hSucc : M.SuccessorOf next stage) :
    Touched M vars next j ↔ Touched M vars stage j ∨ j=v := by
  constructor
  · rintro ⟨k,hk,hkj⟩
    rcases (hSucc k).mp hk with hk | hk
    · exact Or.inl ⟨k,hk,hkj⟩
    · have hEq := he.eq_of_same_members k stage hk
      subst k
      exact Or.inr (hVars.unique stage j v hkj hAt)
  · rintro (⟨k,hk,hkj⟩ | hEq)
    · exact ⟨k,(hSucc k).mpr (Or.inl hk),hkj⟩
    · subst j
      exact ⟨stage,hSucc.predecessor_mem,hAt⟩

theorem agreeOutside_refl {M : SetTheory.Structure.{u}} {vars stage s bound A : M.Domain}
    (hS : Graph M s bound A) : AgreeOutside M vars stage s s bound A :=
  ⟨hS,hS,fun _ _ _ _ _ => Iff.rfl⟩

theorem agreeOutside_empty_eq {M : SetTheory.Structure.{u}} (he : Extensional M)
    {vars stage s t bound A : M.Domain} (hEmpty : ∀ k, ¬M.mem k stage)
    (h : AgreeOutside M vars stage s t bound A) : s=t := by
  classical
  apply h.source.ext he h.target
  intro j hj a
  by_cases ha : M.mem a A
  · exact h.rows j hj (fun ⟨k,hk,_⟩ => hEmpty k hk) a ha
  · exact iff_of_false (fun hq => ha (h.source.bounds he hq).2) (fun hq => ha (h.target.bounds he hq).2)

theorem factor_frame_update_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {vars N bound stage next v s t A : M.Domain} (hVars : Graph M vars N bound)
    (hAt : MemPair M vars stage v) (hSucc : M.SuccessorOf next stage)
    (h : AgreeOutside M vars next s t bound A) :
    ∃ x, M.mem x A ∧ ∃ u, Updated M u s bound A v x ∧ AgreeOutside M vars stage u t bound A := by
  classical
  have hv := (hVars.bounds hM.1 hAt).2
  obtain ⟨x,hx,htvx⟩ := h.target.total v hv
  obtain ⟨u,hu⟩ := update_exists_d hM h.source hx
  refine ⟨x,hx,u,hu,⟨hu.graph,h.target,?_⟩⟩
  intro j hj hNot a ha
  by_cases hjv : j=v
  · subst j
    constructor
    · intro hua
      rcases (hu.rows v hv a ha).mp hua with hNew | hOld
      · have hax := hNew.2
        subst a
        exact htvx
      · exact False.elim (hOld.1 rfl)
    · intro hta
      exact (hu.rows v hv a ha).mpr (Or.inl ⟨rfl,h.target.unique v a x hta htvx⟩)
  · have hNotNext : ¬Touched M vars next j := by
      intro hTouch
      rcases (touched_successor hM.1 hVars hAt hSucc).mp hTouch with hOld | hEq
      · exact hNot hOld
      · exact hjv hEq
    have hUS : MemPair M u j a ↔ MemPair M s j a :=
      (hu.rows j hj a ha).trans
        ⟨fun hq => hq.elim (fun hq => False.elim (hjv hq.1)) And.right,fun hq => Or.inr ⟨hjv,hq⟩⟩
    exact hUS.trans (h.rows j hj hNotNext a ha)

theorem merge_frame_update {M : SetTheory.Structure.{u}} (he : Extensional M)
    {vars N bound stage next v x s u t A : M.Domain} (hVars : Graph M vars N bound)
    (hAt : MemPair M vars stage v) (hSucc : M.SuccessorOf next stage)
    (hS : Graph M s bound A) (hu : Updated M u s bound A v x)
    (h : AgreeOutside M vars stage u t bound A) : AgreeOutside M vars next s t bound A := by
  refine ⟨hS,h.target,?_⟩
  intro j hj hNot a ha
  have hOld : ¬Touched M vars stage j := fun hjOld =>
    hNot ((touched_successor he hVars hAt hSucc).mpr (Or.inl hjOld))
  have hNe : j≠v := fun hjv => hNot ((touched_successor he hVars hAt hSucc).mpr (Or.inr hjv))
  have hSU : MemPair M s j a ↔ MemPair M u j a := by
    constructor
    · intro hq
      exact (hu.rows j hj a ha).mpr (Or.inr ⟨hNe,hq⟩)
    · intro hq
      rcases (hu.rows j hj a ha).mp hq with hNew | hPrev
      · exact False.elim (hNe hNew.1)
      · exact hPrev.2
  exact hSU.trans (h.rows j hj hOld a ha)

end KP1Y.Satisfaction
