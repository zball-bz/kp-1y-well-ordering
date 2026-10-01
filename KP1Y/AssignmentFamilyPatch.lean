import KP1Y.FrameAgreement

/-! 沿单射变量名图同时写入一个实际值图，保留所有其他变量；只用Δ₀分离。 -/
namespace KP1Y.Assignments
open YesMetaZFC YesMetaZFC.SetTheory YesMetaZFC.SetTheory.Definitional
open KP1Y.Kuratowski KP1Y.Functions KP1Y.Satisfaction
universe u

private def constantSchema : Project.Delta0BinarySchema 1 where
  body := Project.Formula.extensionalEq (.bound 0) (.bound 2)
  freeClosed := by simp
  delta0 := .atom _ _ _

theorem constant_assignment_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory) (bound A : M.Domain)
    {zero : M.Domain} (hZero : M.mem zero A) : ∃ s, Graph M s bound A ∧ ∀ i, M.mem i bound → MemPair M s i zero := by
  obtain ⟨s,hSupport,hRaw⟩ := relation_comprehension_d hM constantSchema (oneEnv zero) bound A
  have hEq (i x : M.Domain) : Project.Formula.satisfies (((oneEnv zero).push i).push x) constantSchema.body ↔ x=zero := by
    rw [constantSchema,Project.Formula.satisfies_extensionalEq_iff_eq hM.1]
    rfl
  have hRows (i x : M.Domain) : MemPair M s i x ↔ M.mem i bound ∧ M.mem x A ∧ x=zero := by
    simpa only [hEq] using hRaw i x
  exact ⟨s,⟨hSupport,fun i hi => ⟨zero,hZero,(hRows i zero).mpr ⟨hi,hZero,rfl⟩⟩,
    fun i x y hix hiy => ((hRows i x).mp hix).2.2.trans ((hRows i y).mp hiy).2.2.symm⟩,
    fun i hi => (hRows i zero).mpr ⟨hi,hZero,rfl⟩⟩

private def patchSchema : Project.Delta0BinarySchema 4 where
  body := .disj (Project.Formula.existsMem (.bound 2)
      (.conj (memPairFormula (.bound 4) (.bound 0) (.bound 2)) (memPairFormula (.bound 5) (.bound 0) (.bound 1))))
    (.conj (.neg (touchedFormula (.bound 3) (.bound 2) (.bound 1))) (memPairFormula (.bound 5) (.bound 1) (.bound 0)))
  freeClosed := by
    simp [touchedFormula,memPairFormula,codeFormula,pairFormula,Project.Formula.existsMem,Project.Formula.forallMem,Definitional.Formula.FreeClosed]
  delta0 := .disj (.existsMem _ (.conj (memPairFormula_delta0 _ _ _) (memPairFormula_delta0 _ _ _)))
    (.conj (.neg (touchedFormula_delta0 _ _ _)) (memPairFormula_delta0 _ _ _))

theorem patch_assignment_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {s vars values n bound A : M.Domain} (hS : Graph M s bound A) (hVars : Graph M vars n bound)
    (hInj : ∀ i j v, MemPair M vars i v → MemPair M vars j v → i=j) (hValues : Graph M values n A) :
    ∃ t, AgreeOutside M vars n s t bound A ∧ TupleValue M values vars t n bound A := by
  have hφ (j x : M.Domain) :
      Project.Formula.satisfies ((((((oneEnv s).push values).push vars).push n).push j).push x) patchSchema.body ↔
        ((∃ i, M.mem i n ∧ MemPair M vars i j ∧ MemPair M values i x) ∨ (¬Touched M vars n j ∧ MemPair M s j x)) := by
    simp only [patchSchema,Project.Formula.satisfies_disj_iff,Project.Formula.satisfies_existsMem_iff,
      Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_neg_iff,memPairFormula_iff hM.1,touchedFormula_iff hM.1]
    rfl
  obtain ⟨t,hSupport,hRaw⟩ := relation_comprehension_d hM patchSchema ((((oneEnv s).push values).push vars).push n) bound A
  have hRows (j x : M.Domain) : MemPair M t j x ↔ M.mem j bound ∧ M.mem x A ∧
      ((∃ i, M.mem i n ∧ MemPair M vars i j ∧ MemPair M values i x) ∨ (¬Touched M vars n j ∧ MemPair M s j x)) := by
    simpa only [hφ] using hRaw j x
  have hT : Graph M t bound A := by
    classical
    refine ⟨hSupport,?_,?_⟩
    · intro j hj
      by_cases hTouch : Touched M vars n j
      · obtain ⟨i,hi,hij⟩ := hTouch
        obtain ⟨x,hx,hix⟩ := hValues.total i hi
        exact ⟨x,hx,(hRows j x).mpr ⟨hj,hx,Or.inl ⟨i,hi,hij,hix⟩⟩⟩
      · obtain ⟨x,hx,hjx⟩ := hS.total j hj
        exact ⟨x,hx,(hRows j x).mpr ⟨hj,hx,Or.inr ⟨hTouch,hjx⟩⟩⟩
    · intro j x y hjx hjy
      rcases ((hRows j x).mp hjx).2.2 with ⟨i,hi,hij,hix⟩ | ⟨hNot,hjx⟩
      · rcases ((hRows j y).mp hjy).2.2 with ⟨i',_,hi'j,hi'y⟩ | ⟨hNot,_⟩
        · have hii' := hInj i i' j hij hi'j
          subst i'
          exact hValues.unique i x y hix hi'y
        · exact False.elim (hNot ⟨i,hi,hij⟩)
      · rcases ((hRows j y).mp hjy).2.2 with ⟨i,hi,hij,_⟩ | ⟨_,hjy⟩
        · exact False.elim (hNot ⟨i,hi,hij⟩)
        · exact hS.unique j x y hjx hjy
  refine ⟨t,⟨hS,hT,?_⟩,⟨hVars,hT,hValues,?_⟩⟩
  · intro j hj hNot x hx
    constructor
    · intro hsx
      exact (hRows j x).mpr ⟨hj,hx,Or.inr ⟨hNot,hsx⟩⟩
    · intro htx
      rcases ((hRows j x).mp htx).2.2 with ⟨i,hi,hij,_⟩ | ⟨_,hsx⟩
      · exact False.elim (hNot ⟨i,hi,hij⟩)
      · exact hsx
  · intro i hi j hj x hx hij
    constructor
    · intro hix
      exact (hRows j x).mpr ⟨hj,hx,Or.inl ⟨i,hi,hij,hix⟩⟩
    · intro hjx
      rcases ((hRows j x).mp hjx).2.2 with ⟨i',_,hi'j,hi'x⟩ | ⟨hNot,_⟩
      · have hii' := hInj i i' j hij hi'j
        subst i'
        exact hi'x
      · exact False.elim (hNot ⟨i,hi,hij⟩)

theorem TupleValue.preserve_outside {M : SetTheory.Structure.{u}} {values vars other n no s t bound A : M.Domain}
    (h : TupleValue M values vars s n bound A) (hFrame : AgreeOutside M other no s t bound A)
    (hDisjoint : ∀ i j, MemPair M vars i j → ¬Touched M other no j) : TupleValue M values vars t n bound A := by
  refine ⟨h.variables,hFrame.target,h.values,?_⟩
  intro i hi j hj x hx hij
  exact (h.rows i hi j hj x hx hij).trans (hFrame.rows j hj (hDisjoint i j hij) x hx)

end KP1Y.Assignments
