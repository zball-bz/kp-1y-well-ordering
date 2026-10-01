import KP1Y.ReflectionLabels

/-! 内部有限标签图的相邻递增蕴含全体递增，用对象自然数归纳而非宿主Nat归纳。 -/
namespace KP1Y.Reflection
open YesMetaZFC YesMetaZFC.SetTheory YesMetaZFC.SetTheory.Definitional
open KP1Y.Kuratowski KP1Y.Functions
universe u

def AdjacentIncreasing (M : SetTheory.Structure.{u}) (f m A : M.Domain) : Prop :=
  ∀ i, M.mem i m → ∀ j, M.mem j m → M.SuccessorOf j i → ∀ x, M.mem x A → ∀ y, M.mem y A →
    MemPair M f i x → MemPair M f j y → M.mem x y

def Increasing (M : SetTheory.Structure.{u}) (f m A : M.Domain) : Prop :=
  ∀ i, M.mem i m → ∀ j, M.mem j m → M.mem i j → ∀ x, M.mem x A → ∀ y, M.mem y A →
    MemPair M f i x → MemPair M f j y → M.mem x y

private def prefixIncreasingSchema : Project.Delta0UnarySchema 3 where
  body := .imp (.mem (.bound 0) (.bound 1)) (Project.Formula.forallMem (.bound 2)
    (.imp (memPairFormula (.bound 4) (.bound 1) (.bound 0))
      (Project.Formula.forallMem (.bound 1) (Project.Formula.forallMem (.bound 4)
        (.imp (memPairFormula (.bound 6) (.bound 1) (.bound 0)) (.mem (.bound 0) (.bound 2)))))))
  freeClosed := by
    simp [memPairFormula,codeFormula,pairFormula,Project.Formula.existsMem,Project.Formula.forallMem,Definitional.Formula.FreeClosed]
  delta0 := .imp (.mem _ _) (.forallMem _ (.imp (memPairFormula_delta0 _ _ _) (.forallMem _ (.forallMem _
    (.imp (memPairFormula_delta0 _ _ _) (.mem _ _))))))

private theorem prefixIncreasingSchema_iff {M : SetTheory.Structure.{u}} (he : Extensional M) (f m A j : M.Domain) :
    Project.Formula.satisfies ((((oneEnv f).push A).push m).push j) prefixIncreasingSchema.body ↔
      (M.mem j m → ∀ x, M.mem x A → MemPair M f j x → ∀ i, M.mem i j → ∀ y, M.mem y A → MemPair M f i y → M.mem y x) := by
  simp only [prefixIncreasingSchema,Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_mem_iff,
    Project.Formula.satisfies_forallMem_iff,memPairFormula_iff he]
  rfl

theorem increasing_of_adjacent_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory) {ω m f A : M.Domain}
    (hω : M.IsOmega ω) (hm : M.mem m ω) (hA : M.IsOrdinal A) (hF : Graph M f m A)
    (hAdj : AdjacentIncreasing M f m A) : Increasing M f m A := by
  have hOrdω := KP1Y.Naturals.omega_isOrdinal_d hM hω
  have hOrdM := hOrdω.mem hm
  have hAll := KP1Y.Naturals.natural_induction_d hM prefixIncreasingSchema.toUnarySchema (((oneEnv f).push A).push m) hω
    (by
      intro zero hZero
      apply (prefixIncreasingSchema_iff hM.1 f m A zero).mpr
      intro _ x _ _ i hi
      exact False.elim (hZero i hi))
    (by
      intro p _ ih j hs
      apply (prefixIncreasingSchema_iff hM.1 f m A j).mpr
      intro hj x hx hJx i hij y hy hIy
      have hp := hOrdM.transitive j hj p hs.predecessor_mem
      obtain ⟨z,hz,hPz⟩ := hF.total p hp
      have hzx := hAdj p hp j hj hs z hz x hx hPz hJx
      rcases (hs i).mp hij with hip | hSame
      · have hyz := (prefixIncreasingSchema_iff hM.1 f m A p).mp ih hp z hz hPz i hip y hy hIy
        exact (hA.mem hx).transitive z hzx y hyz
      · have hip := hM.1.eq_of_same_members i p hSame
        subst i
        have hyz := hF.unique p y z hIy hPz
        exact hyz ▸ hzx)
  intro i _ j hj hij x hx y hy hIx hJy
  have hjω := hOrdω.transitive m hm j hj
  exact (prefixIncreasingSchema_iff hM.1 f m A j).mp (hAll j hjω) hj y hy hJy i hij x hx hIx

theorem increasing_iff_adjacent_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory) {ω m f A : M.Domain}
    (hω : M.IsOmega ω) (hm : M.mem m ω) (hA : M.IsOrdinal A) (hF : Graph M f m A) :
    Increasing M f m A ↔ AdjacentIncreasing M f m A :=
  ⟨fun h i hi j hj hs x hx y hy hiX hjY => h i hi j hj hs.predecessor_mem x hx y hy hiX hjY,
    increasing_of_adjacent_d hM hω hm hA hF⟩

end KP1Y.Reflection
