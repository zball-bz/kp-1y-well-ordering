import KP1Y.SquareEnumeration
import KP1Y.BoundedNaturalInduction

/-! 用内部前向／反向自然数归纳证明方形枚举覆盖 ω²。 -/
namespace KP1Y.Naturals
open YesMetaZFC YesMetaZFC.SetTheory YesMetaZFC.SetTheory.Definitional
open KP1Y.Kuratowski
universe u

private def edgeEnv {M : SetTheory.Structure.{u}} (ω P H n : M.Domain) : Env M 4 :=
  (((oneEnv ω).push P).push H).push n

private def rightEdgeSchema : Project.Delta0UnarySchema 4 where
  body := .imp (Project.Formula.subset (.bound 0) (.bound 1))
    (pairReachedFormula (.bound 4) (.bound 3) (.bound 2) (.bound 1) (.bound 0))
  freeClosed := by
    simp [pairReachedFormula, KP1Y.Iteration.reachedFormula, memPairFormula, codeFormula, pairFormula,
      Project.Formula.existsMem, Project.Formula.forallMem, Definitional.Formula.FreeClosed]
  delta0 := .imp (.atom _ _ _) (pairReachedFormula_delta0 _ _ _ _ _)

private theorem rightEdgeSchema_iff {M : SetTheory.Structure.{u}} (he : Extensional M) (ω P H n y : M.Domain) :
    Project.Formula.satisfies ((edgeEnv ω P H n).push y) rightEdgeSchema.body ↔
      (M.MemberSubset y n → PairReached M ω P H n y) := by
  simp only [rightEdgeSchema, Project.Formula.satisfies_imp_iff, Project.Formula.satisfies_subset_iff, pairReachedFormula_iff he]
  rfl

private def topEdgeSchema : Project.Delta0UnarySchema 4 where
  body := pairReachedFormula (.bound 4) (.bound 3) (.bound 2) (.bound 0) (.bound 1)
  freeClosed := by
    simp [pairReachedFormula, KP1Y.Iteration.reachedFormula, memPairFormula, codeFormula, pairFormula,
      Project.Formula.existsMem, Project.Formula.forallMem, Definitional.Formula.FreeClosed]
  delta0 := pairReachedFormula_delta0 _ _ _ _ _

private theorem topEdgeSchema_iff {M : SetTheory.Structure.{u}} (he : Extensional M) (ω P H n x : M.Domain) :
    Project.Formula.satisfies ((edgeEnv ω P H n).push x) topEdgeSchema.body ↔ PairReached M ω P H x n := by
  rw [topEdgeSchema,pairReachedFormula_iff he]
  rfl

private def cornerSchema : Project.Delta0UnarySchema 4 where
  body := pairReachedFormula (.bound 4) (.bound 3) (.bound 2) (.bound 1) (.bound 0)
  freeClosed := by
    simp [pairReachedFormula, KP1Y.Iteration.reachedFormula, memPairFormula, codeFormula, pairFormula,
      Project.Formula.existsMem, Project.Formula.forallMem, Definitional.Formula.FreeClosed]
  delta0 := pairReachedFormula_delta0 _ _ _ _ _

private theorem cornerSchema_iff {M : SetTheory.Structure.{u}} (he : Extensional M) (ω P H zero n : M.Domain) :
    Project.Formula.satisfies ((edgeEnv ω P H zero).push n) cornerSchema.body ↔ PairReached M ω P H zero n := by
  rw [cornerSchema,pairReachedFormula_iff he]
  rfl

theorem successor_mem_omega {M : SetTheory.Structure.{u}} (he : Extensional M) {ω x y : M.Domain}
    (hω : M.IsOmega ω) (hx : M.mem x ω) (hSucc : M.SuccessorOf y x) : M.mem y ω := by
  obtain ⟨y',hy',hy'ω⟩ := hω.1.2 x hx
  exact (Structure.SuccessorOf.eq he hSucc hy') ▸ hy'ω

theorem square_right_edge_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {ω zero P base H n : M.Domain} (hω : M.IsOmega ω) (hT : SquareTrace M ω zero P base H)
    (hEmpty : ∀ x, ¬M.mem x zero) (hn : M.mem n ω) (hStart : PairReached M ω P H n zero) :
    ∀ y, M.mem y ω → M.MemberSubset y n → PairReached M ω P H n y := by
  have hAll := natural_induction_d hM rightEdgeSchema.toUnarySchema (edgeEnv ω P H n) hω
    (fun e he => (rightEdgeSchema_iff hM.1 ω P H n e).mpr (by
      intro _
      have heq := hM.1.eq_of_same_members e zero (fun x => iff_of_false (he x) (hEmpty x))
      exact heq ▸ hStart))
    (fun y hy ih z hz => (rightEdgeSchema_iff hM.1 ω P H n z).mpr (by
      intro hzSub
      have hySub : M.MemberSubset y n := fun x hx => hzSub x ((hz x).mpr (Or.inl hx))
      have hReach := (rightEdgeSchema_iff hM.1 ω P H n y).mp ih hySub
      exact pair_reached_up_d hM hω hT hn hy (successor_mem_omega hM.1 hω hy hz)
        (hzSub y hz.predecessor_mem) hz hReach))
  exact fun y hy => (rightEdgeSchema_iff hM.1 ω P H n y).mp (hAll y hy)

theorem square_top_edge_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {ω zero P base H n : M.Domain} (hω : M.IsOmega ω) (hT : SquareTrace M ω zero P base H)
    (hn : M.mem n ω) (hTop : PairReached M ω P H n n) :
    ∀ x, (x=n ∨ M.mem x n) → PairReached M ω P H x n := by
  have hAll := bounded_backward_induction_d hM topEdgeSchema (edgeEnv ω P H n) hω hn
    ((topEdgeSchema_iff hM.1 ω P H n n).mpr hTop) (by
      intro p hp q hqω hSucc hSub hReach
      have hpω := (omega_isOrdinal_d hM hω).transitive n hn p hp
      have hnq : ¬M.mem n q := fun h => SetTheory.KP.mem_irrefl_d (KP1Y.models_weakKP hM) n (hSub n h)
      exact (topEdgeSchema_iff hM.1 ω P H n p).mpr
        (pair_reached_left_d hM hω hT hqω hn hpω hnq hSucc ((topEdgeSchema_iff hM.1 ω P H n q).mp hReach)))
  exact fun x hx => (topEdgeSchema_iff hM.1 ω P H n x).mp (hAll x hx)

theorem square_all_corners_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {ω zero P base H : M.Domain} (hω : M.IsOmega ω) (hT : SquareTrace M ω zero P base H)
    (hZero : M.mem zero ω) (hEmpty : ∀ x, ¬M.mem x zero) : ∀ n, M.mem n ω → PairReached M ω P H zero n := by
  have hAll := natural_induction_d hM cornerSchema.toUnarySchema (edgeEnv ω P H zero) hω
    (fun e he => (cornerSchema_iff hM.1 ω P H zero e).mpr (by
      have heq := hM.1.eq_of_same_members e zero (fun x => iff_of_false (he x) (hEmpty x))
      subst e
      exact pair_reached_zero hT hZero hEmpty))
    (fun n hn ih m hm => (cornerSchema_iff hM.1 ω P H zero m).mpr (by
      have hmω := successor_mem_omega hM.1 hω hn hm
      have hStart := pair_reached_corner_d hM hω hT hZero hEmpty hn hmω hm ((cornerSchema_iff hM.1 ω P H zero n).mp ih)
      have hDiag := square_right_edge_d hM hω hT hEmpty hmω hStart m hmω (fun _ h => h)
      have hZeroLe := ordinal_subset_cases_d hM (Structure.IsOrdinal.of_no_members hEmpty)
        ((omega_isOrdinal_d hM hω).mem hmω) (fun x hx => False.elim (hEmpty x hx))
      exact square_top_edge_d hM hω hT hmω hDiag zero hZeroLe))
  exact fun n hn => (cornerSchema_iff hM.1 ω P H zero n).mp (hAll n hn)

theorem square_all_pairs_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {ω zero P base H : M.Domain} (hω : M.IsOmega ω) (hT : SquareTrace M ω zero P base H)
    (hZero : M.mem zero ω) (hEmpty : ∀ x, ¬M.mem x zero) :
    ∀ x, M.mem x ω → ∀ y, M.mem y ω → PairReached M ω P H x y := by
  have hCorners := square_all_corners_d hM hω hT hZero hEmpty
  have hStart : ∀ x, M.mem x ω → PairReached M ω P H x zero := by
    intro x hx
    rcases natural_cases hM hω hx with he | ⟨p,hp,hs⟩
    · have heq := hM.1.eq_of_same_members x zero (fun y => iff_of_false (he y) (hEmpty y))
      subst x
      exact pair_reached_zero hT hZero hEmpty
    · exact pair_reached_corner_d hM hω hT hZero hEmpty hp hx hs (hCorners p hp)
  intro x hx y hy
  have hωOrd := omega_isOrdinal_d hM hω
  rcases hωOrd.wellOrder.linear.compare x hx y hy with he | hxy | hyx
  · have hEq := hM.1.eq_of_same_members x y he
    subst y
    exact square_right_edge_d hM hω hT hEmpty hx (hStart x hx) x hx (fun _ h => h)
  · have hDiag := square_right_edge_d hM hω hT hEmpty hy (hStart y hy) y hy (fun _ h => h)
    exact square_top_edge_d hM hω hT hy hDiag x (Or.inr hxy)
  · exact square_right_edge_d hM hω hT hEmpty hx (hStart x hx) y hy ((hωOrd.mem hx).transitive y hyx)

end KP1Y.Naturals
