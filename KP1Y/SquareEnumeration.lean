import KP1Y.SquareEnumerationStep

/-! 在模型内部实际运行方形边界枚举，得到 ω 长函数和有界可达性谓词。 -/
namespace KP1Y.Naturals
open YesMetaZFC YesMetaZFC.SetTheory YesMetaZFC.SetTheory.Definitional
open KP1Y.Kuratowski KP1Y.Functions KP1Y.Iteration
universe u

structure SquareTrace (M : SetTheory.Structure.{u}) (ω zero P base H : M.Domain) : Prop where
  pairs : IsProduct M P ω ω
  start : Codes M base zero zero
  iterator : Iterator M (SquareStep M ω zero) ω P base H

theorem square_trace_exists_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {ω zero : M.Domain} (hω : M.IsOmega ω) (hZero : M.mem zero ω) :
    ∃ P base H, SquareTrace M ω zero P base H := by
  obtain ⟨P,hP⟩ := product_exists hM ω ω
  obtain ⟨base,hBase⟩ := codes_total hM zero zero
  have hBaseP := (hP base).mpr ⟨zero,hZero,zero,hZero,hBase⟩
  have hTotal : ∀ p, M.mem p P → ∃ q, M.mem q P ∧ nextDenote squareSchema ((oneEnv ω).push zero) p q := by
    intro p hp
    obtain ⟨x,hx,y,hy,hCode⟩ := (hP p).mp hp
    obtain ⟨u,hu,v,hv,hMove⟩ := square_move_total_d hM hω hZero hx hy
    obtain ⟨q,hCode'⟩ := codes_total hM u v
    exact ⟨q,(hP q).mpr ⟨u,hu,v,hv,hCode'⟩,(squareSchema_iff hM.1 ω zero p q).mpr
      ⟨x,hx,y,hy,u,hu,v,hv,hCode,hCode',hMove⟩⟩
  have hUnique : ∀ p, M.mem p P → ∀ q, M.mem q P → ∀ r, M.mem r P →
      nextDenote squareSchema ((oneEnv ω).push zero) p q → nextDenote squareSchema ((oneEnv ω).push zero) p r → q=r := by
    intro p _ q _ r _ hpq hpr
    exact square_step_unique_d hM hω ((squareSchema_iff hM.1 ω zero p q).mp hpq) ((squareSchema_iff hM.1 ω zero p r).mp hpr)
  obtain ⟨H,hH⟩ := iterator_exists_d hM squareSchema ((oneEnv ω).push zero) hω hBaseP hTotal hUnique
  exact ⟨P,base,H,hP,hBase,⟨hH.graph,hH.initial,fun i j x y hs hix hjy =>
    (squareSchema_iff hM.1 ω zero x y).mp (hH.transition i j x y hs hix hjy)⟩⟩

def PairReached (M : SetTheory.Structure.{u}) (ω P H x y : M.Domain) : Prop :=
  ∃ p, M.mem p P ∧ Codes M p x y ∧ Reached M ω H p

def pairReachedFormula {n : Nat} (ω P H x y : Project.Term n) : Project.Formula 1 n :=
  Project.Formula.existsMem P (.conj (codeFormula (.bound 0) x.weaken y.weaken)
    (reachedFormula ω.weaken H.weaken (.bound 0)))

theorem pairReachedFormula_delta0 {n : Nat} (ω P H x y : Project.Term n) : (pairReachedFormula ω P H x y).IsDelta0 :=
  .existsMem _ (.conj (codeFormula_delta0 _ _ _) (reachedFormula_delta0 _ _ _))

theorem pairReachedFormula_iff {M : SetTheory.Structure.{u}} (he : Extensional M) {n : Nat}
    (env : Env M n) (ω P H x y : Project.Term n) :
    Project.Formula.satisfies env (pairReachedFormula ω P H x y) ↔
      PairReached M (ω.eval env) (P.eval env) (H.eval env) (x.eval env) (y.eval env) := by
  simp only [pairReachedFormula, Project.Formula.satisfies_existsMem_iff, Project.Formula.satisfies_conj_iff,
    codeFormula_iff he, reachedFormula_iff he, Definitional.Term.eval_weaken]
  rfl

theorem pair_reached_step_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {ω zero P base H x y u v : M.Domain} (hω : M.IsOmega ω) (hT : SquareTrace M ω zero P base H)
    (hx : M.mem x ω) (hy : M.mem y ω) (hu : M.mem u ω) (hv : M.mem v ω)
    (hReached : PairReached M ω P H x y) (hMove : SquareMove M zero x y u v) : PairReached M ω P H u v := by
  obtain ⟨p,_,hCode,hReach⟩ := hReached
  obtain ⟨q,hCode'⟩ := codes_total hM u v
  have hq := (hT.pairs q).mpr ⟨u,hu,v,hv,hCode'⟩
  have hStep : SquareStep M ω zero p q := ⟨x,hx,y,hy,u,hu,v,hv,hCode,hCode',hMove⟩
  exact ⟨q,hq,hCode',reached_next_d hM.1 hω hT.iterator
    (fun _ _ _ _ _ _ hs hs' => square_step_unique_d hM hω hs hs') hReach hq hStep⟩

theorem pair_reached_zero {M : SetTheory.Structure.{u}} {ω zero P base H : M.Domain}
    (hT : SquareTrace M ω zero P base H) (hZero : M.mem zero ω) (hEmpty : ∀ x, ¬M.mem x zero) :
    PairReached M ω P H zero zero :=
  ⟨base,(hT.pairs base).mpr ⟨zero,hZero,zero,hZero,hT.start⟩,hT.start,
    zero,hZero,hT.iterator.initial zero hZero hEmpty⟩

theorem pair_reached_up_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {ω zero P base H x y v : M.Domain} (hω : M.IsOmega ω) (hT : SquareTrace M ω zero P base H)
    (hx : M.mem x ω) (hy : M.mem y ω) (hv : M.mem v ω) (hyx : M.mem y x) (hSucc : M.SuccessorOf v y)
    (hReached : PairReached M ω P H x y) : PairReached M ω P H x v :=
  pair_reached_step_d hM hω hT hx hy hx hv hReached (Or.inl ⟨hyx,rfl,hSucc⟩)

theorem pair_reached_left_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {ω zero P base H x y u : M.Domain} (hω : M.IsOmega ω) (hT : SquareTrace M ω zero P base H)
    (hx : M.mem x ω) (hy : M.mem y ω) (hu : M.mem u ω) (hyx : ¬M.mem y x) (hSucc : M.SuccessorOf x u)
    (hReached : PairReached M ω P H x y) : PairReached M ω P H u y :=
  pair_reached_step_d hM hω hT hx hy hu hy hReached (Or.inr ⟨hyx,Or.inr ⟨u,hSucc.predecessor_mem,hSucc,rfl,rfl⟩⟩)

theorem pair_reached_corner_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {ω zero P base H y u : M.Domain} (hω : M.IsOmega ω) (hT : SquareTrace M ω zero P base H)
    (hZero : M.mem zero ω) (hEmpty : ∀ x, ¬M.mem x zero) (hy : M.mem y ω) (hu : M.mem u ω)
    (hSucc : M.SuccessorOf u y) (hReached : PairReached M ω P H zero y) : PairReached M ω P H u zero :=
  pair_reached_step_d hM hω hT hZero hy hu hZero hReached (Or.inr ⟨hEmpty y,Or.inl ⟨hEmpty,hSucc,rfl⟩⟩)

end KP1Y.Naturals
