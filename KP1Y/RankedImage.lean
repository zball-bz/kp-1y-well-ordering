import KP1Y.OrdinalRank
import KP1Y.CountableFunctions

/-! 已排名集合的满射像按最小源排名排序，选择规则字面Δ₀且输出排名图唯一。 -/
namespace KP1Y.Ranking
open YesMetaZFC YesMetaZFC.SetTheory YesMetaZFC.SetTheory.Definitional
open KP1Y.Kuratowski KP1Y.Functions KP1Y.Cardinal
universe u

def FiberRank (M : SetTheory.Structure.{u}) (X F G y a : M.Domain) : Prop :=
  ∃ x, M.mem x X ∧ MemPair M G x y ∧ MemPair M F x a

def fiberRankFormula {n : Nat} (X F G y a : Project.Term n) : Project.Formula 1 n :=
  Project.Formula.existsMem X (.conj (memPairFormula G.weaken (.bound 0) y.weaken) (memPairFormula F.weaken (.bound 0) a.weaken))

theorem fiberRankFormula_delta0 {n : Nat} (X F G y a : Project.Term n) : (fiberRankFormula X F G y a).IsDelta0 :=
  .existsMem _ (.conj (memPairFormula_delta0 _ _ _) (memPairFormula_delta0 _ _ _))

theorem fiberRankFormula_iff {M : SetTheory.Structure.{u}} (he : Extensional M) {n : Nat}
    (e : Env M n) (X F G y a : Project.Term n) :
    Project.Formula.satisfies e (fiberRankFormula X F G y a) ↔ FiberRank M (X.eval e) (F.eval e) (G.eval e) (y.eval e) (a.eval e) := by
  simp only [fiberRankFormula,Project.Formula.satisfies_existsMem_iff,Project.Formula.satisfies_conj_iff,
    memPairFormula_iff he,Definitional.Term.eval_weaken]
  rfl

def LeastImage (M : SetTheory.Structure.{u}) (X F G Γ y a : M.Domain) : Prop :=
  M.mem a Γ ∧ FiberRank M X F G y a ∧ ∀ b, M.mem b Γ → FiberRank M X F G y b → (a=b ∨ M.mem a b)

def leastImageFormula {n : Nat} (X F G Γ y a : Project.Term n) : Project.Formula 1 n :=
  .conj (.mem a Γ) (.conj (fiberRankFormula X F G y a)
    (Project.Formula.forallMem Γ (.imp (fiberRankFormula X.weaken F.weaken G.weaken y.weaken (.bound 0))
      (.disj (Project.Formula.extensionalEq a.weaken (.bound 0)) (.mem a.weaken (.bound 0))))))

theorem leastImageFormula_delta0 {n : Nat} (X F G Γ y a : Project.Term n) : (leastImageFormula X F G Γ y a).IsDelta0 :=
  .conj (.mem _ _) (.conj (fiberRankFormula_delta0 _ _ _ _ _)
    (.forallMem _ (.imp (fiberRankFormula_delta0 _ _ _ _ _) (.disj (.atom _ _ _) (.mem _ _)))))

theorem leastImageFormula_iff {M : SetTheory.Structure.{u}} (he : Extensional M) {n : Nat}
    (e : Env M n) (X F G Γ y a : Project.Term n) :
    Project.Formula.satisfies e (leastImageFormula X F G Γ y a) ↔
      LeastImage M (X.eval e) (F.eval e) (G.eval e) (Γ.eval e) (y.eval e) (a.eval e) := by
  simp only [leastImageFormula,Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_mem_iff,
    fiberRankFormula_iff he,Project.Formula.satisfies_forallMem_iff,Project.Formula.satisfies_imp_iff,
    Project.Formula.satisfies_disj_iff,Project.Formula.satisfies_extensionalEq_iff_eq he,Definitional.Term.eval_weaken]
  rfl

private def fiberSchema : Project.Delta0UnarySchema 4 where
  body := fiberRankFormula (.bound 2) (.bound 3) (.bound 4) (.bound 1) (.bound 0)
  freeClosed := by
    simp [fiberRankFormula,memPairFormula,codeFormula,pairFormula,Project.Formula.existsMem,Project.Formula.forallMem,Definitional.Formula.FreeClosed]
  delta0 := fiberRankFormula_delta0 _ _ _ _ _

private theorem fiberSchema_iff {M : SetTheory.Structure.{u}} (he : Extensional M) (G F X y a : M.Domain) :
    Project.Formula.satisfies (((((oneEnv G).push F).push X).push y).push a) fiberSchema.body ↔ FiberRank M X F G y a := by
  rw [fiberSchema,fiberRankFormula_iff he]
  rfl

theorem least_image_exists_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory) {F G X Y Γ y : M.Domain}
    (hRank : OrdinalRank M F X Γ) (hG : Onto M G X Y) (hy : M.mem y Y) : ∃ a, LeastImage M X F G Γ y a := by
  obtain ⟨D,hRaw⟩ := SetTheory.KP.separation_exists_d (KP1Y.models_weakKP hM) fiberSchema ((((oneEnv G).push F).push X).push y) Γ
  have hD (a : M.Domain) : M.mem a D ↔ M.mem a Γ ∧ FiberRank M X F G y a := by
    simpa only [fiberSchema_iff hM.1] using hRaw a
  obtain ⟨x,hx,hGxy⟩ := hG.2.2.2 y hy
  obtain ⟨a,ha,hFxa⟩ := hRank.graph.total x hx
  have hNe : ∃ a, M.mem a D := ⟨a,(hD a).mpr ⟨ha,x,hx,hGxy,hFxa⟩⟩
  obtain ⟨b,hb,hMin⟩ := hRank.ordinal.wellOrder.least D (fun a ha => ((hD a).mp ha).1) hNe
  refine ⟨b,((hD b).mp hb).1,((hD b).mp hb).2,?_⟩
  intro c hc hFiber
  rcases hMin c ((hD c).mpr ⟨hc,hFiber⟩) with hSame | hbc
  · exact Or.inl (hM.1.eq_of_same_members b c hSame)
  · exact Or.inr hbc

theorem least_image_unique {M : SetTheory.Structure.{u}} {X F G Γ y a b : M.Domain} (hΓ : M.IsOrdinal Γ)
    (ha : LeastImage M X F G Γ y a) (hb : LeastImage M X F G Γ y b) : a=b := by
  rcases ha.2.2 b hb.1 hb.2.1 with he | hab
  · exact he
  · rcases hb.2.2 a ha.1 ha.2.1 with he | hba
    · exact he.symm
    · exact False.elim (hΓ.wellOrder.linear.irrefl a ha.1 (hΓ.wellOrder.linear.trans a ha.1 b hb.1 a ha.1 hab hba))

private def imageSchema : Project.Delta0BinarySchema 4 where
  body := leastImageFormula (.bound 2) (.bound 3) (.bound 4) (.bound 5) (.bound 1) (.bound 0)
  freeClosed := by
    simp [leastImageFormula,fiberRankFormula,memPairFormula,codeFormula,pairFormula,
      Project.Formula.existsMem,Project.Formula.forallMem,Definitional.Formula.FreeClosed]
  delta0 := leastImageFormula_delta0 _ _ _ _ _ _

private theorem imageSchema_iff {M : SetTheory.Structure.{u}} (he : Extensional M) (Γ G F X y a : M.Domain) :
    Project.Formula.satisfies ((((((oneEnv Γ).push G).push F).push X).push y).push a) imageSchema.body ↔ LeastImage M X F G Γ y a := by
  rw [imageSchema,leastImageFormula_iff he]
  rfl

theorem ranked_image_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory) {F G X Y Γ : M.Domain}
    (hRank : OrdinalRank M F X Γ) (hG : Onto M G X Y) :
    ∃ R, OrdinalRank M R Y Γ ∧ ∀ y a, MemPair M R y a ↔ M.mem y Y ∧ LeastImage M X F G Γ y a := by
  obtain ⟨R,hSupport,hRaw⟩ := relation_comprehension_d hM imageSchema ((((oneEnv Γ).push G).push F).push X) Y Γ
  have hRows (y a : M.Domain) : MemPair M R y a ↔ M.mem y Y ∧ LeastImage M X F G Γ y a := by
    have h := hRaw y a
    rw [imageSchema_iff hM.1] at h
    exact h.trans ⟨fun h => ⟨h.1,h.2.2⟩,fun h => ⟨h.1,h.2.1,h.2⟩⟩
  refine ⟨R,⟨hRank.ordinal,⟨hSupport,?_,?_⟩,?_⟩,hRows⟩
  · intro y hy
    obtain ⟨a,ha⟩ := least_image_exists_d hM hRank hG hy
    exact ⟨a,ha.1,(hRows y a).mpr ⟨hy,ha⟩⟩
  · intro y a b hya hyb
    exact least_image_unique hRank.ordinal ((hRows y a).mp hya).2 ((hRows y b).mp hyb).2
  · intro y y' a hya hy'a
    obtain ⟨x,_,hGxy,hFxa⟩ := ((hRows y a).mp hya).2.2.1
    obtain ⟨x',_,hGxy',hFxa'⟩ := ((hRows y' a).mp hy'a).2.2.1
    have hxx' := hRank.injective x x' a hFxa hFxa'
    subst x'
    exact (hG.toGraph hM.1).unique x y y' hGxy hGxy'

end KP1Y.Ranking
