import KP1Y.RankedDynamics
import KP1Y.OrdinalInduction

/-! 实际秩与展开前缀关系推出同源后代可比，以及 Desc(s)/G 的内部字典序良序。
Reach x s 表示 x 是 s 的后代，Lex x s 表示 x 字典序小于 s。
有限路径语义与具体展开事实是显式接口前提；不声明全部 E 字典序良序。
-/
namespace KP1Y.Dynamics
open YesMetaZFC YesMetaZFC.SetTheory YesMetaZFC.SetTheory.Definitional
open KP1Y.Kuratowski KP1Y.Functions
universe u

def Expansion (M : SetTheory.Structure.{u}) (Keys F s n t : M.Domain) : Prop :=
  ∃ key, M.mem key Keys ∧ Codes M key s n ∧ MemPair M F key t

def expansionFormula {d : Nat} (Keys F s n t : Project.Term d) : Project.Formula 1 d :=
  Project.Formula.existsMem Keys (.conj (codeFormula (.bound 0) s.weaken n.weaken)
    (memPairFormula F.weaken (.bound 0) t.weaken))

theorem expansionFormula_delta0 {d : Nat} (Keys F s n t : Project.Term d) :
    (expansionFormula Keys F s n t).IsDelta0 :=
  .existsMem _ (.conj (codeFormula_delta0 _ _ _) (memPairFormula_delta0 _ _ _))

theorem expansionFormula_iff {M : SetTheory.Structure.{u}} (he : Extensional M) {d : Nat}
    (env : Env M d) (Keys F s n t : Project.Term d) :
    Project.Formula.satisfies env (expansionFormula Keys F s n t) ↔
      Expansion M (Keys.eval env) (F.eval env) (s.eval env) (n.eval env) (t.eval env) := by
  simp only [expansionFormula,Expansion,Project.Formula.satisfies_existsMem_iff,
    Project.Formula.satisfies_conj_iff,codeFormula_iff he,memPairFormula_iff he,Term.eval_weaken]
  rfl

/-- 所有运算/关系是实际集合，组合前提的量词均限制在 E、ω、χ。
首步分解只要求非平凡 Reach；非平凡展开的秩/字典序下降不包含待证的传递路径结论。 -/
structure DescendantSystem (M : SetTheory.Structure.{u}) (ω E χ μ Keys F Reach Lex : M.Domain) : Prop where
  omega : M.IsOmega ω
  ordinal : M.IsOrdinal χ
  rank : Graph M μ E χ
  keys : IsProduct M Keys E ω
  expansion : Graph M F Keys E
  reflexive : ∀ s, M.mem s E → MemPair M Reach s s
  transitive : ∀ x, M.mem x E → ∀ y, M.mem y E → ∀ z, M.mem z E →
    MemPair M Reach x y → MemPair M Reach y z → MemPair M Reach x z
  expansion_reachable : ∀ s, M.mem s E → ∀ n, M.mem n ω → ∀ t, M.mem t E →
    Expansion M Keys F s n t → MemPair M Reach t s
  first_step : ∀ s, M.mem s E → ∀ x, M.mem x E → MemPair M Reach x s → x≠s →
    ∃ n, M.mem n ω ∧ ∃ t, M.mem t E ∧ Expansion M Keys F s n t ∧ t≠s ∧ MemPair M Reach x t
  index_mono : ∀ s, M.mem s E → ∀ i, M.mem i ω → ∀ j, M.mem j ω → i=j ∨ M.mem i j →
    ∀ t, M.mem t E → ∀ u, M.mem u E → Expansion M Keys F s i t → Expansion M Keys F s j u → MemPair M Reach t u
  rank_step : ∀ s, M.mem s E → ∀ n, M.mem n ω → ∀ t, M.mem t E →
    ∀ a, M.mem a χ → ∀ b, M.mem b χ → Expansion M Keys F s n t → t≠s →
      MemPair M μ s a → MemPair M μ t b → M.mem b a
  lex_step : ∀ s, M.mem s E → ∀ n, M.mem n ω → ∀ t, M.mem t E →
    Expansion M Keys F s n t → t≠s → MemPair M Lex t s
  lex_irrefl : ∀ x, M.mem x E → ¬MemPair M Lex x x
  lex_trans : ∀ x, M.mem x E → ∀ y, M.mem y E → ∀ z, M.mem z E →
    MemPair M Lex x y → MemPair M Lex y z → MemPair M Lex x z

private def descentAtSchema : Project.Delta0UnarySchema 5 where
  body := Project.Formula.forallMem (.bound 5) (Project.Formula.forallMem (.bound 6)
    (Project.Formula.forallMem (.bound 5)
      (.imp (.conj (memPairFormula (.bound 7) (.bound 2) (.bound 3))
        (.conj (memPairFormula (.bound 5) (.bound 1) (.bound 2))
          (.conj (.neg (Project.Formula.extensionalEq (.bound 1) (.bound 2)))
            (memPairFormula (.bound 7) (.bound 1) (.bound 0)))))
        (.conj (.mem (.bound 0) (.bound 3)) (memPairFormula (.bound 4) (.bound 1) (.bound 2))))))
  freeClosed := by
    simp [memPairFormula,codeFormula,pairFormula,Project.Formula.forallMem,Project.Formula.existsMem,Definitional.Formula.FreeClosed]
  delta0 := .forallMem _ (.forallMem _ (.forallMem _ (.imp
    (.conj (memPairFormula_delta0 _ _ _) (.conj (memPairFormula_delta0 _ _ _)
      (.conj (.neg (.atom _ _ _)) (memPairFormula_delta0 _ _ _))))
    (.conj (.mem _ _) (memPairFormula_delta0 _ _ _)))))

private theorem descentAtSchema_iff {M : SetTheory.Structure.{u}} (he : Extensional M)
    (E μ χ Reach Lex a : M.Domain) :
    Project.Formula.satisfies ((((((oneEnv E).push μ).push χ).push Reach).push Lex).push a) descentAtSchema.body ↔
      ∀ s, M.mem s E → ∀ x, M.mem x E → ∀ b, M.mem b χ →
        MemPair M μ s a ∧ MemPair M Reach x s ∧ x≠s ∧ MemPair M μ x b → M.mem b a ∧ MemPair M Lex x s := by
  simp only [descentAtSchema,Project.Formula.satisfies_forallMem_iff,Project.Formula.satisfies_imp_iff,
    Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_neg_iff,
    Project.Formula.satisfies_extensionalEq_iff_eq he,Project.Formula.satisfies_mem_iff,memPairFormula_iff he]
  rfl

/-- 非平凡可达的 rank/lex 下降由实际首步分解及对象序数归纳推导。 -/
theorem DescendantSystem.strict_reach_descent_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {ω E χ μ Keys F Reach Lex : M.Domain} (h : DescendantSystem M ω E χ μ Keys F Reach Lex)
    {s x a b : M.Domain} (hReach : MemPair M Reach x s) (hNot : x≠s)
    (hsa : MemPair M μ s a) (hxb : MemPair M μ x b) : M.mem b a ∧ MemPair M Lex x s := by
  classical
  let env := ((((oneEnv E).push μ).push χ).push Reach).push Lex
  have hAll := KP1Y.ordinal_induction_d hM descentAtSchema.toUnarySchema env (by
    intro a hOrd ih
    apply (descentAtSchema_iff hM.1 E μ χ Reach Lex a).mpr
    intro s hs x hx b hb hAnte
    obtain ⟨hsa,hReach,hNot,hxb⟩ := hAnte
    obtain ⟨n,hn,t,ht,hExpand,htNot,hXt⟩ := h.first_step s hs x hx hReach hNot
    obtain ⟨c,hc,htc⟩ := h.rank.total t ht
    have hca := h.rank_step s hs n hn t ht a (h.rank.bounds hM.1 hsa).2 c hc hExpand htNot hsa htc
    have hLex := h.lex_step s hs n hn t ht hExpand htNot
    by_cases hxt : x=t
    · subst x
      have hbc := h.rank.unique t b c hxb htc
      subst b
      exact ⟨hca,hLex⟩
    · have hLower := (descentAtSchema_iff hM.1 E μ χ Reach Lex c).mp (ih c hca)
        t ht x hx b hb ⟨htc,hXt,hxt,hxb⟩
      exact ⟨hOrd.transitive c hca b hLower.1,h.lex_trans x hx t ht s hs hLower.2 hLex⟩)
  exact (descentAtSchema_iff hM.1 E μ χ Reach Lex a).mp (hAll a (h.ordinal.mem (h.rank.bounds hM.1 hsa).2))
    s (h.rank.bounds hM.1 hsa).1 x (h.rank.bounds hM.1 hxb).1 b (h.rank.bounds hM.1 hxb).2 ⟨hsa,hReach,hNot,hxb⟩

private def comparableAtSchema : Project.Delta0UnarySchema 3 where
  body := Project.Formula.forallMem (.bound 3) (Project.Formula.forallMem (.bound 4)
    (Project.Formula.forallMem (.bound 5)
      (.imp (.conj (memPairFormula (.bound 5) (.bound 2) (.bound 3))
        (.conj (memPairFormula (.bound 4) (.bound 1) (.bound 2)) (memPairFormula (.bound 4) (.bound 0) (.bound 2))))
        (.disj (memPairFormula (.bound 4) (.bound 1) (.bound 0)) (memPairFormula (.bound 4) (.bound 0) (.bound 1))))))
  freeClosed := by
    simp [memPairFormula,codeFormula,pairFormula,Project.Formula.forallMem,Project.Formula.existsMem,Definitional.Formula.FreeClosed]
  delta0 := .forallMem _ (.forallMem _ (.forallMem _ (.imp
    (.conj (memPairFormula_delta0 _ _ _) (.conj (memPairFormula_delta0 _ _ _) (memPairFormula_delta0 _ _ _)))
    (.disj (memPairFormula_delta0 _ _ _) (memPairFormula_delta0 _ _ _)))))

private theorem comparableAtSchema_iff {M : SetTheory.Structure.{u}} (he : Extensional M)
    (E μ Reach a : M.Domain) :
    Project.Formula.satisfies ((((oneEnv E).push μ).push Reach).push a) comparableAtSchema.body ↔
      ∀ s, M.mem s E → ∀ x, M.mem x E → ∀ y, M.mem y E →
        MemPair M μ s a ∧ MemPair M Reach x s ∧ MemPair M Reach y s → MemPair M Reach x y ∨ MemPair M Reach y x := by
  simp only [comparableAtSchema,Project.Formula.satisfies_forallMem_iff,Project.Formula.satisfies_imp_iff,
    Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_disj_iff,memPairFormula_iff he]
  rfl

/-- 较小展开索引的结果是较大索引结果的后代，故秩归纳比较任意两个同源后代。 -/
theorem DescendantSystem.common_descendants_comparable_d {M : SetTheory.Structure.{u}}
    (hM : M.Models KP1Y.theory) {ω E χ μ Keys F Reach Lex : M.Domain}
    (h : DescendantSystem M ω E χ μ Keys F Reach Lex) {s x y : M.Domain}
    (hs : M.mem s E) (hx : M.mem x E) (hy : M.mem y E)
    (hXs : MemPair M Reach x s) (hYs : MemPair M Reach y s) : MemPair M Reach x y ∨ MemPair M Reach y x := by
  classical
  let env := ((oneEnv E).push μ).push Reach
  have hAll := KP1Y.ordinal_induction_d hM comparableAtSchema.toUnarySchema env (by
    intro a _ ih
    apply (comparableAtSchema_iff hM.1 E μ Reach a).mpr
    intro s hs x hx y hy hAnte
    obtain ⟨hsa,hXs,hYs⟩ := hAnte
    by_cases hxs : x=s
    · subst x
      exact Or.inr hYs
    · by_cases hys : y=s
      · subst y
        exact Or.inl hXs
      · obtain ⟨i,hi,t,ht,hSi,htNot,hXt⟩ := h.first_step s hs x hx hXs hxs
        obtain ⟨j,hj,u,hu,hSj,huNot,hYu⟩ := h.first_step s hs y hy hYs hys
        have hJoin : ∃ z, M.mem z E ∧ ∃ b, M.mem b a ∧ MemPair M μ z b ∧ MemPair M Reach x z ∧ MemPair M Reach y z := by
          have hOrdω := KP1Y.Naturals.omega_isOrdinal_d hM h.omega
          rcases hOrdω.wellOrder.linear.compare i hi j hj with he | hij | hji
          · have hij := hM.1.eq_of_same_members i j he
            have htu := h.index_mono s hs i hi j hj (Or.inl hij) t ht u hu hSi hSj
            obtain ⟨b,hb,hub⟩ := h.rank.total u hu
            exact ⟨u,hu,b,h.rank_step s hs j hj u hu a (h.rank.bounds hM.1 hsa).2 b hb hSj huNot hsa hub,
              hub,h.transitive x hx t ht u hu hXt htu,hYu⟩
          · have htu := h.index_mono s hs i hi j hj (Or.inr hij) t ht u hu hSi hSj
            obtain ⟨b,hb,hub⟩ := h.rank.total u hu
            exact ⟨u,hu,b,h.rank_step s hs j hj u hu a (h.rank.bounds hM.1 hsa).2 b hb hSj huNot hsa hub,
              hub,h.transitive x hx t ht u hu hXt htu,hYu⟩
          · have hut := h.index_mono s hs j hj i hi (Or.inr hji) u hu t ht hSj hSi
            obtain ⟨b,hb,htb⟩ := h.rank.total t ht
            exact ⟨t,ht,b,h.rank_step s hs i hi t ht a (h.rank.bounds hM.1 hsa).2 b hb hSi htNot hsa htb,
              htb,hXt,h.transitive y hy u hu t ht hYu hut⟩
        obtain ⟨z,hz,b,hba,hzb,hXz,hYz⟩ := hJoin
        exact (comparableAtSchema_iff hM.1 E μ Reach b).mp (ih b hba) z hz x hx y hy ⟨hzb,hXz,hYz⟩)
  obtain ⟨a,ha,hsa⟩ := h.rank.total s hs
  exact (comparableAtSchema_iff hM.1 E μ Reach a).mp (hAll a (h.ordinal.mem ha)) s hs x hx y hy ⟨hsa,hXs,hYs⟩

/-- 字典序与严格可达的对应只在给定共同祖先的两个后代之间成立。 -/
theorem DescendantSystem.lex_iff_strict_reach_d {M : SetTheory.Structure.{u}}
    (hM : M.Models KP1Y.theory) {ω E χ μ Keys F Reach Lex : M.Domain}
    (h : DescendantSystem M ω E χ μ Keys F Reach Lex) {s x y : M.Domain}
    (hs : M.mem s E) (hx : M.mem x E) (hy : M.mem y E)
    (hXs : MemPair M Reach x s) (hYs : MemPair M Reach y s) :
    MemPair M Lex x y ↔ x≠y ∧ MemPair M Reach x y := by
  obtain ⟨a,_,hxa⟩ := h.rank.total x hx
  obtain ⟨b,_,hyb⟩ := h.rank.total y hy
  constructor
  · intro hLex
    have hNe : x≠y := by
      intro he
      subst y
      exact h.lex_irrefl x hx hLex
    refine ⟨hNe,?_⟩
    rcases h.common_descendants_comparable_d hM hs hx hy hXs hYs with hReach | hReverse
    · exact hReach
    · have hReverseLex := (h.strict_reach_descent_d hM hReverse (fun he => hNe he.symm) hxa hyb).2
      exact False.elim (h.lex_irrefl x hx (h.lex_trans x hx y hy x hx hLex hReverseLex))
  · rintro ⟨hNe,hReach⟩
    exact (h.strict_reach_descent_d hM hReach hNe hyb hxa).2

/-- 实际集合 X 中任意两点具有 E 中的共同祖先。 -/
def CommonAncestors (M : SetTheory.Structure.{u}) (Reach E X : M.Domain) : Prop :=
  ∀ x, M.mem x X → ∀ y, M.mem y X → ∃ s, M.mem s E ∧ MemPair M Reach x s ∧ MemPair M Reach y s

/-- 在共同祖先条件下用实际 rank 像的最小序数取得字典序最小元。 -/
theorem DescendantSystem.common_ancestor_wellorder_d {M : SetTheory.Structure.{u}}
    (hM : M.Models KP1Y.theory) {ω E χ μ Keys F Reach Lex X : M.Domain}
    (h : DescendantSystem M ω E χ μ Keys F Reach Lex)
    (hXE : M.MemberSubset X E) (hCommon : CommonAncestors M Reach E X) :
    KP1Y.InternalWellOrder M Lex X ∧ ∀ x, M.mem x X → ∀ y, M.mem y X →
      (MemPair M Lex x y ↔ x≠y ∧ MemPair M Reach x y) := by
  classical
  refine ⟨⟨fun x hx => h.lex_irrefl x (hXE x hx),
    fun x hx y hy z hz => h.lex_trans x (hXE x hx) y (hXE y hy) z (hXE z hz),?_⟩,?_⟩
  · intro S hSX hNe
    have hSE : M.MemberSubset S E := fun x hx => hXE x (hSX x hx)
    obtain ⟨x,hx,a,ha,hxa,hMin⟩ := rank_minimum_d hM h.ordinal h.rank hSE hNe
    refine ⟨x,hx,?_⟩
    intro y hy
    by_cases hxy : x=y
    · exact Or.inl hxy
    · obtain ⟨s,hs,hXs,hYs⟩ := hCommon x (hSX x hx) y (hSX y hy)
      obtain ⟨b,hb,hyb⟩ := h.rank.total y (hSE y hy)
      rcases h.common_descendants_comparable_d hM hs (hSE x hx) (hSE y hy) hXs hYs with hReach | hReverse
      · exact Or.inr ((h.strict_reach_descent_d hM hReach hxy hyb hxa).2)
      · have hba := (h.strict_reach_descent_d hM hReverse (fun he => hxy he.symm) hxa hyb).1
        apply False.elim
        rcases hMin y hy b hyb with he | hab
        · subst b
          exact h.ordinal.wellOrder.linear.irrefl a ha hba
        · exact h.ordinal.wellOrder.linear.irrefl a ha (h.ordinal.wellOrder.linear.trans a ha b hb a ha hab hba)
  · intro x hx y hy
    obtain ⟨s,hs,hXs,hYs⟩ := hCommon x hx y hy
    exact h.lex_iff_strict_reach_d hM hs (hXE x hx) (hXE y hy) hXs hYs

private def descendantSchema : Project.Delta0UnarySchema 2 where
  body := memPairFormula (.bound 2) (.bound 0) (.bound 1)
  freeClosed := by
    simp [memPairFormula,codeFormula,pairFormula,Project.Formula.forallMem,Project.Formula.existsMem,Definitional.Formula.FreeClosed]
  delta0 := memPairFormula_delta0 _ _ _

theorem descendant_set_exists_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    (E Reach s : M.Domain) : ∃ D, ∀ x, M.mem x D ↔ M.mem x E ∧ MemPair M Reach x s := by
  obtain ⟨D,hD⟩ := SetTheory.KP.separation_exists_d (KP1Y.models_weakKP hM) descendantSchema ((oneEnv Reach).push s) E
  have hφ (x : M.Domain) : Project.Formula.satisfies (((oneEnv Reach).push s).push x) descendantSchema.body ↔ MemPair M Reach x s := by
    simp only [descendantSchema,memPairFormula_iff hM.1]
    rfl
  exact ⟨D,fun x => by simpa only [hφ] using hD x⟩

/-- Desc(s) 是实际集合，包含 s；其 lex 良序及严格可达对应由上述归纳得到。 -/
theorem DescendantSystem.descendants_wellorder_d {M : SetTheory.Structure.{u}}
    (hM : M.Models KP1Y.theory) {ω E χ μ Keys F Reach Lex s : M.Domain}
    (h : DescendantSystem M ω E χ μ Keys F Reach Lex) (hs : M.mem s E) :
    ∃ D, (∀ x, M.mem x D ↔ M.mem x E ∧ MemPair M Reach x s) ∧ M.mem s D ∧
      KP1Y.InternalWellOrder M Lex D ∧ ∀ x, M.mem x D → ∀ y, M.mem y D →
        (MemPair M Lex x y ↔ x≠y ∧ MemPair M Reach x y) := by
  obtain ⟨D,hD⟩ := descendant_set_exists_d hM E Reach s
  have hSub : M.MemberSubset D E := fun x hx => ((hD x).mp hx).1
  have hCommon : CommonAncestors M Reach E D := fun x hx y hy =>
    ⟨s,hs,((hD x).mp hx).2,((hD y).mp hy).2⟩
  obtain ⟨hWO,hIff⟩ := h.common_ancestor_wellorder_d hM hSub hCommon
  exact ⟨D,hD,(hD s).mpr ⟨hs,h.reflexive s hs⟩,hWO,hIff⟩

private def generatedSchema : Project.Delta0UnarySchema 2 where
  body := Project.Formula.existsMem (.bound 1) (memPairFormula (.bound 3) (.bound 1) (.bound 0))
  freeClosed := by
    simp [memPairFormula,codeFormula,pairFormula,Project.Formula.forallMem,Project.Formula.existsMem,Definitional.Formula.FreeClosed]
  delta0 := .existsMem _ (memPairFormula_delta0 _ _ _)

theorem generated_set_exists_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    (E Reach Seeds : M.Domain) :
    ∃ G, ∀ x, M.mem x G ↔ M.mem x E ∧ ∃ s, M.mem s Seeds ∧ MemPair M Reach x s := by
  obtain ⟨G,hG⟩ := SetTheory.KP.separation_exists_d (KP1Y.models_weakKP hM) generatedSchema ((oneEnv Reach).push Seeds) E
  have hφ (x : M.Domain) : Project.Formula.satisfies (((oneEnv Reach).push Seeds).push x) generatedSchema.body ↔
      ∃ s, M.mem s Seeds ∧ MemPair M Reach x s := by
    simp only [generatedSchema,Project.Formula.satisfies_existsMem_iff,memPairFormula_iff hM.1]
    rfl
  exact ⟨G,fun x => by simpa only [hφ] using hG x⟩

/-- 两个种子有共同种子祖先，因此实际种子后代并集 G 上成立同样的良序结论。 -/
theorem DescendantSystem.generated_wellorder_d {M : SetTheory.Structure.{u}}
    (hM : M.Models KP1Y.theory) {ω E χ μ Keys F Reach Lex Seeds : M.Domain}
    (h : DescendantSystem M ω E χ μ Keys F Reach Lex) (hSeeds : M.MemberSubset Seeds E)
    (hJoin : ∀ s, M.mem s Seeds → ∀ t, M.mem t Seeds →
      ∃ u, M.mem u Seeds ∧ MemPair M Reach s u ∧ MemPair M Reach t u) :
    ∃ G, (∀ x, M.mem x G ↔ M.mem x E ∧ ∃ s, M.mem s Seeds ∧ MemPair M Reach x s) ∧
      M.MemberSubset Seeds G ∧ KP1Y.InternalWellOrder M Lex G ∧ ∀ x, M.mem x G → ∀ y, M.mem y G →
        (MemPair M Lex x y ↔ x≠y ∧ MemPair M Reach x y) := by
  obtain ⟨G,hG⟩ := generated_set_exists_d hM E Reach Seeds
  have hSub : M.MemberSubset G E := fun x hx => ((hG x).mp hx).1
  have hCommon : CommonAncestors M Reach E G := by
    intro x hx y hy
    obtain ⟨hxE,s,hs,hXs⟩ := (hG x).mp hx
    obtain ⟨hyE,t,ht,hYt⟩ := (hG y).mp hy
    obtain ⟨u,hu,hSu,hTu⟩ := hJoin s hs t ht
    exact ⟨u,hSeeds u hu,h.transitive x hxE s (hSeeds s hs) u (hSeeds u hu) hXs hSu,
      h.transitive y hyE t (hSeeds t ht) u (hSeeds u hu) hYt hTu⟩
  obtain ⟨hWO,hIff⟩ := h.common_ancestor_wellorder_d hM hSub hCommon
  exact ⟨G,hG,fun s hs => (hG s).mpr ⟨hSeeds s hs,s,hs,h.reflexive s (hSeeds s hs)⟩,hWO,hIff⟩

end KP1Y.Dynamics
