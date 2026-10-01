import KP1Y.OneYWellFounded

/-! M04b：实际秩见证、实际 Reach/Lex 集合与显式 `OrderFacts` 实例化通用 O02 定理，
得到每个 Desc(s) 与 G 上字典序（真前缀较小）的内部良序。结论域只限 Desc(s)、G，不扩大到 E。
`OrderFacts` 是文稿 [1, Lemma 9.1, §9] 的有限数值事实，留待 Y07a/Y07b 以实际算法解除；
种子共同祖先由 E₁(1,n+2)=(1,n+1) 经内部自然数归纳推出，不作为前提。 -/
namespace KP1Y.OneYTheorem
open YesMetaZFC YesMetaZFC.SetTheory YesMetaZFC.SetTheory.Definitional
open KP1Y.Kuratowski KP1Y.Functions KP1Y.Naturals KP1Y.Bounded
open KP1Y.OneYFinite KP1Y.OneYRank
universe u

/-- s 是二元表达式 (1,b)：定义域 two=1+1，s(0)=1，s(1)=b。 -/
def PairExpressionIn (M : SetTheory.Structure.{u}) (w z o s b : M.Domain) : Prop :=
  ∃ two, M.mem two w ∧ M.SuccessorOf two o ∧ Graph M s two w ∧ MemPair M s z o ∧ MemPair M s o b

abbrev PairExpression (M : SetTheory.Structure.{u}) (C : ExpressionData M.Domain) (s b : M.Domain) : Prop :=
  PairExpressionIn M C.omega C.zero C.one s b

def pairExpressionFormula {n : Nat} (w z o s b : Project.Term n) : Project.Formula 1 n :=
  Project.Formula.existsMem w (.conj (successorFormula (.bound 0) o.weaken)
    (.conj (graphFormula s.weaken (.bound 0) w.weaken)
      (.conj (memPairFormula s.weaken z.weaken o.weaken) (memPairFormula s.weaken o.weaken b.weaken))))

theorem pairExpressionFormula_delta0 {n : Nat} (w z o s b : Project.Term n) :
    (pairExpressionFormula w z o s b).IsDelta0 :=
  .existsMem _ (.conj (successorFormula_delta0 _ _) (.conj (graphFormula_delta0 _ _ _)
    (.conj (memPairFormula_delta0 _ _ _) (memPairFormula_delta0 _ _ _))))

theorem pairExpressionFormula_freeClosed {n : Nat} (w z o s b : Project.Term n) (hw : w.freeSupport=[])
    (hz : z.freeSupport=[]) (ho : o.freeSupport=[]) (hs : s.freeSupport=[]) (hb : b.freeSupport=[]) :
    (pairExpressionFormula w z o s b).FreeClosed := by
  simp [pairExpressionFormula,successorFormula,graphFormula,memPairFormula,codeFormula,pairFormula,
    Project.Formula.forallMem,Project.Formula.existsMem,Definitional.Formula.FreeClosed,hw,hz,ho,hs,hb]

theorem pairExpressionFormula_iff {M : SetTheory.Structure.{u}} (he : Extensional M) {n : Nat} (e : Env M n)
    (w z o s b : Project.Term n) :
    Project.Formula.satisfies e (pairExpressionFormula w z o s b) ↔
      PairExpressionIn M (w.eval e) (z.eval e) (o.eval e) (s.eval e) (b.eval e) := by
  simp only [pairExpressionFormula,Project.Formula.satisfies_existsMem_iff,Project.Formula.satisfies_conj_iff,
    successorFormula_iff he,graphFormula_iff he,memPairFormula_iff he,Term.eval_weaken]
  rfl

/-- 文稿种子 (1,m)，m≥2，即 1∈m∈ω。 -/
def Seed (M : SetTheory.Structure.{u}) (C : ExpressionData M.Domain) (r : M.Domain) : Prop :=
  ∃ m, M.mem m C.omega ∧ M.mem C.one m ∧ PairExpression M C r m

def seedFormula {n : Nat} (C : ExpressionData (Project.Term n)) (r : Project.Term n) : Project.Formula 1 n :=
  Project.Formula.existsMem C.omega (.conj (.mem C.one.weaken (.bound 0))
    (pairExpressionFormula C.omega.weaken C.zero.weaken C.one.weaken r.weaken (.bound 0)))

theorem seedFormula_delta0 {n : Nat} (C : ExpressionData (Project.Term n)) (r : Project.Term n) :
    (seedFormula C r).IsDelta0 := .existsMem _ (.conj (.mem _ _) (pairExpressionFormula_delta0 _ _ _ _ _))

theorem seedFormula_freeClosed {n : Nat} {C : ExpressionData (Project.Term n)} (hC : C.Closed) (r : Project.Term n)
    (hr : r.freeSupport=[]) : (seedFormula C r).FreeClosed := by
  have hP := pairExpressionFormula_freeClosed C.omega.weaken C.zero.weaken C.one.weaken r.weaken (.bound 0)
    (by simpa using hC.omega) (by simpa using hC.zero) (by simpa using hC.one) (by simpa using hr) rfl
  simp [seedFormula,Project.Formula.existsMem,Definitional.Formula.FreeClosed,hC.omega,hC.one,hP]

theorem seedFormula_iff {M : SetTheory.Structure.{u}} (he : Extensional M) {n : Nat} (e : Env M n)
    (C : ExpressionData (Project.Term n)) (r : Project.Term n) :
    Project.Formula.satisfies e (seedFormula C r) ↔ Seed M (C.eval e) (r.eval e) := by
  simp only [seedFormula,Project.Formula.satisfies_existsMem_iff,Project.Formula.satisfies_conj_iff,
    Project.Formula.satisfies_mem_iff,pairExpressionFormula_iff he,Term.eval_weaken]
  rfl

theorem pair_expression_legal_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {s b : M.Domain} (hPos : M.mem C.zero b)
    (h : PairExpression M C s b) : M.mem s C.expressions := by
  obtain ⟨two,htwo,hTwo,hS,h0,h1⟩ := h
  refine (hC.expressions s).mpr ⟨two,htwo,⟨htwo,hS⟩,?_,Or.inr h0⟩
  intro i hi a _ hia
  rcases (hTwo i).mp hi with hi1 | hie
  · rcases (hC.one_succ i).mp hi1 with hi0 | hie0
    · exact False.elim (hC.zero_empty i hi0)
    · have hi0 : i=C.zero := hM.1.eq_of_same_members i C.zero hie0
      subst i
      have := hS.unique C.zero a C.one hia h0
      subst a
      exact hC.one_succ.predecessor_mem
  · have hi1 : i=C.one := hM.1.eq_of_same_members i C.one hie
    subst i
    have := hS.unique C.one a b hia h1
    subst a
    exact hPos

theorem Seed.legal_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {r : M.Domain} (h : Seed M C r) : M.mem r C.expressions := by
  obtain ⟨m,hm,h1m,hP⟩ := h
  have hPos : M.mem C.zero m := ((omega_isOrdinal_d hM hC.omega).mem hm).transitive C.one h1m C.zero
    hC.one_succ.predecessor_mem
  exact pair_expression_legal_d hM hC hPos hP

/-- 同一 b 的二元表达式唯一。 -/
theorem pair_expression_unique {M : SetTheory.Structure.{u}} (he : Extensional M)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {s s' b : M.Domain}
    (h : PairExpression M C s b) (h' : PairExpression M C s' b) : s=s' := by
  obtain ⟨two,_,hTwo,hS,h0,h1⟩ := h
  obtain ⟨two',_,hTwo',hS',h0',h1'⟩ := h'
  have htt := Structure.SuccessorOf.eq he hTwo' hTwo
  subst two'
  apply hS.ext he hS'
  intro i hi v
  rcases (hTwo i).mp hi with hi1 | hie
  · rcases (hC.one_succ i).mp hi1 with hi0 | hie0
    · exact False.elim (hC.zero_empty i hi0)
    · have hi0 : i=C.zero := he.eq_of_same_members i C.zero hie0
      subst i
      exact ⟨fun hv => (hS.unique _ _ _ hv h0) ▸ h0',fun hv => (hS'.unique _ _ _ hv h0') ▸ h0⟩
  · have hi1 : i=C.one := he.eq_of_same_members i C.one hie
    subst i
    exact ⟨fun hv => (hS.unique _ _ _ hv h1) ▸ h1',fun hv => (hS'.unique _ _ _ hv h1') ▸ h1⟩

theorem pair_expression_exists_d' {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {b : M.Domain} (hb : M.mem b C.omega) (hPos : M.mem C.zero b) :
    ∃ s, PairExpression M C s b ∧ M.mem s C.expressions := by
  obtain ⟨two,s,hTwo,hL,hRows,_⟩ := pair_expression_exists_d hM hC hb hPos
  have hP : PairExpression M C s b := ⟨two,hL.1.1,hTwo,hL.1.2,(hRows C.zero C.one).mpr (.inl ⟨rfl,rfl⟩),
    (hRows C.one b).mpr (.inr ⟨rfl,rfl⟩)⟩
  exact ⟨s,hP,pair_expression_legal_d hM hC hPos hP⟩

/-- 文稿 Lemma 9.1/§9 的有限数值输入，全部以实际 E_N 陈述；由 Y07a/Y07b 解除。 -/
structure OrderFacts (M : SetTheory.Structure.{u}) (C : ExpressionData M.Domain) (T : MatrixArithmetic M.Domain) : Prop where
  /-- i≤j 时 E_i(s) 是 E_j(s) 的后代（由前缀单调与前缀经 E₀ 可达合成；即 Y07a `index_mono_d`）。 -/
  index_mono : ∀ Keys EN Reach, Expansion.Graph M C T Keys EN → Reachability.Relation M C Keys EN Reach →
    ∀ s i j t u, (i=j ∨ M.mem i j) → KP1Y.Dynamics.Expansion M Keys EN s i t →
      KP1Y.Dynamics.Expansion M Keys EN s j u → MemPair M Reach t u
  /-- E_N(s) <lex s（s≠∅，N∈ω）。 -/
  lex_descent : ∀ s, M.mem s C.expressions → s≠C.zero → ∀ N, M.mem N C.omega → ∀ t,
    Expansion.Expands M C T s N t → Lex M C t s
  /-- E₁(1,n+2)=(1,n+1)（n∈ω）。 -/
  seed_step : ∀ n, M.mem n C.omega → ∀ a b, M.SuccessorOf a n → M.SuccessorOf b a → ∀ s t,
    PairExpression M C s b → PairExpression M C t a → Expansion.Expands M C T s C.one t

/-- 实际数据给出 O02 的全部字段。 -/
theorem descendant_system_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {D : TheoremData M.Domain} (hD : D.Valid M) {χ μ Reach L : M.Domain} (hW : RankWitness M D.expr D.arith χ μ)
    (hF : OrderFacts M D.expr D.arith) (hR : Reachability.Relation M D.expr D.keys D.expansion Reach)
    (hL : LexRelation M D.expr L) :
    KP1Y.Dynamics.DescendantSystem M D.expr.omega D.expr.expressions χ μ D.keys D.expansion Reach L := by
  have hFields := hR.fields_d hM hD.expr
  have hNonempty (s n t : M.Domain) (hn : M.mem n D.expr.omega) (hStep : Step M D s n t) (hts : t≠s) :
      s≠D.expr.zero := by
    intro he
    subst s
    exact hts (hD.empty_step_d hM hn hStep)
  refine ⟨hD.expr.omega,hW.ordinal,hW.graph,hD.graph.keys,hD.graph.graph,hFields.reflexive,hFields.transitive,
    hFields.expansion_reachable,hFields.first_step,?_,?_,?_,?_,?_⟩
  · intro s _ i _ j _ hij t _ u _ ht hu
    exact hF.index_mono D.keys D.expansion Reach hD.graph hR s i j t u hij ht hu
  · intro s hs n hn t _ a _ b _ hStep hts hsa htb
    exact witness_step_descends_d hM hD hW hs (hNonempty s n t hn hStep hts) hn hStep hsa htb
  · intro s hs n hn t _ hStep hts
    exact (hL.rows t s).mpr (hF.lex_descent s hs (hNonempty s n t hn hStep hts) n hn t ((hD.step_iff_d hM).mp hStep))
  · exact fun x _ => hL.irrefl_d hM x
  · exact fun _ _ _ _ _ _ hxy hyz => hL.trans_d hM hD.expr hxy hyz

/-- 字典序 Lex 在 X 上为内部良序：严格线性，且每个非空内部子集有最小元。 -/
def LexWellOrder (M : SetTheory.Structure.{u}) (C : ExpressionData M.Domain) (X : M.Domain) : Prop :=
  (∀ x, M.mem x X → ¬Lex M C x x) ∧
  (∀ x, M.mem x X → ∀ y, M.mem y X → ∀ z, M.mem z X → Lex M C x y → Lex M C y z → Lex M C x z) ∧
  (∀ x, M.mem x X → ∀ y, M.mem y X → x=y ∨ Lex M C x y ∨ Lex M C y x) ∧
  ∀ S, M.MemberSubset S X → (∃ x, M.mem x S) → ∃ x, M.mem x S ∧ ∀ y, M.mem y S → x=y ∨ Lex M C x y

theorem lex_wellOrder_of_internal_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {L X : M.Domain} (hL : LexRelation M C L)
    (hXE : M.MemberSubset X C.expressions) (h : KP1Y.InternalWellOrder M L X) : LexWellOrder M C X := by
  refine ⟨fun x _ => Lex.irrefl_d hM,fun x _ y _ z _ hxy hyz => Lex.trans_d hM hC hxy hyz,
    fun x hx y hy => Lex.trichotomy_d hM hC (hXE x hx) (hXE y hy),?_⟩
  intro S hSX hNe
  obtain ⟨x,hx,hLeast⟩ := h.least S hSX hNe
  exact ⟨x,hx,fun y hy => (hLeast y hy).imp id (hL.rows x y).mp⟩

/-- 文稿 Desc(s)：s 的有限步后代（含 s），字典序在其上良序。 -/
def DescClause (M : SetTheory.Structure.{u}) (D : TheoremData M.Domain) : Prop :=
  ∀ s, M.mem s D.expr.expressions → ∃ X,
    (∀ x, M.mem x X ↔ M.mem x D.expr.expressions ∧ Reachability.Reaches M D.expr D.keys D.expansion x s) ∧
      LexWellOrder M D.expr X

/-- 文稿 G：种子 (1,m)，m≥2 的后代并集，字典序在其上良序。 -/
def GenClause (M : SetTheory.Structure.{u}) (D : TheoremData M.Domain) : Prop :=
  ∃ X, (∀ x, M.mem x X ↔ M.mem x D.expr.expressions ∧
      ∃ r, Seed M D.expr r ∧ Reachability.Reaches M D.expr D.keys D.expansion x r) ∧
    LexWellOrder M D.expr X

theorem desc_clause_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {D : TheoremData M.Domain} (hD : D.Valid M) {χ μ : M.Domain} (hW : RankWitness M D.expr D.arith χ μ)
    (hF : OrderFacts M D.expr D.arith) : DescClause M D := by
  intro s hs
  obtain ⟨Reach,hR⟩ := Reachability.reach_relation_exists_d hM hD.expr D.keys D.expansion
  obtain ⟨L,hL⟩ := lex_relation_exists_d hM hD.expr
  obtain ⟨X,hX,_,hWO,_⟩ := (descendant_system_d hM hD hW hF hR hL).descendants_wellorder_d hM hs
  refine ⟨X,fun x => (hX x).trans (and_congr Iff.rfl (hR.rows x s)),?_⟩
  exact lex_wellOrder_of_internal_d hM hD.expr hL (fun x hx => ((hX x).mp hx).1) hWO

private def seedSchema : Project.Delta0UnarySchema 3 where
  body := seedFormula ⟨.bound 3,.bound 2,.bound 1,.bound 1,.bound 1⟩ (.bound 0)
  freeClosed := seedFormula_freeClosed ⟨rfl,rfl,rfl,rfl,rfl⟩ _ rfl
  delta0 := seedFormula_delta0 _ _

theorem seed_set_exists_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) :
    ∃ Seeds, ∀ r, M.mem r Seeds ↔ Seed M C r := by
  obtain ⟨Seeds,hS⟩ := SetTheory.KP.separation_exists_d (KP1Y.models_weakKP hM) seedSchema
    (((oneEnv C.omega).push C.zero).push C.one) C.expressions
  refine ⟨Seeds,fun r => ?_⟩
  have hφ : Project.Formula.satisfies ((((oneEnv C.omega).push C.zero).push C.one).push r) seedSchema.body ↔
      Seed M C r := by
    rw [seedSchema,seedFormula_iff hM.1]
    rfl
  rw [hS r,hφ]
  exact ⟨And.right,fun h => ⟨h.legal_d hM hC,h⟩⟩

private def chainSchema : Project.Delta0UnarySchema 5 where
  body := Project.Formula.forallMem (.bound 5) (Project.Formula.forallMem (.bound 3) (Project.Formula.forallMem (.bound 4)
    (.imp (.conj (pairExpressionFormula (.bound 8) (.bound 7) (.bound 6) (.bound 1) (.bound 2))
      (.conj (pairExpressionFormula (.bound 8) (.bound 7) (.bound 6) (.bound 0) (.bound 3))
        (.conj (.mem (.bound 6) (.bound 2))
          (.disj (Project.Formula.extensionalEq (.bound 2) (.bound 3)) (.mem (.bound 2) (.bound 3))))))
      (memPairFormula (.bound 4) (.bound 1) (.bound 0)))))
  freeClosed := by
    have h1 := pairExpressionFormula_freeClosed (n := 9) (.bound 8) (.bound 7) (.bound 6) (.bound 1) (.bound 2) rfl rfl rfl rfl rfl
    have h2 := pairExpressionFormula_freeClosed (n := 9) (.bound 8) (.bound 7) (.bound 6) (.bound 0) (.bound 3) rfl rfl rfl rfl rfl
    simp [memPairFormula,codeFormula,pairFormula,Project.Formula.forallMem,Project.Formula.existsMem,
      Definitional.Formula.FreeClosed,h1,h2]
  delta0 := .forallMem _ (.forallMem _ (.forallMem _ (.imp
    (.conj (pairExpressionFormula_delta0 _ _ _ _ _) (.conj (pairExpressionFormula_delta0 _ _ _ _ _)
      (.conj (.mem _ _) (.disj (.atom _ _ _) (.mem _ _)))))
    (memPairFormula_delta0 _ _ _))))

private theorem chainSchema_iff {M : SetTheory.Structure.{u}} (he : Extensional M) (C : ExpressionData M.Domain)
    (Reach k : M.Domain) :
    Project.Formula.satisfies ((((((oneEnv C.omega).push C.zero).push C.one).push C.expressions).push Reach).push k)
      chainSchema.body ↔
      ∀ m, M.mem m C.omega → ∀ r, M.mem r C.expressions → ∀ r', M.mem r' C.expressions →
        PairExpression M C r m ∧ PairExpression M C r' k ∧ M.mem C.one m ∧ (m=k ∨ M.mem m k) → MemPair M Reach r r' := by
  simp only [chainSchema,Project.Formula.satisfies_forallMem_iff,Project.Formula.satisfies_imp_iff,
    Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_disj_iff,Project.Formula.satisfies_mem_iff,
    Project.Formula.satisfies_extensionalEq_iff_eq he,pairExpressionFormula_iff he,memPairFormula_iff he]
  rfl

/-- (1,m) 是 (1,k) 的后代（2≤m≤k），由 E₁(1,n+2)=(1,n+1) 经内部自然数归纳。 -/
theorem seed_chain_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {D : TheoremData M.Domain} (hD : D.Valid M) (hF : OrderFacts M D.expr D.arith) {Reach : M.Domain}
    (hR : Reachability.Relation M D.expr D.keys D.expansion Reach) {m k r r' : M.Domain}
    (hm : M.mem m D.expr.omega) (hk : M.mem k D.expr.omega) (hr : PairExpression M D.expr r m)
    (hr' : PairExpression M D.expr r' k) (h1m : M.mem D.expr.one m) (hmk : m=k ∨ M.mem m k) :
    MemPair M Reach r r' := by
  have hC := hD.expr
  have hOrd := omega_isOrdinal_d hM hC.omega
  have hPos (a : M.Domain) (ha : M.mem a D.expr.omega) (h1a : M.mem D.expr.one a) : M.mem D.expr.zero a :=
    (hOrd.mem ha).transitive D.expr.one h1a D.expr.zero hC.one_succ.predecessor_mem
  let env := ((((oneEnv D.expr.omega).push D.expr.zero).push D.expr.one).push D.expr.expressions).push Reach
  have hAll := natural_induction_d hM chainSchema.toUnarySchema env hC.omega
    (fun e he => (chainSchema_iff hM.1 D.expr Reach e).mpr (by
      intro m _ r _ r' _ hAnte
      obtain ⟨_,_,h1m,hmk⟩ := hAnte
      rcases hmk with he' | hme
      · subst m
        exact False.elim (he D.expr.one h1m)
      · exact False.elim (he m hme)))
    (fun p hp ih k hs => (chainSchema_iff hM.1 D.expr Reach k).mpr (by
      intro m hm r hrE r' hr'E hAnte
      obtain ⟨hr,hr',h1m,hmk⟩ := hAnte
      have hkω := natural_successor_mem_d hM hC hp hs
      rcases hmk with hmk | hmk
      · subst m
        have hrr := pair_expression_unique hM.1 hC hr hr'
        subst r'
        exact hR.reflexive_d hM hC hrE
      · have hmp : m=p ∨ M.mem m p := by
          rcases (hs m).mp hmk with h | h
          · exact .inr h
          · exact .inl (hM.1.eq_of_same_members m p h)
        have h1p : M.mem D.expr.one p := by
          rcases hmp with he | h
          · exact he ▸ h1m
          · exact (hOrd.mem hp).transitive m h D.expr.one h1m
        obtain ⟨rp,hrp,hrpE⟩ := pair_expression_exists_d' hM hC hp (hPos p hp h1p)
        have hLower := (chainSchema_iff hM.1 D.expr Reach p).mp ih m hm r hrE rp hrpE ⟨hr,hrp,h1m,hmp⟩
        rcases natural_cases hM hC.omega hp with hEmpty | ⟨n,hn,hpn⟩
        · exact False.elim (hEmpty D.expr.one h1p)
        · have hExp := hF.seed_step n hn p k hpn hs r' rp hr' hrp
          have hStep := hR.actual_expansion_reachable_d hM hC hD.graph hExp
          exact hR.transitive_d hM hC hLower hStep))
  exact (chainSchema_iff hM.1 D.expr Reach k).mp (hAll k hk) m hm r
    (pair_expression_legal_d hM hC (hPos m hm h1m) hr) r'
    (pair_expression_legal_d hM hC (hPos k hk (hmk.elim (fun he => he ▸ h1m) (fun h => (hOrd.mem hk).transitive m h D.expr.one h1m))) hr')
    ⟨hr,hr',h1m,hmk⟩

/-- 任意两个种子有共同的种子祖先（较大的那个）。 -/
theorem seeds_join_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {D : TheoremData M.Domain} (hD : D.Valid M) (hF : OrderFacts M D.expr D.arith) {Reach : M.Domain}
    (hR : Reachability.Relation M D.expr D.keys D.expansion Reach) {s t : M.Domain}
    (hs : Seed M D.expr s) (ht : Seed M D.expr t) :
    ∃ u, Seed M D.expr u ∧ MemPair M Reach s u ∧ MemPair M Reach t u := by
  obtain ⟨m,hm,h1m,hsm⟩ := hs
  obtain ⟨k,hk,h1k,htk⟩ := ht
  rcases (omega_isOrdinal_d hM hD.expr.omega).wellOrder.linear.compare m hm k hk with he | hmk | hkm
  · have hmk := hM.1.eq_of_same_members m k he
    subst k
    exact ⟨t,⟨m,hm,h1k,htk⟩,seed_chain_d hM hD hF hR hm hm hsm htk h1m (.inl rfl),
      seed_chain_d hM hD hF hR hm hm htk htk h1m (.inl rfl)⟩
  · exact ⟨t,⟨k,hk,h1k,htk⟩,seed_chain_d hM hD hF hR hm hk hsm htk h1m (.inr hmk),
      seed_chain_d hM hD hF hR hk hk htk htk h1k (.inl rfl)⟩
  · exact ⟨s,⟨m,hm,h1m,hsm⟩,seed_chain_d hM hD hF hR hm hm hsm hsm h1m (.inl rfl),
      seed_chain_d hM hD hF hR hk hm htk hsm h1k (.inr hkm)⟩

theorem gen_clause_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {D : TheoremData M.Domain} (hD : D.Valid M) {χ μ : M.Domain} (hW : RankWitness M D.expr D.arith χ μ)
    (hF : OrderFacts M D.expr D.arith) : GenClause M D := by
  obtain ⟨Reach,hR⟩ := Reachability.reach_relation_exists_d hM hD.expr D.keys D.expansion
  obtain ⟨L,hL⟩ := lex_relation_exists_d hM hD.expr
  obtain ⟨Seeds,hSeeds⟩ := seed_set_exists_d hM hD.expr
  have hSub : M.MemberSubset Seeds D.expr.expressions := fun r hr => ((hSeeds r).mp hr).legal_d hM hD.expr
  have hJoin : ∀ s, M.mem s Seeds → ∀ t, M.mem t Seeds →
      ∃ u, M.mem u Seeds ∧ MemPair M Reach s u ∧ MemPair M Reach t u := by
    intro s hs t ht
    obtain ⟨u,hu,hSu,hTu⟩ := seeds_join_d hM hD hF hR ((hSeeds s).mp hs) ((hSeeds t).mp ht)
    exact ⟨u,(hSeeds u).mpr hu,hSu,hTu⟩
  obtain ⟨X,hX,_,hWO,_⟩ := (descendant_system_d hM hD hW hF hR hL).generated_wellorder_d hM hSub hJoin
  refine ⟨X,fun x => (hX x).trans (and_congr Iff.rfl ?_),
    lex_wellOrder_of_internal_d hM hD.expr hL (fun x hx => ((hX x).mp hx).1) hWO⟩
  exact ⟨fun ⟨r,hr,hxr⟩ => ⟨r,(hSeeds r).mp hr,(hR.rows x r).mp hxr⟩,
    fun ⟨r,hr,hxr⟩ => ⟨r,(hSeeds r).mpr hr,(hR.rows x r).mpr hxr⟩⟩

end KP1Y.OneYTheorem
