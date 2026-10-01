import KP1Y.OneYExpansionOrderLex
import KP1Y.RankedDescendantOrder

/-! Y07b：实际 Seeds (1,m)，m≥2；单步恒等式 E₁(1,n+2)=(1,n+1)（任意内部 n）；
种子链、任意两种子的共同种子祖先，以及实际后代并集 G。 -/
namespace KP1Y.OneYFinite.Seeds
open YesMetaZFC YesMetaZFC.SetTheory YesMetaZFC.SetTheory.Definitional
open KP1Y.Kuratowski KP1Y.Functions KP1Y.Naturals KP1Y.Bounded KP1Y.Arithmetic
open KP1Y.OneYFinite KP1Y.OneYFinite.Expansion
universe u

/-- 二元表达式 (1,b)。定义体与 LANE-E `PairExpressionIn` 逐字相同。 -/
def PairAtIn (M : SetTheory.Structure.{u}) (w z o s b : M.Domain) : Prop :=
  ∃two, M.mem two w ∧ M.SuccessorOf two o ∧ Graph M s two w ∧ MemPair M s z o ∧ MemPair M s o b

abbrev PairAt (M : SetTheory.Structure.{u}) (C : ExpressionData M.Domain) (s b : M.Domain) : Prop :=
  PairAtIn M C.omega C.zero C.one s b

def pairAtFormula {n : Nat} (w z o s b : Project.Term n) : Project.Formula 1 n :=
  Project.Formula.existsMem w (.conj (successorFormula (.bound 0) o.weaken)
    (.conj (graphFormula s.weaken (.bound 0) w.weaken)
      (.conj (memPairFormula s.weaken z.weaken o.weaken) (memPairFormula s.weaken o.weaken b.weaken))))

theorem pairAtFormula_delta0 {n : Nat} (w z o s b : Project.Term n) : (pairAtFormula w z o s b).IsDelta0 :=
  .existsMem _ (.conj (successorFormula_delta0 _ _) (.conj (graphFormula_delta0 _ _ _)
    (.conj (memPairFormula_delta0 _ _ _) (memPairFormula_delta0 _ _ _))))

theorem pairAtFormula_iff {M : SetTheory.Structure.{u}} (he : Extensional M) {n : Nat} (e : Env M n)
    (w z o s b : Project.Term n) :
    Project.Formula.satisfies e (pairAtFormula w z o s b) ↔ PairAtIn M (w.eval e) (z.eval e) (o.eval e) (s.eval e) (b.eval e) := by
  simp only [pairAtFormula,Project.Formula.satisfies_existsMem_iff,Project.Formula.satisfies_conj_iff,
    successorFormula_iff he,graphFormula_iff he,memPairFormula_iff he,Term.eval_weaken]
  rfl

private theorem two_cases {M : SetTheory.Structure.{u}} (he : Extensional M) {C : ExpressionData M.Domain} (hC : C.Valid M)
    {two i : M.Domain} (hTwo : M.SuccessorOf two C.one) (hi : M.mem i two) : i=C.zero ∨ i=C.one := by
  rcases (hTwo i).mp hi with hi1 | hie
  · rcases (hC.one_succ i).mp hi1 with hi0 | hie0
    · exact False.elim (hC.zero_empty i hi0)
    · exact .inl (he.eq_of_same_members i C.zero hie0)
  · exact .inr (he.eq_of_same_members i C.one hie)

theorem PairAt.legal {M : SetTheory.Structure.{u}} (he : Extensional M) {C : ExpressionData M.Domain} (hC : C.Valid M)
    {s b two : M.Domain} (hPos : M.mem C.zero b) (htwo : M.mem two C.omega) (hTwo : M.SuccessorOf two C.one)
    (hS : Graph M s two C.omega) (h0 : MemPair M s C.zero C.one) (h1 : MemPair M s C.one b) :
    LegalAt M C.omega C.zero C.one s two := by
  refine ⟨⟨htwo,hS⟩,?_,Or.inr h0⟩
  intro i hi a _ hia
  rcases two_cases he hC hTwo hi with rfl | rfl
  · exact (hS.unique C.zero a C.one hia h0) ▸ hC.one_succ.predecessor_mem
  · exact (hS.unique C.one a b hia h1) ▸ hPos

theorem PairAt.unique {M : SetTheory.Structure.{u}} (he : Extensional M) {C : ExpressionData M.Domain} (hC : C.Valid M)
    {s s' b : M.Domain} (h : PairAt M C s b) (h' : PairAt M C s' b) : s=s' := by
  obtain ⟨two,_,hTwo,hS,h0,h1⟩ := h
  obtain ⟨two',_,hTwo',hS',h0',h1'⟩ := h'
  have htt := Structure.SuccessorOf.eq he hTwo' hTwo
  subst two'
  apply hS.ext he hS'
  intro i hi v
  rcases two_cases he hC hTwo hi with rfl | rfl
  · exact ⟨fun hv => (hS.unique _ v _ hv h0) ▸ h0',fun hv => (hS'.unique _ v _ hv h0') ▸ h0⟩
  · exact ⟨fun hv => (hS.unique _ v _ hv h1) ▸ h1',fun hv => (hS'.unique _ v _ hv h1') ▸ h1⟩

theorem pair_at_exists_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {b : M.Domain} (hb : M.mem b C.omega) (hPos : M.mem C.zero b) :
    ∃s, PairAt M C s b ∧ M.mem s C.expressions := by
  obtain ⟨two,s,hTwo,hL,hRows,_⟩ := pair_expression_exists_d hM hC hb hPos
  exact ⟨s,⟨two,hL.1.1,hTwo,hL.1.2,(hRows C.zero C.one).mpr (.inl ⟨rfl,rfl⟩),(hRows C.one b).mpr (.inr ⟨rfl,rfl⟩)⟩,
    (hC.expressions s).mpr ⟨two,hL.1.1,hL⟩⟩

theorem PairAt.expression {M : SetTheory.Structure.{u}} (he : Extensional M) {C : ExpressionData M.Domain} (hC : C.Valid M)
    {s b : M.Domain} (hPos : M.mem C.zero b) (h : PairAt M C s b) : M.mem s C.expressions := by
  obtain ⟨two,htwo,hTwo,hS,h0,h1⟩ := h
  exact (hC.expressions s).mpr ⟨two,htwo,PairAt.legal he hC hPos htwo hTwo hS h0 h1⟩

private theorem successor_positive_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {n a : M.Domain} (ha : M.SuccessorOf a n) (haω : M.mem a C.omega) :
    M.mem C.zero a :=
  (hC.zero_mem_iff hM haω).mpr (fun he => hC.zero_empty n (he ▸ ha.predecessor_mem))

/-- 正自然数的后继至少为二：one∈b。 -/
private theorem one_mem_successor_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {a b : M.Domain} (haω : M.mem a C.omega)
    (hPos : M.mem C.zero a) (hb : M.SuccessorOf b a) : M.mem C.one b := by
  have hw := omega_isOrdinal_d hM hC.omega
  have hSub : M.MemberSubset C.one a := by
    intro x hx
    rcases (hC.one_succ x).mp hx with hx0 | hSame
    · exact False.elim (hC.zero_empty x hx0)
    · exact (hM.1.eq_of_same_members x C.zero hSame) ▸ hPos
  rcases ordinal_subset_cases_d hM (hw.mem hC.one_nat) (hw.mem haω) hSub with he | hlt
  · exact he ▸ hb.predecessor_mem
  · exact (hb C.one).mpr (.inl hlt)

/-- 单根坏部 (y=0,x=1) 的一次复制宽度为二。 -/
private theorem seed_width_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {A : CopyCoordinates.Context M.Domain} (hA : A.Valid M C) (hLast : A.last=C.one) {width two : M.Domain}
    (hW : CopyCoordinates.Width M C T A C.one width) (hTwo : M.SuccessorOf two C.one) : width=two := by
  have hRoot : A.root=C.zero := by
    have hy := hA.below
    rw [hLast] at hy
    rcases (hC.one_succ A.root).mp hy with hy0 | hSame
    · exact False.elim (hC.zero_empty A.root hy0)
    · exact hM.1.eq_of_same_members A.root C.zero hSame
  have hSumL := hA.root_add_length_d hM hC
  rw [hRoot,hLast] at hSumL
  have hLω := hA.length_nat hM.1
  have hL1 : A.length=C.one := (sum_unique_d hM (natural_sum_comm_d hM hC hC.zero_nat hLω hSumL)
    (sum_zero_d hM A.length hC.zero_empty)).symm
  obtain ⟨_,_,off,hOff,hMul,hAdd⟩ := hW
  have hProd := (hT.mul.mul_iff_product hM hC.one_nat hLω).mp hMul
  rw [hL1] at hProd
  have hOff1 : off=C.one := natural_product_one_left_d hM hC hC.one_nat hProd
  subst off
  have hSum := (hT.add.add_iff_sum hM hA.last hOff).mp hAdd
  rw [hLast] at hSum
  have hs := sum_successor_d hM hC.one_succ (sum_zero_d hM C.one hC.zero_empty) hSum
  exact Structure.SuccessorOf.eq hM.1 hs hTwo

/-- Y07b 单步：E₁((1,n+2))=(1,n+1)，对任意内部 n。形状与 LANE-E `OrderFacts.seed_step` 逐字一致。 -/
theorem seed_step_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C) :
    ∀n, M.mem n C.omega → ∀a b, M.SuccessorOf a n → M.SuccessorOf b a → ∀s t,
      PairAt M C s b → PairAt M C t a → Expansion.Expands M C T s C.one t := by
  intro n hn a b ha hb s t hS hTa
  have haω := natural_successor_mem_d hM hC hn ha
  have hbω := natural_successor_mem_d hM hC haω hb
  have hPosA := successor_positive_d hM hC ha haω
  have hPosB := successor_positive_d hM hC hb hbω
  have hOneB := one_mem_successor_d hM hC haω hPosA hb
  have hSexp := PairAt.expression hM.1 hC hPosB hS
  obtain ⟨two,htwo,hTwo,hSg,hS0,hS1⟩ := hS
  have hLegal := PairAt.legal hM.1 hC hPosB htwo hTwo hSg hS0 hS1
  obtain ⟨t',hExp⟩ := expands_exists_d hM hC hT hSexp hC.one_nat
  have hExpSaved := hExp
  obtain ⟨_,m,_,hLegal',hCases⟩ := hExp
  have hmm := legal_length_unique hM.1 hLegal' hLegal
  subst m
  have hOneNe : C.one≠C.zero := fun he => hC.zero_empty C.zero (he ▸ hC.one_succ.predecessor_mem)
  rcases hCases with ⟨hm0,_⟩ | ⟨last,hl,hSucc,hDrop | ⟨W,hSuccess⟩⟩
  · exact False.elim (hC.zero_empty C.one (hm0 ▸ hTwo.predecessor_mem))
  · have hll := Structure.SuccessorOf.predecessor_eq hM.1 ((omega_isOrdinal_d hM hC.omega).mem hl) hSucc hTwo
    subst last
    have hb1 := hSg.unique C.one b C.one hS1 hDrop.1
    subst b
    exact False.elim (SetTheory.KP.mem_irrefl_d (KP1Y.models_weakKP hM) C.one hOneB)
  · have hll := Structure.SuccessorOf.predecessor_eq hM.1 ((omega_isOrdinal_d hM hC.omega).mem hl) hSucc hTwo
    subst last
    obtain ⟨hxn,hSeam⟩ := ExpansionOrder.Successful.first_seam_d hM hC hT hSuccess hTwo hOneNe
    have hAgree := hSuccess.prefix_old_d hM hC hT hTwo
    have hLt := hSuccess.legal_d hM hC hT
    have hWidth := seed_width_d hM hC hT hSuccess.coordinates hSuccess.last hSuccess.width hTwo
    obtain ⟨a',_,hA'⟩ := hLt.1.2.total C.one hxn
    have haa := Structure.SuccessorOf.predecessor_eq hM.1 ((omega_isOrdinal_d hM hC.omega).mem haω) hb (hSeam a' b hA' hS1)
    subst a'
    have hT0 : MemPair M t' C.zero C.one := (hAgree C.zero hC.one_succ.predecessor_mem C.one).mpr hS0
    have hPair : PairAt M C t' a := ⟨two,htwo,hTwo,hWidth ▸ hLt.1.2,hT0,hA'⟩
    have htt := PairAt.unique hM.1 hC hPair hTa
    subst t
    exact hExpSaved

/-- 种子 (1,m)，m≥2（内部 ω）。 -/
def IsSeed (M : SetTheory.Structure.{u}) (C : ExpressionData M.Domain) (r : M.Domain) : Prop :=
  ∃m, M.mem m C.omega ∧ M.mem C.one m ∧ PairAt M C r m

private def seedEnv {M : SetTheory.Structure.{u}} (C : ExpressionData M.Domain) : Env M 3 :=
  ((oneEnv C.omega).push C.zero).push C.one

private def seedSchema : Project.Delta0UnarySchema 3 where
  body := Project.Formula.existsMem (.bound 3)
    (.conj (.mem (.bound 2) (.bound 0)) (pairAtFormula (.bound 4) (.bound 3) (.bound 2) (.bound 1) (.bound 0)))
  freeClosed := by
    simp [pairAtFormula,successorFormula,graphFormula,memPairFormula,codeFormula,pairFormula,Project.Formula.forallMem,
      Project.Formula.existsMem,Project.Formula.subset,Project.Formula.extensionalEq,Definitional.Formula.FreeClosed]
  delta0 := .existsMem _ (.conj (.mem _ _) (pairAtFormula_delta0 _ _ _ _ _))

/-- 实际种子集合 Seeds⊆E（Δ₀ 分离）。 -/
theorem seed_set_exists_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    (C : ExpressionData M.Domain) :
    ∃Seeds, ∀r, M.mem r Seeds ↔ M.mem r C.expressions ∧ IsSeed M C r := by
  obtain ⟨S,hS⟩ := SetTheory.KP.separation_exists_d (KP1Y.models_weakKP hM) seedSchema (seedEnv C) C.expressions
  refine ⟨S,fun r => (hS r).trans (and_congr_right fun _ => ?_)⟩
  simp only [seedSchema,seedEnv,Project.Formula.satisfies_existsMem_iff,Project.Formula.satisfies_conj_iff,
    Project.Formula.satisfies_mem_iff,pairAtFormula_iff hM.1]
  rfl

theorem IsSeed.expression {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {r : M.Domain} (h : IsSeed M C r) : M.mem r C.expressions := by
  obtain ⟨m,hm,h1m,hP⟩ := h
  exact PairAt.expression hM.1 hC (((omega_isOrdinal_d hM hC.omega).mem hm).transitive C.one h1m C.zero
    hC.one_succ.predecessor_mem) hP

private def chainEnv {M : SetTheory.Structure.{u}} (C : ExpressionData M.Domain) (Reach : M.Domain) : Env M 5 :=
  ((((oneEnv C.omega).push C.zero).push C.one).push C.expressions).push Reach

private def chainSchema : Project.Delta0UnarySchema 5 where
  body := Project.Formula.forallMem (.bound 5) (Project.Formula.forallMem (.bound 3) (Project.Formula.forallMem (.bound 4)
    (.imp (.mem (.bound 6) (.bound 2)) (.imp (.disj (Project.Formula.extensionalEq (.bound 2) (.bound 3)) (.mem (.bound 2) (.bound 3)))
      (.imp (pairAtFormula (.bound 8) (.bound 7) (.bound 6) (.bound 1) (.bound 2))
        (.imp (pairAtFormula (.bound 8) (.bound 7) (.bound 6) (.bound 0) (.bound 3))
          (memPairFormula (.bound 4) (.bound 1) (.bound 0))))))))
  freeClosed := by
    simp [pairAtFormula,successorFormula,graphFormula,memPairFormula,codeFormula,pairFormula,Project.Formula.forallMem,
      Project.Formula.existsMem,Project.Formula.subset,Project.Formula.extensionalEq,Definitional.Formula.FreeClosed]
  delta0 := .forallMem _ (.forallMem _ (.forallMem _ (.imp (.mem _ _) (.imp (.disj (.atom _ _ _) (.mem _ _))
    (.imp (pairAtFormula_delta0 _ _ _ _ _) (.imp (pairAtFormula_delta0 _ _ _ _ _) (memPairFormula_delta0 _ _ _)))))))

private theorem chainSchema_iff {M : SetTheory.Structure.{u}} (he : Extensional M)
    (C : ExpressionData M.Domain) (Reach k : M.Domain) :
    Project.Formula.satisfies ((chainEnv C Reach).push k) chainSchema.body ↔
      ∀m, M.mem m C.omega → ∀r, M.mem r C.expressions → ∀r', M.mem r' C.expressions →
        M.mem C.one m → (m=k ∨ M.mem m k) → PairAt M C r m → PairAt M C r' k → MemPair M Reach r r' := by
  simp only [chainSchema,chainEnv,Project.Formula.satisfies_forallMem_iff,Project.Formula.satisfies_imp_iff,
    Project.Formula.satisfies_mem_iff,Project.Formula.satisfies_disj_iff,Project.Formula.satisfies_extensionalEq_iff_eq he,
    pairAtFormula_iff he,memPairFormula_iff he]
  rfl

/-- 种子链：2≤m≤k 时 (1,m) 是 (1,k) 的实际后代（对内部 k 作对象自然数归纳）。 -/
theorem seed_chain_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {Keys EN Reach : M.Domain} (hEN : Expansion.Graph M C T Keys EN) (hR : Reachability.Relation M C Keys EN Reach)
    {m k r r' : M.Domain} (hm : M.mem m C.omega) (hk : M.mem k C.omega) (h1m : M.mem C.one m) (hmk : m=k ∨ M.mem m k)
    (hP : PairAt M C r m) (hP' : PairAt M C r' k) : MemPair M Reach r r' := by
  have hw := omega_isOrdinal_d hM hC.omega
  have hPosOf {b : M.Domain} (hb : M.mem b C.omega) (h1 : M.mem C.one b) : M.mem C.zero b :=
    (hw.mem hb).transitive C.one h1 C.zero hC.one_succ.predecessor_mem
  have hAll := natural_induction_d hM chainSchema.toUnarySchema (chainEnv C Reach) hC.omega
    (fun e hEmpty => (chainSchema_iff hM.1 C Reach e).mpr (by
      intro m _ r _ r' _ h1m hme _ _
      rcases hme with he | hlt
      · exact False.elim (hEmpty C.one (he ▸ h1m))
      · exact False.elim (hEmpty m hlt)))
    (fun p hp ih q hq => (chainSchema_iff hM.1 C Reach q).mpr (by
      intro m hm r hr r' hr' h1m hmq hPr hPr'
      rcases hmq with he | hlt
      · subst m
        have hrr := PairAt.unique hM.1 hC hPr hPr'
        subst r'
        exact hR.reflexive_d hM hC hr
      · have hmp : m=p ∨ M.mem m p := by
          rcases (hq m).mp hlt with hmp | hSame
          · exact .inr hmp
          · exact .inl (hM.1.eq_of_same_members m p hSame)
        have h1p : M.mem C.one p := by
          rcases hmp with he | hmp
          · exact he ▸ h1m
          · exact (hw.mem hp).transitive m hmp C.one h1m
        obtain ⟨r'',hPr'',hr''⟩ := pair_at_exists_d hM hC hp (hPosOf hp h1p)
        have hReach := (chainSchema_iff hM.1 C Reach p).mp ih m hm r hr r'' hr'' h1m hmp hPr hPr''
        rcases natural_cases hM hC.omega hp with hEmpty | ⟨p0,hp0,hps⟩
        · exact False.elim (hEmpty C.one h1p)
        · have hExp := seed_step_d hM hC hT p0 hp0 p q hps hq r' r'' hPr' hPr''
          exact hR.transitive_d hM hC hReach (hR.actual_expansion_reachable_d hM hC hEN hExp)))
  exact (chainSchema_iff hM.1 C Reach k).mp (hAll k hk) m hm r (PairAt.expression hM.1 hC (hPosOf hm h1m) hP)
    r' (PairAt.expression hM.1 hC (hPosOf hk (by
      rcases hmk with he | hlt
      · exact he ▸ h1m
      · exact (hw.mem hk).transitive m hlt C.one h1m)) hP') h1m hmk hP hP'

/-- 任意两种子有共同种子祖先（取较大参数的种子）。 -/
theorem seeds_join_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {Keys EN Reach Seeds : M.Domain} (hEN : Expansion.Graph M C T Keys EN) (hR : Reachability.Relation M C Keys EN Reach)
    (hSeeds : ∀r, M.mem r Seeds ↔ M.mem r C.expressions ∧ IsSeed M C r) :
    ∀s, M.mem s Seeds → ∀t, M.mem t Seeds → ∃u, M.mem u Seeds ∧ MemPair M Reach s u ∧ MemPair M Reach t u := by
  intro s hs t ht
  obtain ⟨hsE,m,hm,h1m,hPs⟩ := (hSeeds s).mp hs
  obtain ⟨htE,k,hk,h1k,hPt⟩ := (hSeeds t).mp ht
  rcases (omega_isOrdinal_d hM hC.omega).wellOrder.linear.compare m hm k hk with he | hmk | hkm
  · have hmk := hM.1.eq_of_same_members m k he
    subst k
    have hst := PairAt.unique hM.1 hC hPs hPt
    subst t
    exact ⟨s,hs,hR.reflexive_d hM hC hsE,hR.reflexive_d hM hC hsE⟩
  · exact ⟨t,ht,seed_chain_d hM hC hT hEN hR hm hk h1m (.inr hmk) hPs hPt,hR.reflexive_d hM hC htE⟩
  · exact ⟨s,hs,hR.reflexive_d hM hC hsE,seed_chain_d hM hC hT hEN hR hk hm h1k (.inr hkm) hPt hPs⟩

/-- 实际 G：Seeds 的实际可达后代之并（不扩大为全部 E）。 -/
theorem generated_set_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (Reach Seeds : M.Domain) :
    ∃G, ∀x, M.mem x G ↔ M.mem x C.expressions ∧ ∃s, M.mem s Seeds ∧ MemPair M Reach x s :=
  KP1Y.Dynamics.generated_set_exists_d hM C.expressions Reach Seeds

/-- 给定实际 DescendantSystem（秩字段由 μ 支线提供），G 上 Lex 为内部良序且等于严格可达。 -/
theorem generated_wellorder_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {Keys EN Reach Lex χ μ : M.Domain} (hEN : Expansion.Graph M C T Keys EN) (hR : Reachability.Relation M C Keys EN Reach)
    (hSys : KP1Y.Dynamics.DescendantSystem M C.omega C.expressions χ μ Keys EN Reach Lex) :
    ∃Seeds G, (∀r, M.mem r Seeds ↔ M.mem r C.expressions ∧ IsSeed M C r) ∧
      (∀x, M.mem x G ↔ M.mem x C.expressions ∧ ∃s, M.mem s Seeds ∧ MemPair M Reach x s) ∧
      M.MemberSubset Seeds G ∧ KP1Y.InternalWellOrder M Lex G ∧ ∀x, M.mem x G → ∀y, M.mem y G →
        (MemPair M Lex x y ↔ x≠y ∧ MemPair M Reach x y) := by
  obtain ⟨Seeds,hSeeds⟩ := seed_set_exists_d hM C
  obtain ⟨G,hG,hSub,hWO,hIff⟩ := hSys.generated_wellorder_d hM (fun r hr => ((hSeeds r).mp hr).1)
    (seeds_join_d hM hC hT hEN hR hSeeds)
  exact ⟨Seeds,G,hSeeds,hG,hSub,hWO,hIff⟩

/-! ### LANE-E `OneYTheorem.OrderFacts` 三字段的逐字形状（无条件） -/

theorem order_index_mono_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C) :
    ∀ Keys EN Reach, Expansion.Graph M C T Keys EN → Reachability.Relation M C Keys EN Reach →
      ∀ s i j t u, (i=j ∨ M.mem i j) → KP1Y.Dynamics.Expansion M Keys EN s i t →
        KP1Y.Dynamics.Expansion M Keys EN s j u → MemPair M Reach t u :=
  fun _ _ _ hEN hR _ _ _ _ _ hij ht hu => ExpansionOrder.index_mono_d hM hC hT hEN hR hij ht hu

theorem order_lex_descent_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C) :
    ∀ s, M.mem s C.expressions → s≠C.zero → ∀ N, M.mem N C.omega → ∀ t,
      Expansion.Expands M C T s N t → Lex M C t s :=
  fun _ _ hs _ _ _ h => ExpansionOrder.Expands.lex_d hM hC hT h hs

theorem order_seed_step_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C) :
    ∀ n, M.mem n C.omega → ∀ a b, M.SuccessorOf a n → M.SuccessorOf b a → ∀ s t,
      PairAt M C s b → PairAt M C t a → Expansion.Expands M C T s C.one t :=
  seed_step_d hM hC hT

end KP1Y.OneYFinite.Seeds
