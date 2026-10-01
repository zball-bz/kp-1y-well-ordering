import KP1Y.OneYExpansionOrderSeam
import KP1Y.OneYExpansionOrder
import KP1Y.RankedDescendantOrder

/-! (c) 实际展开严格降低字典序：E_N(s) <lex s（s≠∅）。N=0或末值1为真前缀；
否则第一差异在 x=|s|-1，且 E_N(s)[x]+1=s[x]。另将 Y07a 全部字段打包为 O02 的实际 DescendantSystem 字段。 -/
namespace KP1Y.OneYFinite.ExpansionOrder
open YesMetaZFC YesMetaZFC.SetTheory YesMetaZFC.SetTheory.Definitional
open KP1Y.Kuratowski KP1Y.Functions KP1Y.Naturals KP1Y.Bounded
open KP1Y.OneYFinite KP1Y.OneYFinite.Expansion
universe u

/-- 成功分支且 N≠0：第一差异位于 x=last，新值比原值少一。 -/
theorem Successful.lex_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {s m last N t : M.Domain} {W : SuccessData M.Domain} (h : Successful M C T s m last N t W)
    (hLegal : LegalAt M C.omega C.zero C.one s m) (hLast : M.SuccessorOf m last) (hN : N≠C.zero) : Lex M C t s := by
  obtain ⟨hxn,hSeam⟩ := Successful.first_seam_d hM hC hT h hLast hN
  have hAgree := h.prefix_old_d hM hC hT hLast
  have hLt := h.legal_d hM hC hT
  obtain ⟨b,hb,hB⟩ := hLegal.1.2.total last hLast.predecessor_mem
  obtain ⟨a,ha,hA⟩ := hLt.1.2.total last hxn
  exact (Lex.at_iff hM.1 hLt hLegal).mpr ⟨last,hLast.predecessor_mem,fun i hi v _ => hAgree i hi v,
    .inr ⟨hxn,a,ha,b,hb,hA,hB,(hSeam a b hA hB).predecessor_mem⟩⟩

/-- 真前缀（长度last<m）严格字典序更小。 -/
theorem prefix_last_lex_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {s m last t : M.Domain}
    (hLegal : LegalAt M C.omega C.zero C.one s m) (hl : M.mem last C.omega) (hLast : M.SuccessorOf m last)
    (hPrefix : Prefix M t s last C.omega) : Lex M C t s := by
  have hSub : M.MemberSubset last m := fun c hc => (hLast c).mpr (.inl hc)
  refine Lex.true_prefix_d hM hC (prefix_legal_d hM hC hLegal hl hSub hPrefix) hLegal hPrefix hSub ?_
  intro he
  exact SetTheory.KP.mem_irrefl_d (KP1Y.models_weakKP hM) last (he ▸ hLast.predecessor_mem)

theorem Expands.lex_of_nonempty_length_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {s N t : M.Domain} (h : Expands M C T s N t)
    (hNe : ∀m, LegalAt M C.omega C.zero C.one s m → m≠C.zero) : Lex M C t s := by
  obtain ⟨_,m,_,hLegal,hCases⟩ := h
  rcases hCases with ⟨hm0,_⟩ | ⟨last,hl,hSucc,hDrop | ⟨W,hSuccess⟩⟩
  · exact False.elim (hNe m hLegal hm0)
  · exact prefix_last_lex_d hM hC hLegal hl hSucc hDrop.2
  · by_cases hN0 : N=C.zero
    · subst N
      exact prefix_last_lex_d hM hC hLegal hl hSucc (hSuccess.zero_prefix_d hM hC hT hSucc)
    · exact Successful.lex_d hM hC hT hSuccess hLegal hSucc hN0

/-- (c) 任一内部 N 与非空实际输入：E_N(s) <lex s。 -/
theorem Expands.lex_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {s N t : M.Domain} (h : Expands M C T s N t) (hs : s≠C.zero) : Lex M C t s := by
  refine Expands.lex_of_nonempty_length_d hM hC hT h (fun m hLegal hm0 => hs ?_)
  subst m
  exact hLegal.1.2.ext hM.1 (empty_graph (V := C.omega) hC.zero_empty) (fun c hc => False.elim (hC.zero_empty c hc))

/-- O02.lex_step 的形状：非平凡实际展开严格字典序下降。 -/
theorem Expands.lex_of_ne_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {s N t : M.Domain} (h : Expands M C T s N t) (hne : t≠s) : Lex M C t s := by
  refine Expands.lex_of_nonempty_length_d hM hC hT h (fun m hLegal hm0 => ?_)
  obtain ⟨_,m',_,hLegal',hCases⟩ := h
  have hmm := legal_length_unique hM.1 hLegal' hLegal
  subst m'
  rcases hCases with ⟨_,ht⟩ | ⟨last,_,hSucc,_⟩
  · exact hne ht
  · exact hC.zero_empty last (hm0 ▸ hSucc.predecessor_mem)

/-- 第一接缝的Expands形式：N≠0且末值b>1时，E_N(s)保留前x项，x在新长度内，且 b=E_N(s)[x]+1。 -/
theorem Expands.first_seam_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {s N t m last b : M.Domain} (h : Expands M C T s N t) (hN : N≠C.zero)
    (hLegal : LegalAt M C.omega C.zero C.one s m) (hLast : M.SuccessorOf m last)
    (hB : MemPair M s last b) (hAbove : M.mem C.one b) :
    ∃n, LegalAt M C.omega C.zero C.one t n ∧ M.mem last n ∧ RowsAgreeOn M t s last ∧
      ∀a, MemPair M t last a → M.SuccessorOf b a := by
  obtain ⟨_,m',_,hLegal',hCases⟩ := h
  have hmm := legal_length_unique hM.1 hLegal' hLegal
  subst m'
  rcases hCases with ⟨hm0,_⟩ | ⟨last',hl',hSucc',hDrop | ⟨W,hSuccess⟩⟩
  · exact False.elim (hC.zero_empty last (hm0 ▸ hLast.predecessor_mem))
  · have hll := Structure.SuccessorOf.predecessor_eq hM.1 ((omega_isOrdinal_d hM hC.omega).mem hl') hSucc' hLast
    subst last'
    have hb1 := hLegal.1.2.unique last b C.one hB hDrop.1
    subst b
    exact False.elim (SetTheory.KP.mem_irrefl_d (KP1Y.models_weakKP hM) C.one hAbove)
  · have hll := Structure.SuccessorOf.predecessor_eq hM.1 ((omega_isOrdinal_d hM hC.omega).mem hl') hSucc' hLast
    subst last'
    obtain ⟨hxn,hSeam⟩ := Successful.first_seam_d hM hC hT hSuccess hLast hN
    exact ⟨W.width,hSuccess.legal_d hM hC hT,hxn,hSuccess.prefix_old_d hM hC hT hLast,fun a hA => hSeam a b hA hB⟩

/-- 交给 O02/LANE-E 的 Y07a 字段，量词形状逐字对应 `KP1Y.Dynamics.DescendantSystem`。 -/
structure OrderFacts (M : SetTheory.Structure.{u}) (ω E Keys F Reach Lex : M.Domain) : Prop where
  index_mono : ∀ s, M.mem s E → ∀ i, M.mem i ω → ∀ j, M.mem j ω → i=j ∨ M.mem i j →
    ∀ t, M.mem t E → ∀ u, M.mem u E → KP1Y.Dynamics.Expansion M Keys F s i t →
      KP1Y.Dynamics.Expansion M Keys F s j u → MemPair M Reach t u
  lex_step : ∀ s, M.mem s E → ∀ n, M.mem n ω → ∀ t, M.mem t E →
    KP1Y.Dynamics.Expansion M Keys F s n t → t≠s → MemPair M Lex t s
  lex_irrefl : ∀ x, M.mem x E → ¬MemPair M Lex x x
  lex_trans : ∀ x, M.mem x E → ∀ y, M.mem y E → ∀ z, M.mem z E →
    MemPair M Lex x y → MemPair M Lex y z → MemPair M Lex x z

/-- 对实际 EN、实际 Reach、实际 Lex 关系图，Y07a 的全部 O02 字段无条件成立。 -/
theorem order_facts_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {Keys EN Reach Lex : M.Domain} (hEN : Expansion.Graph M C T Keys EN)
    (hR : Reachability.Relation M C Keys EN Reach) (hLex : LexRelation M C Lex) :
    OrderFacts M C.omega C.expressions Keys EN Reach Lex where
  index_mono := fun _ _ _ _ _ _ hij _ _ _ _ ht hu => index_mono_d hM hC hT hEN hR hij ht hu
  lex_step := fun _ _ _ _ _ _ hStep hne =>
    (hLex.rows _ _).mpr (Expands.lex_of_ne_d hM hC hT ((Reachability.expansion_step_iff_d hM hC hEN).mp hStep) hne)
  lex_irrefl := fun x _ => hLex.irrefl_d hM x
  lex_trans := fun _ _ _ _ _ _ hXY hYZ => hLex.trans_d hM hC hXY hYZ

/-- 实际 DescendantSystem：除秩下降 μ 字段外全部由实际 EN/Reach/Lex 证明。 -/
theorem descendant_system_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {Keys EN Reach Lex χ μ : M.Domain} (hEN : Expansion.Graph M C T Keys EN)
    (hR : Reachability.Relation M C Keys EN Reach) (hLex : LexRelation M C Lex)
    (hχ : M.IsOrdinal χ) (hμ : Graph M μ C.expressions χ)
    (hRank : ∀s, M.mem s C.expressions → ∀N, M.mem N C.omega → ∀t, M.mem t C.expressions →
      ∀a, M.mem a χ → ∀b, M.mem b χ → KP1Y.Dynamics.Expansion M Keys EN s N t → t≠s →
        MemPair M μ s a → MemPair M μ t b → M.mem b a) :
    KP1Y.Dynamics.DescendantSystem M C.omega C.expressions χ μ Keys EN Reach Lex := by
  have hF := hR.fields_d hM hC
  have hO := order_facts_d hM hC hT hEN hR hLex
  exact ⟨hC.omega,hχ,hμ,hEN.keys,hEN.graph,hF.reflexive,hF.transitive,hF.expansion_reachable,hF.first_step,
    hO.index_mono,hRank,hO.lex_step,hO.lex_irrefl,hO.lex_trans⟩

/-- 秩下降以实际 Expands 与 s≠∅ 表述（即 LANE-D `RankDescends` 的展开体）时同样给出 DescendantSystem。 -/
theorem descendant_system_of_descends_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {Keys EN Reach Lex χ μ : M.Domain} (hEN : Expansion.Graph M C T Keys EN)
    (hR : Reachability.Relation M C Keys EN Reach) (hLex : LexRelation M C Lex)
    (hχ : M.IsOrdinal χ) (hμ : Graph M μ C.expressions χ)
    (hDesc : ∀s, M.mem s C.expressions → s≠C.zero → ∀N, M.mem N C.omega → ∀t, Expansion.Expands M C T s N t →
      ∀a b, MemPair M μ s a → MemPair M μ t b → M.mem b a) :
    KP1Y.Dynamics.DescendantSystem M C.omega C.expressions χ μ Keys EN Reach Lex := by
  refine descendant_system_d hM hC hT hEN hR hLex hχ hμ ?_
  intro s hs N hN t _ a _ b _ hStep hne hA hB
  have hExp := (Reachability.expansion_step_iff_d hM hC hEN).mp hStep
  have hs0 : s≠C.zero := by
    intro he
    subst s
    exact hne ((Expands.empty_iff_d hM hC hT hN).mp hExp)
  exact hDesc s hs hs0 N hN t hExp a b hA hB

end KP1Y.OneYFinite.ExpansionOrder
