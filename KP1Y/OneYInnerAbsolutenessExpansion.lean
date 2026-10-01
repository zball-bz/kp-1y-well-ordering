import KP1Y.OneYInnerAbsoluteness
import KP1Y.OneYRankStatement

/-! Y08 展开部分：L与外部M的实际EN关系相同。L内存在实际展开及其Σ₁证书箱；证书矩阵为
字面Δ₀，故向上绝对；外部展开唯一，因此识别同一输出。覆盖全部内部输入s∈E与N∈ω，
不假设ω标准。由此L中的实际EN图就是外部EN图，L中的秩见证μ就是外部秩见证。 -/
namespace KP1Y.OneYFinite.InnerAbsoluteness
open YesMetaZFC YesMetaZFC.SetTheory YesMetaZFC.SetTheory.Definitional
open KP1Y.Kuratowski KP1Y.Functions KP1Y.Naturals KP1Y.Bounded KP1Y.SetLanguage KP1Y.Classes KP1Y.Constructible
open KP1Y.OneYFinite
universe u

set_option hygiene false in
local notation "𝕃" => innerModel hM env hS

private theorem expansion_env_forget {M : SetTheory.Structure.{u}} {P : M.Domain → Prop} {hNe : ∃ x, P x}
    (D : ExpressionData (classModel M P hNe).Domain) (T : MatrixArithmetic (classModel M P hNe).Domain)
    (AF FL G : (classModel M P hNe).Domain) :
    forgetEnv (Expansion.expansionEnv D T AF FL G) =
      Expansion.expansionEnv (D.map Subtype.val) (T.map Subtype.val) AF.val FL.val G.val := by
  simp only [Expansion.expansionEnv,forgetEnv_push]
  rfl

/-- 向上：L内实际展开的Σ₁证书箱经Δ₀矩阵成为外部证书。 -/
theorem inner_expands_up_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    (env : Env M 24) (hS : FixedSyntax M (defContext.eval env) (defData.eval env) (env.bound 0) (env.bound 1) (env.bound 2))
    {D : ExpressionData (𝕃).Domain} (hD : D.Valid 𝕃) {T : MatrixArithmetic (𝕃).Domain} (hT : T.Valid 𝕃 D)
    {s N t : (𝕃).Domain} (h : Expansion.Expands 𝕃 D T s N t) :
    Expansion.Expands M (D.map Subtype.val) (T.map Subtype.val) s.val N.val t.val := by
  have hTrans := constructible_transitive_class_d hM env hS
  have hL := inner_models_kp_d hM env hS
  have hC := inner_expression_data_outer_valid_d hM env hS hD
  have hTM := inner_matrix_arithmetic_up_d hM env hS hD hT
  obtain ⟨AF,hAF⟩ := ExpressionDiagram.all_forests_exists_d hL hD
  obtain ⟨S,hSp⟩ := MountainReconstruction.spaces_exists_d hL hD AF
  obtain ⟨key,hCode⟩ := codes_total hL s N
  obtain ⟨Box,hBox⟩ := (Expansion.expansion_sigmaOne_iff_d hL hD hT hAF hSp key t).mpr
    ((Expansion.CodedExpands.at_iff hL.1 hD hCode).mpr h)
  have hEnv := expansion_env_forget D T AF S.forestLists S.grids
  have hUp := (witness_matrix_transfer_iff hTrans Expansion.expansionMatrix _ _
    (fun i => congrFun (congrArg Env.bound hEnv) i) key t Box).mp hBox
  have hCoded := (Expansion.expansion_sigmaOne_iff_d hM hC hTM (inner_all_forests_up_d hM env hS hD hAF)
    (inner_spaces_up_d hM env hS hD hSp) key.val t.val).mp ⟨Box.val,hUp⟩
  exact (Expansion.CodedExpands.at_iff hM.1 hC ((codes_class_absolute hM.1 hTrans key s N).mp hCode)).mp hCoded

/-- 双向：内部存在 + 向上绝对 + 外部唯一。 -/
theorem inner_expands_iff_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    (env : Env M 24) (hS : FixedSyntax M (defContext.eval env) (defData.eval env) (env.bound 0) (env.bound 1) (env.bound 2))
    {D : ExpressionData (𝕃).Domain} (hD : D.Valid 𝕃) {T : MatrixArithmetic (𝕃).Domain} (hT : T.Valid 𝕃 D)
    (s N t : (𝕃).Domain) :
    Expansion.Expands 𝕃 D T s N t ↔ Expansion.Expands M (D.map Subtype.val) (T.map Subtype.val) s.val N.val t.val := by
  constructor
  · exact inner_expands_up_d hM env hS hD hT
  · intro h
    have hC := inner_expression_data_outer_valid_d hM env hS hD
    have hTM := inner_matrix_arithmetic_up_d hM env hS hD hT
    obtain ⟨hs,hN,_⟩ := h.legal_d hM hC hTM
    obtain ⟨t',ht'⟩ := Expansion.expands_exists_d (inner_models_kp_d hM env hS) hD hT hs hN
    have hEq : t=t' := Subtype.ext (Expansion.Expands.unique_d hM hC hTM h (inner_expands_up_d hM env hS hD hT ht'))
    rw [hEq]
    exact ht'

/-- 外部任一实际展开的输入、N与输出都在L中，且就是L的实际展开。 -/
theorem outer_expands_inner_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    (env : Env M 24) (hS : FixedSyntax M (defContext.eval env) (defData.eval env) (env.bound 0) (env.bound 1) (env.bound 2))
    {D : ExpressionData (𝕃).Domain} (hD : D.Valid 𝕃) {T : MatrixArithmetic (𝕃).Domain} (hT : T.Valid 𝕃 D)
    {s N t : M.Domain} (h : Expansion.Expands M (D.map Subtype.val) (T.map Subtype.val) s N t) :
    ∃ s0 N0 t0 : (𝕃).Domain, s0.val=s ∧ N0.val=N ∧ t0.val=t ∧ Expansion.Expands 𝕃 D T s0 N0 t0 := by
  have hTrans := constructible_transitive_class_d hM env hS
  obtain ⟨hs,hN,ht⟩ := h.legal_d hM (inner_expression_data_outer_valid_d hM env hS hD) (inner_matrix_arithmetic_up_d hM env hS hD hT)
  let s0 : (𝕃).Domain := ⟨s,hTrans D.expressions.val D.expressions.property s hs⟩
  let N0 : (𝕃).Domain := ⟨N,hTrans D.omega.val D.omega.property N hN⟩
  let t0 : (𝕃).Domain := ⟨t,hTrans D.expressions.val D.expressions.property t ht⟩
  exact ⟨s0,N0,t0,rfl,rfl,rfl,(inner_expands_iff_d hM env hS hD hT s0 N0 t0).mpr h⟩

/-- 与任意外部有效E、T比较：二者由唯一性分别等于L侧数据的值。 -/
theorem inner_expands_outer_iff_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    (env : Env M 24) (hS : FixedSyntax M (defContext.eval env) (defData.eval env) (env.bound 0) (env.bound 1) (env.bound 2))
    {D : ExpressionData (𝕃).Domain} (hD : D.Valid 𝕃) {T0 : MatrixArithmetic (𝕃).Domain} (hT0 : T0.Valid 𝕃 D)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    (s N t : (𝕃).Domain) : Expansion.Expands 𝕃 D T0 s N t ↔ Expansion.Expands M C T s.val N.val t.val := by
  have hDC := expression_data_unique hM.1 (inner_expression_data_outer_valid_d hM env hS hD) hC
  subst hDC
  have hTT := matrix_arithmetic_unique hM.1 (inner_matrix_arithmetic_up_d hM env hS hD hT0) hT
  subst hTT
  exact inner_expands_iff_d hM env hS hD hT0 s N t

/-- L的实际全局EN图(Keys=E×ω)就是外部实际EN图。 -/
theorem inner_expansion_graph_up_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    (env : Env M 24) (hS : FixedSyntax M (defContext.eval env) (defData.eval env) (env.bound 0) (env.bound 1) (env.bound 2))
    {D : ExpressionData (𝕃).Domain} (hD : D.Valid 𝕃) {T : MatrixArithmetic (𝕃).Domain} (hT : T.Valid 𝕃 D)
    {Keys EN : (𝕃).Domain} (h : Expansion.Graph 𝕃 D T Keys EN) :
    Expansion.Graph M (D.map Subtype.val) (T.map Subtype.val) Keys.val EN.val := by
  have hTrans := constructible_transitive_class_d hM env hS
  have hL := inner_models_kp_d hM env hS
  have hKeys := (product_class_absolute_d hM hTrans hL Keys D.expressions D.omega).mp h.keys
  have hGM := (graph_class_absolute hM.1 hTrans EN Keys D.expressions).mp h.graph
  refine ⟨hKeys,hGM,fun key t => ?_⟩
  constructor
  · intro hAt
    obtain ⟨hk,ht⟩ := hGM.bounds hM.1 hAt
    let k0 : (𝕃).Domain := ⟨key,hTrans Keys.val Keys.property key hk⟩
    let t0 : (𝕃).Domain := ⟨t,hTrans D.expressions.val D.expressions.property t ht⟩
    obtain ⟨s,hs,N,hN,hCode,hExp⟩ := (h.rows k0 t0).mp ((memPair_class_absolute hM.1 hTrans EN k0 t0).mpr hAt)
    exact ⟨s.val,hs,N.val,hN,(codes_class_absolute hM.1 hTrans k0 s N).mp hCode,inner_expands_up_d hM env hS hD hT hExp⟩
  · rintro ⟨s,hs,N,hN,hCode,hExp⟩
    obtain ⟨s0,N0,t0,hs0,hN0,ht0,hExp0⟩ := outer_expands_inner_d hM env hS hD hT hExp
    subst hs0 hN0 ht0
    have hk : M.mem key Keys.val := (hKeys key).mpr ⟨s0.val,hs,N0.val,hN,hCode⟩
    let k0 : (𝕃).Domain := ⟨key,hTrans Keys.val Keys.property key hk⟩
    have hCode0 : Codes 𝕃 k0 s0 N0 := (codes_class_absolute hM.1 hTrans k0 s0 N0).mpr hCode
    exact (memPair_class_absolute hM.1 hTrans EN k0 t0).mp ((h.rows k0 t0).mpr ⟨s0,hs,N0,hN,hCode0,hExp0⟩)

/-- 外部实际EN图的Keys与EN本身属于L，并且就是L的实际EN图。 -/
theorem outer_expansion_graph_inner_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    (env : Env M 24) (hS : FixedSyntax M (defContext.eval env) (defData.eval env) (env.bound 0) (env.bound 1) (env.bound 2))
    {D : ExpressionData (𝕃).Domain} (hD : D.Valid 𝕃) {T : MatrixArithmetic (𝕃).Domain} (hT : T.Valid 𝕃 D)
    {Keys EN : M.Domain} (h : Expansion.Graph M (D.map Subtype.val) (T.map Subtype.val) Keys EN) :
    ∃ Keys0 EN0 : (𝕃).Domain, Keys0.val=Keys ∧ EN0.val=EN ∧ Expansion.Graph 𝕃 D T Keys0 EN0 := by
  obtain ⟨Keys0,EN0,h0⟩ := Expansion.expansion_graph_exists_d (inner_models_kp_d hM env hS) hD hT
  obtain ⟨hK,hE⟩ := (inner_expansion_graph_up_d hM env hS hD hT h0).unique hM.1 h
  exact ⟨Keys0,EN0,hK,hE,h0⟩

/-- 回传集合秩见证：L中的χ、μ本身满足外部的实际秩语句。 -/
theorem inner_rank_witness_up_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    (env : Env M 24) (hS : FixedSyntax M (defContext.eval env) (defData.eval env) (env.bound 0) (env.bound 1) (env.bound 2))
    {D : ExpressionData (𝕃).Domain} (hD : D.Valid 𝕃) {T : MatrixArithmetic (𝕃).Domain} (hT : T.Valid 𝕃 D)
    {χ μ : (𝕃).Domain} (h : KP1Y.OneYRank.RankWitness 𝕃 D T χ μ) :
    KP1Y.OneYRank.RankWitness M (D.map Subtype.val) (T.map Subtype.val) χ.val μ.val := by
  have hTrans := constructible_transitive_class_d hM env hS
  have hGraph := (graph_class_absolute hM.1 hTrans μ D.expressions χ).mp h.graph
  refine ⟨(inner_ordinal_absolute_d hM env hS χ).mp h.ordinal,hGraph,
    (memPair_class_absolute hM.1 hTrans μ D.zero D.zero).mp h.empty,?_⟩
  intro s hs hne N hN t hExp a b hsa htb
  obtain ⟨s0,N0,t0,hs0,hN0,ht0,hExp0⟩ := outer_expands_inner_d hM env hS hD hT hExp
  subst hs0 hN0 ht0
  let a0 : (𝕃).Domain := ⟨a,hTrans χ.val χ.property a (hGraph.bounds hM.1 hsa).2⟩
  let b0 : (𝕃).Domain := ⟨b,hTrans χ.val χ.property b (hGraph.bounds hM.1 htb).2⟩
  exact h.descends s0 hs (fun he => hne (congrArg Subtype.val he)) N0 hN t0 hExp0 a0 b0
    ((memPair_class_absolute hM.1 hTrans μ s0 a0).mpr hsa) ((memPair_class_absolute hM.1 hTrans μ t0 b0).mpr htb)

/-- 对L中的χ、μ，秩见证内外等价。 -/
theorem inner_rank_witness_iff_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    (env : Env M 24) (hS : FixedSyntax M (defContext.eval env) (defData.eval env) (env.bound 0) (env.bound 1) (env.bound 2))
    {D : ExpressionData (𝕃).Domain} (hD : D.Valid 𝕃) {T : MatrixArithmetic (𝕃).Domain} (hT : T.Valid 𝕃 D)
    (χ μ : (𝕃).Domain) : KP1Y.OneYRank.RankWitness 𝕃 D T χ μ ↔
      KP1Y.OneYRank.RankWitness M (D.map Subtype.val) (T.map Subtype.val) χ.val μ.val := by
  constructor
  · exact inner_rank_witness_up_d hM env hS hD hT
  · intro h
    have hTrans := constructible_transitive_class_d hM env hS
    refine ⟨(inner_ordinal_absolute_d hM env hS χ).mpr h.ordinal,(graph_class_absolute hM.1 hTrans μ D.expressions χ).mpr h.graph,
      (memPair_class_absolute hM.1 hTrans μ D.zero D.zero).mpr h.empty,?_⟩
    intro s hs hne N hN t hExp a b hsa htb
    exact h.descends s.val hs (fun he => hne (Subtype.ext he)) N.val hN t.val (inner_expands_up_d hM env hS hD hT hExp)
      a.val b.val ((memPair_class_absolute hM.1 hTrans μ s a).mp hsa) ((memPair_class_absolute hM.1 hTrans μ t b).mp htb)

/-- 同一结论对任意外部有效E、T陈述。 -/
theorem inner_rank_witness_outer_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    (env : Env M 24) (hS : FixedSyntax M (defContext.eval env) (defData.eval env) (env.bound 0) (env.bound 1) (env.bound 2))
    {D : ExpressionData (𝕃).Domain} (hD : D.Valid 𝕃) {T0 : MatrixArithmetic (𝕃).Domain} (hT0 : T0.Valid 𝕃 D)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {χ μ : (𝕃).Domain} (h : KP1Y.OneYRank.RankWitness 𝕃 D T0 χ μ) : KP1Y.OneYRank.RankWitness M C T χ.val μ.val := by
  have hDC := expression_data_unique hM.1 (inner_expression_data_outer_valid_d hM env hS hD) hC
  subst hDC
  have hTT := matrix_arithmetic_unique hM.1 (inner_matrix_arithmetic_up_d hM env hS hD hT0) hT
  subst hTT
  exact inner_rank_witness_up_d hM env hS hD hT0 h

end KP1Y.OneYFinite.InnerAbsoluteness
