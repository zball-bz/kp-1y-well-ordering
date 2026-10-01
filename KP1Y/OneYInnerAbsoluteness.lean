import KP1Y.OneYInnerFiniteCodes
import KP1Y.OneYExpansion

/-! Y08 参数部分：构造内模型L与外部M的表达式数据、实际算术表、全宽度森林集合与重建空间相同。
L侧数据由L内唯一性识别；算术表由L内证书向上Δ₀绝对、外部唯一性识别；任意外部有限森林/
序列（包括非标准长度）的构造性来自已证的内部构造闭合，不使用宿主有限性。 -/
namespace KP1Y.OneYFinite.InnerAbsoluteness
open YesMetaZFC YesMetaZFC.SetTheory YesMetaZFC.SetTheory.Definitional
open KP1Y.Kuratowski KP1Y.Functions KP1Y.Naturals KP1Y.Bounded KP1Y.SetLanguage KP1Y.Classes KP1Y.Constructible
open KP1Y.OneYFinite
universe u

set_option hygiene false in
local notation "𝕃" => innerModel hM env hS

theorem expression_data_unique {M : SetTheory.Structure.{u}} (he : Extensional M)
    {C D : ExpressionData M.Domain} (hC : C.Valid M) (hD : D.Valid M) : C=D := by
  have hω : C.omega=D.omega := omega_unique he hC.omega hD.omega
  have hz : C.zero=D.zero := he.eq_of_same_members _ _ (fun x => iff_of_false (hC.zero_empty x) (hD.zero_empty x))
  have hSucc : M.SuccessorOf D.one C.zero := by
    rw [hz]
    exact hD.one_succ
  have ho : C.one=D.one := Structure.SuccessorOf.eq he hC.one_succ hSucc
  have hs : C.sequences=D.sequences := by
    apply he.eq_of_same_members
    intro s
    rw [hC.sequences s,hD.sequences s,hω]
  have hx : C.expressions=D.expressions := by
    apply he.eq_of_same_members
    intro s
    rw [hC.expressions s,hD.expressions s,hω,hz,ho]
  cases C
  cases D
  simp only at hω hz ho hs hx
  subst hω hz ho hs hx
  rfl

/-- L中任一有效表达式数据都是外部E的同一对象代表。 -/
theorem inner_expression_data_eq_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    (env : Env M 24) (hS : FixedSyntax M (defContext.eval env) (defData.eval env) (env.bound 0) (env.bound 1) (env.bound 2))
    {C : ExpressionData M.Domain} (hC : C.Valid M) {D : ExpressionData (𝕃).Domain} (hD : D.Valid 𝕃) :
    D=innerExpressionData hM env hS C hC :=
  expression_data_unique (inner_extensional_d hM env hS) hD (innerExpressionData_valid_d hM env hS C hC)

theorem inner_expression_data_values_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    (env : Env M 24) (hS : FixedSyntax M (defContext.eval env) (defData.eval env) (env.bound 0) (env.bound 1) (env.bound 2))
    {C : ExpressionData M.Domain} (hC : C.Valid M) {D : ExpressionData (𝕃).Domain} (hD : D.Valid 𝕃) :
    D.map Subtype.val=C := by
  rw [inner_expression_data_eq_d hM env hS hC hD]
  rfl

/-- E^L=E^M：L中有效表达式数据的值就是外部有效表达式数据。 -/
theorem inner_expression_data_outer_valid_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    (env : Env M 24) (hS : FixedSyntax M (defContext.eval env) (defData.eval env) (env.bound 0) (env.bound 1) (env.bound 2))
    {D : ExpressionData (𝕃).Domain} (hD : D.Valid 𝕃) : (D.map Subtype.val).Valid M := by
  obtain ⟨ω,hω,_⟩ := exists_omega_d hM
  obtain ⟨C,_,hC⟩ := expression_data_exists_d hM hω
  rw [inner_expression_data_values_d hM env hS hC hD]
  exact hC

/-- L中的ω就是外部ω（同一集合）。 -/
theorem inner_omega_outer_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    (env : Env M 24) (hS : FixedSyntax M (defContext.eval env) (defData.eval env) (env.bound 0) (env.bound 1) (env.bound 2))
    {w : (𝕃).Domain} (hw : (𝕃).IsOmega w) : M.IsOmega w.val := by
  obtain ⟨ω,hω,_⟩ := exists_omega_d hM
  obtain ⟨w',hw'v,hw'⟩ := inner_omega_exists_d hM env hS hω
  rw [omega_unique (inner_extensional_d hM env hS) hw hw',hw'v]
  exact hω

/-! ### 实际算术表 -/

private theorem witness_one_up {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    (env : Env M 24) (hS : FixedSyntax M (defContext.eval env) (defData.eval env) (env.bound 0) (env.bound 1) (env.bound 2))
    (φ : KP1Y.WitnessMatrix 1) (a b c B : (𝕃).Domain)
    (h : Project.Formula.satisfies ((((oneEnv a).push b).push c).push B) φ.body) :
    Project.Formula.satisfies ((((oneEnv a.val).push b.val).push c.val).push B.val) φ.body :=
  (witness_matrix_transfer_iff (constructible_transitive_class_d hM env hS) φ (oneEnv a) (oneEnv a.val)
    (fun _ => rfl) b c B).mp h

theorem inner_sum_up_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    (env : Env M 24) (hS : FixedSyntax M (defContext.eval env) (defData.eval env) (env.bound 0) (env.bound 1) (env.bound 2))
    (a b c : (𝕃).Domain) (h : KP1Y.Arithmetic.Sum 𝕃 a b c) : KP1Y.Arithmetic.Sum M a.val b.val c.val := by
  obtain ⟨B,hB⟩ := (KP1Y.Arithmetic.sum_sigmaOne_iff_d (inner_models_kp_d hM env hS) (oneEnv a) b c).mp h
  exact (KP1Y.Arithmetic.sum_sigmaOne_iff_d hM (oneEnv a.val) b.val c.val).mpr
    ⟨B.val,witness_one_up hM env hS KP1Y.Arithmetic.sumMatrix a b c B hB⟩

theorem inner_product_up_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    (env : Env M 24) (hS : FixedSyntax M (defContext.eval env) (defData.eval env) (env.bound 0) (env.bound 1) (env.bound 2))
    (a b c : (𝕃).Domain) (h : KP1Y.Arithmetic.Product 𝕃 a b c) : KP1Y.Arithmetic.Product M a.val b.val c.val := by
  obtain ⟨B,hB⟩ := (KP1Y.Arithmetic.product_sigmaOne_iff_d (inner_models_kp_d hM env hS) (oneEnv a) b c).mp h
  exact (KP1Y.Arithmetic.product_sigmaOne_iff_d hM (oneEnv a.val) b.val c.val).mpr
    ⟨B.val,witness_one_up hM env hS KP1Y.Arithmetic.productMatrix a b c B hB⟩

theorem inner_difference_up_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    (env : Env M 24) (hS : FixedSyntax M (defContext.eval env) (defData.eval env) (env.bound 0) (env.bound 1) (env.bound 2))
    (w z a b d : (𝕃).Domain) (h : TruncatedDifference 𝕃 w z a b d) :
    TruncatedDifference M w.val z.val a.val b.val d.val := by
  have hTrans := constructible_transitive_class_d hM env hS
  obtain ⟨ha,hb,H,hH,hAt⟩ := h
  let e := (((oneEnv w).push z).push a).push H
  refine ⟨ha,hb,H.val,?_,(memPair_class_absolute hM.1 hTrans H b d).mp hAt⟩
  exact (predecessorIteratorFormula_iff hM.1 (forgetEnv e) (.bound 3) (.bound 2) (.bound 1) (.bound 0)).mp
    ((delta0_class_absolute hTrans (predecessorIteratorFormula_delta0 _ _ _ _) e).mp
      ((predecessorIteratorFormula_iff (inner_extensional_d hM env hS) e (.bound 3) (.bound 2) (.bound 1) (.bound 0)).mpr hH))

/-- 有限二元表的行：L内证书向上绝对，外部唯一性识别同一输出。 -/
private theorem table_rows_up {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    (env : Env M 24) (hS : FixedSyntax M (defContext.eval env) (defData.eval env) (env.bound 0) (env.bound 1) (env.bound 2))
    {R : (𝕃).Domain → (𝕃).Domain → (𝕃).Domain → Prop} {R' : M.Domain → M.Domain → M.Domain → Prop}
    (hUp : ∀ a b c, R a b c → R' a.val b.val c.val) (hUnique : ∀ a b c d, R' a b c → R' a b d → c=d)
    {w P Q : (𝕃).Domain} (hP : IsProduct 𝕃 P w w) (hQ : Graph 𝕃 Q P w)
    (hRows : ∀ a, (𝕃).mem a w → ∀ b, (𝕃).mem b w → ∀ key, Codes 𝕃 key a b → ∀ c, MemPair 𝕃 Q key c ↔ R a b c) :
    ∀ a, M.mem a w.val → ∀ b, M.mem b w.val → ∀ key, Codes M key a b → ∀ c, MemPair M Q.val key c ↔ R' a b c := by
  have hTrans := constructible_transitive_class_d hM env hS
  have hL := inner_models_kp_d hM env hS
  intro a ha b hb key hCode c
  let a0 : (𝕃).Domain := ⟨a,hTrans w.val w.property a ha⟩
  let b0 : (𝕃).Domain := ⟨b,hTrans w.val w.property b hb⟩
  have hPM := (product_class_absolute_d hM hTrans hL P w w).mp hP
  have hk : M.mem key P.val := (hPM key).mpr ⟨a,ha,b,hb,hCode⟩
  let k0 : (𝕃).Domain := ⟨key,hTrans P.val P.property key hk⟩
  have hCode0 : Codes 𝕃 k0 a0 b0 := (codes_class_absolute hM.1 hTrans k0 a0 b0).mpr hCode
  constructor
  · intro hAt
    have hc : M.mem c w.val := (((graph_class_absolute hM.1 hTrans Q P w).mp hQ).bounds hM.1 hAt).2
    let c0 : (𝕃).Domain := ⟨c,hTrans w.val w.property c hc⟩
    exact hUp a0 b0 c0 ((hRows a0 ha b0 hb k0 hCode0 c0).mp ((memPair_class_absolute hM.1 hTrans Q k0 c0).mpr hAt))
  · intro hR
    obtain ⟨c0,_,hAt⟩ := hQ.total k0 hk
    have hc := hUnique a b c c0.val hR (hUp a0 b0 c0 ((hRows a0 ha b0 hb k0 hCode0 c0).mp hAt))
    rw [hc]
    exact (memPair_class_absolute hM.1 hTrans Q k0 c0).mp hAt

/-- L中有效的实际加法、乘法、截断减法表，其值就是外部有效表。 -/
theorem inner_matrix_arithmetic_up_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    (env : Env M 24) (hS : FixedSyntax M (defContext.eval env) (defData.eval env) (env.bound 0) (env.bound 1) (env.bound 2))
    {D : ExpressionData (𝕃).Domain} (hD : D.Valid 𝕃) {T : MatrixArithmetic (𝕃).Domain} (hT : T.Valid 𝕃 D) :
    (T.map Subtype.val).Valid M (D.map Subtype.val) := by
  have hTrans := constructible_transitive_class_d hM env hS
  have hL := inner_models_kp_d hM env hS
  have hC := inner_expression_data_outer_valid_d hM env hS hD
  refine ⟨⟨(product_class_absolute_d hM hTrans hL _ D.omega D.omega).mp hT.add.pairs,
      (graph_class_absolute hM.1 hTrans _ _ D.omega).mp hT.add.graph,
      table_rows_up hM env hS (inner_sum_up_d hM env hS) (fun _ _ _ _ => KP1Y.Arithmetic.sum_unique_d hM)
        hT.add.pairs hT.add.graph hT.add.rows⟩,
    ⟨(product_class_absolute_d hM hTrans hL _ D.omega D.omega).mp hT.mul.pairs,
      (graph_class_absolute hM.1 hTrans _ _ D.omega).mp hT.mul.graph,
      table_rows_up hM env hS (inner_product_up_d hM env hS) (fun _ _ _ _ => KP1Y.Arithmetic.product_unique_d hM)
        hT.mul.pairs hT.mul.graph hT.mul.rows⟩,
    ⟨(product_class_absolute_d hM hTrans hL _ D.omega D.omega).mp hT.diff.pairs,
      (graph_class_absolute hM.1 hTrans _ _ D.omega).mp hT.diff.graph,
      table_rows_up hM env hS (inner_difference_up_d hM env hS D.omega D.zero)
        (fun _ _ _ _ => truncated_difference_unique_d hM hC) hT.diff.pairs hT.diff.graph hT.diff.rows⟩⟩

private theorem table_unique {M : SetTheory.Structure.{u}} (he : Extensional M)
    {R : M.Domain → M.Domain → M.Domain → Prop} {w P Q Q' : M.Domain} (hP : IsProduct M P w w)
    (hQ : Graph M Q P w) (hQ' : Graph M Q' P w)
    (hRows : ∀ a, M.mem a w → ∀ b, M.mem b w → ∀ key, Codes M key a b → ∀ c, MemPair M Q key c ↔ R a b c)
    (hRows' : ∀ a, M.mem a w → ∀ b, M.mem b w → ∀ key, Codes M key a b → ∀ c, MemPair M Q' key c ↔ R a b c) : Q=Q' := by
  apply hQ.ext he hQ'
  intro key hk c
  obtain ⟨a,ha,b,hb,hCode⟩ := (hP key).mp hk
  exact (hRows a ha b hb key hCode c).trans (hRows' a ha b hb key hCode c).symm

private theorem product_unique {M : SetTheory.Structure.{u}} (he : Extensional M) {P P' X Y : M.Domain}
    (hP : IsProduct M P X Y) (hP' : IsProduct M P' X Y) : P=P' :=
  he.eq_of_same_members P P' (fun p => (hP p).trans (hP' p).symm)

theorem matrix_arithmetic_unique {M : SetTheory.Structure.{u}} (he : Extensional M)
    {C : ExpressionData M.Domain} {T T' : MatrixArithmetic M.Domain} (hT : T.Valid M C) (hT' : T'.Valid M C) : T=T' := by
  have ha := product_unique he hT.add.pairs hT'.add.pairs
  have hm := product_unique he hT.mul.pairs hT'.mul.pairs
  have hd := product_unique he hT.diff.pairs hT'.diff.pairs
  have hPlus : T.plus=T'.plus := table_unique he hT.add.pairs hT.add.graph (ha ▸ hT'.add.graph) hT.add.rows hT'.add.rows
  have hTimes : T.times=T'.times := table_unique he hT.mul.pairs hT.mul.graph (hm ▸ hT'.mul.graph) hT.mul.rows hT'.mul.rows
  have hDiff : T.difference=T'.difference :=
    table_unique he hT.diff.pairs hT.diff.graph (hd ▸ hT'.diff.graph) hT.diff.rows hT'.diff.rows
  cases T
  cases T'
  simp only at ha hm hd hPlus hTimes hDiff
  subst ha hm hd hPlus hTimes hDiff
  rfl

/-! ### 全宽度森林集合与重建空间 -/

theorem inner_all_forests_up_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    (env : Env M 24) (hS : FixedSyntax M (defContext.eval env) (defData.eval env) (env.bound 0) (env.bound 1) (env.bound 2))
    {D : ExpressionData (𝕃).Domain} (hD : D.Valid 𝕃) {AF : (𝕃).Domain}
    (h : ExpressionDiagram.AllForests 𝕃 D.omega AF) : ExpressionDiagram.AllForests M D.omega.val AF.val := by
  have hTrans := constructible_transitive_class_d hM env hS
  have hC := inner_expression_data_outer_valid_d hM env hS hD
  intro P
  constructor
  · intro hP
    let P0 : (𝕃).Domain := ⟨P,hTrans AF.val AF.property P hP⟩
    obtain ⟨m,hm,hF⟩ := (h P0).mp hP
    exact ⟨m.val,hm,(forest_class_absolute hM.1 hTrans D.omega m P0).mp hF⟩
  · rintro ⟨m,hm,hF⟩
    let P0 : (𝕃).Domain := ⟨P,finite_forest_constructible_d hM env hS hC hF⟩
    let m0 : (𝕃).Domain := ⟨m,hTrans D.omega.val D.omega.property m hm⟩
    exact (h P0).mpr ⟨m0,hm,(forest_class_absolute hM.1 hTrans D.omega m0 P0).mpr hF⟩

theorem inner_spaces_up_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    (env : Env M 24) (hS : FixedSyntax M (defContext.eval env) (defData.eval env) (env.bound 0) (env.bound 1) (env.bound 2))
    {D : ExpressionData (𝕃).Domain} (hD : D.Valid 𝕃) {AF : (𝕃).Domain} {S : MountainReconstruction.Spaces (𝕃).Domain}
    (h : S.Valid 𝕃 D AF) :
    MountainReconstruction.Spaces.Valid M (D.map Subtype.val) AF.val ⟨S.forestLists.val,S.grids.val⟩ := by
  have hTrans := constructible_transitive_class_d hM env hS
  have hω : M.IsOmega D.omega.val := (inner_expression_data_outer_valid_d hM env hS hD).omega
  constructor
  · intro P
    constructor
    · intro hP
      let P0 : (𝕃).Domain := ⟨P,hTrans S.forestLists.val S.forestLists.property P hP⟩
      obtain ⟨B,hB,hG⟩ := (h.forestLists P0).mp hP
      exact ⟨B.val,hB,(graph_class_absolute hM.1 hTrans P0 B AF).mp hG⟩
    · rintro ⟨B,hB,hG⟩
      let P0 : (𝕃).Domain := ⟨P,finite_sequence_constructible_d hM env hS hω AF.property hB hG⟩
      let B0 : (𝕃).Domain := ⟨B,hTrans D.omega.val D.omega.property B hB⟩
      exact (h.forestLists P0).mpr ⟨B0,hB,(graph_class_absolute hM.1 hTrans P0 B0 AF).mpr hG⟩
  · intro H
    constructor
    · intro hH
      let H0 : (𝕃).Domain := ⟨H,hTrans S.grids.val S.grids.property H hH⟩
      obtain ⟨n,hn,hG⟩ := (h.grids H0).mp hH
      exact ⟨n.val,hn,(graph_class_absolute hM.1 hTrans H0 n D.sequences).mp hG⟩
    · rintro ⟨n,hn,hG⟩
      let H0 : (𝕃).Domain := ⟨H,finite_sequence_constructible_d hM env hS hω D.sequences.property hn hG⟩
      let n0 : (𝕃).Domain := ⟨n,hTrans D.omega.val D.omega.property n hn⟩
      exact (h.grids H0).mpr ⟨n0,hn,(graph_class_absolute hM.1 hTrans H0 n0 D.sequences).mpr hG⟩

end KP1Y.OneYFinite.InnerAbsoluteness
