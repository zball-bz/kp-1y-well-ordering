import KP1Y.CanonicalSyntaxInside
import KP1Y.OneYForestSpace

/-! 内模型中的实际有限输入代码闭合。有限序列闭合复用经对象自然数归纳验证的
SequenceSpaces.space_history_exact_d及其Σ₁空间证书；不推断无限运行历史属于L。 -/
namespace KP1Y.OneYFinite
open YesMetaZFC YesMetaZFC.SetTheory YesMetaZFC.SetTheory.Definitional
open KP1Y.Kuratowski KP1Y.Functions KP1Y.Naturals KP1Y.Bounded KP1Y.SetLanguage KP1Y.Classes KP1Y.Constructible
universe u

theorem natural_constructible_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    (env : Env M 24) (hS : FixedSyntax M (defContext.eval env) (defData.eval env) (env.bound 0) (env.bound 1) (env.bound 2))
    {w n : M.Domain} (hw : M.IsOmega w) (hn : M.mem n w) : InConstructible M env n :=
  ordinal_constructible_d hM env hS ((omega_isOrdinal_d hM hw).mem hn)

theorem natural_sequence_constructible_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    (env : Env M 24) (hS : FixedSyntax M (defContext.eval env) (defData.eval env) (env.bound 0) (env.bound 1) (env.bound 2))
    {w F n : M.Domain} (hw : M.IsOmega w) (hn : M.mem n w) (hF : Graph M F n w) : InConstructible M env F :=
  finite_sequence_constructible_d hM env hS hw (ordinal_constructible_d hM env hS (omega_isOrdinal_d hM hw)) hn hF

theorem finite_code_constructible_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    (env : Env M 24) (hS : FixedSyntax M (defContext.eval env) (defData.eval env) (env.bound 0) (env.bound 1) (env.bound 2))
    {code x y : M.Domain} (hx : InConstructible M env x) (hy : InConstructible M env y) (hCode : Codes M code x y) :
    InConstructible M env code := by
  obtain ⟨a,b,hA,hB,hCode⟩ := hCode
  exact pair_set_constructible_d hM env hS (pair_set_constructible_d hM env hS hx hx hA)
    (pair_set_constructible_d hM env hS hx hy hB) hCode

theorem finite_sequence_packet_constructible_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    (env : Env M 24) (hS : FixedSyntax M (defContext.eval env) (defData.eval env) (env.bound 0) (env.bound 1) (env.bound 2))
    {w A F n code : M.Domain} (hw : M.IsOmega w) (hA : InConstructible M env A) (hn : M.mem n w)
    (hF : Graph M F n A) (hCode : Codes M code n F) : InConstructible M env code :=
  finite_code_constructible_d hM env hS (natural_constructible_d hM env hS hw hn)
    (finite_sequence_constructible_d hM env hS hw hA hn hF) hCode

/-- 对已知构造集合的实际有界分离保持在L中，使用内分离和外延唯一性。 -/
theorem finite_input_subset_constructible_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    (env : Env M 24) (hS : FixedSyntax M (defContext.eval env) (defData.eval env) (env.bound 0) (env.bound 1) (env.bound 2))
    {n : Nat} (φ : Project.Delta0UnarySchema n) (e : Env M n) (hParams : ∀i, InConstructible M env (e.bound i))
    {A B : M.Domain} (hA : InConstructible M env A)
    (hRows : ∀x, M.mem x B ↔ M.mem x A ∧ Project.Formula.satisfies (e.push x) φ.body) : InConstructible M env B := by
  let A0 : (innerModel hM env hS).Domain := ⟨A,hA⟩
  let e0 : Env (innerModel hM env hS) n := liftParameters e hParams A0
  have hTrans := constructible_transitive_class_d hM env hS
  obtain ⟨B0,hB0⟩ := inner_separation_d hM env hS φ e0 A0
  have hEqual : B0.val=B := by
    apply hM.1.eq_of_same_members
    intro x
    constructor
    · intro hx
      let x0 : (innerModel hM env hS).Domain := ⟨x,hTrans B0.val B0.property x hx⟩
      obtain ⟨hxA,hφ⟩ := (hB0 x0).mp hx
      exact (hRows x).mpr ⟨hxA,(unary_matrix_transfer_iff hTrans φ e0 e (fun _ => rfl) x0).mp hφ⟩
    · intro hx
      obtain ⟨hxA,hφ⟩ := (hRows x).mp hx
      let x0 : (innerModel hM env hS).Domain := ⟨x,hA.mem_closed_d hM env hS hxA⟩
      exact (hB0 x0).mpr ⟨hxA,(unary_matrix_transfer_iff hTrans φ e0 e (fun _ => rfl) x0).mpr hφ⟩
  exact hEqual ▸ B0.property

private def finiteParentReadSchema : Project.Delta0BinarySchema 1 where
  body := .conj (.mem (.bound 0) (.bound 1)) (memPairFormula (.bound 2) (.bound 1) (.bound 0))
  freeClosed := by simp [memPairFormula,codeFormula,pairFormula,Project.Formula.forallMem,Project.Formula.existsMem,Definitional.Formula.FreeClosed]
  delta0 := .conj (.mem _ _) (memPairFormula_delta0 _ _ _)

/-- 先构造长度m的自然数父编码（m作无父哨兵），再在L内按同一Δ₀关系解码。 -/
theorem finite_forest_constructible_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    (env : Env M 24) (hS : FixedSyntax M (defContext.eval env) (defData.eval env) (env.bound 0) (env.bound 1) (env.bound 2))
    {C : ExpressionData M.Domain} (hC : C.Valid M) {m P : M.Domain} (hP : Forest M C.omega m P) : InConstructible M env P := by
  obtain ⟨E,hE,hDecode,_⟩ := forest_encoding_exists_d hM hC hP
  have hEL := natural_sequence_constructible_d hM env hS hC.omega hP.width hE
  have hmL := natural_constructible_d hM env hS hC.omega hP.width
  apply relation_constructible_d hM env hS finiteParentReadSchema (oneEnv E) (fun _ => hEL) hmL hmL hP.support
  intro c p
  have hφ : Project.Formula.satisfies (((oneEnv E).push c).push p) finiteParentReadSchema.body ↔ M.mem p c ∧ MemPair M E c p := by
    simp only [finiteParentReadSchema,Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_mem_iff,memPairFormula_iff hM.1]
    rfl
  rw [hφ]
  exact ⟨fun hAt => ⟨(hP.bounds hM.1 hAt).1,(hP.bounds hM.1 hAt).2,
      (hDecode.rows c p (hP.bounds hM.1 hAt).1 (hP.bounds hM.1 hAt).2).mp hAt⟩,
    fun h => (hDecode.rows c p h.1 h.2.1).mpr h.2.2⟩

theorem numeric_input_packet_constructible_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    (env : Env M 24) (hS : FixedSyntax M (defContext.eval env) (defData.eval env) (env.bound 0) (env.bound 1) (env.bound 2))
    {C : ExpressionData M.Domain} (hC : C.Valid M) {m V P code : M.Domain} (hV : Graph M V m C.omega)
    (hP : Forest M C.omega m P) (hCode : Codes M code V P) : InConstructible M env code :=
  finite_code_constructible_d hM env hS (natural_sequence_constructible_d hM env hS hC.omega hP.width hV)
    (finite_forest_constructible_d hM env hS hC hP) hCode

structure ExpressionData.InConstructible (M : SetTheory.Structure.{u}) (env : Env M 24) (C : ExpressionData M.Domain) : Prop where
  omega : KP1Y.Constructible.InConstructible M env C.omega
  zero : KP1Y.Constructible.InConstructible M env C.zero
  one : KP1Y.Constructible.InConstructible M env C.one
  sequences : KP1Y.Constructible.InConstructible M env C.sequences
  expressions : KP1Y.Constructible.InConstructible M env C.expressions

private def inputLegalSchema : Project.Delta0UnarySchema 3 where
  body := legalFormula (.bound 3) (.bound 2) (.bound 1) (.bound 0)
  freeClosed := legalFormula_freeClosed _ _ _ _ rfl rfl rfl rfl
  delta0 := legalFormula_delta0 _ _ _ _

theorem expression_data_constructible_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    (env : Env M 24) (hS : FixedSyntax M (defContext.eval env) (defData.eval env) (env.bound 0) (env.bound 1) (env.bound 2))
    {C : ExpressionData M.Domain} (hC : C.Valid M) : C.InConstructible M env := by
  have hω := ordinal_constructible_d hM env hS (omega_isOrdinal_d hM hC.omega)
  have hz := natural_constructible_d hM env hS hC.omega hC.zero_nat
  have ho := natural_constructible_d hM env hS hC.omega hC.one_nat
  have hSequences := sequence_space_constructible_d hM env hS hC.omega hω hC.sequences
  refine ⟨hω,hz,ho,hSequences,?_⟩
  apply finite_input_subset_constructible_d hM env hS inputLegalSchema (((oneEnv C.omega).push C.zero).push C.one)
    (Fin.cases ho (Fin.cases hz (fun _ => hω))) hSequences
  intro s
  have hφ : Project.Formula.satisfies ((((oneEnv C.omega).push C.zero).push C.one).push s) inputLegalSchema.body ↔
      Legal M C.omega C.zero C.one s := legalFormula_iff hM.1 _ _ _ _ _
  rw [hφ,hC.expressions s]
  constructor
  · intro h
    obtain ⟨m,hm,hLegal⟩ := h
    exact ⟨(hC.sequences s).mpr ⟨m,hm,hLegal.1.2⟩,m,hm,hLegal⟩
  · exact And.right

theorem legal_expression_constructible_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    (env : Env M 24) (hS : FixedSyntax M (defContext.eval env) (defData.eval env) (env.bound 0) (env.bound 1) (env.bound 2))
    {C : ExpressionData M.Domain} (hC : C.Valid M) {s : M.Domain} (hs : M.mem s C.expressions) : InConstructible M env s :=
  (expression_data_constructible_d hM env hS hC).expressions.mem_closed_d hM env hS hs

theorem legalAt_class_absolute {M : SetTheory.Structure.{u}} (he : Extensional M)
    {P : M.Domain → Prop} {hNe : ∃x, P x} (hP : TransitiveClass M P)
    (w z o s m : (classModel M P hNe).Domain) :
    LegalAt (classModel M P hNe) w z o s m ↔ LegalAt M w.val z.val o.val s.val m.val := by
  let e := ((((oneEnv w).push z).push o).push s).push m
  exact (legalAtFormula_iff (class_extensional he hP) e (.bound 4) (.bound 3) (.bound 2) (.bound 1) (.bound 0)).symm.trans
    ((delta0_class_absolute hP (legalAtFormula_delta0 (.bound 4) (.bound 3) (.bound 2) (.bound 1) (.bound 0)) e).trans
      (legalAtFormula_iff he (forgetEnv e) (.bound 4) (.bound 3) (.bound 2) (.bound 1) (.bound 0)))

theorem legal_class_absolute {M : SetTheory.Structure.{u}} (he : Extensional M)
    {P : M.Domain → Prop} {hNe : ∃x, P x} (hP : TransitiveClass M P)
    (w z o s : (classModel M P hNe).Domain) : Legal (classModel M P hNe) w z o s ↔ Legal M w.val z.val o.val s.val := by
  let e := (((oneEnv w).push z).push o).push s
  exact (legalFormula_iff (class_extensional he hP) e (.bound 3) (.bound 2) (.bound 1) (.bound 0)).symm.trans
    ((delta0_class_absolute hP (legalFormula_delta0 (.bound 3) (.bound 2) (.bound 1) (.bound 0)) e).trans
      (legalFormula_iff he (forgetEnv e) (.bound 3) (.bound 2) (.bound 1) (.bound 0)))

theorem forest_class_absolute {M : SetTheory.Structure.{u}} (he : Extensional M)
    {P : M.Domain → Prop} {hNe : ∃x, P x} (hP : TransitiveClass M P)
    (w m F : (classModel M P hNe).Domain) : Forest (classModel M P hNe) w m F ↔ Forest M w.val m.val F.val := by
  let e := ((oneEnv w).push m).push F
  exact (forestFormula_iff (class_extensional he hP) e (.bound 2) (.bound 1) (.bound 0)).symm.trans
    ((delta0_class_absolute hP (forestFormula_delta0 (.bound 2) (.bound 1) (.bound 0)) e).trans
      (forestFormula_iff he (forgetEnv e) (.bound 2) (.bound 1) (.bound 0)))

def innerExpressionData {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    (env : Env M 24) (hS : FixedSyntax M (defContext.eval env) (defData.eval env) (env.bound 0) (env.bound 1) (env.bound 2))
    (C : ExpressionData M.Domain) (hC : C.Valid M) : ExpressionData (innerModel hM env hS).Domain :=
  let hL := expression_data_constructible_d hM env hS hC
  ⟨⟨C.omega,hL.omega⟩,⟨C.zero,hL.zero⟩,⟨C.one,hL.one⟩,⟨C.sequences,hL.sequences⟩,⟨C.expressions,hL.expressions⟩⟩

theorem innerExpressionData_values {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    (env : Env M 24) (hS : FixedSyntax M (defContext.eval env) (defData.eval env) (env.bound 0) (env.bound 1) (env.bound 2))
    (C : ExpressionData M.Domain) (hC : C.Valid M) : (innerExpressionData hM env hS C hC).map Subtype.val=C := rfl

theorem innerExpressionData_valid_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    (env : Env M 24) (hS : FixedSyntax M (defContext.eval env) (defData.eval env) (env.bound 0) (env.bound 1) (env.bound 2))
    (C : ExpressionData M.Domain) (hC : C.Valid M) : (innerExpressionData hM env hS C hC).Valid (innerModel hM env hS) := by
  let D := innerExpressionData hM env hS C hC
  have hTrans := constructible_transitive_class_d hM env hS
  refine ⟨omega_into_class hM.1 hTrans D.omega hC.omega,(empty_class_absolute hTrans D.zero).mpr hC.zero_empty,hC.zero_nat,
    (successor_class_absolute hM.1 hTrans D.one D.zero).mpr hC.one_succ,hC.one_nat,
    sequence_space_into_class hM.1 hTrans D.sequences D.omega D.omega hC.sequences,?_⟩
  intro s
  exact (hC.expressions s.val).trans (legal_class_absolute hM.1 hTrans D.omega D.zero D.one s).symm

theorem inner_expression_data_exists_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    (env : Env M 24) (hS : FixedSyntax M (defContext.eval env) (defData.eval env) (env.bound 0) (env.bound 1) (env.bound 2))
    {C : ExpressionData M.Domain} (hC : C.Valid M) :
    ∃D : ExpressionData (innerModel hM env hS).Domain, D.map Subtype.val=C ∧ D.Valid (innerModel hM env hS) :=
  ⟨innerExpressionData hM env hS C hC,rfl,innerExpressionData_valid_d hM env hS C hC⟩

theorem inner_legal_at_iff_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    (env : Env M 24) (hS : FixedSyntax M (defContext.eval env) (defData.eval env) (env.bound 0) (env.bound 1) (env.bound 2))
    {C : ExpressionData M.Domain} (hC : C.Valid M) (s m : (innerModel hM env hS).Domain) :
    LegalAt (innerModel hM env hS) (innerExpressionData hM env hS C hC).omega (innerExpressionData hM env hS C hC).zero
      (innerExpressionData hM env hS C hC).one s m ↔ LegalAt M C.omega C.zero C.one s.val m.val :=
  legalAt_class_absolute hM.1 (constructible_transitive_class_d hM env hS) _ _ _ s m

/-- 外部的每一个合法表达式都有同一对象的内部代表，包含全部内部有限长度。 -/
theorem inner_expression_domain_iff_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    (env : Env M 24) (hS : FixedSyntax M (defContext.eval env) (defData.eval env) (env.bound 0) (env.bound 1) (env.bound 2))
    {C : ExpressionData M.Domain} (hC : C.Valid M) (s : M.Domain) :
    M.mem s C.expressions ↔ ∃s0 : (innerModel hM env hS).Domain, s0.val=s ∧
      (innerModel hM env hS).mem s0 (innerExpressionData hM env hS C hC).expressions := by
  exact ⟨fun hs => ⟨⟨s,legal_expression_constructible_d hM env hS hC hs⟩,rfl,hs⟩,fun ⟨s0,he,hs⟩ => he ▸ hs⟩

theorem inner_legal_input_exists_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    (env : Env M 24) (hS : FixedSyntax M (defContext.eval env) (defData.eval env) (env.bound 0) (env.bound 1) (env.bound 2))
    {C : ExpressionData M.Domain} (hC : C.Valid M) {s m : M.Domain} (hLegal : LegalAt M C.omega C.zero C.one s m) :
    ∃s0 m0 : (innerModel hM env hS).Domain, s0.val=s ∧ m0.val=m ∧
      LegalAt (innerModel hM env hS) (innerExpressionData hM env hS C hC).omega (innerExpressionData hM env hS C hC).zero
        (innerExpressionData hM env hS C hC).one s0 m0 := by
  let s0 : (innerModel hM env hS).Domain := ⟨s,natural_sequence_constructible_d hM env hS hC.omega hLegal.1.1 hLegal.1.2⟩
  let m0 : (innerModel hM env hS).Domain := ⟨m,natural_constructible_d hM env hS hC.omega hLegal.1.1⟩
  exact ⟨s0,m0,rfl,rfl,(inner_legal_at_iff_d hM env hS hC s0 m0).mpr hLegal⟩

theorem inner_natural_sequence_exists_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    (env : Env M 24) (hS : FixedSyntax M (defContext.eval env) (defData.eval env) (env.bound 0) (env.bound 1) (env.bound 2))
    {C : ExpressionData M.Domain} (hC : C.Valid M) {F m : M.Domain} (hm : M.mem m C.omega) (hF : Graph M F m C.omega) :
    ∃F0 m0 : (innerModel hM env hS).Domain, F0.val=F ∧ m0.val=m ∧
      (innerModel hM env hS).mem m0 (innerExpressionData hM env hS C hC).omega ∧
      Graph (innerModel hM env hS) F0 m0 (innerExpressionData hM env hS C hC).omega := by
  let F0 : (innerModel hM env hS).Domain := ⟨F,natural_sequence_constructible_d hM env hS hC.omega hm hF⟩
  let m0 : (innerModel hM env hS).Domain := ⟨m,natural_constructible_d hM env hS hC.omega hm⟩
  exact ⟨F0,m0,rfl,rfl,hm,(graph_class_absolute hM.1 (constructible_transitive_class_d hM env hS) F0 m0 _).mpr hF⟩

theorem inner_forest_exists_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    (env : Env M 24) (hS : FixedSyntax M (defContext.eval env) (defData.eval env) (env.bound 0) (env.bound 1) (env.bound 2))
    {C : ExpressionData M.Domain} (hC : C.Valid M) {F m : M.Domain} (hF : Forest M C.omega m F) :
    ∃F0 m0 : (innerModel hM env hS).Domain, F0.val=F ∧ m0.val=m ∧
      Forest (innerModel hM env hS) (innerExpressionData hM env hS C hC).omega m0 F0 := by
  let F0 : (innerModel hM env hS).Domain := ⟨F,finite_forest_constructible_d hM env hS hC hF⟩
  let m0 : (innerModel hM env hS).Domain := ⟨m,natural_constructible_d hM env hS hC.omega hF.width⟩
  exact ⟨F0,m0,rfl,rfl,(forest_class_absolute hM.1 (constructible_transitive_class_d hM env hS) _ m0 F0).mpr hF⟩

theorem finite_forest_space_constructible_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    (env : Env M 24) (hS : FixedSyntax M (defContext.eval env) (defData.eval env) (env.bound 0) (env.bound 1) (env.bound 2))
    {C : ExpressionData M.Domain} (hC : C.Valid M) {m Forests : M.Domain} (hm : M.mem m C.omega)
    (hForests : ∀F, M.mem F Forests ↔ Forest M C.omega m F) : InConstructible M env Forests := by
  let D := innerExpressionData hM env hS C hC
  let m0 : (innerModel hM env hS).Domain := ⟨m,natural_constructible_d hM env hS hC.omega hm⟩
  have hTrans := constructible_transitive_class_d hM env hS
  obtain ⟨F0,hF0⟩ := forest_space_exists_d (inner_models_kp_d hM env hS) (innerExpressionData_valid_d hM env hS C hC)
    (show (innerModel hM env hS).mem m0 D.omega from hm)
  have hRows (F : M.Domain) : M.mem F F0.val ↔ Forest M C.omega m F := by
    constructor
    · intro hF
      let p0 : (innerModel hM env hS).Domain := ⟨F,hTrans F0.val F0.property F hF⟩
      exact (forest_class_absolute hM.1 hTrans D.omega m0 p0).mp ((hF0 p0).mp hF)
    · intro hF
      let p0 : (innerModel hM env hS).Domain := ⟨F,finite_forest_constructible_d hM env hS hC hF⟩
      exact (hF0 p0).mpr ((forest_class_absolute hM.1 hTrans D.omega m0 p0).mpr hF)
  have he := hM.1.eq_of_same_members F0.val Forests (fun F => (hRows F).trans (hForests F).symm)
  exact he ▸ F0.property

theorem finite_forest_family_constructible_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    (env : Env M 24) (hS : FixedSyntax M (defContext.eval env) (defData.eval env) (env.bound 0) (env.bound 1) (env.bound 2))
    {C : ExpressionData M.Domain} (hC : C.Valid M) {m n Forests F : M.Domain} (hm : M.mem m C.omega) (hn : M.mem n C.omega)
    (hForests : ∀P, M.mem P Forests ↔ Forest M C.omega m P) (hF : Graph M F n Forests) : InConstructible M env F :=
  finite_sequence_constructible_d hM env hS hC.omega (finite_forest_space_constructible_d hM env hS hC hm hForests) hn hF

/-- 有限序数标签图同样闭合；仅长度有限，不要求值是自然数。 -/
theorem finite_ordinal_sequence_constructible_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    (env : Env M 24) (hS : FixedSyntax M (defContext.eval env) (defData.eval env) (env.bound 0) (env.bound 1) (env.bound 2))
    {w A F n : M.Domain} (hw : M.IsOmega w) (hA : M.IsOrdinal A) (hn : M.mem n w) (hF : Graph M F n A) :
    InConstructible M env F := finite_sequence_constructible_d hM env hS hw (ordinal_constructible_d hM env hS hA) hn hF

private def finiteComposeSchema : Project.Delta0BinarySchema 3 where
  body := Project.Formula.existsMem (.bound 4) (.conj (memPairFormula (.bound 4) (.bound 2) (.bound 0))
    (memPairFormula (.bound 3) (.bound 0) (.bound 1)))
  freeClosed := by simp [memPairFormula,codeFormula,pairFormula,Project.Formula.forallMem,Project.Formula.existsMem,Definitional.Formula.FreeClosed]
  delta0 := .existsMem _ (.conj (memPairFormula_delta0 _ _ _) (memPairFormula_delta0 _ _ _))

private def finiteRecoverSchema : Project.Delta0BinarySchema 3 where
  body := Project.Formula.existsMem (.bound 4) (.conj (memPairFormula (.bound 4) (.bound 0) (.bound 2))
    (memPairFormula (.bound 3) (.bound 0) (.bound 1)))
  freeClosed := by simp [memPairFormula,codeFormula,pairFormula,Project.Formula.forallMem,Project.Formula.existsMem,Definitional.Formula.FreeClosed]
  delta0 := .existsMem _ (.conj (memPairFormula_delta0 _ _ _) (memPairFormula_delta0 _ _ _))

/-- 任意实际有限枚举载域上的表先变为自然数索引有限序列，再有界恢复原表。
枚举可以重复；不需要选取宿主枚举，也不要求载域本身是序数。 -/
theorem finite_enumerated_graph_constructible_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    (env : Env M 24) (hS : FixedSyntax M (defContext.eval env) (defData.eval env) (env.bound 0) (env.bound 1) (env.bound 2))
    {w n A B E F : M.Domain} (hw : M.IsOmega w) (hn : M.mem n w) (hA : InConstructible M env A) (hB : InConstructible M env B)
    (hE : Graph M E n A) (hOnto : ∀x, M.mem x A → ∃i, M.mem i n ∧ MemPair M E i x) (hF : Graph M F A B) :
    InConstructible M env F := by
  let e := ((oneEnv A).push E).push F
  have hφ (i b : M.Domain) : Project.Formula.satisfies ((e.push i).push b) finiteComposeSchema.body ↔
      ∃x, M.mem x A ∧ MemPair M E i x ∧ MemPair M F x b := by
    simp only [finiteComposeSchema,Project.Formula.satisfies_existsMem_iff,Project.Formula.satisfies_conj_iff,memPairFormula_iff hM.1]
    rfl
  obtain ⟨H,hSupport,hRaw⟩ := relation_comprehension_d hM finiteComposeSchema e n B
  have hRows (i b : M.Domain) : MemPair M H i b ↔ M.mem i n ∧ M.mem b B ∧ ∃x, M.mem x A ∧ MemPair M E i x ∧ MemPair M F x b := by
    rw [hRaw i b,hφ]
  have hH : Graph M H n B := by
    refine ⟨hSupport,?_,?_⟩
    · intro i hi
      obtain ⟨x,hx,hIx⟩ := hE.total i hi
      obtain ⟨b,hb,hXb⟩ := hF.total x hx
      exact ⟨b,hb,(hRows i b).mpr ⟨hi,hb,x,hx,hIx,hXb⟩⟩
    · intro i b c hIb hIc
      obtain ⟨_,_,x,_,hIx,hXb⟩ := (hRows i b).mp hIb
      obtain ⟨_,_,y,_,hIy,hYc⟩ := (hRows i c).mp hIc
      have hxy := hE.unique i x y hIx hIy
      subst y
      exact hF.unique x b c hXb hYc
  have hEL := finite_sequence_constructible_d hM env hS hw hA hn hE
  have hHL := finite_sequence_constructible_d hM env hS hw hB hn hH
  have hnL := natural_constructible_d hM env hS hw hn
  apply relation_constructible_d hM env hS finiteRecoverSchema (((oneEnv n).push E).push H)
    (Fin.cases hHL (Fin.cases hEL (fun _ => hnL))) hA hB hF.support
  intro x b
  have hψ : Project.Formula.satisfies (((((oneEnv n).push E).push H).push x).push b) finiteRecoverSchema.body ↔
      ∃i, M.mem i n ∧ MemPair M E i x ∧ MemPair M H i b := by
    simp only [finiteRecoverSchema,Project.Formula.satisfies_existsMem_iff,Project.Formula.satisfies_conj_iff,memPairFormula_iff hM.1]
    rfl
  rw [hψ]
  constructor
  · intro hXb
    obtain ⟨hx,hb⟩ := hF.bounds hM.1 hXb
    obtain ⟨i,hi,hIx⟩ := hOnto x hx
    exact ⟨hx,hb,i,hi,hIx,(hRows i b).mpr ⟨hi,hb,x,hx,hIx,hXb⟩⟩
  · rintro ⟨_,_,i,_,hIx,hIb⟩
    obtain ⟨_,_,y,_,hIy,hYb⟩ := (hRows i b).mp hIb
    exact (hE.unique i y x hIy hIx) ▸ hYb

theorem inner_sequence_domain_iff_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    (env : Env M 24) (hS : FixedSyntax M (defContext.eval env) (defData.eval env) (env.bound 0) (env.bound 1) (env.bound 2))
    {C : ExpressionData M.Domain} (hC : C.Valid M) (s : M.Domain) :
    M.mem s C.sequences ↔ ∃s0 : (innerModel hM env hS).Domain, s0.val=s ∧
      (innerModel hM env hS).mem s0 (innerExpressionData hM env hS C hC).sequences := by
  constructor
  · intro hs
    have hsL := (expression_data_constructible_d hM env hS hC).sequences.mem_closed_d hM env hS hs
    exact ⟨⟨s,hsL⟩,rfl,hs⟩
  · rintro ⟨s0,he,hs⟩
    exact he ▸ hs

theorem inner_forest_domain_iff_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    (env : Env M 24) (hS : FixedSyntax M (defContext.eval env) (defData.eval env) (env.bound 0) (env.bound 1) (env.bound 2))
    {C : ExpressionData M.Domain} (hC : C.Valid M) (F m : M.Domain) :
    Forest M C.omega m F ↔ ∃F0 m0 : (innerModel hM env hS).Domain, F0.val=F ∧ m0.val=m ∧
      Forest (innerModel hM env hS) (innerExpressionData hM env hS C hC).omega m0 F0 := by
  constructor
  · exact inner_forest_exists_d hM env hS hC
  · rintro ⟨F0,m0,hF,hm,hForest⟩
    have hOuter := (forest_class_absolute hM.1 (constructible_transitive_class_d hM env hS)
      (innerExpressionData hM env hS C hC).omega m0 F0).mp hForest
    change Forest M C.omega m0.val F0.val at hOuter
    simpa only [hF,hm] using hOuter

/-- 为后续μ比较提供同一个有限序数标签图的内模型代表。 -/
theorem inner_ordinal_sequence_exists_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    (env : Env M 24) (hS : FixedSyntax M (defContext.eval env) (defData.eval env) (env.bound 0) (env.bound 1) (env.bound 2))
    {w A n F : M.Domain} (hw : M.IsOmega w) (hA : M.IsOrdinal A) (hn : M.mem n w) (hF : Graph M F n A) :
    ∃A0 n0 F0 : (innerModel hM env hS).Domain, A0.val=A ∧ n0.val=n ∧ F0.val=F ∧
      (innerModel hM env hS).IsOrdinal A0 ∧ Graph (innerModel hM env hS) F0 n0 A0 := by
  let A0 : (innerModel hM env hS).Domain := ⟨A,ordinal_constructible_d hM env hS hA⟩
  let n0 : (innerModel hM env hS).Domain := ⟨n,natural_constructible_d hM env hS hw hn⟩
  let F0 : (innerModel hM env hS).Domain := ⟨F,finite_ordinal_sequence_constructible_d hM env hS hw hA hn hF⟩
  exact ⟨A0,n0,F0,rfl,rfl,rfl,(inner_ordinal_absolute_d hM env hS A0).mpr hA,
    (graph_class_absolute hM.1 (constructible_transitive_class_d hM env hS) F0 n0 A0).mpr hF⟩

theorem inner_finite_packet_exists_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    (env : Env M 24) (hS : FixedSyntax M (defContext.eval env) (defData.eval env) (env.bound 0) (env.bound 1) (env.bound 2))
    {code x y : M.Domain} (hx : InConstructible M env x) (hy : InConstructible M env y) (hCode : Codes M code x y) :
    ∃code0 x0 y0 : (innerModel hM env hS).Domain, code0.val=code ∧ x0.val=x ∧ y0.val=y ∧ Codes (innerModel hM env hS) code0 x0 y0 := by
  let code0 : (innerModel hM env hS).Domain := ⟨code,finite_code_constructible_d hM env hS hx hy hCode⟩
  let x0 : (innerModel hM env hS).Domain := ⟨x,hx⟩
  let y0 : (innerModel hM env hS).Domain := ⟨y,hy⟩
  exact ⟨code0,x0,y0,rfl,rfl,rfl,(codes_class_absolute hM.1 (constructible_transitive_class_d hM env hS) code0 x0 y0).mpr hCode⟩

end KP1Y.OneYFinite
