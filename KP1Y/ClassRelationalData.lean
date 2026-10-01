import KP1Y.ClassSetAbsoluteness
import KP1Y.ClassInductiveSets
import KP1Y.SetLanguageInterpretation

/-! 所有语法字段已在传递类中时，完整序列空间与纯集合关系解释可下降到类结构。 -/
namespace KP1Y.Classes
open YesMetaZFC YesMetaZFC.SetTheory YesMetaZFC.SetTheory.Definitional
open KP1Y.Kuratowski KP1Y.Functions KP1Y.Satisfaction KP1Y.SetLanguage
universe u

theorem sequence_space_into_class {M : SetTheory.Structure.{u}} (he : Extensional M)
    {P : M.Domain → Prop} {hNe : ∃ x, P x} (hP : TransitiveClass M P)
    (S ω A : (classModel M P hNe).Domain)
    (hSpace : ∀ F, M.mem F S.val ↔ ∃ n, M.mem n ω.val ∧ Graph M F n A.val) :
    ∀ F, (classModel M P hNe).mem F S ↔ ∃ n, (classModel M P hNe).mem n ω ∧ Graph (classModel M P hNe) F n A := by
  intro F
  constructor
  · intro hF
    obtain ⟨n,hn,hGraph⟩ := (hSpace F.val).mp hF
    let n0 : (classModel M P hNe).Domain := ⟨n,hP ω.val ω.property n hn⟩
    exact ⟨n0,hn,(graph_class_absolute he hP F n0 A).mpr hGraph⟩
  · rintro ⟨n,hn,hGraph⟩
    exact (hSpace F.val).mpr ⟨n.val,hn,(graph_class_absolute he hP F n A).mp hGraph⟩

theorem data_spaces_into_class {M : SetTheory.Structure.{u}} (he : Extensional M)
    {P : M.Domain → Prop} {hNe : ∃ x, P x} (hP : TransitiveClass M P)
    (D : RelationalData (classModel M P hNe).Domain) (hD : DataSpaces M (D.map Subtype.val)) : DataSpaces (classModel M P hNe) D := by
  refine ⟨omega_into_class he hP D.omega hD.omega,
    sequence_space_into_class he hP D.variables D.omega D.omega hD.variables,
    sequence_space_into_class he hP D.values D.omega D.carrier hD.values,?_⟩
  intro a
  constructor
  · intro ha
    obtain ⟨r,hr,vars,hVars,hCode⟩ := (hD.codes a.val).mp ha
    let r0 : (classModel M P hNe).Domain := ⟨r,hP D.symbols.val D.symbols.property r hr⟩
    let vars0 : (classModel M P hNe).Domain := ⟨vars,hP D.variables.val D.variables.property vars hVars⟩
    exact ⟨r0,hr,vars0,hVars,(codes_class_absolute he hP a r0 vars0).mpr hCode⟩
  · rintro ⟨r,hr,vars,hVars,hCode⟩
    exact (hD.codes a.val).mpr ⟨r.val,hr,vars.val,hVars,(codes_class_absolute he hP a r vars).mp hCode⟩

theorem setAtom_class_absolute {M : SetTheory.Structure.{u}} (he : Extensional M)
    {P : M.Domain → Prop} {hNe : ∃ x, P x} (hP : TransitiveClass M P)
    (A zero one two r t : (classModel M P hNe).Domain) :
    SetAtom (classModel M P hNe) A zero one two r t ↔ SetAtom M A.val zero.val one.val two.val r.val t.val := by
  let e := (((((oneEnv A).push zero).push one).push two).push r).push t
  exact (setAtomFormula_iff (class_extensional he hP) e (.bound 5) (.bound 4) (.bound 3) (.bound 2) (.bound 1) (.bound 0)).symm.trans
    ((delta0_class_absolute hP (setAtomFormula_delta0 (.bound 5) (.bound 4) (.bound 3) (.bound 2) (.bound 1) (.bound 0)) e).trans
      (setAtomFormula_iff he (forgetEnv e) (.bound 5) (.bound 4) (.bound 3) (.bound 2) (.bound 1) (.bound 0)))

theorem interpretation_into_class {M : SetTheory.Structure.{u}} (he : Extensional M)
    {P : M.Domain → Prop} {hNe : ∃ x, P x} (hP : TransitiveClass M P)
    (D : RelationalData (classModel M P hNe).Domain) (zero one two : (classModel M P hNe).Domain)
    (h : Interpretation M (D.map Subtype.val) zero.val one.val two.val) : Interpretation (classModel M P hNe) D zero one two := by
  refine ⟨⟨(empty_class_absolute hP zero).mpr h.naturals.zero_empty,h.naturals.zero_nat,
    (successor_class_absolute he hP one zero).mpr h.naturals.one_succ,h.naturals.one_nat,
    (successor_class_absolute he hP two one).mpr h.naturals.two_succ,h.naturals.two_nat⟩,
    data_spaces_into_class he hP D h.spaces,(pair_class_absolute he hP D.symbols zero one).mpr h.symbols,
    (graph_class_absolute he hP D.arity D.symbols D.omega).mpr h.arity,?_,?_⟩
  · intro r n
    constructor
    · intro hAt
      obtain ⟨hr,hn⟩ := (h.arity_rows r.val n.val).mp ((memPair_class_absolute he hP D.arity r n).mp hAt)
      exact ⟨hr,Subtype.ext hn⟩
    · rintro ⟨hr,hn⟩
      exact (memPair_class_absolute he hP D.arity r n).mpr ((h.arity_rows r.val n.val).mpr ⟨hr,congrArg Subtype.val hn⟩)
  · intro r t
    constructor
    · intro hAt
      obtain ⟨hr,ht,hAtom⟩ := (h.relation_rows r.val t.val).mp ((memPair_class_absolute he hP D.interpretation r t).mp hAt)
      exact ⟨hr,ht,(setAtom_class_absolute he hP D.carrier zero one two r t).mpr hAtom⟩
    · rintro ⟨hr,ht,hAtom⟩
      exact (memPair_class_absolute he hP D.interpretation r t).mpr ((h.relation_rows r.val t.val).mpr
        ⟨hr,ht,(setAtom_class_absolute he hP D.carrier zero one two r t).mp hAtom⟩)

end KP1Y.Classes
