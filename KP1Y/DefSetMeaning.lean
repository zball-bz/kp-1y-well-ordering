import KP1Y.DefSetCertificate
import KP1Y.NodeTruth
import KP1Y.FormulaResult

/-! 定义子集构造确实按已核验的公式程序真值求值，变量更新采用实际函数图。 -/
namespace KP1Y.Definability
open YesMetaZFC YesMetaZFC.SetTheory
open KP1Y.Kuratowski KP1Y.Functions KP1Y.Assignments KP1Y.Satisfaction
universe u

theorem definition_point_meaning {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : Context M.Domain} (hC : ContextSpaces M C) {D : RelationalData M.Domain}
    {H Raw Sat zero p length head bound s c x t : M.Domain}
    (hRaw : TruthSet M C H Raw) (hSat : TypedTruthSet M C D Raw Sat)
    (hP : FormulaResult M C D p length head bound) (hS : Graph M s bound C.carrier)
    (hZero : M.mem zero bound) (hCode : Codes M c p s) (hUpdate : Updated M t s bound C.carrier zero x) :
    DefinitionPoint M C D Sat zero c x ↔ NodeTrue M C H p head t := by
  constructor
  · rintro ⟨_,p',_,s',_,hCode',bound',_,hS',_,t',_,hUpdate',d,hd,hDCode,hDSat⟩
    obtain ⟨hPs,hSs⟩ := codes_injective hM.1 hCode hCode'
    subst p'
    subst s'
    have hBounds := domain_unique hM.1 hS hS'
    subst bound'
    have hTs := update_unique hM.1 hUpdate hUpdate'
    subst t'
    have hAt := (typed_truth_at_last hM hC hRaw hSat hP.formula hUpdate.graph hP.head_nat hP.successor hDCode).mp hDSat
    exact ⟨d,hd,hDCode,hAt⟩
  · rintro ⟨d,hd,hDCode,hAt⟩
    have hDSat := (typed_truth_at_last hM hC hRaw hSat hP.formula hUpdate.graph hP.head_nat hP.successor hDCode).mpr hAt
    have hValid := valid_column_of_formula hC hP.formula hS hCode
    have hs := (hC.assignments s).mpr ⟨bound,hP.wellFormed.bound_nat,hS⟩
    have ht := (hC.assignments t).mpr ⟨bound,hP.wellFormed.bound_nat,hUpdate.graph⟩
    exact ⟨hValid,p,hP.program_mem hC,s,hs,hCode,bound,hP.wellFormed.bound_nat,hS,hZero,t,ht,hUpdate,d,hd,hDCode,hDSat⟩

theorem def_set_covers_program_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : Context M.Domain} (hC : ContextSpaces M C) {D : RelationalData M.Domain}
    {H Raw Sat zero Def p length head bound s : M.Domain}
    (hRaw : TruthSet M C H Raw) (hSat : TypedTruthSet M C D Raw Sat) (hDef : DefSet M C D Sat zero Def)
    (hP : FormulaResult M C D p length head bound) (hS : Graph M s bound C.carrier) (hZero : M.mem zero bound) :
    ∃ S, M.mem S Def ∧ ∀ x, M.mem x S ↔ M.mem x C.carrier ∧
      ∃ t, Updated M t s bound C.carrier zero x ∧ NodeTrue M C H p head t := by
  have hs := (hC.assignments s).mpr ⟨bound,hP.wellFormed.bound_nat,hS⟩
  obtain ⟨c,hCode⟩ := codes_total hM p s
  have hc := (hC.columns c).mpr ⟨p,hP.program_mem hC,s,hs,hCode⟩
  obtain ⟨S,hDefined⟩ := defined_by_exists_d hM C D Sat zero c
  refine ⟨S,(hDef S).mpr ⟨c,hc,hDefined⟩,?_⟩
  intro x
  constructor
  · intro hx
    have hxA := hDefined.1 x hx
    obtain ⟨t,hUpdate⟩ := update_exists_d hM hS hxA
    exact ⟨hxA,t,hUpdate,(definition_point_meaning hM hC hRaw hSat hP hS hZero hCode hUpdate).mp ((hDefined.2 x hxA).mp hx)⟩
  · rintro ⟨hxA,t,hUpdate,hTrue⟩
    exact (hDefined.2 x hxA).mpr ((definition_point_meaning hM hC hRaw hSat hP hS hZero hCode hUpdate).mpr hTrue)

end KP1Y.Definability
