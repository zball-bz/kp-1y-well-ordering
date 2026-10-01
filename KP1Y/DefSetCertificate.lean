import KP1Y.DefinableSubsets
import KP1Y.Countability

/-! 用实际定义函数的满射图为 Def 集合提供字面 Δ₀ 证书。 -/
namespace KP1Y.Definability
open YesMetaZFC YesMetaZFC.SetTheory YesMetaZFC.SetTheory.Definitional
open KP1Y.Kuratowski KP1Y.Functions KP1Y.Cardinal KP1Y.Satisfaction
universe u

structure DefCertificate (M : SetTheory.Structure.{u}) (C : Context M.Domain) (D : RelationalData M.Domain)
    (Sat zero Def F : M.Domain) : Prop where
  onto : Onto M F C.columns Def
  rows : ∀ c, M.mem c C.columns → ∀ S, M.mem S Def → MemPair M F c S → DefinedBy M C D Sat zero c S

def defCertificateFormula {n : Nat} (C : Context (Project.Term n)) (D : RelationalData (Project.Term n))
    (Sat zero Def F : Project.Term n) : Project.Formula 1 n :=
  .conj (ontoFormula F C.columns Def)
    (Project.Formula.forallMem C.columns (Project.Formula.forallMem Def.weaken
      (.imp (memPairFormula F.weaken.weaken (.bound 1) (.bound 0))
        (definedByFormula C.weaken.weaken D.weaken.weaken Sat.weaken.weaken zero.weaken.weaken (.bound 1) (.bound 0)))))

theorem defCertificateFormula_delta0 {n : Nat} (C : Context (Project.Term n)) (D : RelationalData (Project.Term n))
    (Sat zero Def F : Project.Term n) : (defCertificateFormula C D Sat zero Def F).IsDelta0 :=
  .conj (ontoFormula_delta0 _ _ _) (.forallMem _ (.forallMem _
    (.imp (memPairFormula_delta0 _ _ _) (definedByFormula_delta0 _ _ _ _ _ _))))

theorem defCertificateFormula_iff {M : SetTheory.Structure.{u}} (he : Extensional M) {n : Nat}
    (env : Env M n) (C : Context (Project.Term n)) (D : RelationalData (Project.Term n)) (Sat zero Def F : Project.Term n) :
    Project.Formula.satisfies env (defCertificateFormula C D Sat zero Def F) ↔
      DefCertificate M (C.eval env) (D.eval env) (Sat.eval env) (zero.eval env) (Def.eval env) (F.eval env) := by
  simp only [defCertificateFormula, Project.Formula.satisfies_conj_iff, ontoFormula_iff he,
    Project.Formula.satisfies_forallMem_iff, Project.Formula.satisfies_imp_iff,
    memPairFormula_iff he, definedByFormula_iff he, Context.eval_weaken,
    RelationalData.eval_weaken, Definitional.Term.eval_weaken]
  exact ⟨fun h => ⟨h.1,h.2⟩,fun h => ⟨h.onto,h.rows⟩⟩

theorem def_certificate_exists_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : Context M.Domain} {D : RelationalData M.Domain} {Sat zero Def : M.Domain}
    (hDef : DefSet M C D Sat zero Def) : ∃ F, DefCertificate M C D Sat zero Def F := by
  obtain ⟨F,hSupport,hRaw⟩ := relation_comprehension_d hM definedBySchema (((syntaxEnv C D).push Sat).push zero) C.columns Def
  have hRows (c S : M.Domain) : MemPair M F c S ↔ M.mem c C.columns ∧ M.mem S Def ∧ DefinedBy M C D Sat zero c S := by
    simpa only [definedBySchema_iff hM.1] using hRaw c S
  refine ⟨F,⟨hSupport,?_,?_,?_⟩,fun c _ S _ hAt => ((hRows c S).mp hAt).2.2⟩
  · intro c hc
    obtain ⟨S,hS⟩ := defined_by_exists_d hM C D Sat zero c
    have hSDef := (hDef S).mpr ⟨c,hc,hS⟩
    exact ⟨S,hSDef,(hRows c S).mpr ⟨hc,hSDef,hS⟩⟩
  · intro c _ S _ T _ hS hT
    exact defined_by_unique hM.1 ((hRows c S).mp hS).2.2 ((hRows c T).mp hT).2.2
  · intro S hS
    obtain ⟨c,hc,hDefined⟩ := (hDef S).mp hS
    exact ⟨c,hc,(hRows c S).mpr ⟨hc,hS,hDefined⟩⟩

theorem def_certificate_exact {M : SetTheory.Structure.{u}} (he : Extensional M)
    {C : Context M.Domain} {D : RelationalData M.Domain} {Sat zero Def F : M.Domain}
    (h : DefCertificate M C D Sat zero Def F) : DefSet M C D Sat zero Def := by
  intro S
  constructor
  · intro hS
    obtain ⟨c,hc,hAt⟩ := h.onto.2.2.2 S hS
    exact ⟨c,hc,h.rows c hc S hS hAt⟩
  · rintro ⟨c,hc,hDefined⟩
    obtain ⟨T,hT,hAt⟩ := h.onto.2.1 c hc
    have hST := defined_by_unique he hDefined (h.rows c hc T hT hAt)
    exact hST ▸ hT

def defCertificateSchema : Project.Delta0BinarySchema 23 where
  body := defCertificateFormula definitionContext definitionData (.bound 3) (.bound 2) (.bound 1) (.bound 0)
  freeClosed := by
    simp [defCertificateFormula, definedByFormula, definitionPointFormula, validColumnFormula,
      formulaProgramFormula, wellFormedProgramFormula, wellFormedAtFormula, scopedAtomFormula,
      instructionAtFormula, Assignments.updatedFormula, graphFormula, ontoFormula,
      memPairFormula, codeFormula, pairFormula, Context.weaken, Context.map, RelationalData.weaken, RelationalData.map,
      definitionContext, definitionData, Project.Formula.existsMem, Project.Formula.forallMem, Definitional.Formula.FreeClosed]
  delta0 := defCertificateFormula_delta0 _ _ _ _ _ _

theorem defCertificateSchema_iff {M : SetTheory.Structure.{u}} (he : Extensional M)
    (C : Context M.Domain) (D : RelationalData M.Domain) (Sat zero Def F : M.Domain) :
    Project.Formula.satisfies (((((syntaxEnv C D).push Sat).push zero).push Def).push F) defCertificateSchema.body ↔
      DefCertificate M C D Sat zero Def F := by
  rw [defCertificateSchema,defCertificateFormula_iff he]
  rfl

theorem def_set_sigmaOne_iff_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    (C : Context M.Domain) (D : RelationalData M.Domain) (Sat zero Def : M.Domain) :
    DefSet M C D Sat zero Def ↔
      ∃ F, Project.Formula.satisfies (((((syntaxEnv C D).push Sat).push zero).push Def).push F) defCertificateSchema.body := by
  constructor
  · intro hDef
    obtain ⟨F,hF⟩ := def_certificate_exists_d hM hDef
    exact ⟨F,(defCertificateSchema_iff hM.1 C D Sat zero Def F).mpr hF⟩
  · rintro ⟨F,hF⟩
    exact def_certificate_exact hM.1 ((defCertificateSchema_iff hM.1 C D Sat zero Def F).mp hF)

end KP1Y.Definability
