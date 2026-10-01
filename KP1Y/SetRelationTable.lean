import KP1Y.SetLanguageSyntax
import KP1Y.RelationTables

/-! 纯集合语言解释图的有界证书，排除非有序对成员并保证图本身唯一。 -/
namespace KP1Y.SetLanguage
open YesMetaZFC YesMetaZFC.SetTheory YesMetaZFC.SetTheory.Definitional
open KP1Y.Kuratowski KP1Y.Functions
universe u

structure SetRelationTable (M : SetTheory.Structure.{u}) (A zero one two symbols values R : M.Domain) : Prop where
  support : RelationSupport M R symbols values
  rows : ∀ r t, MemPair M R r t ↔ M.mem r symbols ∧ M.mem t values ∧ SetAtom M A zero one two r t

def setRelationTableFormula {n : Nat} (A zero one two symbols values R : Project.Term n) : Project.Formula 1 n :=
  .conj (relationSupportFormula R symbols values)
    (Project.Formula.forallMem symbols (Project.Formula.forallMem values.weaken
      (.iff (memPairFormula R.weaken.weaken (.bound 1) (.bound 0))
        (setAtomFormula A.weaken.weaken zero.weaken.weaken one.weaken.weaken two.weaken.weaken (.bound 1) (.bound 0)))))

theorem setRelationTableFormula_delta0 {n : Nat} (A zero one two symbols values R : Project.Term n) :
    (setRelationTableFormula A zero one two symbols values R).IsDelta0 :=
  .conj (relationSupportFormula_delta0 _ _ _) (.forallMem _ (.forallMem _
    (.iff (memPairFormula_delta0 _ _ _) (setAtomFormula_delta0 _ _ _ _ _ _))))

theorem setRelationTableFormula_iff {M : SetTheory.Structure.{u}} (he : Extensional M) {n : Nat}
    (env : Env M n) (A zero one two symbols values R : Project.Term n) :
    Project.Formula.satisfies env (setRelationTableFormula A zero one two symbols values R) ↔
      SetRelationTable M (A.eval env) (zero.eval env) (one.eval env) (two.eval env)
        (symbols.eval env) (values.eval env) (R.eval env) := by
  simp only [setRelationTableFormula,Project.Formula.satisfies_conj_iff,relationSupportFormula_iff he,
    Project.Formula.satisfies_forallMem_iff,Project.Formula.satisfies_iff_iff,memPairFormula_iff he,
    setAtomFormula_iff he,Definitional.Term.eval_weaken]
  constructor
  · rintro ⟨hSupport,hRows⟩
    refine ⟨hSupport,?_⟩
    intro r t
    constructor
    · intro hAt
      have hBounds := hSupport.bounds he hAt
      exact ⟨hBounds.1,hBounds.2,(hRows r hBounds.1 t hBounds.2).mp hAt⟩
    · rintro ⟨hr,ht,hAt⟩
      exact (hRows r hr t ht).mpr hAt
  · intro h
    exact ⟨h.support,fun r hr t ht => (h.rows r t).trans ⟨fun h => h.2.2,fun h => ⟨hr,ht,h⟩⟩⟩

private def setRowSchema : Project.Delta0BinarySchema 4 where
  body := setAtomFormula (.bound 2) (.bound 3) (.bound 4) (.bound 5) (.bound 1) (.bound 0)
  freeClosed := by
    simp [setAtomFormula,graphFormula,memPairFormula,codeFormula,pairFormula,
      Project.Formula.forallMem,Project.Formula.existsMem,Definitional.Formula.FreeClosed]
  delta0 := setAtomFormula_delta0 _ _ _ _ _ _

private def setRowEnv {M : SetTheory.Structure.{u}} (A zero one two : M.Domain) : Env M 4 :=
  ⟨Fin.cases A (Fin.cases zero (Fin.cases one (fun _ => two))),fun _ => A⟩

private theorem setRowSchema_iff {M : SetTheory.Structure.{u}} (he : Extensional M) (A zero one two r t : M.Domain) :
    Project.Formula.satisfies (((setRowEnv A zero one two).push r).push t) setRowSchema.body ↔
      SetAtom M A zero one two r t := by
  rw [setRowSchema,setAtomFormula_iff he]
  rfl

theorem set_relation_table_exists_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    (A zero one two symbols values : M.Domain) : ∃ R, SetRelationTable M A zero one two symbols values R := by
  obtain ⟨R,hSupport,hRows⟩ := relation_comprehension_d hM setRowSchema (setRowEnv A zero one two) symbols values
  refine ⟨R,hSupport,?_⟩
  intro r t
  simpa only [setRowSchema_iff hM.1] using hRows r t

theorem SetRelationTable.unique {M : SetTheory.Structure.{u}} (he : Extensional M)
    {A zero one two symbols values R R' : M.Domain}
    (h : SetRelationTable M A zero one two symbols values R) (h' : SetRelationTable M A zero one two symbols values R') : R=R' :=
  relation_ext he h.support h'.support (fun r t => (h.rows r t).trans (h'.rows r t).symm)

end KP1Y.SetLanguage
