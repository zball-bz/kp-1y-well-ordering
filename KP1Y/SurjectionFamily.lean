import KP1Y.EnumerationInitialSegment
import KP1Y.LeastChoice

/-! 从一个已给定内部良序的候选集合，选择所有正初段的满射图。 -/
namespace KP1Y.Cardinal
open YesMetaZFC YesMetaZFC.SetTheory YesMetaZFC.SetTheory.Definitional
open KP1Y.Kuratowski KP1Y.Functions
universe u

private def positiveSchema : Project.Delta0UnarySchema 0 where
  body := Project.Formula.existsMem (.bound 0) .truth
  freeClosed := by simp [Project.Formula.existsMem,Definitional.Formula.FreeClosed]
  delta0 := .existsMem _ .truth

private theorem positiveSchema_iff {M : SetTheory.Structure.{u}} (env : Env M 0) (a : M.Domain) :
    Project.Formula.satisfies (env.push a) positiveSchema.body ↔ ∃ x, M.mem x a := by
  simp only [positiveSchema, Project.Formula.satisfies_existsMem_iff, Project.Formula.satisfies_truth_iff, and_true]
  rfl

private def surjectionSchema : Project.Delta0BinarySchema 1 where
  body := ontoFormula (.bound 0) (.bound 2) (.bound 1)
  freeClosed := by
    simp [ontoFormula, memPairFormula, codeFormula, pairFormula, Project.Formula.existsMem,
      Project.Formula.forallMem, Definitional.Formula.FreeClosed]
  delta0 := ontoFormula_delta0 _ _ _

private theorem surjectionSchema_iff {M : SetTheory.Structure.{u}} (he : Extensional M) (ω a f : M.Domain) :
    Project.Formula.satisfies (((oneEnv ω).push a).push f) surjectionSchema.body ↔ Onto M f ω a := by
  rw [surjectionSchema,ontoFormula_iff he]
  rfl

structure SurjectionFamily (M : SetTheory.Structure.{u}) (ω κ W Pos F : M.Domain) : Prop where
  positive : ∀ a, M.mem a Pos ↔ M.mem a κ ∧ ∃ x, M.mem x a
  graph : Graph M F Pos W
  values : ∀ a f, MemPair M F a f → Onto M f ω a

theorem surjection_family_from_wellorder_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {ω κ W order : M.Domain} (hOrder : KP1Y.InternalWellOrder M order W)
    (hCandidates : ∀ a, M.mem a κ → (∃ x, M.mem x a) → ∃ f, M.mem f W ∧ Onto M f ω a) :
    ∃ Pos F, SurjectionFamily M ω κ W Pos F := by
  let env : Env M 0 := ⟨Fin.elim0,fun _ => ω⟩
  obtain ⟨Pos,hPos⟩ := SetTheory.KP.separation_exists_d (KP1Y.models_weakKP hM) positiveSchema env κ
  have hPositive (a : M.Domain) : M.mem a Pos ↔ M.mem a κ ∧ ∃ x, M.mem x a := by
    simpa only [positiveSchema_iff] using hPos a
  obtain ⟨F,hSupport,hTotal,hUnique,hValues⟩ := KP1Y.least_choice_graph_d hM surjectionSchema (oneEnv ω) hOrder
    (fun a ha => by
      obtain ⟨haκ,x,hx⟩ := (hPositive a).mp ha
      obtain ⟨f,hf,hOnto⟩ := hCandidates a haκ ⟨x,hx⟩
      exact ⟨f,hf,(surjectionSchema_iff hM.1 ω a f).mpr hOnto⟩)
  exact ⟨Pos,F,hPositive,⟨hSupport,hTotal,hUnique⟩,
    fun a f hAt => (surjectionSchema_iff hM.1 ω a f).mp (hValues a f hAt)⟩

end KP1Y.Cardinal
