import KP1Y.WellFormedPrograms

/-! 只保留合法非空公式程序及匹配的赋值域，得到经过语法检查的满意度集合。 -/
namespace KP1Y.Satisfaction
open YesMetaZFC YesMetaZFC.SetTheory YesMetaZFC.SetTheory.Definitional
open KP1Y.Kuratowski KP1Y.Functions
universe u

def ValidColumn (M : SetTheory.Structure.{u}) (C : Context M.Domain) (D : RelationalData M.Domain) (c : M.Domain) : Prop :=
  ∃ p, M.mem p C.programs ∧ ∃ s, M.mem s C.assignments ∧ Codes M c p s ∧
    ∃ length, M.mem length C.omega ∧ ∃ bound, M.mem bound C.omega ∧
      FormulaProgram M C D p length bound ∧ Graph M s bound C.carrier

def validColumnFormula {n : Nat} (C : Context (Project.Term n)) (D : RelationalData (Project.Term n))
    (c : Project.Term n) : Project.Formula 1 n :=
  Project.Formula.existsMem C.programs (Project.Formula.existsMem C.assignments.weaken
    (.conj (codeFormula c.weaken.weaken (.bound 1) (.bound 0))
      (Project.Formula.existsMem C.omega.weaken.weaken (Project.Formula.existsMem C.omega.weaken.weaken.weaken
        (.conj (formulaProgramFormula C.weaken.weaken.weaken.weaken D.weaken.weaken.weaken.weaken
            (.bound 3) (.bound 1) (.bound 0))
          (graphFormula (.bound 2) (.bound 0) C.carrier.weaken.weaken.weaken.weaken))))))

theorem validColumnFormula_delta0 {n : Nat} (C : Context (Project.Term n)) (D : RelationalData (Project.Term n))
    (c : Project.Term n) : (validColumnFormula C D c).IsDelta0 :=
  .existsMem _ (.existsMem _ (.conj (codeFormula_delta0 _ _ _)
    (.existsMem _ (.existsMem _ (.conj (formulaProgramFormula_delta0 _ _ _ _ _) (graphFormula_delta0 _ _ _))))))

theorem validColumnFormula_iff {M : SetTheory.Structure.{u}} (he : Extensional M) {n : Nat}
    (env : Env M n) (C : Context (Project.Term n)) (D : RelationalData (Project.Term n)) (c : Project.Term n) :
    Project.Formula.satisfies env (validColumnFormula C D c) ↔ ValidColumn M (C.eval env) (D.eval env) (c.eval env) := by
  simp only [validColumnFormula, Project.Formula.satisfies_existsMem_iff,
    Project.Formula.satisfies_conj_iff, codeFormula_iff he, formulaProgramFormula_iff he,
    graphFormula_iff he, Context.eval_weaken, RelationalData.eval_weaken, Definitional.Term.eval_weaken]
  rfl

def syntaxContextParameters : Context (Project.Term 21) :=
  ⟨.bound 0,.bound 1,.bound 2,.bound 3,.bound 4,.bound 5,.bound 6,
    .bound 7,.bound 8,.bound 9,.bound 10,.bound 11,.bound 12⟩

def syntaxDataParameters : RelationalData (Project.Term 21) :=
  ⟨.bound 13,.bound 14,.bound 15,.bound 16,.bound 17,.bound 18,.bound 19,.bound 20⟩

def syntaxEnv {M : SetTheory.Structure.{u}} (C : Context M.Domain) (D : RelationalData M.Domain) : Env M 21 where
  bound k := match k.val with
    | 0 => C.omega | 1 => C.carrier | 2 => C.operands | 3 => C.pairs
    | 4 => C.instructions | 5 => C.programs | 6 => C.assignments | 7 => C.columns
    | 8 => C.atomic | 9 => C.atomTag | 10 => C.negTag | 11 => C.impTag | 12 => C.allTag
    | 13 => D.omega | 14 => D.carrier | 15 => D.symbols | 16 => D.arity
    | 17 => D.interpretation | 18 => D.variables | 19 => D.values | _ => D.codes
  free _ := C.omega

private def validColumnSchema : Project.Delta0UnarySchema 21 where
  body := validColumnFormula syntaxContextParameters.weaken syntaxDataParameters.weaken (.bound 0)
  freeClosed := by
    simp [validColumnFormula, formulaProgramFormula, wellFormedProgramFormula, wellFormedAtFormula,
      scopedAtomFormula, instructionAtFormula, graphFormula, memPairFormula, codeFormula, pairFormula,
      Context.weaken, Context.map, RelationalData.weaken, RelationalData.map,
      syntaxContextParameters, syntaxDataParameters, Project.Formula.existsMem,
      Project.Formula.forallMem, Definitional.Formula.FreeClosed]
  delta0 := validColumnFormula_delta0 _ _ _

private theorem validColumnSchema_iff {M : SetTheory.Structure.{u}} (he : Extensional M)
    (C : Context M.Domain) (D : RelationalData M.Domain) (c : M.Domain) :
    Project.Formula.satisfies ((syntaxEnv C D).push c) validColumnSchema.body ↔ ValidColumn M C D c := by
  simp only [validColumnSchema, validColumnFormula_iff he, Context.eval_weaken, RelationalData.eval_weaken]
  rfl

def TypedTruthSet (M : SetTheory.Structure.{u}) (C : Context M.Domain) (D : RelationalData M.Domain)
    (Raw Sat : M.Domain) : Prop := ∀ c, M.mem c Sat ↔ M.mem c Raw ∧ ValidColumn M C D c

def typedTruthFormula {n : Nat} (C : Context (Project.Term n)) (D : RelationalData (Project.Term n))
    (Raw Sat : Project.Term n) : Project.Formula 1 n :=
  .conj (Project.Formula.subset Sat Raw)
    (Project.Formula.forallMem Raw (.iff (.mem (.bound 0) Sat.weaken)
      (validColumnFormula C.weaken D.weaken (.bound 0))))

theorem typedTruthFormula_delta0 {n : Nat} (C : Context (Project.Term n)) (D : RelationalData (Project.Term n))
    (Raw Sat : Project.Term n) : (typedTruthFormula C D Raw Sat).IsDelta0 :=
  .conj (.atom _ _ _) (.forallMem _ (.iff (.mem _ _) (validColumnFormula_delta0 _ _ _)))

theorem typedTruthFormula_iff {M : SetTheory.Structure.{u}} (he : Extensional M) {n : Nat}
    (env : Env M n) (C : Context (Project.Term n)) (D : RelationalData (Project.Term n)) (Raw Sat : Project.Term n) :
    Project.Formula.satisfies env (typedTruthFormula C D Raw Sat) ↔
      TypedTruthSet M (C.eval env) (D.eval env) (Raw.eval env) (Sat.eval env) := by
  simp only [typedTruthFormula, Project.Formula.satisfies_conj_iff, Project.Formula.satisfies_subset_iff,
    Project.Formula.satisfies_forallMem_iff, Project.Formula.satisfies_iff_iff,
    Project.Formula.satisfies_mem_iff, validColumnFormula_iff he,
    Context.eval_weaken, RelationalData.eval_weaken, Definitional.Term.eval_weaken]
  constructor
  · rintro ⟨hSub,hRows⟩ c
    exact ⟨fun hc => ⟨hSub c hc,(hRows c (hSub c hc)).mp hc⟩,fun hc => (hRows c hc.1).mpr hc.2⟩
  · intro h
    exact ⟨fun c hc => ((h c).mp hc).1,
      fun c hc => ⟨fun hSat => ((h c).mp hSat).2,fun hValid => (h c).mpr ⟨hc,hValid⟩⟩⟩

theorem typed_truth_set_exists_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    (C : Context M.Domain) (D : RelationalData M.Domain) (Raw : M.Domain) : ∃ Sat, TypedTruthSet M C D Raw Sat := by
  obtain ⟨Sat,hSat⟩ := SetTheory.KP.separation_exists_d (KP1Y.models_weakKP hM) validColumnSchema (syntaxEnv C D) Raw
  refine ⟨Sat,fun c => ?_⟩
  simpa only [validColumnSchema_iff hM.1] using hSat c

theorem valid_column_of_formula {M : SetTheory.Structure.{u}} {C : Context M.Domain} (hC : ContextSpaces M C)
    {D : RelationalData M.Domain} {p s length bound c : M.Domain}
    (hP : FormulaProgram M C D p length bound) (hS : Graph M s bound C.carrier) (hCode : Codes M c p s) :
    ValidColumn M C D c :=
  ⟨p,(hC.programs p).mpr ⟨length,hP.1.length_nat,hP.1.graph⟩,
    s,(hC.assignments s).mpr ⟨bound,hP.1.bound_nat,hS⟩,hCode,length,hP.1.length_nat,bound,hP.1.bound_nat,hP,hS⟩

theorem typed_truth_at_last {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : Context M.Domain} (hC : ContextSpaces M C) {D : RelationalData M.Domain}
    {H Raw Sat p s i length bound c : M.Domain} (hRaw : TruthSet M C H Raw) (hSat : TypedTruthSet M C D Raw Sat)
    (hP : FormulaProgram M C D p length bound) (hS : Graph M s bound C.carrier)
    (hi : M.mem i C.omega) (hSucc : M.SuccessorOf length i) (hCode : Codes M c p s) :
    M.mem c Sat ↔ MemPair M H i c := by
  have hValid := valid_column_of_formula hC hP hS hCode
  have hFilter : M.mem c Sat ↔ M.mem c Raw :=
    (hSat c).trans ⟨And.left,fun h => ⟨h,hValid⟩⟩
  exact hFilter.trans (truth_at_last hM hC hRaw hP.1.graph
    ((hC.assignments s).mpr ⟨bound,hP.1.bound_nat,hS⟩) hi hP.1.length_nat hSucc hCode)

end KP1Y.Satisfaction
