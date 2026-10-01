import KP1Y.TypedSatisfactionSentence

/-! 相对于实际满意度集合的定义子集；全部变量、赋值和程序搜索均有集合界。 -/
namespace KP1Y.Definability
open YesMetaZFC YesMetaZFC.SetTheory YesMetaZFC.SetTheory.Definitional
open KP1Y.Kuratowski KP1Y.Functions KP1Y.Assignments KP1Y.Satisfaction
universe u

def DefinitionPoint (M : SetTheory.Structure.{u}) (C : Context M.Domain) (D : RelationalData M.Domain)
    (Sat zero c x : M.Domain) : Prop :=
  ValidColumn M C D c ∧ ∃ p, M.mem p C.programs ∧ ∃ s, M.mem s C.assignments ∧ Codes M c p s ∧
    ∃ bound, M.mem bound C.omega ∧ Graph M s bound C.carrier ∧ M.mem zero bound ∧
      ∃ t, M.mem t C.assignments ∧ Updated M t s bound C.carrier zero x ∧
        ∃ d, M.mem d C.columns ∧ Codes M d p t ∧ M.mem d Sat

def definitionPointFormula {n : Nat} (C : Context (Project.Term n)) (D : RelationalData (Project.Term n))
    (Sat zero c x : Project.Term n) : Project.Formula 1 n :=
  .conj (validColumnFormula C D c)
    (Project.Formula.existsMem C.programs (Project.Formula.existsMem C.assignments.weaken
      (.conj (codeFormula c.weaken.weaken (.bound 1) (.bound 0))
        (Project.Formula.existsMem C.omega.weaken.weaken
          (.conj (graphFormula (.bound 1) (.bound 0) C.carrier.weaken.weaken.weaken)
            (.conj (.mem zero.weaken.weaken.weaken (.bound 0))
              (Project.Formula.existsMem C.assignments.weaken.weaken.weaken
                (.conj (updatedFormula (.bound 0) (.bound 2) (.bound 1) C.carrier.weaken.weaken.weaken.weaken
                    zero.weaken.weaken.weaken.weaken x.weaken.weaken.weaken.weaken)
                  (Project.Formula.existsMem C.columns.weaken.weaken.weaken.weaken
                    (.conj (codeFormula (.bound 0) (.bound 4) (.bound 1))
                      (.mem (.bound 0) Sat.weaken.weaken.weaken.weaken.weaken)))))))))))

theorem definitionPointFormula_delta0 {n : Nat} (C : Context (Project.Term n)) (D : RelationalData (Project.Term n))
    (Sat zero c x : Project.Term n) : (definitionPointFormula C D Sat zero c x).IsDelta0 :=
  .conj (validColumnFormula_delta0 _ _ _) (.existsMem _ (.existsMem _ (.conj (codeFormula_delta0 _ _ _)
    (.existsMem _ (.conj (graphFormula_delta0 _ _ _) (.conj (.mem _ _)
      (.existsMem _ (.conj (updatedFormula_delta0 _ _ _ _ _ _)
        (.existsMem _ (.conj (codeFormula_delta0 _ _ _) (.mem _ _)))))))))))

theorem definitionPointFormula_iff {M : SetTheory.Structure.{u}} (he : Extensional M) {n : Nat}
    (env : Env M n) (C : Context (Project.Term n)) (D : RelationalData (Project.Term n)) (Sat zero c x : Project.Term n) :
    Project.Formula.satisfies env (definitionPointFormula C D Sat zero c x) ↔
      DefinitionPoint M (C.eval env) (D.eval env) (Sat.eval env) (zero.eval env) (c.eval env) (x.eval env) := by
  simp only [definitionPointFormula, Project.Formula.satisfies_conj_iff, Project.Formula.satisfies_existsMem_iff,
    Project.Formula.satisfies_mem_iff, validColumnFormula_iff he, codeFormula_iff he,
    graphFormula_iff he, updatedFormula_iff he, Definitional.Term.eval_weaken]
  rfl

def DefinedBy (M : SetTheory.Structure.{u}) (C : Context M.Domain) (D : RelationalData M.Domain)
    (Sat zero c subset : M.Domain) : Prop :=
  M.MemberSubset subset C.carrier ∧ ∀ x, M.mem x C.carrier → (M.mem x subset ↔ DefinitionPoint M C D Sat zero c x)

def definedByFormula {n : Nat} (C : Context (Project.Term n)) (D : RelationalData (Project.Term n))
    (Sat zero c subset : Project.Term n) : Project.Formula 1 n :=
  .conj (Project.Formula.subset subset C.carrier)
    (Project.Formula.forallMem C.carrier (.iff (.mem (.bound 0) subset.weaken)
      (definitionPointFormula C.weaken D.weaken Sat.weaken zero.weaken c.weaken (.bound 0))))

theorem definedByFormula_delta0 {n : Nat} (C : Context (Project.Term n)) (D : RelationalData (Project.Term n))
    (Sat zero c subset : Project.Term n) : (definedByFormula C D Sat zero c subset).IsDelta0 :=
  .conj (.atom _ _ _) (.forallMem _ (.iff (.mem _ _) (definitionPointFormula_delta0 _ _ _ _ _ _)))

theorem definedByFormula_iff {M : SetTheory.Structure.{u}} (he : Extensional M) {n : Nat}
    (env : Env M n) (C : Context (Project.Term n)) (D : RelationalData (Project.Term n)) (Sat zero c subset : Project.Term n) :
    Project.Formula.satisfies env (definedByFormula C D Sat zero c subset) ↔
      DefinedBy M (C.eval env) (D.eval env) (Sat.eval env) (zero.eval env) (c.eval env) (subset.eval env) := by
  simp only [definedByFormula, Project.Formula.satisfies_conj_iff, Project.Formula.satisfies_subset_iff,
    Project.Formula.satisfies_forallMem_iff, Project.Formula.satisfies_iff_iff, Project.Formula.satisfies_mem_iff,
    definitionPointFormula_iff he, Context.eval_weaken, RelationalData.eval_weaken, Definitional.Term.eval_weaken]
  rfl

def definitionContext : Context (Project.Term 25) :=
  ⟨.bound 4,.bound 5,.bound 6,.bound 7,.bound 8,.bound 9,.bound 10,
    .bound 11,.bound 12,.bound 13,.bound 14,.bound 15,.bound 16⟩
def definitionData : RelationalData (Project.Term 25) :=
  ⟨.bound 17,.bound 18,.bound 19,.bound 20,.bound 21,.bound 22,.bound 23,.bound 24⟩

def definitionPointSchema : Project.Delta0UnarySchema 24 where
  body := definitionPointFormula definitionContext definitionData (.bound 3) (.bound 2) (.bound 1) (.bound 0)
  freeClosed := by
    simp [definitionPointFormula, validColumnFormula, formulaProgramFormula, wellFormedProgramFormula,
      wellFormedAtFormula, scopedAtomFormula, instructionAtFormula, updatedFormula, graphFormula,
      memPairFormula, codeFormula, pairFormula, Context.weaken, Context.map, RelationalData.weaken, RelationalData.map,
      definitionContext, definitionData, Project.Formula.existsMem, Project.Formula.forallMem, Definitional.Formula.FreeClosed]
  delta0 := definitionPointFormula_delta0 _ _ _ _ _ _

theorem definitionPointSchema_iff {M : SetTheory.Structure.{u}} (he : Extensional M)
    (C : Context M.Domain) (D : RelationalData M.Domain) (Sat zero c x : M.Domain) :
    Project.Formula.satisfies (((((syntaxEnv C D).push Sat).push zero).push c).push x) definitionPointSchema.body ↔
      DefinitionPoint M C D Sat zero c x := by
  rw [definitionPointSchema,definitionPointFormula_iff he]
  rfl

def definedBySchema : Project.Delta0BinarySchema 23 where
  body := definedByFormula definitionContext definitionData (.bound 3) (.bound 2) (.bound 1) (.bound 0)
  freeClosed := by
    simp [definedByFormula, definitionPointFormula, validColumnFormula, formulaProgramFormula, wellFormedProgramFormula,
      wellFormedAtFormula, scopedAtomFormula, instructionAtFormula, updatedFormula, graphFormula,
      memPairFormula, codeFormula, pairFormula, Context.weaken, Context.map, RelationalData.weaken, RelationalData.map,
      definitionContext, definitionData, Project.Formula.existsMem, Project.Formula.forallMem, Definitional.Formula.FreeClosed]
  delta0 := definedByFormula_delta0 _ _ _ _ _ _

theorem definedBySchema_iff {M : SetTheory.Structure.{u}} (he : Extensional M)
    (C : Context M.Domain) (D : RelationalData M.Domain) (Sat zero c subset : M.Domain) :
    Project.Formula.satisfies (((((syntaxEnv C D).push Sat).push zero).push c).push subset) definedBySchema.body ↔
      DefinedBy M C D Sat zero c subset := by
  rw [definedBySchema,definedByFormula_iff he]
  rfl

end KP1Y.Definability
