import KP1Y.ReflectionClause
import KP1Y.BoundedRecursion

/-! 真实FR行公式及其Local证明；未使用的阶段和无效条目自动为空。 -/
namespace KP1Y.Reflection
open YesMetaZFC YesMetaZFC.SetTheory YesMetaZFC.SetTheory.Definitional
open KP1Y.Kuratowski KP1Y.Functions
universe u

def dataTerms : Data (Project.Term 13) :=
  ⟨⟨.bound 0,.bound 1,.bound 2,.bound 3,.bound 4,.bound 5,.bound 6⟩,
    .bound 7,.bound 8,.bound 9,.bound 10,.bound 11,.bound 12⟩

def dataEnv {M : SetTheory.Structure.{u}} (C : Data M.Domain) : Env M 13 :=
  ⟨Fin.cases C.omega (Fin.cases C.cap (Fin.cases C.middle (Fin.cases C.keys (Fin.cases C.block
    (Fin.cases C.bound (Fin.cases C.index (Fin.cases C.pairs (Fin.cases C.edgeCodes (Fin.cases C.needCodes
      (Fin.cases C.edgeLists (Fin.cases C.needLists (fun _ => C.labels)))))))))))),fun _ => C.omega⟩

theorem dataTerms_dataEnv {M : SetTheory.Structure.{u}} (C : Data M.Domain) : dataTerms.eval (dataEnv C)=C := rfl

def Row (M : SetTheory.Structure.{u}) (C : Data M.Domain) (σ a H : M.Domain) : Prop :=
  ∃ b, M.mem b C.cap ∧ ∃ K, M.mem K C.omega ∧ ∃ θ, M.mem θ C.cap ∧
    Cursor M C.keys C.index b K θ σ ∧ ValidQuery M C.toIndexData K θ a b ∧ Reflect M C H K θ a b

private def bodyData : Data (Project.Term 19) :=
  ⟨⟨.bound 6,.bound 7,.bound 8,.bound 9,.bound 10,.bound 11,.bound 12⟩,
    .bound 13,.bound 14,.bound 15,.bound 16,.bound 17,.bound 18⟩

private def rowBody : Project.Formula 1 19 :=
  .conj (cursorFormula bodyData.keys bodyData.index (.bound 2) (.bound 1) (.bound 0) (.bound 5))
    (.conj (validQueryFormula bodyData.toIndexData (.bound 1) (.bound 0) (.bound 4) (.bound 2))
      (reflectionFormula bodyData (.bound 3) (.bound 1) (.bound 0) (.bound 4) (.bound 2)))

private theorem rowBody_freeClosed : rowBody.FreeClosed := by
  have hData : bodyData.Closed := by constructor <;> rfl
  simp only [rowBody,Definitional.Formula.FreeClosed]
  refine ⟨cursorFormula_freeClosed _ _ _ _ _ _ rfl rfl rfl rfl rfl rfl,?_,
    reflectionFormula_freeClosed hData _ _ _ _ _ rfl rfl rfl rfl rfl⟩
  simp [validQueryFormula,bodyData,Definitional.Formula.FreeClosed]

def rowMatrix : KP1Y.Recursion.StepMatrix 13 where
  body := Project.Formula.existsMem (.bound 4) (Project.Formula.existsMem (.bound 4) (Project.Formula.existsMem (.bound 6) rowBody))
  freeClosed := by simp [Project.Formula.existsMem,Definitional.Formula.FreeClosed,rowBody_freeClosed]
  delta0 := .existsMem _ (.existsMem _ (.existsMem _ (.conj (cursorFormula_delta0 _ _ _ _ _ _)
    (.conj (validQueryFormula_delta0 _ _ _ _ _) (reflectionFormula_delta0 _ _ _ _ _ _)))))

theorem rowMatrix_iff {M : SetTheory.Structure.{u}} (he : Extensional M) (e : Env M 13) (σ a H : M.Domain) :
    rowMatrix.denote e σ a H ↔ Row M (dataTerms.eval e) σ a H := by
  simp only [KP1Y.Recursion.StepMatrix.denote,rowMatrix,Project.Formula.satisfies_existsMem_iff,rowBody,
    Project.Formula.satisfies_conj_iff,cursorFormula_iff he,validQueryFormula_iff he,reflectionFormula_iff he,Data.eval_index]
  rfl

theorem row_local_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory) (e : Env M 13)
    (hC : (dataTerms.eval e).Valid M) : KP1Y.Recursion.Local M (dataTerms.eval e).bound (dataTerms.eval e).cap (rowMatrix.denote e) := by
  intro σ _ H J hAgree a _
  rw [rowMatrix_iff hM.1,rowMatrix_iff hM.1]
  constructor
  · rintro ⟨b,hb,K,hK,θ,hθ,hCursor,hValid,hFR⟩
    exact ⟨b,hb,K,hK,θ,hθ,hCursor,hValid,
      (reflection_agrees_d hM hC hCursor hValid.2.2.2.2.2.1 hAgree).mp hFR⟩
  · rintro ⟨b,hb,K,hK,θ,hθ,hCursor,hValid,hFR⟩
    exact ⟨b,hb,K,hK,θ,hθ,hCursor,hValid,
      (reflection_agrees_d hM hC hCursor hValid.2.2.2.2.2.1 hAgree).mpr hFR⟩

theorem reflection_history_exists_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory) (e : Env M 13)
    (hC : (dataTerms.eval e).Valid M) :
    ∃ H, KP1Y.Recursion.History M (rowMatrix.denote e) H (dataTerms.eval e).bound (dataTerms.eval e).cap :=
  KP1Y.Recursion.bounded_recursion_d hM rowMatrix e (hC.bound.isOrdinal_d hM) (row_local_d hM e hC)

theorem reflection_history_unique_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory) (e : Env M 13)
    (hC : (dataTerms.eval e).Valid M) {H J : M.Domain}
    (h : KP1Y.Recursion.History M (rowMatrix.denote e) H (dataTerms.eval e).bound (dataTerms.eval e).cap)
    (h' : KP1Y.Recursion.History M (rowMatrix.denote e) J (dataTerms.eval e).bound (dataTerms.eval e).cap) : H=J :=
  KP1Y.Recursion.history_unique hM (hC.bound.isOrdinal_d hM) (fun _ h => h) (row_local_d hM e hC) h h'

end KP1Y.Reflection
