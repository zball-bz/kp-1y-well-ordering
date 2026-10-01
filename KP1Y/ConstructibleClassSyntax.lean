import KP1Y.LevelCompatibility

/-! 全局构造类的实际Σ₁定义：成员属于某一经证书验证的层。 -/
namespace KP1Y.Constructible
open YesMetaZFC YesMetaZFC.SetTheory YesMetaZFC.SetTheory.Definitional
universe u

def InConstructible (M : SetTheory.Structure.{u}) (env : Env M 24) (x : M.Domain) : Prop :=
  ∃ α T, IsLevel M env α T ∧ M.mem x T

def ConstructibleCertificate (M : SetTheory.Structure.{u}) (env : Env M 24) (x B : M.Domain) : Prop :=
  ∃ α, M.mem α B ∧ ∃ T, M.mem T B ∧ ∃ C, M.mem C B ∧ LevelCertificate M env α T C ∧ M.mem x T

private def constructibleLevelSlots : Fin 27 → Fin 29 :=
  Fin.cases 0 (Fin.cases 1 (Fin.cases 2 (fun i => ⟨i.val+5,by omega⟩)))

def constructibleMatrix : Project.Delta0BinarySchema 24 where
  body := Project.Formula.existsMem (.bound 0) (Project.Formula.existsMem (.bound 1)
    (Project.Formula.existsMem (.bound 2)
      (.conj (levelCertificateMatrix.body.rename constructibleLevelSlots) (.mem (.bound 4) (.bound 1)))))
  freeClosed := by
    simp [Project.Formula.existsMem,Definitional.Formula.FreeClosed,levelCertificateMatrix.freeClosed]
  delta0 := .existsMem _ (.existsMem _ (.existsMem _
    (.conj (KP1Y.delta0_rename levelCertificateMatrix.delta0 _) (.mem _ _))))

private theorem constructibleLevelSlots_env {M : SetTheory.Structure.{u}} (env : Env M 24) (x B α T C : M.Domain) :
    (((((env.push x).push B).push α).push T).push C).reindex constructibleLevelSlots =
      ((env.push α).push T).push C := by
  rw [Env.mk.injEq]
  constructor
  · funext i
    refine Fin.cases ?_ (fun i => ?_) i
    · rfl
    · refine Fin.cases ?_ (fun i => ?_) i
      · rfl
      · refine Fin.cases ?_ (fun _ => ?_) i <;> rfl
  · rfl

theorem constructibleMatrix_iff {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    (env : Env M 24) (x B : M.Domain) :
    Project.Formula.satisfies ((env.push x).push B) constructibleMatrix.body ↔ ConstructibleCertificate M env x B := by
  simp only [constructibleMatrix,Project.Formula.satisfies_existsMem_iff,
    Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_mem_iff,
    Project.Formula.satisfies_rename,constructibleLevelSlots_env,levelCertificateMatrix_iff hM]
  rfl

theorem constructible_sigmaOne_iff_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    (env : Env M 24) (x : M.Domain) : InConstructible M env x ↔
      ∃ B, Project.Formula.satisfies ((env.push x).push B) constructibleMatrix.body := by
  constructor
  · rintro ⟨α,T,⟨C,hC⟩,hxT⟩
    obtain ⟨B0,hB0⟩ := SetTheory.KP.exists_pair (KP1Y.models_weakKP hM) α T
    obtain ⟨B,hB⟩ := SetTheory.KP.exists_insert (KP1Y.models_weakKP hM) B0 C
    exact ⟨B,(constructibleMatrix_iff hM env x B).mpr
      ⟨α,(hB α).mpr (Or.inl ((hB0 α).mpr (Or.inl rfl))),
        T,(hB T).mpr (Or.inl ((hB0 T).mpr (Or.inr rfl))),C,(hB C).mpr (Or.inr rfl),hC,hxT⟩⟩
  · rintro ⟨B,hB⟩
    obtain ⟨α,_,T,_,C,_,hC,hxT⟩ := (constructibleMatrix_iff hM env x B).mp hB
    exact ⟨α,T,⟨C,hC⟩,hxT⟩

def constructibleSchema : Project.UnarySchema 24 where
  body := .existsE constructibleMatrix.body
  freeClosed := by simpa only [Definitional.Formula.FreeClosed] using constructibleMatrix.freeClosed

theorem constructibleSchema_iff {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    (env : Env M 24) (x : M.Domain) :
    Project.Formula.satisfies (env.push x) constructibleSchema.body ↔ InConstructible M env x := by
  rw [constructibleSchema,Project.Formula.satisfies_exists_iff]
  exact (constructible_sigmaOne_iff_d hM env x).symm

end KP1Y.Constructible
