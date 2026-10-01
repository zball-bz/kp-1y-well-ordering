import KP1Y.ConstructibleSeparation

/-! Δ₀关系见证与构造性证书的统一Σ₁矩阵，以及有界证书过滤；保持两套参数环境。 -/
namespace KP1Y.Constructible
open YesMetaZFC YesMetaZFC.SetTheory YesMetaZFC.SetTheory.Definitional
open KP1Y.Classes
universe u

private def relationSlots {n : Nat} : Fin (n+2) → Fin ((n+24)+3) :=
  Fin.cases 1 (Fin.cases 2 (fun i => (frontIndex i).succ.succ.succ))

private def constructibleRelationSlots {n : Nat} : Fin 26 → Fin ((n+24)+3) :=
  Fin.cases 0 (Fin.cases 1 (fun i => (tailIndex n i).succ.succ.succ))

def constructibleRelationMatrix {n : Nat} (φ : Project.Delta0BinarySchema n) : KP1Y.WitnessMatrix (n+24) where
  body := .conj (φ.body.rename relationSlots) (constructibleMatrix.body.rename constructibleRelationSlots)
  freeClosed := by simp [Definitional.Formula.FreeClosed,φ.freeClosed,constructibleMatrix.freeClosed]
  delta0 := .conj (KP1Y.delta0_rename φ.delta0 _) (KP1Y.delta0_rename constructibleMatrix.delta0 _)

private theorem relationSlots_env {M : SetTheory.Structure.{u}} {n : Nat} (e : Env M n) (env : Env M 24)
    (x y B : M.Domain) :
    ((((joinedEnv e env).push x).push y).push B).reindex relationSlots = (e.push x).push y := by
  rw [Env.mk.injEq]
  constructor
  · funext i
    refine Fin.cases ?_ (fun i => ?_) i
    · rfl
    · refine Fin.cases ?_ (fun i => ?_) i
      · rfl
      · exact joinedEnv_front e env i
  · rfl

private theorem constructibleRelationSlots_iff {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {n : Nat} (e : Env M n) (env : Env M 24) (x y B : M.Domain) :
    Project.Formula.satisfies ((((joinedEnv e env).push x).push y).push B)
      (constructibleMatrix.body.rename constructibleRelationSlots) ↔ ConstructibleCertificate M env y B := by
  rw [Project.Formula.satisfies_rename]
  apply (KP1Y.formula_bound_congr constructibleMatrix.body constructibleMatrix.freeClosed _ ((env.push y).push B) ?_).trans
    (constructibleMatrix_iff hM env y B)
  intro i
  refine Fin.cases ?_ (fun i => ?_) i
  · rfl
  · refine Fin.cases ?_ (fun i => ?_) i
    · rfl
    · exact joinedEnv_tail e env i

theorem constructibleRelationMatrix_iff {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {n : Nat} (φ : Project.Delta0BinarySchema n) (e : Env M n) (env : Env M 24) (x y B : M.Domain) :
    Project.Formula.satisfies ((((joinedEnv e env).push x).push y).push B) (constructibleRelationMatrix φ).body ↔
      Project.Formula.satisfies ((e.push x).push y) φ.body ∧ ConstructibleCertificate M env y B := by
  simp only [constructibleRelationMatrix,Project.Formula.satisfies_conj_iff,
    constructibleRelationSlots_iff hM,Project.Formula.satisfies_rename,relationSlots_env]

private def boundedCertificateSlots : Fin 26 → Fin 27 :=
  Fin.cases 0 (Fin.cases 1 (fun i => ⟨i.val+3,by omega⟩))

def boundedConstructibleSchema : Project.Delta0UnarySchema 25 where
  body := Project.Formula.existsMem (.bound 1) (constructibleMatrix.body.rename boundedCertificateSlots)
  freeClosed := by simp [Project.Formula.existsMem,Definitional.Formula.FreeClosed,constructibleMatrix.freeClosed]
  delta0 := .existsMem _ (KP1Y.delta0_rename constructibleMatrix.delta0 _)

private theorem boundedCertificateSlots_env {M : SetTheory.Structure.{u}} (env : Env M 24) (W y B : M.Domain) :
    (((env.push W).push y).push B).reindex boundedCertificateSlots = (env.push y).push B := by
  rw [Env.mk.injEq]
  constructor
  · funext i
    refine Fin.cases ?_ (fun i => ?_) i
    · rfl
    · refine Fin.cases ?_ (fun _ => ?_) i <;> rfl
  · rfl

theorem boundedConstructibleSchema_iff {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    (env : Env M 24) (W y : M.Domain) :
    Project.Formula.satisfies ((env.push W).push y) boundedConstructibleSchema.body ↔
      ∃ B, M.mem B W ∧ ConstructibleCertificate M env y B := by
  simp only [boundedConstructibleSchema,Project.Formula.satisfies_existsMem_iff,
    Project.Formula.satisfies_rename,boundedCertificateSlots_env,constructibleMatrix_iff hM]
  rfl

theorem ConstructibleCertificate.in_class {M : SetTheory.Structure.{u}} {env : Env M 24} {y B : M.Domain}
    (h : ConstructibleCertificate M env y B) : InConstructible M env y := by
  obtain ⟨α,_,T,_,C,_,hC,hyT⟩ := h
  exact ⟨α,T,⟨C,hC⟩,hyT⟩

end KP1Y.Constructible
