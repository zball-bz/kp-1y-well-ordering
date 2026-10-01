import KP1Y.SigmaOneCollection
import YesMetaZFC.SetTheory.Separation

/-! 互补的 Σ₁ 定义给出 Δ₁ 分离：见证界由 Δ₀ 收集产生。 -/
namespace KP1Y
open YesMetaZFC YesMetaZFC.SetTheory YesMetaZFC.SetTheory.Definitional
universe u

def existsUnary {n : Nat} (φ : Project.Delta0BinarySchema n) : Project.UnarySchema n where
  body := .existsE φ.body
  freeClosed := by simpa only [Definitional.Formula.FreeClosed] using φ.freeClosed

def eitherWitness {n : Nat} (φ ψ : Project.Delta0BinarySchema n) :
    Project.Delta0BinarySchema n where
  body := .disj φ.body ψ.body
  freeClosed := by
    simp only [Definitional.Formula.FreeClosed]
    exact ⟨φ.freeClosed,ψ.freeClosed⟩
  delta0 := .disj φ.delta0 ψ.delta0

def skipBound {n : Nat} : Fin (n+2) → Fin (n+3) :=
  BoundEmbedding.lift (BoundEmbedding.lift (Fin.succ : Fin n → Fin (n+1)))

def boundedWitness {n : Nat} (φ : Project.Delta0BinarySchema n) :
    Project.Delta0UnarySchema (n+1) where
  body := Project.Formula.existsMem (.bound 1) (φ.body.rename skipBound)
  freeClosed := by
    simp [Project.Formula.existsMem, Definitional.Formula.FreeClosed, φ.freeClosed]
  delta0 := .existsMem _ (delta0_rename φ.delta0 skipBound)

private theorem skipBound_env {ℳ : SetTheory.Structure.{u}} {n : Nat}
    (env : Env ℳ n) (C x z : ℳ.Domain) :
    (((env.push C).push x).push z).reindex skipBound = (env.push x).push z := by
  rw [Env.mk.injEq]
  constructor
  · funext i
    refine Fin.cases ?_ (fun i => ?_) i
    · rfl
    · refine Fin.cases ?_ (fun i => ?_) i <;> rfl
  · rfl

theorem boundedWitness_iff {ℳ : SetTheory.Structure.{u}} {n : Nat}
    (φ : Project.Delta0BinarySchema n) (env : Env ℳ n) (C x : ℳ.Domain) :
    Project.Formula.satisfies ((env.push C).push x) (boundedWitness φ).body ↔
      ∃ z, ℳ.mem z C ∧ Project.Formula.satisfies ((env.push x).push z) φ.body := by
  simp only [boundedWitness, Project.Formula.satisfies_existsMem_iff,
    Project.Formula.satisfies_rename, skipBound_env]
  rfl

/-- 无界的一重存在量词由收集所得的实际集合 C 界住。 -/
theorem deltaOne_separation_d {ℳ : SetTheory.Structure.{u}} (hKP : ℳ.Models theory)
    {n : Nat} (φ ψ : Project.Delta0BinarySchema n) (env : Env ℳ n)
    (hComplement : ∀ x,
      (∃ z, Project.Formula.satisfies ((env.push x).push z) φ.body) ↔
      ¬∃ z, Project.Formula.satisfies ((env.push x).push z) ψ.body)
    (source : ℳ.Domain) :
    ∃ subset, ∀ x, ℳ.mem x subset ↔ ℳ.mem x source ∧
      ∃ z, Project.Formula.satisfies ((env.push x).push z) φ.body := by
  classical
  have hw := models_weakKP hKP
  have ht : ∀ x, ℳ.mem x source → ∃ z,
      Project.Formula.satisfies ((env.push x).push z) (eitherWitness φ ψ).body := by
    intro x _
    by_cases hp : ∃ z, Project.Formula.satisfies ((env.push x).push z) φ.body
    · obtain ⟨z,hz⟩ := hp
      exact ⟨z, (Project.Formula.satisfies_disj_iff _ _ _).mpr (Or.inl hz)⟩
    · have hn : ∃ z, Project.Formula.satisfies ((env.push x).push z) ψ.body :=
        Classical.byContradiction (fun h => hp ((hComplement x).mpr h))
      obtain ⟨z,hz⟩ := hn
      exact ⟨z, (Project.Formula.satisfies_disj_iff _ _ _).mpr (Or.inr hz)⟩
  obtain ⟨C,hC⟩ := SetTheory.KP.collection_exists_d hw (eitherWitness φ ψ) env source ht
  obtain ⟨subset,hs⟩ := SetTheory.KP.separation_exists_d hw (boundedWitness φ) (env.push C) source
  refine ⟨subset, ?_⟩
  intro x
  rw [hs x, boundedWitness_iff]
  constructor
  · rintro ⟨hx,z,hz,hφ⟩
    exact ⟨hx,z,hφ⟩
  · rintro ⟨hx,hφ⟩
    obtain ⟨z,hz,hzφ⟩ := hC x hx
    rcases (Project.Formula.satisfies_disj_iff _ _ _).mp hzφ with hpos | hneg
    · exact ⟨hx,z,hz,hpos⟩
    · exact False.elim ((hComplement x).mp hφ ⟨z,hneg⟩)

/-- 两个 Σ₁ 定义互补时的分离闭句；互补性是前件，不是新公理。 -/
def deltaOneSeparationCore {n : Nat} (φ ψ : Project.Delta0BinarySchema n) :
    Project.Formula 1 n :=
  .imp (.forallE (.iff (existsUnary φ).body (.neg (existsUnary ψ).body)))
    (Axioms.Schema.separationCore (existsUnary φ))

def deltaOneSeparationSentence {n : Nat} (φ ψ : Project.Delta0BinarySchema n) :
    Project.Sentence :=
  Project.Sentence.forallClosure (deltaOneSeparationCore φ ψ) (by
    simp [deltaOneSeparationCore, existsUnary, Axioms.Schema.separationCore,
      Definitional.Formula.FreeClosed, φ.freeClosed, ψ.freeClosed])

/-- 实际 KPω ⊢ Δ₁-Separation 的这组标准规范形实例。 -/
theorem deltaOne_separation_derivable {n : Nat} (φ ψ : Project.Delta0BinarySchema n) :
    Derives (deltaOneSeparationSentence φ ψ) := by
  apply derives_of_all_models
  intro M hM free
  apply (Project.Formula.satisfies_forallClosure_iff free (deltaOneSeparationCore φ ψ)).mpr
  intro bound
  let env : Env M n := ⟨bound,free⟩
  apply (Project.Formula.satisfies_imp_iff _ _ _).mpr
  intro hComp
  have hc : ∀ x, (∃ z, Project.Formula.satisfies ((env.push x).push z) φ.body) ↔
      ¬∃ z, Project.Formula.satisfies ((env.push x).push z) ψ.body := by
    simpa only [Project.Formula.satisfies_forall_iff, Project.Formula.satisfies_iff_iff,
      existsUnary, Project.Formula.satisfies_exists_iff, Project.Formula.satisfies_neg_iff]
      using hComp
  apply (Axioms.Schema.separation_sat_iff_d env (existsUnary φ)).mpr
  intro source
  simpa only [existsUnary, Project.Formula.satisfies_exists_iff] using
    deltaOne_separation_d hM φ ψ env hc source

end KP1Y
