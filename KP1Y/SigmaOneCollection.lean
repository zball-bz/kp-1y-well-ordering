import KP1Y.Completeness
import KP1Y.BoundedSyntax
import YesMetaZFC.SetTheory.Collection

/-! 从 Δ₀ 收集实际推出一重存在前缀的 Σ₁ 收集，不添加新公理。 -/
namespace KP1Y
open YesMetaZFC YesMetaZFC.SetTheory YesMetaZFC.SetTheory.Definitional
universe u

/-- 主变量依次为见证 z、输出 y、输入 x，随后是参数。 -/
structure WitnessMatrix (n : Nat) where
  body : Project.Formula 1 (n+3)
  freeClosed : body.FreeClosed
  delta0 : body.IsDelta0

def WitnessMatrix.existsSchema {n : Nat} (φ : WitnessMatrix n) : Project.BinarySchema n where
  body := .existsE φ.body
  freeClosed := by simpa only [Definitional.Formula.FreeClosed] using φ.freeClosed

/-- 在 z,y 后插入无序对容器 t 的变量槽。 -/
def skipBox {n : Nat} : Fin (n+3) → Fin (n+4) :=
  BoundEmbedding.lift (BoundEmbedding.lift (Fin.succ : Fin (n+1) → Fin (n+2)))

def WitnessMatrix.boxed {n : Nat} (φ : WitnessMatrix n) : Project.Delta0BinarySchema n where
  body := Project.Formula.existsMem (.bound 0)
    (Project.Formula.existsMem (.bound 1) (φ.body.rename skipBox))
  freeClosed := by
    simp [Project.Formula.existsMem, Definitional.Formula.FreeClosed, φ.freeClosed]
  delta0 := .existsMem _ (.existsMem _ (delta0_rename φ.delta0 skipBox))

private theorem skipBox_env {ℳ : SetTheory.Structure.{u}} {n : Nat}
    (env : Env ℳ n) (x t y z : ℳ.Domain) :
    ((((env.push x).push t).push y).push z).reindex skipBox =
      ((env.push x).push y).push z := by
  rw [Env.mk.injEq]
  constructor
  · funext i
    refine Fin.cases ?_ (fun i => ?_) i
    · rfl
    · refine Fin.cases ?_ (fun i => ?_) i
      · rfl
      · rfl
  · rfl

theorem boxed_iff {ℳ : SetTheory.Structure.{u}} {n : Nat}
    (φ : WitnessMatrix n) (env : Env ℳ n) (x t : ℳ.Domain) :
    Project.Formula.satisfies ((env.push x).push t) φ.boxed.body ↔
      ∃ y, ℳ.mem y t ∧ ∃ z, ℳ.mem z t ∧
        Project.Formula.satisfies (((env.push x).push y).push z) φ.body := by
  simp only [WitnessMatrix.boxed, Project.Formula.satisfies_existsMem_iff,
    Project.Formula.satisfies_rename, skipBox_env]
  rfl

/-- 把输出及其见证装入无序对后只调用一次 Δ₀ 收集，再取并集。 -/
theorem sigmaOne_collection_d {ℳ : SetTheory.Structure.{u}}
    (hKP : ℳ.Models theory) {n : Nat} (φ : WitnessMatrix n) (env : Env ℳ n)
    (source : ℳ.Domain)
    (ht : ∀ x, ℳ.mem x source → ∃ y z,
      Project.Formula.satisfies (((env.push x).push y).push z) φ.body) :
    ∃ bound, ∀ x, ℳ.mem x source → ∃ y, ℳ.mem y bound ∧ ∃ z,
      Project.Formula.satisfies (((env.push x).push y).push z) φ.body := by
  have hw := models_weakKP hKP
  have hboxed : ∀ x, ℳ.mem x source → ∃ t,
      Project.Formula.satisfies ((env.push x).push t) φ.boxed.body := by
    intro x hx
    obtain ⟨y,z,hyz⟩ := ht x hx
    obtain ⟨t,ht⟩ := SetTheory.KP.exists_pair hw y z
    exact ⟨t, (boxed_iff φ env x t).mpr
      ⟨y,(ht y).mpr (Or.inl rfl),z,(ht z).mpr (Or.inr rfl),hyz⟩⟩
  obtain ⟨C,hC⟩ := SetTheory.KP.collection_exists_d hw φ.boxed env source hboxed
  obtain ⟨B,hB⟩ := SetTheory.KP.exists_union hw C
  refine ⟨B, ?_⟩
  intro x hx
  obtain ⟨t,ht,hφ⟩ := hC x hx
  obtain ⟨y,hy,z,hz,hyz⟩ := (boxed_iff φ env x t).mp hφ
  exact ⟨y,(hB y).mpr ⟨t,ht,hy⟩,z,hyz⟩

/-- 每个指定矩阵的 Σ₁ 收集实例都有真实 KPω Hilbert 推导。 -/
theorem sigmaOne_collection_derivable {n : Nat} (φ : WitnessMatrix n) :
    Derives (Axioms.Schema.collection φ.existsSchema) := by
  apply derives_of_all_models
  intro M hM free
  apply (Project.Formula.satisfies_forallClosure_iff free
    (Axioms.Schema.collectionCore φ.existsSchema)).mpr
  intro bound
  let env : Env M n := ⟨bound,free⟩
  apply (Axioms.Schema.collection_sat_iff_d env φ.existsSchema).mpr
  intro source ht
  simp only [WitnessMatrix.existsSchema, Project.Formula.satisfies_exists_iff] at ht ⊢
  exact sigmaOne_collection_d hM φ env source ht

end KP1Y
