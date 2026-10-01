import KP1Y.DeltaOneSeparation

/-! KPω 中全定义 Δ₀ 函数的精确像集；全定义条件不能省略。 -/
namespace KP1Y
open YesMetaZFC YesMetaZFC.SetTheory YesMetaZFC.SetTheory.Definitional
universe u

def imageSlots {n : Nat} : Fin (n+2) → Fin (n+3) :=
  Fin.cases 1 (Fin.cases 0 (fun i => ⟨i.val+3, by omega⟩))

def imageMember {n : Nat} (φ : Project.Delta0BinarySchema n) :
    Project.Delta0UnarySchema (n+1) where
  body := Project.Formula.existsMem (.bound 1) (φ.body.rename imageSlots)
  freeClosed := by
    simp [Project.Formula.existsMem, Definitional.Formula.FreeClosed, φ.freeClosed]
  delta0 := .existsMem _ (delta0_rename φ.delta0 imageSlots)

private theorem imageSlots_env {M : SetTheory.Structure.{u}} {n : Nat}
    (env : Env M n) (A y x : M.Domain) :
    (((env.push A).push y).push x).reindex imageSlots = (env.push x).push y := by
  rw [Env.mk.injEq]
  constructor
  · funext i
    refine Fin.cases ?_ (fun i => ?_) i
    · rfl
    · refine Fin.cases ?_ (fun i => ?_) i <;> rfl
  · rfl

theorem imageMember_iff {M : SetTheory.Structure.{u}} {n : Nat}
    (φ : Project.Delta0BinarySchema n) (env : Env M n) (A y : M.Domain) :
    Project.Formula.satisfies ((env.push A).push y) (imageMember φ).body ↔
      ∃ x, M.mem x A ∧ Project.Formula.satisfies ((env.push x).push y) φ.body := by
  simp only [imageMember, Project.Formula.satisfies_existsMem_iff,
    Project.Formula.satisfies_rename, imageSlots_env]
  rfl

/-- 先 Δ₀ 收集，再在所得界内 Δ₀ 分离；不调用 ZF 的替换模式。 -/
theorem functional_image_d {M : SetTheory.Structure.{u}} (hM : M.Models theory)
    {n : Nat} (φ : Project.Delta0BinarySchema n) (env : Env M n) (A : M.Domain)
    (hTotal : ∀ x, M.mem x A → ∃ y,
      Project.Formula.satisfies ((env.push x).push y) φ.body)
    (hUnique : ∀ x, M.mem x A → ∀ y z,
      Project.Formula.satisfies ((env.push x).push y) φ.body →
      Project.Formula.satisfies ((env.push x).push z) φ.body → y=z) :
    ∃ B, ∀ y, M.mem y B ↔ ∃ x, M.mem x A ∧
      Project.Formula.satisfies ((env.push x).push y) φ.body := by
  have hw := models_weakKP hM
  obtain ⟨C,hC⟩ := SetTheory.KP.collection_exists_d hw φ env A hTotal
  obtain ⟨B,hB⟩ := SetTheory.KP.separation_exists_d hw (imageMember φ) (env.push A) C
  refine ⟨B, ?_⟩
  intro y
  rw [hB y, imageMember_iff]
  constructor
  · exact And.right
  · rintro ⟨x,hx,hxy⟩
    obtain ⟨z,hz,hxz⟩ := hC x hx
    have hyz := hUnique x hx y z hxy hxz
    exact ⟨hyz ▸ hz,x,hx,hxy⟩

end KP1Y
