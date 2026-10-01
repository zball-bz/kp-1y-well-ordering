import KP1Y.SigmaOneCollection

/-! 同时界住 Σ₁ 输出和证书，供一般递归历史的集合打包使用。 -/
namespace KP1Y
open YesMetaZFC YesMetaZFC.SetTheory YesMetaZFC.SetTheory.Definitional
universe u

theorem joint_collection_d {M : SetTheory.Structure.{u}} (hM : M.Models theory)
    {n : Nat} (φ : WitnessMatrix n) (env : Env M n) (A : M.Domain)
    (ht : ∀ x, M.mem x A → ∃ y z,
      Project.Formula.satisfies (((env.push x).push y).push z) φ.body) :
    ∃ B, ∀ x, M.mem x A → ∃ y, M.mem y B ∧ ∃ z, M.mem z B ∧
      Project.Formula.satisfies (((env.push x).push y).push z) φ.body := by
  have hw := models_weakKP hM
  have hboxed : ∀ x, M.mem x A → ∃ t,
      Project.Formula.satisfies ((env.push x).push t) φ.boxed.body := by
    intro x hx
    obtain ⟨y,z,hyz⟩ := ht x hx
    obtain ⟨t,ht⟩ := SetTheory.KP.exists_pair hw y z
    exact ⟨t,(boxed_iff φ env x t).mpr
      ⟨y,(ht y).mpr (Or.inl rfl),z,(ht z).mpr (Or.inr rfl),hyz⟩⟩
  obtain ⟨C,hC⟩ := SetTheory.KP.collection_exists_d hw φ.boxed env A hboxed
  obtain ⟨B,hB⟩ := SetTheory.KP.exists_union hw C
  refine ⟨B,?_⟩
  intro x hx
  obtain ⟨t,ht,hφ⟩ := hC x hx
  obtain ⟨y,hy,z,hz,hyz⟩ := (boxed_iff φ env x t).mp hφ
  exact ⟨y,(hB y).mpr ⟨t,ht,hy⟩,z,(hB z).mpr ⟨t,ht,hz⟩,hyz⟩

end KP1Y
