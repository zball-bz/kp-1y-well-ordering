import KP1Y.History

/-! 递归历史的实际前缀集合及不同长度历史的相容性。 -/
namespace KP1Y.Recursion
open YesMetaZFC YesMetaZFC.SetTheory YesMetaZFC.SetTheory.Definitional
open KP1Y.Kuratowski
universe u

theorem History.bounds {M : SetTheory.Structure.{u}} (he : Extensional M)
    {step : M.Domain → M.Domain → M.Domain → Prop} {H δ B t a : M.Domain}
    (hH : History M step H δ B) (hm : MemPair M H t a) : M.mem t δ ∧ M.mem a B := by
  obtain ⟨p,hp,hcode⟩ := hm
  obtain ⟨s,hs,b,hb,hcode'⟩ := hH.1 p hp
  obtain ⟨hts,hab⟩ := codes_injective he hcode hcode'
  cases hts
  cases hab
  exact ⟨hs,hb⟩

def memberSchema : Project.Delta0BinarySchema 1 where
  body := memPairFormula (.bound 2) (.bound 1) (.bound 0)
  freeClosed := by
    simp [memPairFormula, codeFormula, pairFormula, Project.Formula.existsMem,
      Project.Formula.forallMem, Definitional.Formula.FreeClosed]
  delta0 := memPairFormula_delta0 _ _ _

theorem memberSchema_iff {M : SetTheory.Structure.{u}} (he : Extensional M) (H t a : M.Domain) :
    Project.Formula.satisfies (((oneEnv H).push t).push a) memberSchema.body ↔ MemPair M H t a := by
  rw [memberSchema, memPairFormula_iff he]
  rfl

theorem history_prefix {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {Γ B δ ρ H : M.Domain} {step : M.Domain → M.Domain → M.Domain → Prop}
    (hρ : M.IsOrdinal ρ) (hρδ : M.MemberSubset ρ δ) (hδΓ : M.MemberSubset δ Γ)
    (hLocal : Local M Γ B step) (hH : History M step H δ B) :
    ∃ J, History M step J ρ B ∧
      ∀ t, M.mem t ρ → ∀ a, M.mem a B → (MemPair M J t a ↔ MemPair M H t a) := by
  obtain ⟨J,hs,hj⟩ := relation_comprehension_d hM memberSchema (oneEnv H) ρ B
  have heq : ∀ t, M.mem t ρ → ∀ a, M.mem a B → (MemPair M J t a ↔ MemPair M H t a) := by
    intro t ht a ha
    have h := hj t a
    rw [memberSchema_iff hM.1] at h
    simpa only [ht,ha,true_and] using h
  refine ⟨J, ⟨hs,?_⟩,heq⟩
  intro t ht a ha
  have hloc := hLocal t (hδΓ t (hρδ t ht)) J H
    (fun s hs b hb => heq s (hρ.transitive t ht s hs) b hb) a ha
  exact (heq t ht a ha).trans ((hH.2 t (hρδ t ht) a ha).trans hloc.symm)

/-- 所有真实历史在其共同定义域上一致，故极限处可以取兼容并。 -/
theorem history_overlap {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {Γ B δ ε H J : M.Domain} {step : M.Domain → M.Domain → M.Domain → Prop}
    (hδ : M.IsOrdinal δ) (hε : M.IsOrdinal ε)
    (hδΓ : M.MemberSubset δ Γ) (hεΓ : M.MemberSubset ε Γ)
    (hLocal : Local M Γ B step) (hH : History M step H δ B) (hJ : History M step J ε B) :
    ∀ t, M.mem t δ → M.mem t ε → ∀ a, M.mem a B →
      (MemPair M H t a ↔ MemPair M J t a) := by
  have hw := KP1Y.models_weakKP hM
  rcases Structure.IsOrdinal.trichotomy hM.1 hδ hε
    (SetTheory.KP.difference_exists_d hw) (SetTheory.KP.intersection_exists_d hw δ ε) with
    he | hδε | hεδ
  · have heq := hM.1.eq_of_same_members δ ε he
    cases heq
    intro t ht _ a ha
    exact history_rows_agree hM hδ hδΓ hLocal hH hJ t ht a ha
  · obtain ⟨P,hP,hPref⟩ := history_prefix hM hδ (hε.transitive δ hδε) hεΓ hLocal hJ
    intro t ht _ a ha
    exact (history_rows_agree hM hδ hδΓ hLocal hH hP t ht a ha).trans (hPref t ht a ha)
  · obtain ⟨P,hP,hPref⟩ := history_prefix hM hε (hδ.transitive ε hεδ) hδΓ hLocal hH
    intro t _ ht a ha
    exact (hPref t ht a ha).symm.trans (history_rows_agree hM hε hεΓ hLocal hP hJ t ht a ha)

end KP1Y.Recursion
