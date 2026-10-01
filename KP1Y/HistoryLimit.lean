import KP1Y.HistorySuccessor

/-! 极限阶段由收集实际历史并取兼容并得到；不存在幂集或选择序列前提。 -/
namespace KP1Y.Recursion
open YesMetaZFC YesMetaZFC.SetTheory YesMetaZFC.SetTheory.Definitional
open KP1Y.Kuratowski
universe u

theorem history_limit {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {n : Nat} (φ : StepMatrix n) (env : Env M n)
    {Γ B δ : M.Domain} (hδ : M.IsLimitOrdinal δ) (hδΓ : M.MemberSubset δ Γ)
    (hLocal : Local M Γ B (φ.denote env))
    (ih : ∀ ε, M.mem ε δ → ∃ H, History M (φ.denote env) H ε B) :
    ∃ U, History M (φ.denote env) U δ B := by
  have hsmall {ε : M.Domain} (hε : M.mem ε δ) : M.MemberSubset ε Γ :=
    fun t ht => hδΓ t (hδ.1.transitive ε hε t ht)
  obtain ⟨C,hC⟩ := KP1Y.functional_image_d hM (historySchema φ) (env.push B) δ
    (fun ε hε => by
      obtain ⟨H,hH⟩ := ih ε hε
      exact ⟨H,(historySchema_iff hM.1 φ env B ε H).mpr hH⟩)
    (fun ε hε H J hH hJ => history_unique hM (hδ.1.mem hε) (hsmall hε) hLocal
      ((historySchema_iff hM.1 φ env B ε H).mp hH)
      ((historySchema_iff hM.1 φ env B ε J).mp hJ))
  have hc (H : M.Domain) : M.mem H C ↔ ∃ ε, M.mem ε δ ∧ History M (φ.denote env) H ε B := by
    simpa only [historySchema_iff hM.1] using hC H
  obtain ⟨U,hU⟩ := SetTheory.KP.exists_union (KP1Y.models_weakKP hM) C
  have hAgree : ∀ H ε, M.mem H C → M.mem ε δ → History M (φ.denote env) H ε B →
      ∀ t, M.mem t ε → ∀ a, M.mem a B → (MemPair M U t a ↔ MemPair M H t a) := by
    intro H ε hHC hε hH t ht a ha
    constructor
    · rintro ⟨p,hp,hcode⟩
      obtain ⟨J,hJC,hpJ⟩ := (hU p).mp hp
      obtain ⟨ζ,hζ,hJ⟩ := (hc J).mp hJC
      have htζ := (hJ.bounds hM.1 ⟨p,hpJ,hcode⟩).1
      exact (history_overlap hM (hδ.1.mem hε) (hδ.1.mem hζ)
        (hsmall hε) (hsmall hζ) hLocal hH hJ t ht htζ a ha).mpr ⟨p,hpJ,hcode⟩
    · rintro ⟨p,hp,hcode⟩
      exact ⟨p,(hU p).mpr ⟨H,hHC,hp⟩,hcode⟩
  refine ⟨U,?_,?_⟩
  · intro p hp
    obtain ⟨H,hHC,hpH⟩ := (hU p).mp hp
    obtain ⟨ε,hε,hH⟩ := (hc H).mp hHC
    obtain ⟨t,ht,a,ha,hcode⟩ := hH.1 p hpH
    exact ⟨t,hδ.1.transitive ε hε t ht,a,ha,hcode⟩
  · intro t ht a ha
    obtain ⟨ε,hε,htε⟩ := hδ.2.2 t ht
    obtain ⟨H,hH⟩ := ih ε hε
    have hHC := (hc H).mpr ⟨ε,hε,hH⟩
    have hPast := fun s hs b hb => hAgree H ε hHC hε hH s
      ((hδ.1.mem hε).transitive t htε s hs) b hb
    have hloc := hLocal t (hδΓ t ht) U H hPast a ha
    exact (hAgree H ε hHC hε hH t htε a ha).trans ((hH.2 t htε a ha).trans hloc.symm)

end KP1Y.Recursion
