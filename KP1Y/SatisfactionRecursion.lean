import KP1Y.SatisfactionSyntax

/-! 四分支只读更早行，故 KPω 中有唯一的实际求值表；原子解释仍由参数提供。 -/
namespace KP1Y.Satisfaction
open YesMetaZFC YesMetaZFC.SetTheory YesMetaZFC.SetTheory.Definitional
open KP1Y.Kuratowski KP1Y.Functions
universe u

theorem negation_local {M : SetTheory.Structure.{u}} {C : Context M.Domain}
    {p i c H J : M.Domain} (hc : M.mem c C.columns)
    (hPast : ∀ j, M.mem j i → ∀ b, M.mem b C.columns → (MemPair M H j b ↔ MemPair M J j b)) :
    NegationCase M C p i c H ↔ NegationCase M C p i c J := by
  constructor
  · rintro ⟨j,hj,r,hr,hInstr,hNot⟩
    exact ⟨j,hj,r,hr,hInstr,fun h => hNot ((hPast j hj c hc).mpr h)⟩
  · rintro ⟨j,hj,r,hr,hInstr,hNot⟩
    exact ⟨j,hj,r,hr,hInstr,fun h => hNot ((hPast j hj c hc).mp h)⟩

theorem implication_local {M : SetTheory.Structure.{u}} {C : Context M.Domain}
    {p i c H J : M.Domain} (hc : M.mem c C.columns)
    (hPast : ∀ j, M.mem j i → ∀ b, M.mem b C.columns → (MemPair M H j b ↔ MemPair M J j b)) :
    ImplicationCase M C p i c H ↔ ImplicationCase M C p i c J := by
  constructor
  · rintro ⟨j,hj,k,hk,hInstr,hImp⟩
    exact ⟨j,hj,k,hk,hInstr,fun h => (hPast k hk c hc).mp (hImp ((hPast j hj c hc).mpr h))⟩
  · rintro ⟨j,hj,k,hk,hInstr,hImp⟩
    exact ⟨j,hj,k,hk,hInstr,fun h => (hPast k hk c hc).mpr (hImp ((hPast j hj c hc).mp h))⟩

private theorem universal_transport {M : SetTheory.Structure.{u}} {C : Context M.Domain}
    {p s i H J : M.Domain}
    (hPast : ∀ j, M.mem j i → ∀ b, M.mem b C.columns → MemPair M H j b → MemPair M J j b)
    (h : UniversalCase M C p s i H) : UniversalCase M C p s i J := by
  obtain ⟨j,hj,v,hv,n,hn,hInstr,hS,hvn,hAll⟩ := h
  refine ⟨j,hj,v,hv,n,hn,hInstr,hS,hvn,?_⟩
  intro x hx
  obtain ⟨t,ht,hUpdate,b,hb,hCode,hTrue⟩ := hAll x hx
  exact ⟨t,ht,hUpdate,b,hb,hCode,hPast j hj b hb hTrue⟩

theorem universal_local {M : SetTheory.Structure.{u}} {C : Context M.Domain}
    {p s i H J : M.Domain}
    (hPast : ∀ j, M.mem j i → ∀ b, M.mem b C.columns → (MemPair M H j b ↔ MemPair M J j b)) :
    UniversalCase M C p s i H ↔ UniversalCase M C p s i J :=
  ⟨universal_transport (fun j hj b hb => (hPast j hj b hb).mp),
    universal_transport (fun j hj b hb => (hPast j hj b hb).mpr)⟩

theorem evalStep_congr {M : SetTheory.Structure.{u}} {C : Context M.Domain}
    {i c H J : M.Domain} (hc : M.mem c C.columns)
    (hPast : ∀ j, M.mem j i → ∀ b, M.mem b C.columns → (MemPair M H j b ↔ MemPair M J j b)) :
    EvalStep M C i c H ↔ EvalStep M C i c J := by
  have hCases (p s : M.Domain) :
      (AtomicCase M C p s i ∨ NegationCase M C p i c H ∨
        ImplicationCase M C p i c H ∨ UniversalCase M C p s i H) ↔
      (AtomicCase M C p s i ∨ NegationCase M C p i c J ∨
        ImplicationCase M C p i c J ∨ UniversalCase M C p s i J) :=
    or_congr Iff.rfl (or_congr (negation_local hc hPast)
      (or_congr (implication_local hc hPast) (universal_local hPast)))
  constructor
  · rintro ⟨p,hp,s,hs,hCode,h⟩
    exact ⟨p,hp,s,hs,hCode,(hCases p s).mp h⟩
  · rintro ⟨p,hp,s,hs,hCode,h⟩
    exact ⟨p,hp,s,hs,hCode,(hCases p s).mpr h⟩

theorem evalStep_local {M : SetTheory.Structure.{u}} (C : Context M.Domain) :
    KP1Y.Recursion.Local M C.omega C.columns (EvalStep M C) :=
  fun _ _ _ _ hPast _ hc => evalStep_congr hc hPast

theorem evalMatrix_local {M : SetTheory.Structure.{u}} (he : Extensional M) (C : Context M.Domain) :
    KP1Y.Recursion.Local M C.omega C.columns (evalMatrix.denote (contextEnv C)) := by
  intro i _ H J hPast c hc
  exact (evalMatrix_iff he C i c H).trans ((evalStep_congr hc hPast).trans (evalMatrix_iff he C i c J).symm)

theorem evaluation_exists_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    (C : Context M.Domain) (hω : M.IsOmega C.omega) : ∃ H, Evaluation M C H := by
  obtain ⟨H,hH⟩ := KP1Y.Recursion.bounded_recursion_d hM evalMatrix (contextEnv C)
    (KP1Y.Naturals.omega_isOrdinal_d hM hω) (evalMatrix_local hM.1 C)
  exact ⟨H,hH.1,fun i hi c hc => (hH.2 i hi c hc).trans (evalMatrix_iff hM.1 C i c H)⟩

theorem evaluation_unique_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : Context M.Domain} (hω : M.IsOmega C.omega) {H J : M.Domain}
    (hH : Evaluation M C H) (hJ : Evaluation M C J) : H=J :=
  KP1Y.Recursion.history_unique hM (KP1Y.Naturals.omega_isOrdinal_d hM hω)
    (fun _ h => h) (evalStep_local C) hH hJ

/-- 对十三个实际对象参数闭合的 KPω 推导，没有假设满意度集合存在。 -/
theorem evaluation_derivable : KP1Y.Derives evaluationSentence := by
  apply KP1Y.derives_of_all_models
  intro M hM free
  apply (Project.Formula.satisfies_forallClosure_iff free evaluationCore).mpr
  intro bound
  let env : Env M 13 := ⟨bound,free⟩
  exact (evaluationCore_iff hM.1 env).mpr (fun hω => evaluation_exists_d hM (rootParameters.eval env) hω)

end KP1Y.Satisfaction
