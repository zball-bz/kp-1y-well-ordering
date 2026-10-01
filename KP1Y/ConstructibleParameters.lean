import KP1Y.ConstructibleUnion

/-! 任意对象公理模式的有限参数环境与源集合可同时放入一个实际构造层。 -/
namespace KP1Y.Constructible
open YesMetaZFC YesMetaZFC.SetTheory
open KP1Y.SetLanguage
universe u

theorem constructible_parameters_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    (env : Env M 24) (hS : FixedSyntax M (defContext.eval env) (defData.eval env)
      (env.bound 0) (env.bound 1) (env.bound 2)) {a : M.Domain} (ha : InConstructible M env a)
    {n : Nat} (vals : Fin n → M.Domain) (hVals : ∀ i, InConstructible M env (vals i)) :
    ∃ α T, IsLevel M env α T ∧ M.mem a T ∧ ∀ i, M.mem (vals i) T := by
  induction n with
  | zero =>
      obtain ⟨α,T,hT,haT⟩ := ha
      exact ⟨α,T,hT,haT,fun i => Fin.elim0 i⟩
  | succ n ih =>
      obtain ⟨α,T,hT,haT,hTail⟩ := ih (fun i => vals i.succ) (fun i => hVals i.succ)
      obtain ⟨β,U,hU,hTU,h0⟩ := constructible_pair_parameters_d hM env hS (hT.constructible_d hM env hS) (hVals 0)
      have hSub := hU.transitive_d hM env hS T hTU
      refine ⟨β,U,hU,hSub a haT,?_⟩
      intro i
      exact Fin.cases h0 (fun j => hSub (vals j.succ) (hTail j)) i

end KP1Y.Constructible
