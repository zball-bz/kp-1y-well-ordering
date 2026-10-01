import KP1Y.ConstructibleClassSyntax

/-! 构造类的传递性、空对象及各层自身属于该类。 -/
namespace KP1Y.Constructible
open YesMetaZFC YesMetaZFC.SetTheory
open KP1Y.SetLanguage
universe u

theorem InConstructible.mem_closed_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    (env : Env M 24) (hS : FixedSyntax M (defContext.eval env) (defData.eval env)
      (env.bound 0) (env.bound 1) (env.bound 2)) {x y : M.Domain}
    (hx : InConstructible M env x) (hyx : M.mem y x) : InConstructible M env y := by
  obtain ⟨α,T,hT,hxT⟩ := hx
  exact ⟨α,T,hT,hT.transitive_d hM env hS x hxT y hyx⟩

theorem IsLevel.constructible_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    (env : Env M 24) (hS : FixedSyntax M (defContext.eval env) (defData.eval env)
      (env.bound 0) (env.bound 1) (env.bound 2)) {α T : M.Domain} (h : IsLevel M env α T) : InConstructible M env T := by
  obtain ⟨β,hs⟩ := SetTheory.KP.exists_successor (KP1Y.models_weakKP hM) α
  have hβ := SetTheory.KP.successor_isOrdinal (KP1Y.models_weakKP hM) h.ordinal hs
  obtain ⟨U,hU⟩ := is_level_exists_d hM env hS hβ
  exact ⟨β,U,hU,level_member_d hM env hS h hU hs.predecessor_mem⟩

theorem empty_constructible_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    (env : Env M 24) (hS : FixedSyntax M (defContext.eval env) (defData.eval env)
      (env.bound 0) (env.bound 1) (env.bound 2)) {e : M.Domain} (he : Empty M e) : InConstructible M env e := by
  obtain ⟨T,hT⟩ := is_level_exists_d hM env hS (Structure.IsOrdinal.of_no_members he)
  have hTE : T=e := hM.1.eq_of_same_members T e (fun x => iff_of_false (hT.empty_value_d hM he x) (he x))
  exact hTE ▸ hT.constructible_d hM env hS

theorem constructible_nonempty_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    (env : Env M 24) (hS : FixedSyntax M (defContext.eval env) (defData.eval env)
      (env.bound 0) (env.bound 1) (env.bound 2)) : ∃ x, InConstructible M env x := by
  obtain ⟨e,he⟩ := SetTheory.KP.exists_empty (KP1Y.models_weakKP hM)
  exact ⟨e,empty_constructible_d hM env hS he⟩

end KP1Y.Constructible
