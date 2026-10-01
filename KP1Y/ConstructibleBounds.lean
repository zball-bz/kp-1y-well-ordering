import KP1Y.ConstructibleClass

/-! 在KP中收集构造成员的Σ₁证书，取序数界，使任意集合的构造成员落入共同层。 -/
namespace KP1Y.Constructible
open YesMetaZFC YesMetaZFC.SetTheory YesMetaZFC.SetTheory.Definitional
open KP1Y.Bounded KP1Y.SetLanguage
universe u

private def ordinalOnlySchema : Project.Delta0UnarySchema 0 where
  body := ordinalFormula (.bound 0)
  freeClosed := by
    simp [ordinalFormula,Project.Formula.isTransitive,Project.Formula.forallMem,Definitional.Formula.FreeClosed]
  delta0 := ordinalFormula_delta0 _

private theorem ordinalOnlySchema_iff {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    (env : Env M 0) (α : M.Domain) :
    Project.Formula.satisfies (env.push α) ordinalOnlySchema.body ↔ M.IsOrdinal α := by
  rw [ordinalOnlySchema,ordinalFormula_iff hM]
  rfl

theorem constructible_set_bounded_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    (env : Env M 24) (hS : FixedSyntax M (defContext.eval env) (defData.eval env)
      (env.bound 0) (env.bound 1) (env.bound 2)) (A : M.Domain)
    (hA : ∀ x, M.mem x A → InConstructible M env x) :
    ∃ β T, IsLevel M env β T ∧ M.MemberSubset A T := by
  have hw := KP1Y.models_weakKP hM
  obtain ⟨W,hW⟩ := SetTheory.KP.collection_exists_d hw constructibleMatrix env A
    (fun x hx => (constructible_sigmaOne_iff_d hM env x).mp (hA x hx))
  obtain ⟨U,hU⟩ := SetTheory.KP.exists_union hw W
  let e : Env M 0 := ⟨Fin.elim0,env.free⟩
  obtain ⟨O,hRawO⟩ := SetTheory.KP.separation_exists_d hw ordinalOnlySchema e U
  have hO (α : M.Domain) : M.mem α O ↔ M.mem α U ∧ M.IsOrdinal α := by
    simpa only [ordinalOnlySchema_iff hM] using hRawO α
  obtain ⟨β,hβUnion⟩ := SetTheory.KP.exists_union hw O
  have hβ : M.IsOrdinal β := Structure.IsOrdinal.of_union hw hβUnion (fun α hα => ((hO α).mp hα).2)
  obtain ⟨T,hT⟩ := is_level_exists_d hM env hS hβ
  refine ⟨β,T,hT,?_⟩
  intro x hx
  obtain ⟨B,hBW,hB⟩ := hW x hx
  obtain ⟨α,hαB,L,_,C,_,hC,hxL⟩ := (constructibleMatrix_iff hM env x B).mp hB
  have hαO := (hO α).mpr ⟨(hU α).mpr ⟨B,hBW,hαB⟩,hC.1⟩
  have hαβ : M.MemberSubset α β := fun y hy => (hβUnion y).mpr ⟨α,hαO,hy⟩
  exact level_subset_of_ordinal_subset_d hM env hS ⟨C,hC⟩ hT hαβ x hxL

theorem constructible_pair_parameters_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    (env : Env M 24) (hS : FixedSyntax M (defContext.eval env) (defData.eval env)
      (env.bound 0) (env.bound 1) (env.bound 2)) {x y : M.Domain}
    (hx : InConstructible M env x) (hy : InConstructible M env y) :
    ∃ α T, IsLevel M env α T ∧ M.mem x T ∧ M.mem y T := by
  obtain ⟨A,hA⟩ := SetTheory.KP.exists_pair (KP1Y.models_weakKP hM) x y
  have hAll : ∀ z, M.mem z A → InConstructible M env z := by
    intro z hz
    rcases (hA z).mp hz with he | he
    · exact he ▸ hx
    · exact he ▸ hy
  obtain ⟨α,T,hT,hSub⟩ := constructible_set_bounded_d hM env hS A hAll
  exact ⟨α,T,hT,hSub x ((hA x).mpr (Or.inl rfl)),hSub y ((hA y).mpr (Or.inr rfl))⟩

end KP1Y.Constructible
