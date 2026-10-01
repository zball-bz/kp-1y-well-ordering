import KP1Y.DefOrdinalSlice
import KP1Y.LevelCompatibility
import KP1Y.ConstructibleClassSyntax

/-! 对象序数归纳证明Lα包含α的全部成员且没有更大的序数，并推出所有M序数可构造。 -/
namespace KP1Y.Constructible
open YesMetaZFC YesMetaZFC.SetTheory YesMetaZFC.SetTheory.Definitional
open KP1Y.Kuratowski KP1Y.Functions KP1Y.Bounded KP1Y.SetLanguage
universe u

def OrdinalContent (M : SetTheory.Structure.{u}) (H Γ V i : M.Domain) : Prop :=
  M.mem i Γ → ∀ T, M.mem T V → MemPair M H i T →
    M.MemberSubset i T ∧ ∀ x, M.mem x T → M.IsOrdinal x → M.mem x i

def ordinalContentFormula {n : Nat} (H Γ V i : Project.Term n) : Project.Formula 1 n :=
  .imp (.mem i Γ) (Project.Formula.forallMem V
    (.imp (memPairFormula H.weaken i.weaken (.bound 0))
      (.conj (Project.Formula.subset i.weaken (.bound 0))
        (Project.Formula.forallMem (.bound 0) (.imp (ordinalFormula (.bound 0)) (.mem (.bound 0) i.weaken.weaken))))))

theorem ordinalContentFormula_delta0 {n : Nat} (H Γ V i : Project.Term n) :
    (ordinalContentFormula H Γ V i).IsDelta0 :=
  .imp (.mem _ _) (.forallMem _ (.imp (memPairFormula_delta0 _ _ _)
    (.conj (.atom _ _ _) (.forallMem _ (.imp (ordinalFormula_delta0 _) (.mem _ _))))))

theorem ordinalContentFormula_iff {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory) {n : Nat}
    (e : Env M n) (H Γ V i : Project.Term n) :
    Project.Formula.satisfies e (ordinalContentFormula H Γ V i) ↔
      OrdinalContent M (H.eval e) (Γ.eval e) (V.eval e) (i.eval e) := by
  simp only [ordinalContentFormula,Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_mem_iff,
    Project.Formula.satisfies_forallMem_iff,Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_subset_iff,
    ordinalFormula_iff hM,memPairFormula_iff hM.1,Definitional.Term.eval_weaken]
  rfl

private def ordinalContentSchema : Project.Delta0UnarySchema 3 where
  body := ordinalContentFormula (.bound 3) (.bound 1) (.bound 2) (.bound 0)
  freeClosed := by
    simp [ordinalContentFormula,ordinalFormula,Project.Formula.isTransitive,memPairFormula,codeFormula,pairFormula,
      Project.Formula.forallMem,Project.Formula.existsMem,Definitional.Formula.FreeClosed]
  delta0 := ordinalContentFormula_delta0 _ _ _ _

private theorem ordinalContentSchema_iff {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory) (H Γ V i : M.Domain) :
    Project.Formula.satisfies ((((oneEnv H).push V).push Γ).push i) ordinalContentSchema.body ↔ OrdinalContent M H Γ V i := by
  rw [ordinalContentSchema,ordinalContentFormula_iff hM]
  rfl

theorem history_ordinal_content_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    (env : Env M 24) (hS : FixedSyntax M (defContext.eval env) (defData.eval env)
      (env.bound 0) (env.bound 1) (env.bound 2)) {H Γ V Q : M.Domain} (hΓ : M.IsOrdinal Γ)
    (h : KP1Y.SigmaRecursion.ValueHistory M (levelStepMatrix.denote env) H Γ V Q) :
    ∀ i, M.mem i Γ → ∀ T, MemPair M H i T → M.MemberSubset i T ∧ ∀ x, M.mem x T → M.IsOrdinal x → M.mem x i := by
  have hAll := KP1Y.ordinal_induction_d hM ordinalContentSchema.toUnarySchema (((oneEnv H).push V).push Γ) (by
    intro i hi ih
    apply (ordinalContentSchema_iff hM H Γ V i).mpr
    intro hiΓ T _ hAt
    have hEarlier (j : M.Domain) (hj : M.mem j i) : OrdinalContent M H Γ V j :=
      (ordinalContentSchema_iff hM H Γ V j).mp (ih j hj)
    rcases KP1Y.ordinal_cases hM.1 hi with hEmpty | ⟨p,hpOrd,hs⟩ | hLimit
    · have hT := history_empty_value_d hM h hiΓ hEmpty hAt
      exact ⟨fun x hx => False.elim (hEmpty x hx),fun x hx => False.elim (hT x hx)⟩
    · have hp := hs.predecessor_mem
      have hpΓ := hΓ.transitive i hiΓ p hp
      obtain ⟨A,hAV,hPrev⟩ := h.values.total p hpΓ
      have hPrevContent := hEarlier p hp hpΓ A hAV hPrev
      have hTransA := (history_transitive_and_cumulative_d hM env hS hΓ h p hpΓ A hPrev).1
      have hDef := history_successor_value_d hM hΓ h hiΓ hs hAt hPrev
      obtain ⟨S,hST,hSlice⟩ := hDef.ordinal_slice_d hM env hS hTransA
      have hSp : S=p := by
        apply hM.1.eq_of_same_members
        intro x
        constructor
        · intro hx
          obtain ⟨hxA,hOrd⟩ := (hSlice x).mp hx
          exact hPrevContent.2 x hxA hOrd
        · intro hx
          exact (hSlice x).mpr ⟨hPrevContent.1 x hx,hpOrd.mem hx⟩
      have hpT : M.mem p T := hSp ▸ hST
      have hSubAT := ((hDef.properties_d hM env hS).2 hTransA).1
      refine ⟨?_,?_⟩
      · intro x hx
        rcases (hs x).mp hx with hx | hSame
        · exact hSubAT x (hPrevContent.1 x hx)
        · exact (hM.1.eq_of_same_members x p hSame) ▸ hpT
      · intro x hxT hOrdX
        have hSubXA := hDef.member_subset_d hM env hS hxT
        have hSubXp : M.MemberSubset x p := fun y hy => hPrevContent.2 y (hSubXA y hy) (hOrdX.mem hy)
        rcases KP1Y.Naturals.ordinal_subset_cases_d hM hOrdX hpOrd hSubXp with he | hxp
        · subst x
          exact hs.predecessor_mem
        · exact (hs x).mpr (Or.inl hxp)
    · have hUnion := history_limit_value_d hM h hiΓ hLimit hAt
      refine ⟨?_,?_⟩
      · intro x hx
        obtain ⟨j,hj,hxj⟩ := hLimit.2.2 x hx
        have hjΓ := hΓ.transitive i hiΓ j hj
        obtain ⟨A,hAV,hJA⟩ := h.values.total j hjΓ
        have hPrev := hEarlier j hj hjΓ A hAV hJA
        exact (hUnion x).mpr ⟨j,hj,A,hJA,hPrev.1 x hxj⟩
      · intro x hx hOrdX
        obtain ⟨j,hj,A,hJA,hxA⟩ := (hUnion x).mp hx
        have hjΓ := hΓ.transitive i hiΓ j hj
        have hPrev := hEarlier j hj hjΓ A (h.values.bounds hM.1 hJA).2 hJA
        exact hi.transitive j hj x (hPrev.2 x hxA hOrdX))
  intro i hi T hAt
  exact (ordinalContentSchema_iff hM H Γ V i).mp (hAll i (hΓ.mem hi)) hi T (h.values.bounds hM.1 hAt).2 hAt

theorem level_ordinal_content_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    (env : Env M 24) (hS : FixedSyntax M (defContext.eval env) (defData.eval env)
      (env.bound 0) (env.bound 1) (env.bound 2)) {α T : M.Domain} (hT : IsLevel M env α T) :
    M.MemberSubset α T ∧ ∀ x, M.mem x T → M.IsOrdinal x → M.mem x α := by
  obtain ⟨δ,H,V,Q,hs,hH,hAt⟩ := hT.history
  have hδ := SetTheory.KP.successor_isOrdinal (KP1Y.models_weakKP hM) hT.ordinal hs
  exact history_ordinal_content_d hM env hS hδ hH α hs.predecessor_mem T hAt

theorem level_ordinals_iff_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    (env : Env M 24) (hS : FixedSyntax M (defContext.eval env) (defData.eval env)
      (env.bound 0) (env.bound 1) (env.bound 2)) {α T : M.Domain} (hT : IsLevel M env α T) :
    ∀ x, (M.mem x T ∧ M.IsOrdinal x) ↔ M.mem x α := by
  have hContent := level_ordinal_content_d hM env hS hT
  intro x
  exact ⟨fun h => hContent.2 x h.1 h.2,fun hx => ⟨hContent.1 x hx,hT.ordinal.mem hx⟩⟩

theorem ordinal_constructible_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    (env : Env M 24) (hS : FixedSyntax M (defContext.eval env) (defData.eval env)
      (env.bound 0) (env.bound 1) (env.bound 2)) {α : M.Domain} (hα : M.IsOrdinal α) : InConstructible M env α := by
  obtain ⟨β,hs⟩ := SetTheory.KP.exists_successor (KP1Y.models_weakKP hM) α
  have hβ := SetTheory.KP.successor_isOrdinal (KP1Y.models_weakKP hM) hα hs
  obtain ⟨T,hT⟩ := is_level_exists_d hM env hS hβ
  exact ⟨β,T,hT,(level_ordinal_content_d hM env hS hT).1 α hs.predecessor_mem⟩

end KP1Y.Constructible
