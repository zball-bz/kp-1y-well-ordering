import KP1Y.RankedFamilyUnions

/-! 在实际索引序数内取元素首次出现的阶段；仅对内部集合使用最小元。 -/
namespace KP1Y.Ranking
open YesMetaZFC YesMetaZFC.SetTheory YesMetaZFC.SetTheory.Definitional
open KP1Y.Kuratowski KP1Y.Functions
universe u

def FirstStage (M : SetTheory.Structure.{u}) (H I V x j : M.Domain) : Prop :=
  M.mem j I ∧ FamilyMember M H V j x ∧ ∀ k, M.mem k I → FamilyMember M H V k x → j=k ∨ M.mem j k

def firstStageFormula {n : Nat} (H I V x j : Project.Term n) : Project.Formula 1 n :=
  .conj (.mem j I) (.conj (familyMemberFormula H V j x) (Project.Formula.forallMem I
    (.imp (familyMemberFormula H.weaken V.weaken (.bound 0) x.weaken)
      (.disj (Project.Formula.extensionalEq j.weaken (.bound 0)) (.mem j.weaken (.bound 0))))))

theorem firstStageFormula_delta0 {n : Nat} (H I V x j : Project.Term n) : (firstStageFormula H I V x j).IsDelta0 :=
  .conj (.mem _ _) (.conj (familyMemberFormula_delta0 _ _ _ _) (.forallMem _
    (.imp (familyMemberFormula_delta0 _ _ _ _) (.disj (.atom _ _ _) (.mem _ _)))))

theorem firstStageFormula_freeClosed {n : Nat} (H I V x j : Project.Term n)
    (hH : H.freeSupport=[]) (hI : I.freeSupport=[]) (hV : V.freeSupport=[])
    (hx : x.freeSupport=[]) (hj : j.freeSupport=[]) : (firstStageFormula H I V x j).FreeClosed := by
  simp only [firstStageFormula,Project.Formula.forallMem,Definitional.Formula.FreeClosed]
  refine ⟨by simp [hj,hI],familyMemberFormula_freeClosed _ _ _ _ hH hV hj hx,by simp [hI],?_,?_⟩
  · apply familyMemberFormula_freeClosed <;> simp [hH,hV,hx]
  · simp [hj]

theorem firstStageFormula_iff {M : SetTheory.Structure.{u}} (he : Extensional M) {n : Nat}
    (e : Env M n) (H I V x j : Project.Term n) : Project.Formula.satisfies e (firstStageFormula H I V x j) ↔
      FirstStage M (H.eval e) (I.eval e) (V.eval e) (x.eval e) (j.eval e) := by
  simp only [firstStageFormula,Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_mem_iff,
    familyMemberFormula_iff he,Project.Formula.satisfies_forallMem_iff,Project.Formula.satisfies_imp_iff,
    Project.Formula.satisfies_disj_iff,Project.Formula.satisfies_extensionalEq_iff_eq he,Term.eval_weaken]
  rfl

private def occurrenceSchema : Project.Delta0UnarySchema 3 where
  body := familyMemberFormula (.bound 3) (.bound 2) (.bound 0) (.bound 1)
  freeClosed := familyMemberFormula_freeClosed _ _ _ _ rfl rfl rfl rfl
  delta0 := familyMemberFormula_delta0 _ _ _ _

theorem first_stage_exists_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {H I V A κ x : M.Domain} (hI : M.IsOrdinal I) (hUnion : FamilyUnions M H I V A κ) (hx : M.mem x A) :
    ∃ j, FirstStage M H I V x j := by
  have hφ (j : M.Domain) : Project.Formula.satisfies ((((oneEnv H).push V).push x).push j) occurrenceSchema.body ↔
      FamilyMember M H V j x := by
    rw [occurrenceSchema,familyMemberFormula_iff hM.1]
    rfl
  obtain ⟨S,hRaw⟩ := SetTheory.KP.separation_exists_d (KP1Y.models_weakKP hM) occurrenceSchema (((oneEnv H).push V).push x) I
  have hS (j : M.Domain) : M.mem j S ↔ M.mem j I ∧ FamilyMember M H V j x := by
    simpa only [hφ] using hRaw j
  obtain ⟨j,hj,hOcc⟩ := (hUnion.carrier x).mp hx
  obtain ⟨k,hk,hMin⟩ := hI.wellOrder.least S (fun j hj => ((hS j).mp hj).1) ⟨j,(hS j).mpr ⟨hj,hOcc⟩⟩
  refine ⟨k,((hS k).mp hk).1,((hS k).mp hk).2,?_⟩
  intro l hl hOccL
  rcases hMin l ((hS l).mpr ⟨hl,hOccL⟩) with hSame | hkl
  · exact Or.inl (hM.1.eq_of_same_members k l hSame)
  · exact Or.inr hkl

theorem first_stage_unique {M : SetTheory.Structure.{u}} {H I V x j k : M.Domain} (hI : M.IsOrdinal I)
    (hj : FirstStage M H I V x j) (hk : FirstStage M H I V x k) : j=k := by
  rcases hj.2.2 k hk.1 hk.2.1 with he | hjk
  · exact he
  · rcases hk.2.2 j hj.1 hj.2.1 with he | hkj
    · exact he.symm
    · exact False.elim (hI.wellOrder.linear.irrefl j hj.1 (hI.wellOrder.linear.trans j hj.1 k hk.1 j hj.1 hjk hkj))

theorem firstStage_values_congr {M : SetTheory.Structure.{u}} (he : Extensional M) {H I V V' : M.Domain}
    (hH : Graph M H I V) (hH' : Graph M H I V') (x j : M.Domain) :
    FirstStage M H I V x j ↔ FirstStage M H I V' x j := by
  constructor
  · intro h
    exact ⟨h.1,(familyMember_values_congr he hH hH' j x).mp h.2.1,
      fun k hk hOcc => h.2.2 k hk ((familyMember_values_congr he hH hH' k x).mpr hOcc)⟩
  · intro h
    exact ⟨h.1,(familyMember_values_congr he hH hH' j x).mpr h.2.1,
      fun k hk hOcc => h.2.2 k hk ((familyMember_values_congr he hH hH' k x).mp hOcc)⟩

end KP1Y.Ranking
