import KP1Y.Countability

/-! 小于最小不可数序数的正序数均有满射，并由 Δ₀ 收集统一取得见证集合。 -/
namespace KP1Y.Cardinal
open YesMetaZFC YesMetaZFC.SetTheory YesMetaZFC.SetTheory.Definitional
open KP1Y.Kuratowski
universe u

def clampSchema : Project.Delta0BinarySchema 2 where
  body := .disj (.conj (.mem (.bound 1) (.bound 2))
      (Project.Formula.extensionalEq (.bound 0) (.bound 1)))
    (.conj (.neg (.mem (.bound 1) (.bound 2)))
      (Project.Formula.extensionalEq (.bound 0) (.bound 3)))
  freeClosed := by simp [Definitional.Formula.FreeClosed]
  delta0 := .disj (.conj (.mem _ _) (.atom _ _ _)) (.conj (.neg (.mem _ _)) (.atom _ _ _))

def clampEnv {M : SetTheory.Structure.{u}} (z α : M.Domain) : Env M 2 :=
  ⟨Fin.cases α (fun _ => z),fun _ => z⟩

theorem clampSchema_iff {M : SetTheory.Structure.{u}} (he : Extensional M) (z α x y : M.Domain) :
    Project.Formula.satisfies (((clampEnv z α).push x).push y) clampSchema.body ↔
      ((M.mem x α ∧ y=x) ∨ (¬M.mem x α ∧ y=z)) := by
  simp only [clampSchema, Project.Formula.satisfies_disj_iff, Project.Formula.satisfies_conj_iff,
    Project.Formula.satisfies_mem_iff, Project.Formula.satisfies_neg_iff,
    Project.Formula.satisfies_extensionalEq_iff_eq he]
  rfl

/-- 有指定元素的非空子集可由母集满射：子集外全部送到该指定元素。 -/
theorem subset_surjection_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {X Y z : M.Domain} (hYX : M.MemberSubset Y X) (hz : M.mem z Y) : ∃ f, Onto M f X Y := by
  classical
  obtain ⟨f,hf,hMap⟩ := relation_comprehension_d hM clampSchema (clampEnv z Y) X Y
  have hm (x y : M.Domain) : MemPair M f x y ↔ M.mem x X ∧ M.mem y Y ∧
      ((M.mem x Y ∧ y=x) ∨ (¬M.mem x Y ∧ y=z)) := by
    simpa only [clampSchema_iff hM.1] using hMap x y
  refine ⟨f,hf,?_,?_,?_⟩
  · intro x hx
    by_cases hy : M.mem x Y
    · exact ⟨x,hy,(hm x x).mpr ⟨hx,hy,Or.inl ⟨hy,rfl⟩⟩⟩
    · exact ⟨z,hz,(hm x z).mpr ⟨hx,hz,Or.inr ⟨hy,rfl⟩⟩⟩
  · intro x hx a ha b hb hxa hxb
    have h1 := ((hm x a).mp hxa).2.2
    have h2 := ((hm x b).mp hxb).2.2
    rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2
    · exact h1.2.trans h2.2.symm
    · exact False.elim (h2.1 h1.1)
    · exact False.elim (h1.1 h2.1)
    · exact h1.2.trans h2.2.symm
  · intro y hy
    exact ⟨y,hYX y hy,(hm y y).mpr ⟨hYX y hy,hy,Or.inl ⟨hy,rfl⟩⟩⟩

theorem countable_segment_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {ω κ α : M.Domain} (hκ : UncountableOrdinal M ω κ)
    (hLeast : ∀ β, UncountableOrdinal M ω β → (κ=β ∨ M.mem κ β))
    (hακ : M.mem α κ) (hpos : ∃ x, M.mem x α) : ∃ f, Onto M f ω α := by
  have hw := KP1Y.models_weakKP hM
  have hα := hκ.1.mem hακ
  have hω := hκ.1.mem hκ.2.1
  rcases Structure.IsOrdinal.trichotomy hM.1 hα hω
    (SetTheory.KP.difference_exists_d hw) (SetTheory.KP.intersection_exists_d hw α ω) with
    he | haω | hωa
  · obtain ⟨z,hz⟩ := hpos
    exact subset_surjection_d hM (fun x hx => (he x).mp hx) hz
  · obtain ⟨z,hz⟩ := hpos
    exact subset_surjection_d hM (hω.transitive α haω) hz
  · exact countable_above_omega_d hM hκ hLeast hακ hωa

def collectedSchema : Project.Delta0BinarySchema 1 where
  body := .disj
    (.conj (Project.Formula.forallMem (.bound 1) .falsum)
      (Project.Formula.forallMem (.bound 0) .falsum))
    (.conj (Project.Formula.existsMem (.bound 1) .truth)
      (ontoFormula (.bound 0) (.bound 2) (.bound 1)))
  freeClosed := by
    simp [Project.Formula.forallMem, Project.Formula.existsMem, ontoFormula,
      memPairFormula, codeFormula, pairFormula, Definitional.Formula.FreeClosed]
  delta0 := .disj (.conj (.forallMem _ .falsum) (.forallMem _ .falsum))
    (.conj (.existsMem _ .truth) (ontoFormula_delta0 _ _ _))

theorem collectedSchema_iff {M : SetTheory.Structure.{u}} (he : Extensional M) (ω α f : M.Domain) :
    Project.Formula.satisfies (((oneEnv ω).push α).push f) collectedSchema.body ↔
      ((∀ x, ¬M.mem x α) ∧ (∀ x, ¬M.mem x f)) ∨ ((∃ x, M.mem x α) ∧ Onto M f ω α) := by
  simp only [collectedSchema, Project.Formula.satisfies_disj_iff,
    Project.Formula.satisfies_conj_iff, Project.Formula.satisfies_forallMem_iff,
    Project.Formula.satisfies_falsum_iff, Project.Formula.satisfies_existsMem_iff,
    Project.Formula.satisfies_truth_iff, and_true, ontoFormula_iff he]
  rfl

/-- KPω 先给出全部满射见证的一个集合；这里没有断言已选出统一 e。 -/
theorem surjection_witnesses_collected {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {ω κ : M.Domain} (hκ : UncountableOrdinal M ω κ)
    (hLeast : ∀ β, UncountableOrdinal M ω β → (κ=β ∨ M.mem κ β)) :
    ∃ C, ∀ α, M.mem α κ → (∃ x, M.mem x α) → ∃ f, M.mem f C ∧ Onto M f ω α := by
  classical
  have ht : ∀ α, M.mem α κ → ∃ f,
      Project.Formula.satisfies (((oneEnv ω).push α).push f) collectedSchema.body := by
    intro α hα
    by_cases hpos : ∃ x, M.mem x α
    · obtain ⟨f,hf⟩ := countable_segment_d hM hκ hLeast hα hpos
      exact ⟨f,(collectedSchema_iff hM.1 ω α f).mpr (Or.inr ⟨hpos,hf⟩)⟩
    · obtain ⟨f,hf⟩ := SetTheory.KP.exists_empty (KP1Y.models_weakKP hM)
      exact ⟨f,(collectedSchema_iff hM.1 ω α f).mpr
        (Or.inl ⟨fun x hx => hpos ⟨x,hx⟩,hf⟩)⟩
  obtain ⟨C,hC⟩ := SetTheory.KP.collection_exists_d (KP1Y.models_weakKP hM)
    collectedSchema (oneEnv ω) κ ht
  refine ⟨C,?_⟩
  intro α hα hpos
  obtain ⟨f,hf,hcert⟩ := hC α hα
  rcases (collectedSchema_iff hM.1 ω α f).mp hcert with h | h
  · obtain ⟨x,hx⟩ := hpos
    exact False.elim (h.1 x hx)
  · exact ⟨f,hf,h.2⟩

end KP1Y.Cardinal
