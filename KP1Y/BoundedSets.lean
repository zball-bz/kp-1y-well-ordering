import KP1Y.OrdinalCases
import KP1Y.BoundedSyntax

/-! 常用集合定义的字面 Δ₀ 版本。序数的有界刻画使用 KP 基础，不量化幂集。 -/
namespace KP1Y.Bounded
open YesMetaZFC YesMetaZFC.SetTheory YesMetaZFC.SetTheory.Definitional
universe u

def emptyFormula {n : Nat} (a : Project.Term n) : Project.Formula 1 n :=
  Project.Formula.forallMem a .falsum

theorem emptyFormula_delta0 {n : Nat} (a : Project.Term n) : (emptyFormula a).IsDelta0 :=
  .forallMem _ .falsum

theorem emptyFormula_iff {M : SetTheory.Structure.{u}} {n : Nat}
    (env : Env M n) (a : Project.Term n) :
    Project.Formula.satisfies env (emptyFormula a) ↔ ∀ x, ¬M.mem x (a.eval env) := by
  simp only [emptyFormula, Project.Formula.satisfies_forallMem_iff, Project.Formula.satisfies_falsum_iff]

def successorFormula {n : Nat} (b a : Project.Term n) : Project.Formula 1 n :=
  .conj (.mem a b) (.conj (Project.Formula.subset a b)
    (Project.Formula.forallMem b (.disj (.mem (.bound 0) a.weaken)
      (Project.Formula.extensionalEq (.bound 0) a.weaken))))

theorem successorFormula_delta0 {n : Nat} (b a : Project.Term n) : (successorFormula b a).IsDelta0 :=
  .conj (.mem _ _) (.conj (.atom _ _ _) (.forallMem _ (.disj (.mem _ _) (.atom _ _ _))))

theorem successorFormula_iff {M : SetTheory.Structure.{u}} (he : Extensional M) {n : Nat}
    (env : Env M n) (b a : Project.Term n) :
    Project.Formula.satisfies env (successorFormula b a) ↔ M.SuccessorOf (b.eval env) (a.eval env) := by
  simp only [successorFormula, Project.Formula.satisfies_conj_iff,
    Project.Formula.satisfies_mem_iff, Project.Formula.satisfies_subset_iff,
    Project.Formula.satisfies_forallMem_iff, Project.Formula.satisfies_disj_iff,
    Project.Formula.satisfies_extensionalEq_iff_eq he, Definitional.Term.eval_weaken]
  constructor
  · rintro ⟨ha,hab,hb⟩ x
    constructor
    · intro hx
      rcases hb x hx with hx | hx
      · exact Or.inl hx
      · exact Or.inr (hx ▸ fun _ => Iff.rfl)
    · rintro (hx | hx)
      · exact hab x hx
      · exact (he.eq_of_same_members x (a.eval env) hx) ▸ ha
  · intro h
    refine ⟨h.predecessor_mem,fun x hx => (h x).mpr (Or.inl hx),?_⟩
    intro x hx
    rcases (h x).mp hx with hx | hx
    · exact Or.inl hx
    · exact Or.inr (he.eq_of_same_members x (a.eval env) hx)

def unionFormula {n : Nat} (U F : Project.Term n) : Project.Formula 1 n :=
  .conj (Project.Formula.forallMem U (Project.Formula.existsMem F.weaken (.mem (.bound 1) (.bound 0))))
    (Project.Formula.forallMem F (Project.Formula.forallMem (.bound 0) (.mem (.bound 0) U.weaken.weaken)))

theorem unionFormula_delta0 {n : Nat} (U F : Project.Term n) : (unionFormula U F).IsDelta0 :=
  .conj (.forallMem _ (.existsMem _ (.mem _ _))) (.forallMem _ (.forallMem _ (.mem _ _)))

theorem unionFormula_iff {M : SetTheory.Structure.{u}} {n : Nat}
    (env : Env M n) (U F : Project.Term n) :
    Project.Formula.satisfies env (unionFormula U F) ↔
      ∀ x, M.mem x (U.eval env) ↔ ∃ a, M.mem a (F.eval env) ∧ M.mem x a := by
  simp only [unionFormula, Project.Formula.satisfies_conj_iff,
    Project.Formula.satisfies_forallMem_iff, Project.Formula.satisfies_existsMem_iff,
    Project.Formula.satisfies_mem_iff, Definitional.Term.eval_weaken]
  exact ⟨fun h x => ⟨h.1 x,fun ⟨a,ha,hx⟩ => h.2 a ha x hx⟩,
    fun h => ⟨fun x hx => (h x).mp hx,fun a ha x hx => (h x).mpr ⟨a,ha,hx⟩⟩⟩

def ordinalFormula {n : Nat} (a : Project.Term n) : Project.Formula 1 n :=
  .conj (Project.Formula.isTransitive a)
    (.conj (Project.Formula.forallMem a (Project.Formula.isTransitive (.bound 0)))
      (Project.Formula.forallMem a (Project.Formula.forallMem a.weaken
        (.disj (Project.Formula.extensionalEq (.bound 1) (.bound 0))
          (.disj (.mem (.bound 1) (.bound 0)) (.mem (.bound 0) (.bound 1)))))))

theorem transitiveFormula_delta0 {n : Nat} (a : Project.Term n) : (Project.Formula.isTransitive a).IsDelta0 :=
  .forallMem _ (.forallMem _ (.mem _ _))

theorem ordinalFormula_delta0 {n : Nat} (a : Project.Term n) : (ordinalFormula a).IsDelta0 :=
  .conj (transitiveFormula_delta0 _) (.conj (.forallMem _ (transitiveFormula_delta0 _))
    (.forallMem _ (.forallMem _ (.disj (.atom _ _ _) (.disj (.mem _ _) (.mem _ _))))))

theorem ordinalFormula_iff {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory) {n : Nat}
    (env : Env M n) (a : Project.Term n) :
    Project.Formula.satisfies env (ordinalFormula a) ↔ M.IsOrdinal (a.eval env) := by
  simp only [ordinalFormula, Project.Formula.satisfies_conj_iff,
    Project.Formula.satisfies_isTransitive_iff, Project.Formula.satisfies_forallMem_iff,
    Project.Formula.satisfies_disj_iff, Project.Formula.satisfies_extensionalEq_iff_eq hM.1,
    Project.Formula.satisfies_mem_iff, Definitional.Term.eval_weaken]
  have hw := KP1Y.models_weakKP hM
  constructor
  · rintro ⟨hTrans,hMembers,hCompare⟩
    refine ⟨hTrans,⟨?_,?_⟩⟩
    · refine ⟨fun x _ => SetTheory.KP.mem_irrefl_d hw x,
        fun x _ y _ z hz hxy hyz => hMembers z hz y hyz x hxy,?_⟩
      intro x hx y hy
      rcases hCompare x hx y hy with he | hxy | hyx
      · change x=y at he
        exact Or.inl (he ▸ fun _ => Iff.rfl)
      · exact Or.inr (Or.inl hxy)
      · exact Or.inr (Or.inr hyx)
    · intro S hSA hNonempty
      obtain ⟨m,hm,hmin⟩ := SetTheory.KP.mem_minimal_exists_d hw hNonempty
      refine ⟨m,hm,?_⟩
      intro x hx
      rcases hCompare m (hSA m hm) x (hSA x hx) with he | hmx | hxm
      · change m=x at he
        exact Or.inl (he ▸ fun _ => Iff.rfl)
      · exact Or.inr hmx
      · exact False.elim (hmin x hx hxm)
  · intro h
    refine ⟨h.transitive,fun x hx => (h.mem hx).transitive,?_⟩
    intro x hx y hy
    rcases h.wellOrder.linear.compare x hx y hy with he | hxy | hyx
    · exact Or.inl (hM.1.eq_of_same_members x y he)
    · exact Or.inr (Or.inl hxy)
    · exact Or.inr (Or.inr hyx)

theorem ordinal_of_transitive_members_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {a : M.Domain} (ht : M.TransitiveSet a) (hm : ∀ x, M.mem x a → M.IsOrdinal x) : M.IsOrdinal a := by
  have hw := KP1Y.models_weakKP hM
  refine ⟨ht,⟨?_,?_⟩⟩
  · refine ⟨fun x _ => SetTheory.KP.mem_irrefl_d hw x,
      fun x _ y _ z hz hxy hyz => (hm z hz).transitive y hyz x hxy,?_⟩
    intro x hx y hy
    exact Structure.IsOrdinal.trichotomy hM.1 (hm x hx) (hm y hy)
      (SetTheory.KP.difference_exists_d hw) (SetTheory.KP.intersection_exists_d hw x y)
  · intro S hSA hNonempty
    obtain ⟨m,hmS,hmin⟩ := SetTheory.KP.mem_minimal_exists_d hw hNonempty
    refine ⟨m,hmS,?_⟩
    intro x hx
    rcases Structure.IsOrdinal.trichotomy hM.1 (hm m (hSA m hmS)) (hm x (hSA x hx))
      (SetTheory.KP.difference_exists_d hw) (SetTheory.KP.intersection_exists_d hw m x) with he | hmx | hxm
    · exact Or.inl he
    · exact Or.inr hmx
    · exact False.elim (hmin x hx hxm)

end KP1Y.Bounded
