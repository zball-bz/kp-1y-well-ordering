import KP1Y.RelationComprehension

/-! 对一个已经良序的候选集合取最小见证；不假定对象选择公理。 -/
namespace KP1Y
open YesMetaZFC YesMetaZFC.SetTheory YesMetaZFC.SetTheory.Definitional
open KP1Y.Kuratowski
universe u

/-- 最小元量化的是模型内部的集合子集，不是宿主 `Set M.Domain`。 -/
structure InternalWellOrder (M : SetTheory.Structure.{u}) (order C : M.Domain) : Prop where
  irrefl : ∀ x, M.mem x C → ¬MemPair M order x x
  trans : ∀ x, M.mem x C → ∀ y, M.mem y C → ∀ z, M.mem z C →
    MemPair M order x y → MemPair M order y z → MemPair M order x z
  least : ∀ S, M.MemberSubset S C → (∃ x, M.mem x S) →
    ∃ x, M.mem x S ∧ ∀ y, M.mem y S → (x=y ∨ MemPair M order x y)

def LeastWitness {M : SetTheory.Structure.{u}} (order C : M.Domain)
    (P : M.Domain → M.Domain → Prop) (x y : M.Domain) : Prop :=
  M.mem y C ∧ P x y ∧ ∀ z, M.mem z C → P x z → (y=z ∨ MemPair M order y z)

def fiberSchema {n : Nat} (φ : Project.Delta0BinarySchema n) : Project.Delta0UnarySchema (n+1) where
  body := φ.body
  freeClosed := φ.freeClosed
  delta0 := φ.delta0

def leastCandidateSlots {n : Nat} : Fin (n+2) → Fin (n+5) :=
  Fin.cases 0 (Fin.cases 2 (fun i => ⟨i.val+5, by omega⟩))

def leastSchema {n : Nat} (φ : Project.Delta0BinarySchema n) : Project.Delta0BinarySchema (n+2) where
  body := .conj (.mem (.bound 0) (.bound 2))
    (.conj (φ.body.rename BoundEmbedding.binaryUnderTwo)
      (Project.Formula.forallMem (.bound 2) (.imp (φ.body.rename leastCandidateSlots)
        (.disj (Project.Formula.extensionalEq (.bound 1) (.bound 0))
          (memPairFormula (.bound 4) (.bound 1) (.bound 0))))))
  freeClosed := by
    simp [Definitional.Formula.FreeClosed, Project.Formula.forallMem, Project.Formula.existsMem,
      memPairFormula, codeFormula, pairFormula, φ.freeClosed]
  delta0 := .conj (.mem _ _) (.conj (delta0_rename φ.delta0 _)
    (.forallMem _ (.imp (delta0_rename φ.delta0 _) (.disj (.atom _ _ _) (memPairFormula_delta0 _ _ _)))))

private theorem leastCandidateSlots_env {M : SetTheory.Structure.{u}} {n : Nat}
    (env : Env M n) (order C x y z : M.Domain) :
    (((((env.push order).push C).push x).push y).push z).reindex leastCandidateSlots =
      (env.push x).push z := by
  rw [Env.mk.injEq]
  constructor
  · funext i
    refine Fin.cases ?_ (fun i => ?_) i
    · rfl
    · refine Fin.cases ?_ (fun i => ?_) i <;> rfl
  · rfl

theorem leastSchema_iff {M : SetTheory.Structure.{u}} (he : Extensional M) {n : Nat}
    (φ : Project.Delta0BinarySchema n) (env : Env M n) (order C x y : M.Domain) :
    Project.Formula.satisfies ((((env.push order).push C).push x).push y) (leastSchema φ).body ↔
      LeastWitness order C (fun x y => Project.Formula.satisfies ((env.push x).push y) φ.body) x y := by
  simp only [leastSchema, Project.Formula.satisfies_conj_iff, Project.Formula.satisfies_mem_iff,
    Project.Formula.satisfies_forallMem_iff, Project.Formula.satisfies_imp_iff,
    Project.Formula.satisfies_disj_iff, Project.Formula.satisfies_extensionalEq_iff_eq he,
    memPairFormula_iff he, Project.Formula.satisfies_rename,
    Env.reindex_push_binaryUnderTwo, leastCandidateSlots_env]
  rfl

theorem least_witness_exists_d {M : SetTheory.Structure.{u}} (hM : M.Models theory)
    {n : Nat} (φ : Project.Delta0BinarySchema n) (env : Env M n)
    {order C x : M.Domain} (hOrder : InternalWellOrder M order C)
    (ht : ∃ y, M.mem y C ∧ Project.Formula.satisfies ((env.push x).push y) φ.body) :
    ∃ y, LeastWitness order C
      (fun x y => Project.Formula.satisfies ((env.push x).push y) φ.body) x y := by
  obtain ⟨S,hS⟩ := SetTheory.KP.separation_exists_d (models_weakKP hM) (fiberSchema φ) (env.push x) C
  obtain ⟨y,hy,hφ⟩ := ht
  have hne : ∃ y, M.mem y S := ⟨y,(hS y).mpr ⟨hy,hφ⟩⟩
  obtain ⟨z,hz,hmin⟩ := hOrder.least S (fun y hy => ((hS y).mp hy).1) hne
  exact ⟨z,((hS z).mp hz).1,((hS z).mp hz).2,
    fun y hy hφ => hmin y ((hS y).mpr ⟨hy,hφ⟩)⟩

theorem least_witness_unique {M : SetTheory.Structure.{u}} {order C x y z : M.Domain}
    (hOrder : InternalWellOrder M order C) {P : M.Domain → M.Domain → Prop}
    (hy : LeastWitness order C P x y) (hz : LeastWitness order C P x z) : y=z := by
  rcases hy.2.2 z hz.1 hz.2.1 with he | hyz
  · exact he
  · rcases hz.2.2 y hy.1 hy.2.1 with he | hzy
    · exact he.symm
    · exact False.elim (hOrder.irrefl y hy.1 (hOrder.trans y hy.1 z hz.1 y hy.1 hyz hzy))

/-- 得到模型内实际的单值、全定义选择图；其候选良序是明确输入。 -/
theorem least_choice_graph_d {M : SetTheory.Structure.{u}} (hM : M.Models theory)
    {n : Nat} (φ : Project.Delta0BinarySchema n) (env : Env M n)
    {A C order : M.Domain} (hOrder : InternalWellOrder M order C)
    (ht : ∀ x, M.mem x A → ∃ y, M.mem y C ∧
      Project.Formula.satisfies ((env.push x).push y) φ.body) :
    ∃ F, (∀ p, M.mem p F → ∃ x, M.mem x A ∧ ∃ y, M.mem y C ∧ Codes M p x y) ∧
      (∀ x, M.mem x A → ∃ y, M.mem y C ∧ MemPair M F x y) ∧
      (∀ x y z, MemPair M F x y → MemPair M F x z → y=z) ∧
      (∀ x y, MemPair M F x y → Project.Formula.satisfies ((env.push x).push y) φ.body) := by
  obtain ⟨F,hSupport,hF⟩ := relation_comprehension_d hM (leastSchema φ) ((env.push order).push C) A C
  have hspec (x y : M.Domain) : MemPair M F x y ↔ M.mem x A ∧ M.mem y C ∧
      LeastWitness order C (fun x y => Project.Formula.satisfies ((env.push x).push y) φ.body) x y := by
    simpa only [leastSchema_iff hM.1] using hF x y
  refine ⟨F,hSupport,?_,?_,?_⟩
  · intro x hx
    obtain ⟨y,hy⟩ := least_witness_exists_d hM φ env hOrder (ht x hx)
    exact ⟨y,hy.1,(hspec x y).mpr ⟨hx,hy.1,hy⟩⟩
  · intro x y z hy hz
    exact least_witness_unique hOrder ((hspec x y).mp hy).2.2 ((hspec x z).mp hz).2.2
  · intro x y hy
    exact ((hspec x y).mp hy).2.2.2.1

end KP1Y
