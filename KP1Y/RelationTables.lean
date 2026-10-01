import KP1Y.RelationComprehension

/-! 集合关系图及笛卡尔积的字面有界验证与外延唯一性。 -/
namespace KP1Y.Kuratowski
open YesMetaZFC YesMetaZFC.SetTheory YesMetaZFC.SetTheory.Definitional
universe u

def RelationSupport (M : SetTheory.Structure.{u}) (R X Y : M.Domain) : Prop :=
  ∀ p, M.mem p R → ∃ x, M.mem x X ∧ ∃ y, M.mem y Y ∧ Codes M p x y

def relationSupportFormula {n : Nat} (R X Y : Project.Term n) : Project.Formula 1 n :=
  Project.Formula.forallMem R (Project.Formula.existsMem X.weaken
    (Project.Formula.existsMem Y.weaken.weaken (codeFormula (.bound 2) (.bound 1) (.bound 0))))

theorem relationSupportFormula_delta0 {n : Nat} (R X Y : Project.Term n) :
    (relationSupportFormula R X Y).IsDelta0 := .forallMem _ (.existsMem _ (.existsMem _ (codeFormula_delta0 _ _ _)))

theorem relationSupportFormula_iff {M : SetTheory.Structure.{u}} (he : Extensional M) {n : Nat}
    (env : Env M n) (R X Y : Project.Term n) :
    Project.Formula.satisfies env (relationSupportFormula R X Y) ↔
      RelationSupport M (R.eval env) (X.eval env) (Y.eval env) := by
  simp only [relationSupportFormula,Project.Formula.satisfies_forallMem_iff,
    Project.Formula.satisfies_existsMem_iff,codeFormula_iff he,Definitional.Term.eval_weaken]
  rfl

theorem RelationSupport.bounds {M : SetTheory.Structure.{u}} (he : Extensional M) {R X Y x y : M.Domain}
    (h : RelationSupport M R X Y) (hAt : MemPair M R x y) : M.mem x X ∧ M.mem y Y := by
  obtain ⟨p,hp,hCode⟩ := hAt
  obtain ⟨x',hx,y',hy,hCode'⟩ := h p hp
  obtain ⟨hxx',hyy'⟩ := codes_injective he hCode hCode'
  subst x'
  subst y'
  exact ⟨hx,hy⟩

theorem relation_ext {M : SetTheory.Structure.{u}} (he : Extensional M) {R S X Y X' Y' : M.Domain}
    (hR : RelationSupport M R X Y) (hS : RelationSupport M S X' Y')
    (hRows : ∀ x y, MemPair M R x y ↔ MemPair M S x y) : R=S := by
  apply he.eq_of_same_members
  intro p
  constructor
  · intro hp
    obtain ⟨x,_,y,_,hCode⟩ := hR p hp
    obtain ⟨q,hq,hCode'⟩ := (hRows x y).mp ⟨p,hp,hCode⟩
    exact (codes_unique he hCode hCode') ▸ hq
  · intro hp
    obtain ⟨x,_,y,_,hCode⟩ := hS p hp
    obtain ⟨q,hq,hCode'⟩ := (hRows x y).mpr ⟨p,hp,hCode⟩
    exact (codes_unique he hCode hCode') ▸ hq

def productBoundedFormula {n : Nat} (P X Y : Project.Term n) : Project.Formula 1 n :=
  .conj (relationSupportFormula P X Y)
    (Project.Formula.forallMem X (Project.Formula.forallMem Y.weaken
      (memPairFormula P.weaken.weaken (.bound 1) (.bound 0))))

theorem productBoundedFormula_delta0 {n : Nat} (P X Y : Project.Term n) :
    (productBoundedFormula P X Y).IsDelta0 :=
  .conj (relationSupportFormula_delta0 _ _ _) (.forallMem _ (.forallMem _ (memPairFormula_delta0 _ _ _)))

theorem productBoundedFormula_iff {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory) {n : Nat}
    (env : Env M n) (P X Y : Project.Term n) :
    Project.Formula.satisfies env (productBoundedFormula P X Y) ↔
      IsProduct M (P.eval env) (X.eval env) (Y.eval env) := by
  simp only [productBoundedFormula,Project.Formula.satisfies_conj_iff,relationSupportFormula_iff hM.1,
    Project.Formula.satisfies_forallMem_iff,memPairFormula_iff hM.1,Definitional.Term.eval_weaken]
  constructor
  · rintro ⟨hSupport,hRows⟩ p
    refine ⟨hSupport p,?_⟩
    rintro ⟨x,hx,y,hy,hCode⟩
    obtain ⟨q,hq,hCode'⟩ := hRows x hx y hy
    exact (codes_unique hM.1 hCode hCode') ▸ hq
  · intro h
    refine ⟨fun p hp => (h p).mp hp,?_⟩
    intro x hx y hy
    obtain ⟨p,hCode⟩ := codes_total hM x y
    exact ⟨p,(h p).mpr ⟨x,hx,y,hy,hCode⟩,hCode⟩

end KP1Y.Kuratowski
