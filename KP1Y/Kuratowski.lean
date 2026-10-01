import KP1Y.BoundedSyntax
import KP1Y.Model

/-! KPω 中的有界 Kuratowski 编码；不给配对存在性另加公理。 -/
namespace KP1Y.Kuratowski
open YesMetaZFC YesMetaZFC.SetTheory YesMetaZFC.SetTheory.Definitional
universe u

def PairSet (M : SetTheory.Structure.{u}) (p x y : M.Domain) : Prop :=
  ∀ z, M.mem z p ↔ z = x ∨ z = y

def pairFormula {n : Nat} (p x y : Project.Term n) : Project.Formula 1 n :=
  .conj (.mem x p) (.conj (.mem y p)
    (Project.Formula.forallMem p (.disj
      (Project.Formula.extensionalEq (.bound 0) x.weaken)
      (Project.Formula.extensionalEq (.bound 0) y.weaken))))

theorem pairFormula_delta0 {n : Nat} (p x y : Project.Term n) :
    (pairFormula p x y).IsDelta0 :=
  .conj (.mem _ _) (.conj (.mem _ _) (.forallMem _ (.disj (.atom _ _ _) (.atom _ _ _))))

theorem pairFormula_iff {M : SetTheory.Structure.{u}} (hM : Extensional M)
    {n : Nat} (env : Env M n) (p x y : Project.Term n) :
    Project.Formula.satisfies env (pairFormula p x y) ↔
      PairSet M (p.eval env) (x.eval env) (y.eval env) := by
  simp only [pairFormula, Project.Formula.satisfies_conj_iff,
    Project.Formula.satisfies_mem_iff, Project.Formula.satisfies_forallMem_iff,
    Project.Formula.satisfies_disj_iff, Project.Formula.satisfies_extensionalEq_iff_eq hM,
    Definitional.Term.eval_weaken]
  change (_ ∧ _ ∧ ∀ z, M.mem z (p.eval env) → z = x.eval env ∨ z = y.eval env) ↔ _
  constructor
  · rintro ⟨hx,hy,h⟩ z
    exact ⟨h z, fun hz => hz.elim (fun he => he ▸ hx) (fun he => he ▸ hy)⟩
  · intro h
    exact ⟨(h _).mpr (Or.inl rfl),(h _).mpr (Or.inr rfl),fun z hz => (h z).mp hz⟩

theorem PairSet.unique {M : SetTheory.Structure.{u}} (he : Extensional M)
    {p q x y : M.Domain} (hp : PairSet M p x y) (hq : PairSet M q x y) : p = q :=
  he.eq_of_same_members p q (fun z => (hp z).trans (hq z).symm)

theorem PairSet.second_unique {M : SetTheory.Structure.{u}} {p x y z : M.Domain}
    (hp : PairSet M p x y) (hq : PairSet M p x z) : y = z := by
  rcases (hq y).mp ((hp y).mpr (Or.inr rfl)) with hy | hy
  · rcases (hp z).mp ((hq z).mpr (Or.inr rfl)) with hz | hz
    · exact hy.trans hz.symm
    · exact hz.symm
  · exact hy

def Codes (M : SetTheory.Structure.{u}) (p x y : M.Domain) : Prop :=
  ∃ a b, PairSet M a x x ∧ PairSet M b x y ∧ PairSet M p a b

def codeFormula {n : Nat} (p x y : Project.Term n) : Project.Formula 1 n :=
  Project.Formula.existsMem p (Project.Formula.existsMem p.weaken
    (.conj (pairFormula (.bound 1) x.weaken.weaken x.weaken.weaken)
      (.conj (pairFormula (.bound 0) x.weaken.weaken y.weaken.weaken)
        (pairFormula p.weaken.weaken (.bound 1) (.bound 0)))))

theorem codeFormula_delta0 {n : Nat} (p x y : Project.Term n) :
    (codeFormula p x y).IsDelta0 :=
  .existsMem _ (.existsMem _ (.conj (pairFormula_delta0 _ _ _)
    (.conj (pairFormula_delta0 _ _ _) (pairFormula_delta0 _ _ _))))

theorem codeFormula_iff {M : SetTheory.Structure.{u}} (he : Extensional M)
    {n : Nat} (env : Env M n) (p x y : Project.Term n) :
    Project.Formula.satisfies env (codeFormula p x y) ↔
      Codes M (p.eval env) (x.eval env) (y.eval env) := by
  simp only [codeFormula, Project.Formula.satisfies_existsMem_iff,
    Project.Formula.satisfies_conj_iff, pairFormula_iff he,
    Definitional.Term.eval_weaken]
  change (∃ a, M.mem a (p.eval env) ∧ ∃ b, M.mem b (p.eval env) ∧
    PairSet M a (x.eval env) (x.eval env) ∧ PairSet M b (x.eval env) (y.eval env) ∧
      PairSet M (p.eval env) a b) ↔ _
  constructor
  · rintro ⟨a,_,b,_,ha,hb,hp⟩
    exact ⟨a,b,ha,hb,hp⟩
  · rintro ⟨a,b,ha,hb,hp⟩
    exact ⟨a,(hp a).mpr (Or.inl rfl),b,(hp b).mpr (Or.inr rfl),ha,hb,hp⟩

theorem codes_total {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    (x y : M.Domain) : ∃ p, Codes M p x y := by
  have hw := KP1Y.models_weakKP hM
  obtain ⟨a,ha⟩ := SetTheory.KP.exists_pair hw x x
  obtain ⟨b,hb⟩ := SetTheory.KP.exists_pair hw x y
  obtain ⟨p,hp⟩ := SetTheory.KP.exists_pair hw a b
  exact ⟨p,a,b,ha,hb,hp⟩

theorem codes_unique {M : SetTheory.Structure.{u}} (he : Extensional M)
    {p q x y : M.Domain} (hp : Codes M p x y) (hq : Codes M q x y) : p = q := by
  obtain ⟨a,b,ha,hb,hp⟩ := hp
  obtain ⟨c,d,hc,hd,hq⟩ := hq
  have hac := ha.unique he hc
  have hbd := hb.unique he hd
  cases hac
  cases hbd
  exact hp.unique he hq

theorem codes_injective {M : SetTheory.Structure.{u}} (he : Extensional M)
    {p x y x' y' : M.Domain} (h : Codes M p x y) (h' : Codes M p x' y') :
    x = x' ∧ y = y' := by
  obtain ⟨a,b,ha,hb,hp⟩ := h
  obtain ⟨a',b',ha',hb',hp'⟩ := h'
  have hx'a : M.mem x' a := by
    rcases (hp' a).mp ((hp a).mpr (Or.inl rfl)) with h | h
    · rw [h]
      exact (ha' x').mpr (Or.inl rfl)
    · rw [h]
      exact (hb' x').mpr (Or.inl rfl)
  have hxx' : x = x' := ((ha x').mp hx'a).elim Eq.symm Eq.symm
  cases hxx'
  have haa' := ha.unique he ha'
  cases haa'
  have hbb' := hp.second_unique hp'
  cases hbb'
  exact ⟨rfl,hb.second_unique hb'⟩

def convention : Project.OrderedPairConvention where
  code := codeFormula
  freeClosed_code := by
    intro n p x y hp hx hy
    simp [codeFormula, pairFormula, Project.Formula.existsMem, Project.Formula.forallMem,
      Definitional.Formula.FreeClosed, hp, hx, hy]

def interpretation {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory) :
    convention.Interpretation M where
  Codes := Codes M
  realizes := codeFormula_iff hM.1
  total := codes_total hM
  unique := codes_unique hM.1
  injective := codes_injective hM.1

end KP1Y.Kuratowski
