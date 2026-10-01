import KP1Y.Product

/-! 给定实际集合界后，在 KPω 内用 Δ₀ 分离形成关系表。 -/
namespace KP1Y.Kuratowski
open YesMetaZFC YesMetaZFC.SetTheory YesMetaZFC.SetTheory.Definitional
universe u

def MemPair (M : SetTheory.Structure.{u}) (R x y : M.Domain) : Prop :=
  ∃ p, M.mem p R ∧ Codes M p x y

def memPairFormula {n : Nat} (R x y : Project.Term n) : Project.Formula 1 n :=
  Project.Formula.existsMem R (codeFormula (.bound 0) x.weaken y.weaken)

theorem memPairFormula_delta0 {n : Nat} (R x y : Project.Term n) :
    (memPairFormula R x y).IsDelta0 := .existsMem _ (codeFormula_delta0 _ _ _)

theorem memPairFormula_iff {M : SetTheory.Structure.{u}} (he : Extensional M)
    {n : Nat} (env : Env M n) (R x y : Project.Term n) :
    Project.Formula.satisfies env (memPairFormula R x y) ↔
      MemPair M (R.eval env) (x.eval env) (y.eval env) := by
  simp only [memPairFormula, Project.Formula.satisfies_existsMem_iff,
    codeFormula_iff he, Definitional.Term.eval_weaken]
  rfl

def graphSlots {n : Nat} : Fin (n+2) → Fin (n+5) :=
  Fin.cases 0 (Fin.cases 1 (fun i => ⟨i.val+5, by omega⟩))

def graphMember {n : Nat} (φ : Project.Delta0BinarySchema n) :
    Project.Delta0UnarySchema (n+2) where
  body := Project.Formula.existsMem (.bound 2)
    (Project.Formula.existsMem (.bound 2)
      (.conj (codeFormula (.bound 2) (.bound 1) (.bound 0))
        (φ.body.rename graphSlots)))
  freeClosed := by
    simp [Project.Formula.existsMem, codeFormula, pairFormula, Project.Formula.forallMem,
      Definitional.Formula.FreeClosed, φ.freeClosed]
  delta0 := .existsMem _ (.existsMem _
    (.conj (codeFormula_delta0 _ _ _) (KP1Y.delta0_rename φ.delta0 graphSlots)))

private theorem graphSlots_env {M : SetTheory.Structure.{u}} {n : Nat}
    (env : Env M n) (I J p x y : M.Domain) :
    (((((env.push I).push J).push p).push x).push y).reindex graphSlots =
      (env.push x).push y := by
  rw [Env.mk.injEq]
  constructor
  · funext i
    refine Fin.cases ?_ (fun i => ?_) i
    · rfl
    · refine Fin.cases ?_ (fun i => ?_) i <;> rfl
  · rfl

theorem graphMember_iff {M : SetTheory.Structure.{u}} (he : Extensional M) {n : Nat}
    (φ : Project.Delta0BinarySchema n) (env : Env M n) (I J p : M.Domain) :
    Project.Formula.satisfies (((env.push I).push J).push p) (graphMember φ).body ↔
      ∃ x, M.mem x I ∧ ∃ y, M.mem y J ∧ Codes M p x y ∧
        Project.Formula.satisfies ((env.push x).push y) φ.body := by
  simp only [graphMember, Project.Formula.satisfies_existsMem_iff,
    Project.Formula.satisfies_conj_iff, codeFormula_iff he,
    Project.Formula.satisfies_rename, graphSlots_env]
  rfl

/-- 关系的每个成员均为界内有序对，并精确识别被指定的 Δ₀ 关系。 -/
theorem relation_comprehension_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {n : Nat} (φ : Project.Delta0BinarySchema n) (env : Env M n) (I J : M.Domain) :
    ∃ R, (∀ p, M.mem p R → ∃ x, M.mem x I ∧ ∃ y, M.mem y J ∧ Codes M p x y) ∧
      ∀ x y, MemPair M R x y ↔ M.mem x I ∧ M.mem y J ∧
        Project.Formula.satisfies ((env.push x).push y) φ.body := by
  obtain ⟨P,hP⟩ := product_exists hM I J
  obtain ⟨R,hR⟩ := SetTheory.KP.separation_exists_d (KP1Y.models_weakKP hM)
    (graphMember φ) ((env.push I).push J) P
  have hc (p : M.Domain) : M.mem p R ↔ ∃ x, M.mem x I ∧ ∃ y, M.mem y J ∧
      Codes M p x y ∧ Project.Formula.satisfies ((env.push x).push y) φ.body := by
    rw [hR p, graphMember_iff hM.1]
    constructor
    · exact And.right
    · rintro ⟨x,hx,y,hy,hcode,hφ⟩
      exact ⟨(hP p).mpr ⟨x,hx,y,hy,hcode⟩,x,hx,y,hy,hcode,hφ⟩
  refine ⟨R, ?_, ?_⟩
  · intro p hp
    obtain ⟨x,hx,y,hy,hcode,_⟩ := (hc p).mp hp
    exact ⟨x,hx,y,hy,hcode⟩
  · intro x y
    constructor
    · rintro ⟨p,hp,hcode⟩
      obtain ⟨a,ha,b,hb,hcode',hφ⟩ := (hc p).mp hp
      obtain ⟨hxa,hyb⟩ := codes_injective hM.1 hcode hcode'
      cases hxa
      cases hyb
      exact ⟨ha,hb,hφ⟩
    · rintro ⟨hx,hy,hφ⟩
      obtain ⟨p,hcode⟩ := codes_total hM x y
      exact ⟨p,(hc p).mpr ⟨x,hx,y,hy,hcode,hφ⟩,hcode⟩

end KP1Y.Kuratowski
