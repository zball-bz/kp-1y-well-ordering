import KP1Y.Kuratowski
import KP1Y.FunctionalImage

/-! 在 KPω 内构造笛卡尔积，只使用两次全定义 Δ₀ 像集和并集。 -/
namespace KP1Y.Kuratowski
open YesMetaZFC YesMetaZFC.SetTheory YesMetaZFC.SetTheory.Definitional
universe u

def pairSchema : Project.Delta0BinarySchema 1 where
  body := codeFormula (.bound 0) (.bound 2) (.bound 1)
  freeClosed := convention.freeClosed_code _ _ _ rfl rfl rfl
  delta0 := codeFormula_delta0 _ _ _

def oneEnv {M : SetTheory.Structure.{u}} (x : M.Domain) : Env M 1 :=
  ⟨fun _ => x, fun _ => x⟩

theorem pairSchema_iff {M : SetTheory.Structure.{u}} (he : Extensional M)
    (x y p : M.Domain) :
    Project.Formula.satisfies (((oneEnv x).push y).push p) pairSchema.body ↔ Codes M p x y := by
  rw [pairSchema, codeFormula_iff he]
  rfl

theorem row_exists {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    (x Y : M.Domain) : ∃ row, ∀ p, M.mem p row ↔ ∃ y, M.mem y Y ∧ Codes M p x y := by
  obtain ⟨row,hrow⟩ := KP1Y.functional_image_d hM pairSchema (oneEnv x) Y
    (fun y _ => by
      obtain ⟨p,hp⟩ := codes_total hM x y
      exact ⟨p,(pairSchema_iff hM.1 x y p).mpr hp⟩)
    (fun y _ p q hp hq => codes_unique hM.1
      ((pairSchema_iff hM.1 x y p).mp hp) ((pairSchema_iff hM.1 x y q).mp hq))
  exact ⟨row, fun p => (hrow p).trans (by simp only [pairSchema_iff hM.1])⟩

/-- 既覆盖 Y 中全部坐标，也排除错误成员；所有量词都有集合界。 -/
def rowFormula {n : Nat} (row x Y : Project.Term n) : Project.Formula 1 n :=
  .conj
    (Project.Formula.forallMem row (Project.Formula.existsMem Y.weaken
      (codeFormula (.bound 1) x.weaken.weaken (.bound 0))))
    (Project.Formula.forallMem Y (Project.Formula.existsMem row.weaken
      (codeFormula (.bound 0) x.weaken.weaken (.bound 1))))

theorem rowFormula_delta0 {n : Nat} (row x Y : Project.Term n) :
    (rowFormula row x Y).IsDelta0 :=
  .conj (.forallMem _ (.existsMem _ (codeFormula_delta0 _ _ _)))
    (.forallMem _ (.existsMem _ (codeFormula_delta0 _ _ _)))

theorem rowFormula_iff {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {n : Nat} (env : Env M n) (row x Y : Project.Term n) :
    Project.Formula.satisfies env (rowFormula row x Y) ↔
      ∀ p, M.mem p (row.eval env) ↔ ∃ y, M.mem y (Y.eval env) ∧ Codes M p (x.eval env) y := by
  simp only [rowFormula, Project.Formula.satisfies_conj_iff,
    Project.Formula.satisfies_forallMem_iff, Project.Formula.satisfies_existsMem_iff,
    codeFormula_iff hM.1, Definitional.Term.eval_weaken]
  change ((∀ p, M.mem p (row.eval env) → ∃ y, M.mem y (Y.eval env) ∧ Codes M p (x.eval env) y) ∧
      (∀ y, M.mem y (Y.eval env) → ∃ p, M.mem p (row.eval env) ∧ Codes M p (x.eval env) y)) ↔ _
  constructor
  · rintro ⟨hf,hg⟩ p
    refine ⟨hf p, ?_⟩
    rintro ⟨y,hy,hp⟩
    obtain ⟨q,hq,hcode⟩ := hg y hy
    have he := codes_unique hM.1 hp hcode
    exact he ▸ hq
  · intro h
    refine ⟨fun p hp => (h p).mp hp, ?_⟩
    intro y hy
    obtain ⟨p,hp⟩ := codes_total hM (x.eval env) y
    exact ⟨p,(h p).mpr ⟨y,hy,hp⟩,hp⟩

def rowSchema : Project.Delta0BinarySchema 1 where
  body := rowFormula (.bound 0) (.bound 1) (.bound 2)
  freeClosed := by
    simp [rowFormula, codeFormula, pairFormula, Project.Formula.forallMem,
      Project.Formula.existsMem, Definitional.Formula.FreeClosed]
  delta0 := rowFormula_delta0 _ _ _

theorem rowSchema_iff {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    (Y x row : M.Domain) :
    Project.Formula.satisfies (((oneEnv Y).push x).push row) rowSchema.body ↔
      ∀ p, M.mem p row ↔ ∃ y, M.mem y Y ∧ Codes M p x y := by
  rw [rowSchema, rowFormula_iff hM]
  rfl

def IsProduct (M : SetTheory.Structure.{u}) (P X Y : M.Domain) : Prop :=
  ∀ p, M.mem p P ↔ ∃ x, M.mem x X ∧ ∃ y, M.mem y Y ∧ Codes M p x y

theorem product_exists {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    (X Y : M.Domain) : ∃ P, IsProduct M P X Y := by
  obtain ⟨rows,hr⟩ := KP1Y.functional_image_d hM rowSchema (oneEnv Y) X
    (fun x _ => by
      obtain ⟨row,hrow⟩ := row_exists hM x Y
      exact ⟨row,(rowSchema_iff hM Y x row).mpr hrow⟩)
    (fun x _ r s hr hs => hM.1.eq_of_same_members r s (fun p =>
      ((rowSchema_iff hM Y x r).mp hr p).trans ((rowSchema_iff hM Y x s).mp hs p).symm))
  obtain ⟨P,hP⟩ := SetTheory.KP.exists_union (KP1Y.models_weakKP hM) rows
  refine ⟨P, ?_⟩
  intro p
  constructor
  · intro hp
    obtain ⟨row,hrow,hpr⟩ := (hP p).mp hp
    obtain ⟨x,hx,hxrow⟩ := (hr row).mp hrow
    obtain ⟨y,hy,hcode⟩ := ((rowSchema_iff hM Y x row).mp hxrow p).mp hpr
    exact ⟨x,hx,y,hy,hcode⟩
  · rintro ⟨x,hx,y,hy,hcode⟩
    obtain ⟨row,hrow⟩ := row_exists hM x Y
    have hrmem := (hr row).mpr ⟨x,hx,(rowSchema_iff hM Y x row).mpr hrow⟩
    exact (hP p).mpr ⟨row,hrmem,(hrow p).mpr ⟨y,hy,hcode⟩⟩

def productSentence : Project.Sentence :=
  Project.Sentence.ofFormula
    (.forallE (.forallE (.existsE (.forallE
      (.iff (.mem (.bound 0) (.bound 1))
        (Project.Formula.existsMem (.bound 3) (Project.Formula.existsMem (.bound 3)
          (codeFormula (.bound 2) (.bound 1) (.bound 0))))))))) (by
    simp [codeFormula, pairFormula, Project.Formula.forallMem, Project.Formula.existsMem,
      Definitional.Formula.FreeClosed])

/-- 笛卡尔积存在性的纯 ∈ 对象 KPω 推导。 -/
theorem product_derivable : KP1Y.Derives productSentence := by
  apply KP1Y.derives_of_all_models
  intro M hM free
  change Project.Formula.satisfies ({bound := Fin.elim0, free := free} : Env M 0)
    productSentence.formula
  simp only [productSentence, Project.Sentence.ofFormula,
    Project.Formula.satisfies_forall_iff, Project.Formula.satisfies_exists_iff,
    Project.Formula.satisfies_iff_iff, Project.Formula.satisfies_mem_iff,
    Project.Formula.satisfies_existsMem_iff, codeFormula_iff hM.1]
  change ∀ X Y, ∃ P, IsProduct M P X Y
  exact product_exists hM

end KP1Y.Kuratowski
