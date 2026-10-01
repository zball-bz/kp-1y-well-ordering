import KP1Y.FunctionGraphs

/-! 普通有限公式编译的源语言：固定有限变量名，量词覆盖指定名字。实际代码仍由后续KP构造给出。 -/
namespace KP1Y.Named
open YesMetaZFC YesMetaZFC.SetTheory
universe u v

inductive Formula (k : Nat) where
  | equal : Fin k → Fin k → Formula k
  | member : Fin k → Fin k → Formula k
  | neg : Formula k → Formula k
  | imp : Formula k → Formula k → Formula k
  | all : Fin k → Formula k → Formula k

def setValue {k : Nat} {α : Type v} (vals : Fin k → α) (i : Fin k) (x : α) : Fin k → α :=
  fun j => if j=i then x else vals j

theorem setValue_same {k : Nat} {α : Type v} (vals : Fin k → α) (i : Fin k) (x : α) : setValue vals i x i=x := by
  simp [setValue]

theorem setValue_other {k : Nat} {α : Type v} (vals : Fin k → α) {i j : Fin k} (x : α) (h : j≠i) :
    setValue vals i x j=vals j := by simp [setValue,h]

def Holds {k : Nat} (M : SetTheory.Structure.{u}) (A : M.Domain) (vals : Fin k → M.Domain) : Formula k → Prop
  | .equal i j => vals i=vals j
  | .member i j => M.mem (vals i) (vals j)
  | .neg φ => ¬Holds M A vals φ
  | .imp φ ψ => Holds M A vals φ → Holds M A vals ψ
  | .all i φ => ∀ x, M.mem x A → Holds M A (setValue vals i x) φ

def Formula.truth {k : Nat} (i : Fin k) : Formula k := .equal i i
def Formula.falsum {k : Nat} (i : Fin k) : Formula k := .neg (.truth i)
def Formula.conj {k : Nat} (φ ψ : Formula k) : Formula k := .neg (.imp φ (.neg ψ))
def Formula.disj {k : Nat} (φ ψ : Formula k) : Formula k := .imp (.neg φ) ψ
def Formula.iff {k : Nat} (φ ψ : Formula k) : Formula k := .conj (.imp φ ψ) (.imp ψ φ)
def Formula.exists {k : Nat} (i : Fin k) (φ : Formula k) : Formula k := .neg (.all i (.neg φ))

theorem holds_truth {M : SetTheory.Structure.{u}} {k : Nat} (A : M.Domain) (vals : Fin k → M.Domain) (i : Fin k) :
    Holds M A vals (.truth i) := rfl

theorem not_holds_falsum {M : SetTheory.Structure.{u}} {k : Nat} (A : M.Domain) (vals : Fin k → M.Domain) (i : Fin k) :
    ¬Holds M A vals (.falsum i) := fun h => h rfl

theorem holds_conj_iff {M : SetTheory.Structure.{u}} {k : Nat} (A : M.Domain) (vals : Fin k → M.Domain) (φ ψ : Formula k) :
    Holds M A vals (.conj φ ψ) ↔ Holds M A vals φ ∧ Holds M A vals ψ := by
  classical
  constructor
  · intro h
    exact ⟨Classical.byContradiction (fun hn => h (fun hp => False.elim (hn hp))),
      Classical.byContradiction (fun hn => h (fun _ => hn))⟩
  · rintro ⟨hφ,hψ⟩ h
    exact h hφ hψ

theorem holds_disj_iff {M : SetTheory.Structure.{u}} {k : Nat} (A : M.Domain) (vals : Fin k → M.Domain) (φ ψ : Formula k) :
    Holds M A vals (.disj φ ψ) ↔ Holds M A vals φ ∨ Holds M A vals ψ := by
  classical
  constructor
  · intro h
    by_cases hp : Holds M A vals φ
    · exact Or.inl hp
    · exact Or.inr (h hp)
  · rintro (hφ | hψ) hn
    · exact False.elim (hn hφ)
    · exact hψ

theorem holds_iff_iff {M : SetTheory.Structure.{u}} {k : Nat} (A : M.Domain) (vals : Fin k → M.Domain) (φ ψ : Formula k) :
    Holds M A vals (.iff φ ψ) ↔ (Holds M A vals φ ↔ Holds M A vals ψ) := by
  rw [Formula.iff,holds_conj_iff]
  exact ⟨fun h => ⟨h.1,h.2⟩,fun h => ⟨h.mp,h.mpr⟩⟩

theorem holds_exists_iff {M : SetTheory.Structure.{u}} {k : Nat} (A : M.Domain) (vals : Fin k → M.Domain)
    (i : Fin k) (φ : Formula k) :
    Holds M A vals (.exists i φ) ↔ ∃ x, M.mem x A ∧ Holds M A (setValue vals i x) φ := by
  classical
  constructor
  · intro h
    apply Classical.byContradiction
    intro hNone
    exact h (fun x hx hφ => hNone ⟨x,hx,hφ⟩)
  · rintro ⟨x,hx,hφ⟩ hAll
    exact hAll x hx hφ

end KP1Y.Named
