import KP1Y.NamedFormula
import KP1Y.AssignmentUpdate

/-! 有限源变量的值由实际对象赋值图读取，命名必须单射；更新保持其他名字。 -/
namespace KP1Y.Named
open YesMetaZFC YesMetaZFC.SetTheory
open KP1Y.Kuratowski KP1Y.Functions KP1Y.Assignments
universe u

def Reads {k : Nat} (M : SetTheory.Structure.{u}) (s : M.Domain) (names vals : Fin k → M.Domain) : Prop :=
  ∀ i, MemPair M s (names i) (vals i)

def InjectiveNames {k : Nat} {α : Type u} (names : Fin k → α) : Prop :=
  ∀ i j, names i=names j → i=j

theorem Reads.range {M : SetTheory.Structure.{u}} (he : Extensional M) {k : Nat}
    {s bound A : M.Domain} {names vals : Fin k → M.Domain} (hS : Graph M s bound A) (hR : Reads M s names vals) :
    ∀ i, M.mem (vals i) A := fun i => (hS.bounds he (hR i)).2

theorem Reads.unique {M : SetTheory.Structure.{u}} {k : Nat} {s bound A : M.Domain}
    {names vals vals' : Fin k → M.Domain} (hS : Graph M s bound A) (hR : Reads M s names vals) (hR' : Reads M s names vals') :
    vals=vals' := by
  funext i
  exact hS.unique (names i) (vals i) (vals' i) (hR i) (hR' i)

theorem reads_updated {M : SetTheory.Structure.{u}} (he : Extensional M) {k : Nat}
    {s t bound A x : M.Domain} {names vals : Fin k → M.Domain}
    (hNames : ∀ i, M.mem (names i) bound) (hInj : InjectiveNames names) (hS : Graph M s bound A)
    (hR : Reads M s names vals) (v : Fin k) (hx : M.mem x A) (hU : Updated M t s bound A (names v) x) :
    Reads M t names (setValue vals v x) := by
  intro i
  by_cases hi : i=v
  · subst i
    rw [setValue_same]
    exact (hU.rows (names v) (hNames v) x hx).mpr (Or.inl ⟨rfl,rfl⟩)
  · rw [setValue_other vals x hi]
    have hNamesNe : names i≠names v := fun heq => hi (hInj i v heq)
    exact (hU.rows (names i) (hNames i) (vals i) (hR.range he hS i)).mpr (Or.inr ⟨hNamesNe,hR i⟩)

end KP1Y.Named
