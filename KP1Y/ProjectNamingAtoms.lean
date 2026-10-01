import KP1Y.ProjectNamingSyntax
import KP1Y.ClassStructures

/-! 命名转换的环境、变量更新及三个集合原子的语义桥。 -/
namespace KP1Y.Named
open YesMetaZFC YesMetaZFC.SetTheory YesMetaZFC.SetTheory.Definitional
open KP1Y.Classes
universe u

def ValueMatch {M : SetTheory.Structure.{u}} {P : M.Domain → Prop} {hNe : ∃ x, P x} {n k : Nat}
    (ρ : Fin n → Fin k) (vals : Fin k → M.Domain) (s : Env (classModel M P hNe) n) : Prop :=
  ∀ i, vals (ρ i)=(s.bound i).val

theorem ValueMatch.term {M : SetTheory.Structure.{u}} {P : M.Domain → Prop} {hNe : ∃ x, P x} {n k : Nat}
    {ρ : Fin n → Fin k} {vals : Fin k → M.Domain} {s : Env (classModel M P hNe) n}
    (h : ValueMatch ρ vals s) (fallback : Fin k) (t : Project.Term n) (hClosed : t.freeSupport=[]) :
    vals (termIndex fallback ρ t)=(t.eval s).val := by
  cases t with
  | bound i => exact h i
  | free i => simp at hClosed

theorem ValueMatch.updated {M : SetTheory.Structure.{u}} {P : M.Domain → Prop} {hNe : ∃ x, P x} {n k : Nat}
    {ρ : Fin n → Fin k} {vals : Fin k → M.Domain} {s : Env (classModel M P hNe) n}
    (h : ValueMatch ρ vals s) (v : Fin k) (hFresh : ∀ i, ρ i≠v) (x : (classModel M P hNe).Domain) :
    ValueMatch (Fin.cases v ρ) (setValue vals v x.val) (s.push x) := by
  intro i
  refine Fin.cases ?_ (fun i => ?_) i
  · exact setValue_same vals v x.val
  · exact (setValue_other vals x.val (hFresh i)).trans (h i)

theorem termIndex_ne_fresh {n k : Nat} (fallback : Fin k) {ρ : Fin n → Fin k} {fresh : Nat}
    (hρ : ∀ i, (ρ i).val<fresh) (v : Fin k) (hv : v.val=fresh) (t : Project.Term n) (hClosed : t.freeSupport=[]) :
    termIndex fallback ρ t≠v := by
  intro he
  have hLt := termIndex_lt fallback ρ hρ t hClosed
  have hVal := congrArg Fin.val he
  omega

theorem encoded_member_iff {M : SetTheory.Structure.{u}} {A : M.Domain} {hNe : ∃ x, M.mem x A} {n k : Nat}
    (fallback : Fin k) (ρ : Fin n → Fin k) (vals : Fin k → M.Domain)
    (s : Env (classModel M (fun x => M.mem x A) hNe) n) (hMatch : ValueMatch ρ vals s)
    (a b : Project.Term n) (ha : a.freeSupport=[]) (hb : b.freeSupport=[]) :
    Holds M A vals (.member (termIndex fallback ρ a) (termIndex fallback ρ b)) ↔
      Project.Formula.satisfies s (.mem a b) := by
  rw [Project.Formula.satisfies_mem_iff]
  change M.mem (vals (termIndex fallback ρ a)) (vals (termIndex fallback ρ b)) ↔ M.mem (a.eval s).val (b.eval s).val
  rw [hMatch.term fallback a ha,hMatch.term fallback b hb]

theorem encoded_equality_iff {M : SetTheory.Structure.{u}} (he : Extensional M) {A : M.Domain}
    (hA : M.TransitiveSet A) {hNe : ∃ x, M.mem x A} {n k : Nat}
    (fallback : Fin k) (ρ : Fin n → Fin k) (vals : Fin k → M.Domain)
    (s : Env (classModel M (fun x => M.mem x A) hNe) n) (hMatch : ValueMatch ρ vals s)
    (args : TermVector 2 n) (hClosed : args.FreeClosed) (hs : Project.coreSignature.stage Project.CoreAtom.extensionalEq<1) :
    Holds M A vals (.equal (termIndex fallback ρ (args 0)) (termIndex fallback ρ (args 1))) ↔
      Project.Formula.satisfies s (.atom .extensionalEq hs args) := by
  rw [Project.Formula.satisfies_atom_extensionalEq_iff]
  change vals (termIndex fallback ρ (args 0))=vals (termIndex fallback ρ (args 1)) ↔ _
  rw [hMatch.term fallback (args 0) (hClosed 0),hMatch.term fallback (args 1) (hClosed 1)]
  constructor
  · intro hVal
    have hTerms : (args 0).eval s=(args 1).eval s := Subtype.ext hVal
    intro z
    rw [hTerms]
  · intro hSame
    exact congrArg Subtype.val ((class_extensional he hA).eq_of_same_members _ _ hSame)

theorem encoded_subset_iff {M : SetTheory.Structure.{u}} {A : M.Domain} {hNe : ∃ x, M.mem x A} {n k : Nat}
    (fallback : Fin k) (ρ : Fin n → Fin k) (vals : Fin k → M.Domain)
    (s : Env (classModel M (fun x => M.mem x A) hNe) n) (hMatch : ValueMatch ρ vals s)
    {fresh : Nat} (hρ : ∀ i, (ρ i).val<fresh) (v : Fin k) (hv : v.val=fresh)
    (args : TermVector 2 n) (hClosed : args.FreeClosed) (hs : Project.coreSignature.stage Project.CoreAtom.subset<1) :
    Holds M A vals (.all v (.imp (.member v (termIndex fallback ρ (args 0))) (.member v (termIndex fallback ρ (args 1))))) ↔
      Project.Formula.satisfies s (.atom .subset hs args) := by
  have hNe0 := termIndex_ne_fresh fallback hρ v hv (args 0) (hClosed 0)
  have hNe1 := termIndex_ne_fresh fallback hρ v hv (args 1) (hClosed 1)
  have hOld0 (x : M.Domain) := setValue_other vals x hNe0
  have hOld1 (x : M.Domain) := setValue_other vals x hNe1
  simp only [Holds,setValue_same,hOld0,hOld1,hMatch.term fallback (args 0) (hClosed 0),
    hMatch.term fallback (args 1) (hClosed 1),Project.Formula.satisfies_atom_subset_iff]
  constructor
  · intro h z hz
    exact h z.val z.property hz
  · intro h x hx hx0
    exact h ⟨x,hx⟩ hx0

end KP1Y.Named
