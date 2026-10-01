import KP1Y.ClosedEnvironments
import KP1Y.ClassStructures

/-! 一般集合公式对24参数可定义类的相对化；保留原变量并追加类定义参数。 -/
namespace KP1Y.Classes
open YesMetaZFC YesMetaZFC.SetTheory YesMetaZFC.SetTheory.Definitional
universe u

def frontIndex {n : Nat} (i : Fin n) : Fin (n+24) := ⟨i.val,by omega⟩

def tailIndex (n : Nat) (i : Fin 24) : Fin (n+24) := ⟨n+i.val,by omega⟩

def joinedEnv {M : SetTheory.Structure.{u}} {n : Nat} (s : Env M n) (params : Env M 24) : Env M (n+24) where
  bound i := if h : i.val<n then s.bound ⟨i.val,h⟩ else params.bound ⟨i.val-n,by omega⟩
  free := s.free

theorem joinedEnv_front {M : SetTheory.Structure.{u}} {n : Nat} (s : Env M n) (params : Env M 24) (i : Fin n) :
    (joinedEnv s params).bound (frontIndex i) = s.bound i := by
  simp [joinedEnv,frontIndex,i.isLt]

theorem joinedEnv_tail {M : SetTheory.Structure.{u}} {n : Nat} (s : Env M n) (params : Env M 24) (i : Fin 24) :
    (joinedEnv s params).bound (tailIndex n i) = params.bound i := by
  have hNot : ¬n+i.val<n := by omega
  simp [joinedEnv,tailIndex,hNot]

theorem joinedEnv_reindex_front {M : SetTheory.Structure.{u}} {n : Nat} (s : Env M n) (params : Env M 24) :
    (joinedEnv s params).reindex frontIndex = s := by
  rw [Env.mk.injEq]
  exact ⟨funext (joinedEnv_front s params),rfl⟩

theorem joinedEnv_push {M : SetTheory.Structure.{u}} {n : Nat} (s : Env M n) (params : Env M 24) (x : M.Domain) :
    joinedEnv (s.push x) params = (joinedEnv s params).push x := by
  rw [Env.mk.injEq]
  constructor
  · funext i
    refine Fin.cases ?_ (fun i => ?_) i
    · simp [joinedEnv,Env.push]
    · by_cases hi : i.val<n
      · simp [joinedEnv,Env.push,hi]
      · simp [joinedEnv,Env.push,hi]
  · rfl

def predicateSlots {n : Nat} : Fin 25 → Fin ((n+24)+1) :=
  Fin.cases 0 (fun i => (tailIndex n i).succ)

theorem predicateSlots_iff {M : SetTheory.Structure.{u}} {n : Nat} (χ : Project.UnarySchema 24)
    (s : Env M n) (params : Env M 24) (x : M.Domain) :
    Project.Formula.satisfies ((joinedEnv s params).push x) (χ.body.rename (predicateSlots (n := n))) ↔
      Project.Formula.satisfies (params.push x) χ.body := by
  rw [Project.Formula.satisfies_rename]
  apply KP1Y.formula_bound_congr χ.body χ.freeClosed
  intro i
  refine Fin.cases ?_ (fun i => ?_) i
  · rfl
  · exact joinedEnv_tail s params i

def relativize (χ : Project.UnarySchema 24) : {n : Nat} → Project.Formula 1 n → Project.Formula 1 (n+24)
  | _, .falsum => .falsum
  | _, .truth => .truth
  | _, .mem a b => .mem (a.rename frontIndex) (b.rename frontIndex)
  | _, .atom s hs args => .atom s hs (args.rename frontIndex)
  | _, .neg φ => .neg (relativize χ φ)
  | _, .conj φ ψ => .conj (relativize χ φ) (relativize χ ψ)
  | _, .disj φ ψ => .disj (relativize χ φ) (relativize χ ψ)
  | _, .imp φ ψ => .imp (relativize χ φ) (relativize χ ψ)
  | _, .iff φ ψ => .iff (relativize χ φ) (relativize χ ψ)
  | n, .forallE φ => .forallE (.imp (χ.body.rename (predicateSlots (n := n))) (relativize χ φ))
  | n, .existsE φ => .existsE (.conj (χ.body.rename (predicateSlots (n := n))) (relativize χ φ))

theorem relativize_freeClosed {n : Nat} (χ : Project.UnarySchema 24) (φ : Project.Formula 1 n) :
    (relativize χ φ).FreeClosed ↔ φ.FreeClosed := by
  induction φ with
  | falsum => simp [relativize,Definitional.Formula.FreeClosed]
  | truth => simp [relativize,Definitional.Formula.FreeClosed]
  | mem a b => simp [relativize,Definitional.Formula.FreeClosed]
  | atom s hs args => simp [relativize,Definitional.Formula.FreeClosed]
  | neg φ ih => simpa only [relativize,Definitional.Formula.FreeClosed] using ih
  | conj φ ψ ihφ ihψ => simp [relativize,Definitional.Formula.FreeClosed,ihφ,ihψ]
  | disj φ ψ ihφ ihψ => simp [relativize,Definitional.Formula.FreeClosed,ihφ,ihψ]
  | imp φ ψ ihφ ihψ => simp [relativize,Definitional.Formula.FreeClosed,ihφ,ihψ]
  | iff φ ψ ihφ ihψ => simp [relativize,Definitional.Formula.FreeClosed,ihφ,ihψ]
  | forallE φ ih => simp [relativize,Definitional.Formula.FreeClosed,χ.freeClosed,ih]
  | existsE φ ih => simp [relativize,Definitional.Formula.FreeClosed,χ.freeClosed,ih]

end KP1Y.Classes
