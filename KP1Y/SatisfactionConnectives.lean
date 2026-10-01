import KP1Y.SatisfactionRecursion
import KP1Y.SatisfactionSpaces

/-! 对实际程序节点消去其他操作码，得到原子、否定和蕴涵的解释方程。 -/
namespace KP1Y.Satisfaction
open YesMetaZFC YesMetaZFC.SetTheory
open KP1Y.Kuratowski KP1Y.Functions
universe u

def Clauses (M : SetTheory.Structure.{u}) (C : Context M.Domain) (p s i c H : M.Domain) : Prop :=
  AtomicCase M C p s i ∨ NegationCase M C p i c H ∨
    ImplicationCase M C p i c H ∨ UniversalCase M C p s i H

theorem instruction_fields {M : SetTheory.Structure.{u}} (he : Extensional M)
    {C : Context M.Domain} (hC : ContextSpaces M C) {p i op x y : M.Domain}
    (h : InstructionAt M C.instructions C.pairs p i op x y) :
    M.mem x C.operands ∧ M.mem y C.operands := by
  obtain ⟨_,_,args,hArgs,_,_,hCode⟩ := h
  obtain ⟨x',hx,y',hy,hCode'⟩ := (hC.pairs args).mp hArgs
  obtain ⟨hxx',hyy'⟩ := codes_injective he hCode hCode'
  subst x'
  subst y'
  exact ⟨hx,hy⟩

theorem evalStep_column_iff {M : SetTheory.Structure.{u}} (he : Extensional M)
    {C : Context M.Domain} {p s i c H : M.Domain}
    (hp : M.mem p C.programs) (hs : M.mem s C.assignments) (hCode : Codes M c p s) :
    EvalStep M C i c H ↔ Clauses M C p s i c H := by
  constructor
  · rintro ⟨p',_,s',_,hCode',hCases⟩
    obtain ⟨hpp',hss'⟩ := codes_injective he hCode hCode'
    subst p'
    subst s'
    exact hCases
  · exact fun h => ⟨p,hp,s,hs,hCode,h⟩

theorem evaluation_node {M : SetTheory.Structure.{u}} (he : Extensional M)
    {C : Context M.Domain} (hC : ContextSpaces M C) {p s i c H : M.Domain}
    (hH : Evaluation M C H) (hp : M.mem p C.programs) (hs : M.mem s C.assignments)
    (hi : M.mem i C.omega) (hCode : Codes M c p s) :
    MemPair M H i c ↔ Clauses M C p s i c H :=
  (hH.2 i hi c ((hC.columns c).mpr ⟨p,hp,s,hs,hCode⟩)).trans (evalStep_column_iff he hp hs hCode)

theorem atomic_clauses_iff {M : SetTheory.Structure.{u}} (he : Extensional M)
    {C : Context M.Domain} (hC : ContextSpaces M C) {p s i c H a r m V : M.Domain}
    (hP : Graph M p m V) (hInstr : InstructionAt M C.instructions C.pairs p i C.atomTag a r) :
    Clauses M C p s i c H ↔ MemPair M C.atomic a s := by
  constructor
  · intro h
    rcases h with ⟨a',_,r',_,hInstr',hTrue⟩ | ⟨j,_,r',_,hInstr',_⟩ |
      ⟨j,_,k,_,hInstr',_⟩ | ⟨j,_,v,_,n,_,hInstr',_⟩
    · obtain ⟨_,haa',_⟩ := instruction_unique he hP hInstr hInstr'
      subst a'
      exact hTrue
    · exact False.elim (hC.distinct.atom_neg (instruction_unique he hP hInstr hInstr').1)
    · exact False.elim (hC.distinct.atom_imp (instruction_unique he hP hInstr hInstr').1)
    · exact False.elim (hC.distinct.atom_all (instruction_unique he hP hInstr hInstr').1)
  · intro hTrue
    have hf := instruction_fields he hC hInstr
    exact Or.inl ⟨a,hf.1,r,hf.2,hInstr,hTrue⟩

theorem negation_clauses_iff {M : SetTheory.Structure.{u}} (he : Extensional M)
    {C : Context M.Domain} (hC : ContextSpaces M C) {p s i c H j r m V : M.Domain}
    (hP : Graph M p m V) (hInstr : InstructionAt M C.instructions C.pairs p i C.negTag j r)
    (hj : M.mem j i) : Clauses M C p s i c H ↔ ¬MemPair M H j c := by
  constructor
  · intro h
    rcases h with ⟨a,_,r',_,hInstr',_⟩ | ⟨j',_,r',_,hInstr',hNot⟩ |
      ⟨j',_,k,_,hInstr',_⟩ | ⟨j',_,v,_,n,_,hInstr',_⟩
    · exact False.elim (hC.distinct.atom_neg (instruction_unique he hP hInstr hInstr').1.symm)
    · obtain ⟨_,hjj',_⟩ := instruction_unique he hP hInstr hInstr'
      subst j'
      exact hNot
    · exact False.elim (hC.distinct.neg_imp (instruction_unique he hP hInstr hInstr').1)
    · exact False.elim (hC.distinct.neg_all (instruction_unique he hP hInstr hInstr').1)
  · intro hNot
    exact Or.inr (Or.inl ⟨j,hj,r,(instruction_fields he hC hInstr).2,hInstr,hNot⟩)

theorem implication_clauses_iff {M : SetTheory.Structure.{u}} (he : Extensional M)
    {C : Context M.Domain} (hC : ContextSpaces M C) {p s i c H j k m V : M.Domain}
    (hP : Graph M p m V) (hInstr : InstructionAt M C.instructions C.pairs p i C.impTag j k)
    (hj : M.mem j i) (hk : M.mem k i) :
    Clauses M C p s i c H ↔ (MemPair M H j c → MemPair M H k c) := by
  constructor
  · intro h
    rcases h with ⟨a,_,r,_,hInstr',_⟩ | ⟨j',_,r,_,hInstr',_⟩ |
      ⟨j',_,k',_,hInstr',hImp⟩ | ⟨j',_,v,_,n,_,hInstr',_⟩
    · exact False.elim (hC.distinct.atom_imp (instruction_unique he hP hInstr hInstr').1.symm)
    · exact False.elim (hC.distinct.neg_imp (instruction_unique he hP hInstr hInstr').1.symm)
    · obtain ⟨_,hjj',hkk'⟩ := instruction_unique he hP hInstr hInstr'
      subst j'
      subst k'
      exact hImp
    · exact False.elim (hC.distinct.imp_all (instruction_unique he hP hInstr hInstr').1)
  · intro hImp
    exact Or.inr (Or.inr (Or.inl ⟨j,hj,k,hk,hInstr,hImp⟩))

theorem evaluation_atomic {M : SetTheory.Structure.{u}} (he : Extensional M)
    {C : Context M.Domain} (hC : ContextSpaces M C) {p s i c H a r : M.Domain}
    (hH : Evaluation M C H) (hp : M.mem p C.programs) (hs : M.mem s C.assignments)
    (hi : M.mem i C.omega) (hCode : Codes M c p s)
    (hInstr : InstructionAt M C.instructions C.pairs p i C.atomTag a r) :
    MemPair M H i c ↔ MemPair M C.atomic a s := by
  obtain ⟨m,_,hP⟩ := (hC.programs p).mp hp
  exact (evaluation_node he hC hH hp hs hi hCode).trans (atomic_clauses_iff he hC hP hInstr)

theorem evaluation_negation {M : SetTheory.Structure.{u}} (he : Extensional M)
    {C : Context M.Domain} (hC : ContextSpaces M C) {p s i c H j r : M.Domain}
    (hH : Evaluation M C H) (hp : M.mem p C.programs) (hs : M.mem s C.assignments)
    (hi : M.mem i C.omega) (hCode : Codes M c p s)
    (hInstr : InstructionAt M C.instructions C.pairs p i C.negTag j r) (hj : M.mem j i) :
    MemPair M H i c ↔ ¬MemPair M H j c := by
  obtain ⟨m,_,hP⟩ := (hC.programs p).mp hp
  exact (evaluation_node he hC hH hp hs hi hCode).trans (negation_clauses_iff he hC hP hInstr hj)

theorem evaluation_implication {M : SetTheory.Structure.{u}} (he : Extensional M)
    {C : Context M.Domain} (hC : ContextSpaces M C) {p s i c H j k : M.Domain}
    (hH : Evaluation M C H) (hp : M.mem p C.programs) (hs : M.mem s C.assignments)
    (hi : M.mem i C.omega) (hCode : Codes M c p s)
    (hInstr : InstructionAt M C.instructions C.pairs p i C.impTag j k)
    (hj : M.mem j i) (hk : M.mem k i) :
    MemPair M H i c ↔ (MemPair M H j c → MemPair M H k c) := by
  obtain ⟨m,_,hP⟩ := (hC.programs p).mp hp
  exact (evaluation_node he hC hH hp hs hi hCode).trans (implication_clauses_iff he hC hP hInstr hj hk)

end KP1Y.Satisfaction
