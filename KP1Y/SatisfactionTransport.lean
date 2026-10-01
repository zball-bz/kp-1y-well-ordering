import KP1Y.SatisfactionQuantifier

/-! 比较同一求值表中两个程序的列，准备证明后续指令不影响已有节点。 -/
namespace KP1Y.Satisfaction
open YesMetaZFC YesMetaZFC.SetTheory
open KP1Y.Kuratowski KP1Y.Functions
universe u

def NodeAgreement (M : SetTheory.Structure.{u}) (C : Context M.Domain) (H p q i : M.Domain) : Prop :=
  ∀ s, M.mem s C.assignments → ∀ c, M.mem c C.columns → ∀ d, M.mem d C.columns →
    Codes M c p s ∧ Codes M d q s → (MemPair M H i c ↔ MemPair M H i d)

theorem instruction_transport {M : SetTheory.Structure.{u}} {C : Context M.Domain}
    {p q i op x y : M.Domain}
    (hRows : ∀ instr, M.mem instr C.instructions → (MemPair M p i instr ↔ MemPair M q i instr)) :
    InstructionAt M C.instructions C.pairs p i op x y ↔ InstructionAt M C.instructions C.pairs q i op x y := by
  constructor
  · rintro ⟨instr,hInstr,args,hArgs,hPi,hCode,hFields⟩
    exact ⟨instr,hInstr,args,hArgs,(hRows instr hInstr).mp hPi,hCode,hFields⟩
  · rintro ⟨instr,hInstr,args,hArgs,hQi,hCode,hFields⟩
    exact ⟨instr,hInstr,args,hArgs,(hRows instr hInstr).mpr hQi,hCode,hFields⟩

private theorem universal_program_transport {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : Context M.Domain} (hC : ContextSpaces M C) {H p q s i : M.Domain}
    (hq : M.mem q C.programs)
    (hInstr : ∀ op x y, InstructionAt M C.instructions C.pairs p i op x y →
      InstructionAt M C.instructions C.pairs q i op x y)
    (hPast : ∀ j, M.mem j i → ∀ t, M.mem t C.assignments → ∀ c, M.mem c C.columns →
      ∀ d, M.mem d C.columns → Codes M c p t → Codes M d q t → MemPair M H j c → MemPair M H j d)
    (hAll : UniversalCase M C p s i H) : UniversalCase M C q s i H := by
  obtain ⟨j,hj,v,hv,n,hn,hPi,hS,hvn,hAll⟩ := hAll
  refine ⟨j,hj,v,hv,n,hn,hInstr _ _ _ hPi,hS,hvn,?_⟩
  intro x hx
  obtain ⟨t,ht,hUpdate,c,hc,hCode,hTrue⟩ := hAll x hx
  obtain ⟨d,hd,hCode'⟩ := column_exists_d hM hC hq ht
  exact ⟨t,ht,hUpdate,d,hd,hCode',hPast j hj t ht c hc d hd hCode hCode' hTrue⟩

theorem clauses_program_congr {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : Context M.Domain} (hC : ContextSpaces M C) {H p q s i c d : M.Domain}
    (hp : M.mem p C.programs) (hq : M.mem q C.programs) (hs : M.mem s C.assignments)
    (hc : M.mem c C.columns) (hd : M.mem d C.columns) (hCode : Codes M c p s) (hCode' : Codes M d q s)
    (hRows : ∀ instr, M.mem instr C.instructions → (MemPair M p i instr ↔ MemPair M q i instr))
    (hPast : ∀ j, M.mem j i → NodeAgreement M C H p q j) :
    Clauses M C p s i c H ↔ Clauses M C q s i d H := by
  have hInstr (op x y : M.Domain) := instruction_transport (op := op) (x := x) (y := y) hRows
  have hTruth (j : M.Domain) (hj : M.mem j i) : MemPair M H j c ↔ MemPair M H j d :=
    hPast j hj s hs c hc d hd ⟨hCode,hCode'⟩
  constructor
  · intro h
    rcases h with ⟨a,ha,r,hr,hPi,hTrue⟩ | ⟨j,hj,r,hr,hPi,hNot⟩ |
      ⟨j,hj,k,hk,hPi,hImp⟩ | hAll
    · exact Or.inl ⟨a,ha,r,hr,(hInstr _ _ _).mp hPi,hTrue⟩
    · exact Or.inr (Or.inl ⟨j,hj,r,hr,(hInstr _ _ _).mp hPi,fun h => hNot ((hTruth j hj).mpr h)⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨j,hj,k,hk,(hInstr _ _ _).mp hPi,
        fun h => (hTruth k hk).mp (hImp ((hTruth j hj).mpr h))⟩))
    · exact Or.inr (Or.inr (Or.inr (universal_program_transport hM hC hq
        (fun op x y => (hInstr op x y).mp)
        (fun j hj t ht c hc d hd hcp hdq => (hPast j hj t ht c hc d hd ⟨hcp,hdq⟩).mp) hAll)))
  · intro h
    rcases h with ⟨a,ha,r,hr,hQi,hTrue⟩ | ⟨j,hj,r,hr,hQi,hNot⟩ |
      ⟨j,hj,k,hk,hQi,hImp⟩ | hAll
    · exact Or.inl ⟨a,ha,r,hr,(hInstr _ _ _).mpr hQi,hTrue⟩
    · exact Or.inr (Or.inl ⟨j,hj,r,hr,(hInstr _ _ _).mpr hQi,fun h => hNot ((hTruth j hj).mp h)⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨j,hj,k,hk,(hInstr _ _ _).mpr hQi,
        fun h => (hTruth k hk).mpr (hImp ((hTruth j hj).mp h))⟩))
    · exact Or.inr (Or.inr (Or.inr (universal_program_transport hM hC hp
        (fun op x y => (hInstr op x y).mpr)
        (fun j hj t ht d hd c hc hdq hcp => (hPast j hj t ht c hc d hd ⟨hcp,hdq⟩).mpr) hAll)))

end KP1Y.Satisfaction
