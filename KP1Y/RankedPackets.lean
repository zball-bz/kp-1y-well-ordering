import KP1Y.OrdinalRank

/-! 层级值编码p=(A,(Γ,F))。解包量词全部以Kuratowski编码内部成员为界。 -/
namespace KP1Y.Ranking
open YesMetaZFC YesMetaZFC.SetTheory YesMetaZFC.SetTheory.Definitional
open KP1Y.Kuratowski KP1Y.Functions
universe u

def Packet (M : SetTheory.Structure.{u}) (p A Γ F : M.Domain) : Prop :=
  ∃ q, Codes M p A q ∧ Codes M q Γ F

theorem codes_components_bounded {M : SetTheory.Structure.{u}} {p x y : M.Domain} (h : Codes M p x y) :
    ∃ b, M.mem b p ∧ M.mem x b ∧ M.mem y b := by
  obtain ⟨a,b,_,hb,hp⟩ := h
  exact ⟨b,(hp b).mpr (Or.inr rfl),(hb x).mpr (Or.inl rfl),(hb y).mpr (Or.inr rfl)⟩

theorem packet_exists_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory) (A Γ F : M.Domain) :
    ∃ p, Packet M p A Γ F := by
  obtain ⟨q,hq⟩ := codes_total hM Γ F
  obtain ⟨p,hp⟩ := codes_total hM A q
  exact ⟨p,q,hp,hq⟩

theorem Packet.unique {M : SetTheory.Structure.{u}} (he : Extensional M) {p p' A Γ F : M.Domain}
    (h : Packet M p A Γ F) (h' : Packet M p' A Γ F) : p=p' := by
  obtain ⟨q,hp,hq⟩ := h
  obtain ⟨q',hp',hq'⟩ := h'
  have hqq' := codes_unique he hq hq'
  subst q'
  exact codes_unique he hp hp'

theorem Packet.injective {M : SetTheory.Structure.{u}} (he : Extensional M) {p A Γ F A' Γ' F' : M.Domain}
    (h : Packet M p A Γ F) (h' : Packet M p A' Γ' F') : A=A' ∧ Γ=Γ' ∧ F=F' := by
  obtain ⟨q,hp,hq⟩ := h
  obtain ⟨q',hp',hq'⟩ := h'
  obtain ⟨hAA',hqq'⟩ := codes_injective he hp hp'
  subst q'
  exact ⟨hAA',codes_injective he hq hq'⟩

private def unpackSlots {n : Nat} : Fin (n+3) → Fin (n+6) :=
  Fin.cases 0 (Fin.cases 1 (Fin.cases 4 (fun i => ⟨i.val+6,by omega⟩)))

def existsPacketFormula {n : Nat} (p : Project.Term n) (φ : Project.Formula 1 (n+3)) : Project.Formula 1 n :=
  Project.Formula.existsMem p (Project.Formula.existsMem (.bound 0) (Project.Formula.existsMem (.bound 1)
    (Project.Formula.existsMem (.bound 0) (Project.Formula.existsMem (.bound 0) (Project.Formula.existsMem (.bound 1)
      (.conj (codeFormula p.weaken.weaken.weaken.weaken.weaken.weaken (.bound 4) (.bound 3))
        (.conj (codeFormula (.bound 3) (.bound 1) (.bound 0)) (φ.rename unpackSlots))))))))

theorem existsPacketFormula_delta0 {n : Nat} (p : Project.Term n) {φ : Project.Formula 1 (n+3)}
    (hφ : φ.IsDelta0) : (existsPacketFormula p φ).IsDelta0 :=
  .existsMem _ (.existsMem _ (.existsMem _ (.existsMem _ (.existsMem _ (.existsMem _
    (.conj (codeFormula_delta0 _ _ _) (.conj (codeFormula_delta0 _ _ _) (KP1Y.delta0_rename hφ _))))))))

theorem existsPacketFormula_freeClosed {n : Nat} (p : Project.Term n) {φ : Project.Formula 1 (n+3)}
    (hp : p.freeSupport=[]) (hφ : φ.FreeClosed) : (existsPacketFormula p φ).FreeClosed := by
  simp [existsPacketFormula,codeFormula,pairFormula,Project.Formula.existsMem,Project.Formula.forallMem,
    Definitional.Formula.FreeClosed,hp,hφ]

private theorem unpackSlots_env {M : SetTheory.Structure.{u}} {n : Nat} (e : Env M n)
    (b A q c Γ F : M.Domain) :
    ((((((e.push b).push A).push q).push c).push Γ).push F).reindex unpackSlots = ((e.push A).push Γ).push F := by
  rw [Env.mk.injEq]
  constructor
  · funext i
    refine Fin.cases ?_ (fun i => ?_) i
    · rfl
    · refine Fin.cases ?_ (fun i => ?_) i
      · rfl
      · refine Fin.cases ?_ (fun _ => ?_) i <;> rfl
  · rfl

theorem existsPacketFormula_iff {M : SetTheory.Structure.{u}} (he : Extensional M) {n : Nat}
    (e : Env M n) (p : Project.Term n) (φ : Project.Formula 1 (n+3)) :
    Project.Formula.satisfies e (existsPacketFormula p φ) ↔
      ∃ A Γ F, Packet M (p.eval e) A Γ F ∧ Project.Formula.satisfies (((e.push A).push Γ).push F) φ := by
  simp only [existsPacketFormula,Project.Formula.satisfies_existsMem_iff,Project.Formula.satisfies_conj_iff,
    codeFormula_iff he,Project.Formula.satisfies_rename,unpackSlots_env,Term.eval_weaken]
  constructor
  · rintro ⟨b,_,A,_,q,_,c,_,Γ,_,F,_,hp,hq,hφ⟩
    exact ⟨A,Γ,F,⟨q,hp,hq⟩,hφ⟩
  · rintro ⟨A,Γ,F,⟨q,hp,hq⟩,hφ⟩
    obtain ⟨b,hbp,hAb,hqb⟩ := codes_components_bounded hp
    obtain ⟨c,hcq,hΓc,hFc⟩ := codes_components_bounded hq
    exact ⟨b,hbp,A,hAb,q,hqb,c,hcq,Γ,hΓc,F,hFc,hp,hq,hφ⟩

def RankedPacket (M : SetTheory.Structure.{u}) (p : M.Domain) : Prop :=
  ∃ A Γ F, Packet M p A Γ F ∧ OrdinalRank M F A Γ

def rankedPacketFormula {n : Nat} (p : Project.Term n) : Project.Formula 1 n :=
  existsPacketFormula p (rankFormula (.bound 0) (.bound 2) (.bound 1))

theorem rankedPacketFormula_delta0 {n : Nat} (p : Project.Term n) : (rankedPacketFormula p).IsDelta0 :=
  existsPacketFormula_delta0 _ (rankFormula_delta0 _ _ _)

theorem rankedPacketFormula_freeClosed {n : Nat} (p : Project.Term n) (hp : p.freeSupport=[]) :
    (rankedPacketFormula p).FreeClosed := by
  apply existsPacketFormula_freeClosed _ hp
  simp [rankFormula,KP1Y.Bounded.ordinalFormula,Project.Formula.isTransitive,graphFormula,memPairFormula,codeFormula,pairFormula,
    Project.Formula.existsMem,Project.Formula.forallMem,Definitional.Formula.FreeClosed]

theorem rankedPacketFormula_iff {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory) {n : Nat}
    (e : Env M n) (p : Project.Term n) : Project.Formula.satisfies e (rankedPacketFormula p) ↔ RankedPacket M (p.eval e) := by
  simp only [rankedPacketFormula,existsPacketFormula_iff hM.1,rankFormula_iff hM]
  rfl

theorem RankedPacket.rank {M : SetTheory.Structure.{u}} (he : Extensional M) {p A Γ F : M.Domain}
    (h : RankedPacket M p) (hp : Packet M p A Γ F) : OrdinalRank M F A Γ := by
  obtain ⟨A',Γ',F',hp',hRank⟩ := h
  obtain ⟨hA,hΓ,hF⟩ := hp.injective he hp'
  subst A'
  subst Γ'
  subst F'
  exact hRank

theorem empty_ranked_packet_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {zero : M.Domain} (hZero : ∀ x, ¬M.mem x zero) : ∃ p, Packet M p zero zero zero ∧ RankedPacket M p := by
  obtain ⟨p,hp⟩ := packet_exists_d hM zero zero zero
  have hRank : OrdinalRank M zero zero zero := by
    refine ⟨Structure.IsOrdinal.of_no_members hZero,empty_graph hZero,?_⟩
    intro x y a hxa _
    obtain ⟨q,hq,_⟩ := hxa
    exact False.elim (hZero q hq)
  exact ⟨p,hp,zero,zero,zero,hp,hRank⟩

end KP1Y.Ranking
