import KP1Y.RankedPackets

/-! 实际函数历史中的已排名值及两种成员查询；查询随合法值域界变化而保持不变。 -/
namespace KP1Y.Ranking
open YesMetaZFC YesMetaZFC.SetTheory YesMetaZFC.SetTheory.Definitional
open KP1Y.Kuratowski KP1Y.Functions
universe u

def PacketCarrierMember (M : SetTheory.Structure.{u}) (p x : M.Domain) : Prop :=
  ∃ A Γ F, Packet M p A Γ F ∧ M.mem x A

def PacketOrdinalMember (M : SetTheory.Structure.{u}) (p x : M.Domain) : Prop :=
  ∃ A Γ F, Packet M p A Γ F ∧ M.mem x Γ

def packetCarrierMemberFormula {n : Nat} (p x : Project.Term n) : Project.Formula 1 n :=
  existsPacketFormula p (.mem x.weaken.weaken.weaken (.bound 2))

def packetOrdinalMemberFormula {n : Nat} (p x : Project.Term n) : Project.Formula 1 n :=
  existsPacketFormula p (.mem x.weaken.weaken.weaken (.bound 1))

theorem packetCarrierMemberFormula_delta0 {n : Nat} (p x : Project.Term n) :
    (packetCarrierMemberFormula p x).IsDelta0 := existsPacketFormula_delta0 _ (.mem _ _)

theorem packetOrdinalMemberFormula_delta0 {n : Nat} (p x : Project.Term n) :
    (packetOrdinalMemberFormula p x).IsDelta0 := existsPacketFormula_delta0 _ (.mem _ _)

theorem packetCarrierMemberFormula_freeClosed {n : Nat} (p x : Project.Term n)
    (hp : p.freeSupport=[]) (hx : x.freeSupport=[]) : (packetCarrierMemberFormula p x).FreeClosed := by
  apply existsPacketFormula_freeClosed _ hp
  simp [Definitional.Formula.FreeClosed,hx]

theorem packetOrdinalMemberFormula_freeClosed {n : Nat} (p x : Project.Term n)
    (hp : p.freeSupport=[]) (hx : x.freeSupport=[]) : (packetOrdinalMemberFormula p x).FreeClosed := by
  apply existsPacketFormula_freeClosed _ hp
  simp [Definitional.Formula.FreeClosed,hx]

theorem packetCarrierMemberFormula_iff {M : SetTheory.Structure.{u}} (he : Extensional M) {n : Nat}
    (e : Env M n) (p x : Project.Term n) : Project.Formula.satisfies e (packetCarrierMemberFormula p x) ↔
      PacketCarrierMember M (p.eval e) (x.eval e) := by
  simp only [packetCarrierMemberFormula,existsPacketFormula_iff he,Project.Formula.satisfies_mem_iff,Term.eval_weaken]
  rfl

theorem packetOrdinalMemberFormula_iff {M : SetTheory.Structure.{u}} (he : Extensional M) {n : Nat}
    (e : Env M n) (p x : Project.Term n) : Project.Formula.satisfies e (packetOrdinalMemberFormula p x) ↔
      PacketOrdinalMember M (p.eval e) (x.eval e) := by
  simp only [packetOrdinalMemberFormula,existsPacketFormula_iff he,Project.Formula.satisfies_mem_iff,Term.eval_weaken]
  rfl

def FamilyMember (M : SetTheory.Structure.{u}) (H V j x : M.Domain) : Prop :=
  ∃ p, M.mem p V ∧ MemPair M H j p ∧ PacketCarrierMember M p x

def FamilyOrdinalMember (M : SetTheory.Structure.{u}) (H V j x : M.Domain) : Prop :=
  ∃ p, M.mem p V ∧ MemPair M H j p ∧ PacketOrdinalMember M p x

def familyMemberFormula {n : Nat} (H V j x : Project.Term n) : Project.Formula 1 n :=
  Project.Formula.existsMem V (.conj (memPairFormula H.weaken j.weaken (.bound 0))
    (packetCarrierMemberFormula (.bound 0) x.weaken))

def familyOrdinalMemberFormula {n : Nat} (H V j x : Project.Term n) : Project.Formula 1 n :=
  Project.Formula.existsMem V (.conj (memPairFormula H.weaken j.weaken (.bound 0))
    (packetOrdinalMemberFormula (.bound 0) x.weaken))

theorem familyMemberFormula_delta0 {n : Nat} (H V j x : Project.Term n) : (familyMemberFormula H V j x).IsDelta0 :=
  .existsMem _ (.conj (memPairFormula_delta0 _ _ _) (packetCarrierMemberFormula_delta0 _ _))

theorem familyOrdinalMemberFormula_delta0 {n : Nat} (H V j x : Project.Term n) : (familyOrdinalMemberFormula H V j x).IsDelta0 :=
  .existsMem _ (.conj (memPairFormula_delta0 _ _ _) (packetOrdinalMemberFormula_delta0 _ _))

theorem familyMemberFormula_freeClosed {n : Nat} (H V j x : Project.Term n)
    (hH : H.freeSupport=[]) (hV : V.freeSupport=[]) (hj : j.freeSupport=[]) (hx : x.freeSupport=[]) :
    (familyMemberFormula H V j x).FreeClosed := by
  unfold familyMemberFormula
  simp only [Project.Formula.existsMem,Definitional.Formula.FreeClosed]
  refine ⟨by simp [hV],?_,packetCarrierMemberFormula_freeClosed _ _ rfl (by simp [hx])⟩
  simp [memPairFormula,codeFormula,pairFormula,Project.Formula.existsMem,Project.Formula.forallMem,Definitional.Formula.FreeClosed,hH,hj]

theorem familyOrdinalMemberFormula_freeClosed {n : Nat} (H V j x : Project.Term n)
    (hH : H.freeSupport=[]) (hV : V.freeSupport=[]) (hj : j.freeSupport=[]) (hx : x.freeSupport=[]) :
    (familyOrdinalMemberFormula H V j x).FreeClosed := by
  unfold familyOrdinalMemberFormula
  simp only [Project.Formula.existsMem,Definitional.Formula.FreeClosed]
  refine ⟨by simp [hV],?_,packetOrdinalMemberFormula_freeClosed _ _ rfl (by simp [hx])⟩
  simp [memPairFormula,codeFormula,pairFormula,Project.Formula.existsMem,Project.Formula.forallMem,Definitional.Formula.FreeClosed,hH,hj]

theorem familyMemberFormula_iff {M : SetTheory.Structure.{u}} (he : Extensional M) {n : Nat}
    (e : Env M n) (H V j x : Project.Term n) : Project.Formula.satisfies e (familyMemberFormula H V j x) ↔
      FamilyMember M (H.eval e) (V.eval e) (j.eval e) (x.eval e) := by
  simp only [familyMemberFormula,Project.Formula.satisfies_existsMem_iff,Project.Formula.satisfies_conj_iff,
    memPairFormula_iff he,packetCarrierMemberFormula_iff he,Term.eval_weaken]
  rfl

theorem familyOrdinalMemberFormula_iff {M : SetTheory.Structure.{u}} (he : Extensional M) {n : Nat}
    (e : Env M n) (H V j x : Project.Term n) : Project.Formula.satisfies e (familyOrdinalMemberFormula H V j x) ↔
      FamilyOrdinalMember M (H.eval e) (V.eval e) (j.eval e) (x.eval e) := by
  simp only [familyOrdinalMemberFormula,Project.Formula.satisfies_existsMem_iff,Project.Formula.satisfies_conj_iff,
    memPairFormula_iff he,packetOrdinalMemberFormula_iff he,Term.eval_weaken]
  rfl

structure RankedFamily (M : SetTheory.Structure.{u}) (H I V : M.Domain) : Prop where
  graph : Graph M H I V
  ranked : ∀ j p, MemPair M H j p → RankedPacket M p

def rankedFamilyFormula {n : Nat} (H I V : Project.Term n) : Project.Formula 1 n :=
  .conj (graphFormula H I V) (Project.Formula.forallMem I (Project.Formula.forallMem V.weaken
    (.imp (memPairFormula H.weaken.weaken (.bound 1) (.bound 0)) (rankedPacketFormula (.bound 0)))))

theorem rankedFamilyFormula_delta0 {n : Nat} (H I V : Project.Term n) : (rankedFamilyFormula H I V).IsDelta0 :=
  .conj (graphFormula_delta0 _ _ _) (.forallMem _ (.forallMem _ (.imp (memPairFormula_delta0 _ _ _) (rankedPacketFormula_delta0 _))))

theorem rankedFamilyFormula_freeClosed {n : Nat} (H I V : Project.Term n)
    (hH : H.freeSupport=[]) (hI : I.freeSupport=[]) (hV : V.freeSupport=[]) : (rankedFamilyFormula H I V).FreeClosed := by
  unfold rankedFamilyFormula
  simp only [Project.Formula.forallMem,Definitional.Formula.FreeClosed]
  refine ⟨?_,?_,?_,?_,rankedPacketFormula_freeClosed _ rfl⟩ <;>
    simp [graphFormula,memPairFormula,codeFormula,pairFormula,Project.Formula.existsMem,
      Project.Formula.forallMem,Definitional.Formula.FreeClosed,hH,hI,hV]

theorem rankedFamilyFormula_iff {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory) {n : Nat}
    (e : Env M n) (H I V : Project.Term n) : Project.Formula.satisfies e (rankedFamilyFormula H I V) ↔
      RankedFamily M (H.eval e) (I.eval e) (V.eval e) := by
  simp only [rankedFamilyFormula,Project.Formula.satisfies_conj_iff,graphFormula_iff hM.1,
    Project.Formula.satisfies_forallMem_iff,Project.Formula.satisfies_imp_iff,memPairFormula_iff hM.1,
    rankedPacketFormula_iff hM,Term.eval_weaken]
  constructor
  · rintro ⟨hG,hR⟩
    exact ⟨hG,fun j p hAt => hR j (hG.bounds hM.1 hAt).1 p (hG.bounds hM.1 hAt).2 hAt⟩
  · intro h
    exact ⟨h.graph,fun j _ p _ => h.ranked j p⟩

theorem familyMember_values_congr {M : SetTheory.Structure.{u}} (he : Extensional M)
    {H I V V' : M.Domain} (h : Graph M H I V) (h' : Graph M H I V') (j x : M.Domain) :
    FamilyMember M H V j x ↔ FamilyMember M H V' j x :=
  ⟨fun ⟨p,_,hp,hx⟩ => ⟨p,(h'.bounds he hp).2,hp,hx⟩,fun ⟨p,_,hp,hx⟩ => ⟨p,(h.bounds he hp).2,hp,hx⟩⟩

theorem familyOrdinalMember_values_congr {M : SetTheory.Structure.{u}} (he : Extensional M)
    {H I V V' : M.Domain} (h : Graph M H I V) (h' : Graph M H I V') (j x : M.Domain) :
    FamilyOrdinalMember M H V j x ↔ FamilyOrdinalMember M H V' j x :=
  ⟨fun ⟨p,_,hp,hx⟩ => ⟨p,(h'.bounds he hp).2,hp,hx⟩,fun ⟨p,_,hp,hx⟩ => ⟨p,(h.bounds he hp).2,hp,hx⟩⟩

end KP1Y.Ranking
