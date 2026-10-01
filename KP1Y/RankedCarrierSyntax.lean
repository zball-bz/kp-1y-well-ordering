import KP1Y.RankedPacketTerms

/-! packet的载域关系用于两个实际历史之间的对象归纳模式。 -/
namespace KP1Y.Ranking
open YesMetaZFC YesMetaZFC.SetTheory YesMetaZFC.SetTheory.Definitional
universe u

def CarrierOf (M : SetTheory.Structure.{u}) (p A : M.Domain) : Prop := ∃ Γ F, Packet M p A Γ F

def carrierOfFormula {n : Nat} (p A : Project.Term n) : Project.Formula 1 n :=
  existsPacketFormula p (Project.Formula.extensionalEq (.bound 2) A.weaken.weaken.weaken)

theorem carrierOfFormula_delta0 {n : Nat} (p A : Project.Term n) : (carrierOfFormula p A).IsDelta0 :=
  existsPacketFormula_delta0 _ (.atom _ _ _)

theorem carrierOfFormula_freeClosed {n : Nat} (p A : Project.Term n) (hp : p.freeSupport=[]) (hA : A.freeSupport=[]) :
    (carrierOfFormula p A).FreeClosed := by
  apply existsPacketFormula_freeClosed _ hp
  simp [hA]

theorem carrierOfFormula_iff {M : SetTheory.Structure.{u}} (he : Extensional M) {n : Nat} (e : Env M n)
    (p A : Project.Term n) : Project.Formula.satisfies e (carrierOfFormula p A) ↔ CarrierOf M (p.eval e) (A.eval e) := by
  simp only [carrierOfFormula,existsPacketFormula_iff he,Project.Formula.satisfies_extensionalEq_iff_eq he,Term.eval_weaken]
  constructor
  · rintro ⟨T,Γ,F,hPacket,hEq⟩
    exact ⟨Γ,F,hEq ▸ hPacket⟩
  · rintro ⟨Γ,F,hPacket⟩
    exact ⟨A.eval e,Γ,F,hPacket,rfl⟩

end KP1Y.Ranking
