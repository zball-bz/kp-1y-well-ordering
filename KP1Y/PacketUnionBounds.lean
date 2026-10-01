import KP1Y.RankedFamily

/-! 五次实际并集足以界住值域中所有packet的载域成员及序数界成员。 -/
namespace KP1Y.Ranking
open YesMetaZFC YesMetaZFC.SetTheory YesMetaZFC.SetTheory.Definitional
open KP1Y.Kuratowski KP1Y.Bounded
universe u v

structure PacketUnionBounds (α : Type u) where
  first : α
  second : α
  third : α
  fourth : α
  fifth : α

def PacketUnionBounds.map {α : Type u} {β : Type v} (W : PacketUnionBounds α) (f : α → β) : PacketUnionBounds β :=
  ⟨f W.first,f W.second,f W.third,f W.fourth,f W.fifth⟩

def PacketUnionBounds.eval {M : SetTheory.Structure.{u}} {n : Nat}
    (W : PacketUnionBounds (Project.Term n)) (e : Env M n) : PacketUnionBounds M.Domain := W.map (fun t => t.eval e)

structure PacketUnionBounds.Valid (M : SetTheory.Structure.{u}) (V : M.Domain) (W : PacketUnionBounds M.Domain) : Prop where
  first : M.IsUnionOf W.first V
  second : M.IsUnionOf W.second W.first
  third : M.IsUnionOf W.third W.second
  fourth : M.IsUnionOf W.fourth W.third
  fifth : M.IsUnionOf W.fifth W.fourth

def packetUnionBoundsFormula {n : Nat} (V : Project.Term n) (W : PacketUnionBounds (Project.Term n)) : Project.Formula 1 n :=
  .conj (unionFormula W.first V) (.conj (unionFormula W.second W.first) (.conj (unionFormula W.third W.second)
    (.conj (unionFormula W.fourth W.third) (unionFormula W.fifth W.fourth))))

theorem packetUnionBoundsFormula_delta0 {n : Nat} (V : Project.Term n) (W : PacketUnionBounds (Project.Term n)) :
    (packetUnionBoundsFormula V W).IsDelta0 :=
  .conj (unionFormula_delta0 _ _) (.conj (unionFormula_delta0 _ _) (.conj (unionFormula_delta0 _ _)
    (.conj (unionFormula_delta0 _ _) (unionFormula_delta0 _ _))))

theorem packetUnionBoundsFormula_freeClosed {n : Nat} (V : Project.Term n) (W : PacketUnionBounds (Project.Term n))
    (hV : V.freeSupport=[]) (h1 : W.first.freeSupport=[]) (h2 : W.second.freeSupport=[])
    (h3 : W.third.freeSupport=[]) (h4 : W.fourth.freeSupport=[]) (h5 : W.fifth.freeSupport=[]) :
    (packetUnionBoundsFormula V W).FreeClosed := by
  simp [packetUnionBoundsFormula,unionFormula,Project.Formula.existsMem,Project.Formula.forallMem,
    Definitional.Formula.FreeClosed,hV,h1,h2,h3,h4,h5]

theorem packetUnionBoundsFormula_iff {M : SetTheory.Structure.{u}} {n : Nat} (e : Env M n)
    (V : Project.Term n) (W : PacketUnionBounds (Project.Term n)) :
    Project.Formula.satisfies e (packetUnionBoundsFormula V W) ↔ PacketUnionBounds.Valid M (V.eval e) (W.eval e) := by
  simp only [packetUnionBoundsFormula,Project.Formula.satisfies_conj_iff,unionFormula_iff]
  exact ⟨fun h => ⟨h.1,h.2.1,h.2.2.1,h.2.2.2.1,h.2.2.2.2⟩,fun h => ⟨h.first,h.second,h.third,h.fourth,h.fifth⟩⟩

theorem packet_union_bounds_exists_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory) (V : M.Domain) :
    ∃ W, PacketUnionBounds.Valid M V W := by
  obtain ⟨A,hA⟩ := SetTheory.KP.exists_union (KP1Y.models_weakKP hM) V
  obtain ⟨B,hB⟩ := SetTheory.KP.exists_union (KP1Y.models_weakKP hM) A
  obtain ⟨C,hC⟩ := SetTheory.KP.exists_union (KP1Y.models_weakKP hM) B
  obtain ⟨D,hD⟩ := SetTheory.KP.exists_union (KP1Y.models_weakKP hM) C
  obtain ⟨E,hE⟩ := SetTheory.KP.exists_union (KP1Y.models_weakKP hM) D
  exact ⟨⟨A,B,C,D,E⟩,hA,hB,hC,hD,hE⟩

theorem PacketUnionBounds.Valid.carrier_bound {M : SetTheory.Structure.{u}} {V p x : M.Domain}
    {W : PacketUnionBounds M.Domain} (h : W.Valid M V) (hp : M.mem p V) (hx : PacketCarrierMember M p x) : M.mem x W.third := by
  obtain ⟨A,Γ,F,⟨q,hpCode,_⟩,hxA⟩ := hx
  obtain ⟨b,hbp,hAb,_⟩ := codes_components_bounded hpCode
  exact (h.third x).mpr ⟨A,(h.second A).mpr ⟨b,(h.first b).mpr ⟨p,hp,hbp⟩,hAb⟩,hxA⟩

theorem PacketUnionBounds.Valid.ordinal_bound {M : SetTheory.Structure.{u}} {V p x : M.Domain}
    {W : PacketUnionBounds M.Domain} (h : W.Valid M V) (hp : M.mem p V) (hx : PacketOrdinalMember M p x) : M.mem x W.fifth := by
  obtain ⟨A,Γ,F,⟨q,hpCode,hqCode⟩,hxΓ⟩ := hx
  obtain ⟨b,hbp,_,hqb⟩ := codes_components_bounded hpCode
  obtain ⟨c,hcq,hΓc,_⟩ := codes_components_bounded hqCode
  have hb := (h.first b).mpr ⟨p,hp,hbp⟩
  have hq := (h.second q).mpr ⟨b,hb,hqb⟩
  have hc := (h.third c).mpr ⟨q,hq,hcq⟩
  have hΓ := (h.fourth Γ).mpr ⟨c,hc,hΓc⟩
  exact (h.fifth x).mpr ⟨Γ,hΓ,hxΓ⟩

end KP1Y.Ranking
