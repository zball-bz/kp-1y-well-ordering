import KP1Y.RankedDefSuccessor
import KP1Y.RankedPacketTerms

/-! 解包一个已排名载域，调用已核验Def后继，并保持统一packet输出。 -/
namespace KP1Y.ConstructibleRank
open YesMetaZFC YesMetaZFC.SetTheory YesMetaZFC.SetTheory.Definitional
open KP1Y.Kuratowski KP1Y.Functions KP1Y.Ranking KP1Y.SetLanguage KP1Y.Satisfaction
universe u

def rankContext : Context (Project.Term 26) :=
  ⟨.bound 5,.bound 6,.bound 7,.bound 8,.bound 9,.bound 10,.bound 11,.bound 12,
    .bound 13,.bound 14,.bound 15,.bound 16,.bound 17⟩

def rankData : RelationalData (Project.Term 26) :=
  ⟨.bound 18,.bound 19,.bound 20,.bound 21,.bound 22,.bound 23,.bound 24,.bound 25⟩

def rankEnv {M : SetTheory.Structure.{u}} (C : Context M.Domain) (D : RelationalData M.Domain)
    (zero one two FP π : M.Domain) : Env M 26 := ((defEnv C D zero one two).push π).push FP

private def payloadParams : Fin 28 → Project.Term 32 :=
  Fin.cases (.bound 0) (Fin.cases (.bound 1) (fun i => .bound ⟨i.val+6,by omega⟩))

private def payloadBody : Project.Formula 1 32 :=
  witnessInstanceFormula rankedDefSuccessorMatrix payloadParams (.bound 2) (.bound 4) (.bound 3)

def successorPacketMatrix : KP1Y.WitnessMatrix 26 where
  body := existsPacketFormula (.bound 2) payloadBody
  freeClosed := by
    apply existsPacketFormula_freeClosed _ rfl
    apply witnessInstanceFormula_freeClosed
    · exact Fin.cases rfl (Fin.cases rfl (fun _ => rfl))
    · rfl
    · rfl
    · rfl
  delta0 := existsPacketFormula_delta0 _ (witnessInstanceFormula_delta0 _ _ _ _ _)

private theorem payloadBody_iff {M : SetTheory.Structure.{u}} (e : Env M 26) (p Out B A γ F : M.Domain) :
    Project.Formula.satisfies ((((((e.push p).push Out).push B).push A).push γ).push F) payloadBody ↔
      Project.Formula.satisfies (((((e.push γ).push F).push A).push Out).push B) rankedDefSuccessorMatrix.body := by
  have hEnv : Env.substitute ((((((e.push p).push Out).push B).push A).push γ).push F)
      (Fin.cases (.bound 3) (Fin.cases (.bound 4) (Fin.cases (.bound 2) payloadParams))) =
        ((((e.push γ).push F).push A).push Out).push B := by
    rw [Env.mk.injEq]
    constructor
    · funext i
      refine Fin.cases ?_ (fun i => ?_) i
      · rfl
      · refine Fin.cases ?_ (fun i => ?_) i
        · rfl
        · refine Fin.cases ?_ (fun i => ?_) i
          · rfl
          · refine Fin.cases ?_ (fun i => ?_) i
            · rfl
            · refine Fin.cases ?_ (fun _ => ?_) i <;> rfl
    · rfl
  rw [payloadBody,witnessInstanceFormula,Project.Formula.satisfies_bind,hEnv]

theorem successorPacketMatrix_iff {M : SetTheory.Structure.{u}} (he : Extensional M) (e : Env M 26) (p Out B : M.Domain) :
    Project.Formula.satisfies (((e.push p).push Out).push B) successorPacketMatrix.body ↔
      ∃ A γ F, Packet M p A γ F ∧ Project.Formula.satisfies (((((e.push γ).push F).push A).push Out).push B) rankedDefSuccessorMatrix.body := by
  simp only [successorPacketMatrix,existsPacketFormula_iff he,payloadBody_iff]
  rfl

theorem successor_packet_total_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    (e : Env M 26) (hS : FixedSyntax M (rankContext.eval e) (rankData.eval e) (e.bound 2) (e.bound 3) (e.bound 4))
    (hP : OrdinalRank M (e.bound 0) (rankContext.eval e).programs (e.bound 1)) {p : M.Domain} (hp : RankedPacket M p) :
    ∃ Out B, Project.Formula.satisfies (((e.push p).push Out).push B) successorPacketMatrix.body := by
  obtain ⟨A,γ,F,hPacket,hRank⟩ := hp
  obtain ⟨Out,B,hOut⟩ := ranked_def_successor_total_d hM ((e.push γ).push F) hS hRank hP
  exact ⟨Out,B,(successorPacketMatrix_iff hM.1 e p Out B).mpr ⟨A,γ,F,hPacket,hOut⟩⟩

theorem successor_packet_functional_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    (e : Env M 26) (hS : FixedSyntax M (rankContext.eval e) (rankData.eval e) (e.bound 2) (e.bound 3) (e.bound 4))
    (hP : Graph M (e.bound 0) (rankContext.eval e).programs (e.bound 1)) {p Out Out' B B' : M.Domain}
    (h : Project.Formula.satisfies (((e.push p).push Out).push B) successorPacketMatrix.body)
    (h' : Project.Formula.satisfies (((e.push p).push Out').push B') successorPacketMatrix.body) : Out=Out' := by
  obtain ⟨A,γ,F,hPacket,hDef⟩ := (successorPacketMatrix_iff hM.1 e p Out B).mp h
  obtain ⟨A',γ',F',hPacket',hDef'⟩ := (successorPacketMatrix_iff hM.1 e p Out' B').mp h'
  obtain ⟨hA,hγ,hF⟩ := hPacket.injective hM.1 hPacket'
  subst A'
  subst γ'
  subst F'
  exact ranked_def_successor_functional_d hM ((e.push γ).push F) hS hP hDef hDef'

theorem successor_packet_ranked_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    (e : Env M 26) (hω : M.IsOmega (rankContext.eval e).omega)
    (hP : OrdinalRank M (e.bound 0) (rankContext.eval e).programs (e.bound 1)) {p Out B : M.Domain} (hp : RankedPacket M p)
    (h : Project.Formula.satisfies (((e.push p).push Out).push B) successorPacketMatrix.body) : RankedPacket M Out := by
  obtain ⟨A,γ,F,hPacket,hDef⟩ := (successorPacketMatrix_iff hM.1 e p Out B).mp h
  obtain ⟨Def,Γ,R,q,_,hOut,hq,_,hRank⟩ := ranked_def_successor_rank_d hM ((e.push γ).push F) hω (hp.rank hM.1 hPacket) hP hDef
  exact ⟨Def,Γ,R,⟨q,hOut,hq⟩,hRank⟩

theorem successor_packet_stage_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    (e : Env M 26) {p Out B A γ F Def Γ R : M.Domain} (hp : Packet M p A γ F) (hOut : Packet M Out Def Γ R)
    (h : Project.Formula.satisfies (((e.push p).push Out).push B) successorPacketMatrix.body) :
    ∃ SW, StageWitness.Valid M (rankContext.eval e) (rankData.eval e) (e.bound 2) (e.bound 3) (e.bound 4) A Def SW := by
  obtain ⟨A',γ',F',hp',hDef⟩ := (successorPacketMatrix_iff hM.1 e p Out B).mp h
  obtain ⟨hA,hγ,hF⟩ := hp.injective hM.1 hp'
  subst A'
  subst γ'
  subst F'
  obtain ⟨Def',_,Γ',_,R',_,q,_,SW,_,_,_,hOut',hq,hStage⟩ := (rankedDefSuccessorMatrix_iff hM ((e.push γ).push F) A Out B).mp hDef
  have hDD' := (hOut.injective hM.1 ⟨q,hOut',hq⟩).1
  subst Def'
  exact ⟨SW,hStage.stage⟩

end KP1Y.ConstructibleRank
