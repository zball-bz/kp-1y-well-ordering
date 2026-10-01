import KP1Y.DefSuccessorMatrix
import KP1Y.DefRankWitness

/-! 实际Def层与规范排名证书的连接；不同求值/收集证书产生相同集合和排名。 -/
namespace KP1Y.SetLanguage
open YesMetaZFC YesMetaZFC.SetTheory YesMetaZFC.SetTheory.Definitional
open KP1Y.Kuratowski KP1Y.Functions KP1Y.Satisfaction KP1Y.Definability KP1Y.Ranking
universe u

private theorem definitions_unique {M : SetTheory.Structure.{u}} (he : Extensional M)
    {C : Context M.Domain} {D : RelationalData M.Domain} {Sat zero Def F F' : M.Domain}
    (h : DefCertificate M C D Sat zero Def F) (h' : DefCertificate M C D Sat zero Def F') : F=F' := by
  have hF := h.onto.toGraph he
  have hF' := h'.onto.toGraph he
  apply hF.ext he hF'
  intro c hc S
  obtain ⟨T,hT,hcT⟩ := hF.total c hc
  obtain ⟨T',hT',hcT'⟩ := hF'.total c hc
  have hTT' := defined_by_unique he (h.rows c hc T hT hcT) (h'.rows c hc T' hT' hcT')
  subst T'
  constructor
  · intro hcS
    exact (hF.unique c T S hcT hcS) ▸ hcT'
  · intro hcS
    exact (hF'.unique c T S hcT' hcS) ▸ hcT

theorem StageWitness.Valid.rank_inputs_unique_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : Context M.Domain} {D : RelationalData M.Domain} {zero one two A Def Def' : M.Domain}
    {W W' : StageWitness M.Domain} (hω : M.IsOmega D.omega) (hCω : M.IsOmega C.omega)
    (h : W.Valid M C D zero one two A Def) (h' : W'.Valid M C D zero one two A Def') :
    Def=Def' ∧ W.values=W'.values ∧ W.columns=W'.columns ∧ W.definitions=W'.definitions := by
  rcases W with ⟨V,B,R,Atom,Col,H,Raw,Sat,F⟩
  rcases W' with ⟨V',B',R',Atom',Col',H',Raw',Sat',F'⟩
  have hV : V=V' := KP1Y.Sequences.space_certificate_unique_d hM hω h.sequences h'.sequences
  subst V'
  have hR : R=R' := h.relation.unique hM.1 h'.relation
  subst R'
  have hAtom : Atom=Atom' := h.atomic.unique hM.1 h'.atomic
  subst Atom'
  have hCol : Col=Col' := hM.1.eq_of_same_members Col Col' (fun p => (h.columns p).trans (h'.columns p).symm)
  subst Col'
  have hH : H=H' := evaluation_unique_d hM (C := C.withInterpretation A V Col Atom) hCω h.evaluation h'.evaluation
  subst H'
  have hRaw : Raw=Raw' := hM.1.eq_of_same_members Raw Raw' (fun c => (h.raw c).trans (h'.raw c).symm)
  subst Raw'
  have hSat : Sat=Sat' := hM.1.eq_of_same_members Sat Sat' (fun c => (h.typed c).trans (h'.typed c).symm)
  subst Sat'
  have hDef := (def_certificate_exact hM.1 h.definitions).unique hM.1 (def_certificate_exact hM.1 h'.definitions)
  subst Def'
  exact ⟨rfl,rfl,rfl,definitions_unique hM.1 h.definitions h'.definitions⟩

structure RankedDefStage (M : SetTheory.Structure.{u}) (C : Context M.Domain) (D : RelationalData M.Domain)
    (zero one two FA A α FP π Def Γ R : M.Domain) (SW : StageWitness M.Domain) (RW : DefRankWitness M.Domain) : Prop where
  stage : SW.Valid M C D zero one two A Def
  ranking : RW.Valid M C.omega FA A α FP C.programs π SW.values SW.columns SW.definitions Def Γ R

def rankedDefStageFormula {n : Nat} (C : Context (Project.Term n)) (D : RelationalData (Project.Term n))
    (zero one two FA A α FP π Def Γ R : Project.Term n)
    (SW : StageWitness (Project.Term n)) (RW : DefRankWitness (Project.Term n)) : Project.Formula 1 n :=
  .conj (stageWitnessFormula C D zero one two A Def SW)
    (defRankWitnessFormula C.omega FA A α FP C.programs π SW.values SW.columns SW.definitions Def Γ R RW)

theorem rankedDefStageFormula_delta0 {n : Nat} (C : Context (Project.Term n)) (D : RelationalData (Project.Term n))
    (zero one two FA A α FP π Def Γ R : Project.Term n)
    (SW : StageWitness (Project.Term n)) (RW : DefRankWitness (Project.Term n)) :
    (rankedDefStageFormula C D zero one two FA A α FP π Def Γ R SW RW).IsDelta0 :=
  .conj (stageWitnessFormula_delta0 _ _ _ _ _ _ _ _) (defRankWitnessFormula_delta0 _ _ _ _ _ _ _ _ _ _ _ _ _ _)

theorem rankedDefStageFormula_iff {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory) {n : Nat}
    (e : Env M n) (C : Context (Project.Term n)) (D : RelationalData (Project.Term n))
    (zero one two FA A α FP π Def Γ R : Project.Term n)
    (SW : StageWitness (Project.Term n)) (RW : DefRankWitness (Project.Term n)) :
    Project.Formula.satisfies e (rankedDefStageFormula C D zero one two FA A α FP π Def Γ R SW RW) ↔
      RankedDefStage M (C.eval e) (D.eval e) (zero.eval e) (one.eval e) (two.eval e) (FA.eval e) (A.eval e)
        (α.eval e) (FP.eval e) (π.eval e) (Def.eval e) (Γ.eval e) (R.eval e) (SW.eval e) (RW.eval e) := by
  simp only [rankedDefStageFormula,Project.Formula.satisfies_conj_iff,stageWitnessFormula_iff hM,defRankWitnessFormula_iff hM]
  exact ⟨fun h => ⟨h.1,h.2⟩,fun h => ⟨h.stage,h.ranking⟩⟩

theorem ranked_def_stage_exists_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : Context M.Domain} {D : RelationalData M.Domain} {zero one two FA A α FP π : M.Domain}
    (hS : FixedSyntax M C D zero one two) (hA : OrdinalRank M FA A α) (hP : OrdinalRank M FP C.programs π) :
    ∃ Def Γ R SW RW, RankedDefStage M C D zero one two FA A α FP π Def Γ R SW RW := by
  obtain ⟨Def,SW,hSW⟩ := stage_witness_exists_d hM hS A
  have hStage := hSW.stage_d hM hS
  obtain ⟨Γ,R,RW,hRW⟩ := def_rank_witness_exists_d hM hS.spaces.omega hA hP hStage.spaces.assignments hSW.columns hSW.definitions.onto
  exact ⟨Def,Γ,R,SW,RW,hSW,hRW⟩

theorem RankedDefStage.rank_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : Context M.Domain} {D : RelationalData M.Domain} {zero one two FA A α FP π Def Γ R : M.Domain}
    {SW : StageWitness M.Domain} {RW : DefRankWitness M.Domain}
    (hω : M.IsOmega C.omega) (hA : OrdinalRank M FA A α) (hP : OrdinalRank M FP C.programs π)
    (h : RankedDefStage M C D zero one two FA A α FP π Def Γ R SW RW) : OrdinalRank M R Def Γ :=
  h.ranking.rank_d hM hω hA hP (h.stage.definitions.onto.toGraph hM.1)

theorem RankedDefStage.unique_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : Context M.Domain} {D : RelationalData M.Domain} {zero one two FA A α FP π Def Γ R Def' Γ' R' : M.Domain}
    {SW SW' : StageWitness M.Domain} {RW RW' : DefRankWitness M.Domain}
    (hω : M.IsOmega D.omega) (hCω : M.IsOmega C.omega) (hP : Graph M FP C.programs π)
    (h : RankedDefStage M C D zero one two FA A α FP π Def Γ R SW RW)
    (h' : RankedDefStage M C D zero one two FA A α FP π Def' Γ' R' SW' RW') : Def=Def' ∧ Γ=Γ' ∧ R=R' := by
  obtain ⟨hDef,hValues,hColumns,hDefinitions⟩ := h.stage.rank_inputs_unique_d hM hω hCω h'.stage
  subst Def'
  have hRank' : RW'.Valid M C.omega FA A α FP C.programs π SW.values SW.columns SW.definitions Def Γ' R' :=
    Eq.mpr (congrArg (fun F => RW'.Valid M C.omega FA A α FP C.programs π SW.values SW.columns F Def Γ' R') hDefinitions)
      (Eq.mpr (congrArg (fun Col => RW'.Valid M C.omega FA A α FP C.programs π SW.values Col SW'.definitions Def Γ' R') hColumns)
        (Eq.mpr (congrArg (fun V => RW'.Valid M C.omega FA A α FP C.programs π V SW'.columns SW'.definitions Def Γ' R') hValues) h'.ranking))
  exact ⟨rfl,h.ranking.unique_d hM hCω hP hRank'⟩

end KP1Y.SetLanguage
