import KP1Y.RankedDefSuccessorSyntax

/-! 已排名集合的Def后继为实际单值Σ₁输出，编码同时保存Def集合、序数界和排名函数图。 -/
namespace KP1Y.SetLanguage
open YesMetaZFC YesMetaZFC.SetTheory YesMetaZFC.SetTheory.Definitional
open KP1Y.Kuratowski KP1Y.Functions KP1Y.Satisfaction KP1Y.Ranking
universe u

private theorem finite_container_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    (xs : List M.Domain) : ∃ B, ∀ x, x∈xs → M.mem x B := by
  induction xs with
  | nil =>
      obtain ⟨B,_⟩ := SetTheory.KP.exists_empty (KP1Y.models_weakKP hM)
      exact ⟨B,fun x hx => False.elim (List.not_mem_nil hx)⟩
  | cons x xs ih =>
      obtain ⟨B,hB⟩ := ih
      obtain ⟨C,hC⟩ := SetTheory.KP.exists_insert (KP1Y.models_weakKP hM) B x
      refine ⟨C,?_⟩
      intro y hy
      rcases List.mem_cons.mp hy with he | hy
      · exact (hC y).mpr (Or.inr he)
      · exact (hC y).mpr (Or.inl (hB y hy))

theorem ranked_def_box_exists_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    (Def Γ R q : M.Domain) (SW : StageWitness M.Domain) (RW : DefRankWitness M.Domain) :
    ∃ B, M.mem Def B ∧ M.mem Γ B ∧ M.mem R B ∧ M.mem q B ∧ SW.InBox M B ∧ rankWitnessInBox M RW B := by
  obtain ⟨B,hB⟩ := finite_container_d hM
    [Def,Γ,R,q,SW.values,SW.sequences,SW.relation,SW.atomic,SW.columns,SW.table,SW.raw,SW.typed,SW.definitions,
      RW.sequences.ordWords,RW.sequences.ordSpace,RW.sequences.image,RW.sequences.ordRank,RW.sequences.ceiling,
      RW.sequences.ceilingWitness,RW.sequences.rangeWitness,RW.sequences.rowsWitness,
      RW.sequenceBound,RW.sequenceRank,RW.columnRank,RW.productWitness,RW.rowsWitness]
  refine ⟨B,hB Def (by simp),hB Γ (by simp),hB R (by simp),hB q (by simp),?_,?_⟩
  · refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_⟩ <;> apply hB <;> simp
  · refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩ <;> apply hB <;> simp

theorem ranked_def_successor_total_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    (e : Env M 28) (hS : FixedSyntax M (rankDefContext.eval e) (rankDefData.eval e) (e.bound 4) (e.bound 5) (e.bound 6))
    {A : M.Domain} (hA : OrdinalRank M (e.bound 0) A (e.bound 1))
    (hP : OrdinalRank M (e.bound 2) (rankDefContext.eval e).programs (e.bound 3)) :
    ∃ Out B, Project.Formula.satisfies (((e.push A).push Out).push B) rankedDefSuccessorMatrix.body := by
  obtain ⟨Def,Γ,R,SW,RW,hStage⟩ := ranked_def_stage_exists_d hM hS hA hP
  obtain ⟨q,hq⟩ := codes_total hM Γ R
  obtain ⟨Out,hOut⟩ := codes_total hM Def q
  obtain ⟨B,hDef,hΓ,hR,hqB,hSW,hRW⟩ := ranked_def_box_exists_d hM Def Γ R q SW RW
  exact ⟨Out,B,(rankedDefSuccessorMatrix_iff hM e A Out B).mpr
    ⟨Def,hDef,Γ,hΓ,R,hR,q,hqB,SW,hSW,RW,hRW,hOut,hq,hStage⟩⟩

theorem ranked_def_successor_functional_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    (e : Env M 28) (hS : FixedSyntax M (rankDefContext.eval e) (rankDefData.eval e) (e.bound 4) (e.bound 5) (e.bound 6))
    (hP : Graph M (e.bound 2) (rankDefContext.eval e).programs (e.bound 3)) {A Out Out' B B' : M.Domain}
    (h : Project.Formula.satisfies (((e.push A).push Out).push B) rankedDefSuccessorMatrix.body)
    (h' : Project.Formula.satisfies (((e.push A).push Out').push B') rankedDefSuccessorMatrix.body) : Out=Out' := by
  obtain ⟨Def,_,Γ,_,R,_,q,_,SW,_,RW,_,hOut,hq,hStage⟩ := (rankedDefSuccessorMatrix_iff hM e A Out B).mp h
  obtain ⟨Def',_,Γ',_,R',_,q',_,SW',_,RW',_,hOut',hq',hStage'⟩ := (rankedDefSuccessorMatrix_iff hM e A Out' B').mp h'
  obtain ⟨hDef,hΓ,hR⟩ := hStage.unique_d hM hS.interpretation.spaces.omega hS.spaces.omega hP hStage'
  subst Def'
  subst Γ'
  subst R'
  have hqq' := codes_unique hM.1 hq hq'
  subst q'
  exact codes_unique hM.1 hOut hOut'

theorem ranked_def_successor_rank_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    (e : Env M 28) (hω : M.IsOmega (rankDefContext.eval e).omega) {A Out B : M.Domain}
    (hA : OrdinalRank M (e.bound 0) A (e.bound 1))
    (hP : OrdinalRank M (e.bound 2) (rankDefContext.eval e).programs (e.bound 3))
    (h : Project.Formula.satisfies (((e.push A).push Out).push B) rankedDefSuccessorMatrix.body) :
    ∃ Def Γ R q SW, Codes M Out Def q ∧ Codes M q Γ R ∧
      StageWitness.Valid M (rankDefContext.eval e) (rankDefData.eval e) (e.bound 4) (e.bound 5) (e.bound 6) A Def SW ∧
      OrdinalRank M R Def Γ := by
  obtain ⟨Def,_,Γ,_,R,_,q,_,SW,_,RW,_,hOut,hq,hStage⟩ := (rankedDefSuccessorMatrix_iff hM e A Out B).mp h
  exact ⟨Def,Γ,R,q,SW,hOut,hq,hStage.stage,hStage.rank_d hM hω hA hP⟩

end KP1Y.SetLanguage
