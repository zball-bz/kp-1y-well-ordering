import KP1Y.RankedDefStage

/-! 规范排名Def后继的字面Σ₁矩阵。26个辅助字段全部量化于同一个对象证书集合。 -/
namespace KP1Y.SetLanguage
open YesMetaZFC YesMetaZFC.SetTheory YesMetaZFC.SetTheory.Definitional
open KP1Y.Kuratowski KP1Y.Functions KP1Y.Sequences KP1Y.Satisfaction KP1Y.Definability KP1Y.Ranking
universe u

def rankDefContext : Context (Project.Term 28) :=
  ⟨.bound 7,.bound 8,.bound 9,.bound 10,.bound 11,.bound 12,.bound 13,.bound 14,
    .bound 15,.bound 16,.bound 17,.bound 18,.bound 19⟩

def rankDefData : RelationalData (Project.Term 28) :=
  ⟨.bound 20,.bound 21,.bound 22,.bound 23,.bound 24,.bound 25,.bound 26,.bound 27⟩

def rankDefEnv {M : SetTheory.Structure.{u}} (C : Context M.Domain) (D : RelationalData M.Domain)
    (zero one two FA α FP π : M.Domain) : Env M 28 :=
  ((((defEnv C D zero one two).push π).push FP).push α).push FA

private def bodyContext : Context (Project.Term 57) :=
  ⟨.bound 36,.bound 37,.bound 38,.bound 39,.bound 40,.bound 41,.bound 42,.bound 43,
    .bound 44,.bound 45,.bound 46,.bound 47,.bound 48⟩

private def bodyData : RelationalData (Project.Term 57) :=
  ⟨.bound 49,.bound 50,.bound 51,.bound 52,.bound 53,.bound 54,.bound 55,.bound 56⟩

private def bodyStage : StageWitness (Project.Term 57) :=
  ⟨.bound 21,.bound 20,.bound 19,.bound 18,.bound 17,.bound 16,.bound 15,.bound 14,.bound 13⟩

private def bodyRank : DefRankWitness (Project.Term 57) :=
  ⟨⟨.bound 12,.bound 11,.bound 10,.bound 9,.bound 8,.bound 7,.bound 6,.bound 5⟩,
    .bound 4,.bound 3,.bound 2,.bound 1,.bound 0⟩

private theorem bodyStage_freeClosed :
    (stageWitnessFormula bodyContext bodyData (.bound 33) (.bound 34) (.bound 35) (.bound 28) (.bound 25) bodyStage).FreeClosed := by
  unfold stageWitnessFormula
  simp only [Definitional.Formula.FreeClosed]
  refine ⟨spaceCertificateFormula_freeClosed _ _ _ _ rfl rfl rfl rfl,?_⟩
  simp [setRelationTableFormula,atomicTableFormula,productBoundedFormula,relationSupportFormula,
    atomValueFormula,setAtomFormula,Assignments.tupleValueFormula,
    evaluationFormula,truthFormula,finalTrueFormula,typedTruthFormula,
    defCertificateFormula,definedByFormula,definitionPointFormula,validColumnFormula,
    formulaProgramFormula,wellFormedProgramFormula,wellFormedAtFormula,scopedAtomFormula,
    evalFormula,atomicFormula,negationFormula,implicationFormula,universalFormula,
    instructionAtFormula,Assignments.updatedFormula,graphFormula,KP1Y.Cardinal.ontoFormula,
    KP1Y.Bounded.successorFormula,memPairFormula,codeFormula,pairFormula,
    StageWitness.context,StageWitness.data,Context.withInterpretation,RelationalData.withInterpretation,
    Context.weaken,Context.map,RelationalData.weaken,RelationalData.map,
    bodyContext,bodyData,bodyStage,Project.Formula.existsMem,Project.Formula.forallMem,Definitional.Formula.FreeClosed]

private def rankedCertificateBody : Project.Formula 1 57 :=
  .conj (codeFormula (.bound 27) (.bound 25) (.bound 22))
    (.conj (codeFormula (.bound 22) (.bound 24) (.bound 23))
      (rankedDefStageFormula bodyContext bodyData (.bound 33) (.bound 34) (.bound 35)
        (.bound 29) (.bound 28) (.bound 30) (.bound 31) (.bound 32) (.bound 25) (.bound 24) (.bound 23) bodyStage bodyRank))

private theorem rankedCertificateBody_freeClosed : rankedCertificateBody.FreeClosed := by
  simp only [rankedCertificateBody,rankedDefStageFormula,Definitional.Formula.FreeClosed]
  refine ⟨?_,?_,bodyStage_freeClosed,?_⟩
  · simp [codeFormula,pairFormula,Project.Formula.existsMem,Project.Formula.forallMem,Definitional.Formula.FreeClosed]
  · simp [codeFormula,pairFormula,Project.Formula.existsMem,Project.Formula.forallMem,Definitional.Formula.FreeClosed]
  · exact defRankWitnessFormula_freeClosed _ _ _ _ _ _ _ _ _ _ _ _ _ _
      rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
      ⟨⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩,rfl,rfl,rfl,rfl,rfl⟩

def rankedDefSuccessorMatrix : KP1Y.WitnessMatrix 28 where
  body := Project.Formula.existsMem (.bound 0) (
    Project.Formula.existsMem (.bound 1) (
    Project.Formula.existsMem (.bound 2) (
    Project.Formula.existsMem (.bound 3) (
    Project.Formula.existsMem (.bound 4) (
    Project.Formula.existsMem (.bound 5) (
    Project.Formula.existsMem (.bound 6) (
    Project.Formula.existsMem (.bound 7) (
    Project.Formula.existsMem (.bound 8) (
    Project.Formula.existsMem (.bound 9) (
    Project.Formula.existsMem (.bound 10) (
    Project.Formula.existsMem (.bound 11) (
    Project.Formula.existsMem (.bound 12) (
    Project.Formula.existsMem (.bound 13) (
    Project.Formula.existsMem (.bound 14) (
    Project.Formula.existsMem (.bound 15) (
    Project.Formula.existsMem (.bound 16) (
    Project.Formula.existsMem (.bound 17) (
    Project.Formula.existsMem (.bound 18) (
    Project.Formula.existsMem (.bound 19) (
    Project.Formula.existsMem (.bound 20) (
    Project.Formula.existsMem (.bound 21) (
    Project.Formula.existsMem (.bound 22) (
    Project.Formula.existsMem (.bound 23) (
    Project.Formula.existsMem (.bound 24) (
    Project.Formula.existsMem (.bound 25) (rankedCertificateBody))))))))))))))))))))))))))
  freeClosed := by simp [Project.Formula.existsMem,Definitional.Formula.FreeClosed,rankedCertificateBody_freeClosed]
  delta0 := .existsMem _ (.existsMem _ (.existsMem _ (.existsMem _ (.existsMem _ (.existsMem _ (.existsMem _ (.existsMem _ (.existsMem _ (.existsMem _ (.existsMem _ (.existsMem _ (.existsMem _ (.existsMem _ (.existsMem _ (.existsMem _ (.existsMem _ (.existsMem _ (.existsMem _ (.existsMem _ (.existsMem _ (.existsMem _ (.existsMem _ (.existsMem _ (.existsMem _ (.existsMem _ ((.conj (codeFormula_delta0 _ _ _) (.conj (codeFormula_delta0 _ _ _) (rankedDefStageFormula_delta0 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _)))))))))))))))))))))))))))))

def rankWitnessInBox (M : SetTheory.Structure.{u}) (W : DefRankWitness M.Domain) (B : M.Domain) : Prop :=
  M.mem W.sequences.ordWords B ∧ M.mem W.sequences.ordSpace B ∧ M.mem W.sequences.image B ∧ M.mem W.sequences.ordRank B ∧
    M.mem W.sequences.ceiling B ∧ M.mem W.sequences.ceilingWitness B ∧ M.mem W.sequences.rangeWitness B ∧ M.mem W.sequences.rowsWitness B ∧
    M.mem W.sequenceBound B ∧ M.mem W.sequenceRank B ∧ M.mem W.columnRank B ∧ M.mem W.productWitness B ∧ M.mem W.rowsWitness B

def RankedDefCertificate (M : SetTheory.Structure.{u}) (C : Context M.Domain) (D : RelationalData M.Domain)
    (zero one two FA A α FP π Out B : M.Domain) : Prop :=
  ∃ Def, M.mem Def B ∧ ∃ Γ, M.mem Γ B ∧ ∃ R, M.mem R B ∧ ∃ q, M.mem q B ∧
    ∃ SW : StageWitness M.Domain, SW.InBox M B ∧ ∃ RW : DefRankWitness M.Domain, rankWitnessInBox M RW B ∧
      Codes M Out Def q ∧ Codes M q Γ R ∧ RankedDefStage M C D zero one two FA A α FP π Def Γ R SW RW

theorem rankedDefSuccessorMatrix_iff {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    (e : Env M 28) (A Out B : M.Domain) :
    Project.Formula.satisfies (((e.push A).push Out).push B) rankedDefSuccessorMatrix.body ↔
      RankedDefCertificate M (rankDefContext.eval e) (rankDefData.eval e)
        (e.bound 4) (e.bound 5) (e.bound 6) (e.bound 0) A (e.bound 1) (e.bound 2) (e.bound 3) Out B := by
  simp only [rankedDefSuccessorMatrix,Project.Formula.satisfies_existsMem_iff,rankedCertificateBody,
    Project.Formula.satisfies_conj_iff,codeFormula_iff hM.1,rankedDefStageFormula_iff hM]
  constructor
  · rintro ⟨Def,hDef,Γ,hΓ,R,hR,q,hq,V,hV,SB,hSB,relTable,hrelTable,Atom,hAtom,Col,hCol,H,hH,Raw,hRaw,Sat,hSat,F,hF,
      OW,hOW,OS,hOS,I,hI,OR,hOR,C,hC,BC,hBC,BP,hBP,BG,hBG,β,hβ,FV,hFV,FC,hFC,PB,hPB,GB,hGB,hOut,hqCode,hStage⟩
    exact ⟨Def,hDef,Γ,hΓ,R,hR,q,hq,⟨V,SB,relTable,Atom,Col,H,Raw,Sat,F⟩,
      ⟨hV,hSB,hrelTable,hAtom,hCol,hH,hRaw,hSat,hF⟩,⟨⟨OW,OS,I,OR,C,BC,BP,BG⟩,β,FV,FC,PB,GB⟩,
      ⟨hOW,hOS,hI,hOR,hC,hBC,hBP,hBG,hβ,hFV,hFC,hPB,hGB⟩,hOut,hqCode,hStage⟩
  · rintro ⟨Def,hDef,Γ,hΓ,R,hR,q,hq,⟨V,SB,relTable,Atom,Col,H,Raw,Sat,F⟩,hSW,
      ⟨⟨OW,OS,I,OR,C,BC,BP,BG⟩,β,FV,FC,PB,GB⟩,hRW,hOut,hqCode,hStage⟩
    obtain ⟨hV,hSB,hrelTable,hAtom,hCol,hH,hRaw,hSat,hF⟩ := hSW
    obtain ⟨hOW,hOS,hI,hOR,hC,hBC,hBP,hBG,hβ,hFV,hFC,hPB,hGB⟩ := hRW
    exact ⟨Def,hDef,Γ,hΓ,R,hR,q,hq,V,hV,SB,hSB,relTable,hrelTable,Atom,hAtom,Col,hCol,H,hH,Raw,hRaw,Sat,hSat,F,hF,
      OW,hOW,OS,hOS,I,hI,OR,hOR,C,hC,BC,hBC,BP,hBP,BG,hBG,β,hβ,FV,hFV,FC,hFC,PB,hPB,GB,hGB,hOut,hqCode,hStage⟩

end KP1Y.SetLanguage
