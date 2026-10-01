import KP1Y.DefWitnessSyntax

/-! 固定语法的Def后继为全定义单值Σ₁关系：九个字段全部界于一个对象集合证书。 -/
namespace KP1Y.SetLanguage
open YesMetaZFC YesMetaZFC.SetTheory YesMetaZFC.SetTheory.Definitional
open KP1Y.Kuratowski KP1Y.Functions KP1Y.Sequences KP1Y.Satisfaction KP1Y.Definability
universe u

def defContext : Context (Project.Term 24) :=
  ⟨.bound 3,.bound 4,.bound 5,.bound 6,.bound 7,.bound 8,.bound 9,.bound 10,
    .bound 11,.bound 12,.bound 13,.bound 14,.bound 15⟩

def defData : RelationalData (Project.Term 24) :=
  ⟨.bound 16,.bound 17,.bound 18,.bound 19,.bound 20,.bound 21,.bound 22,.bound 23⟩

def defEnv {M : SetTheory.Structure.{u}} (C : Context M.Domain) (D : RelationalData M.Domain)
    (zero one two : M.Domain) : Env M 24 := (((syntaxEnv C D).push two).push one).push zero

private def bodyContext : Context (Project.Term 36) :=
  ⟨.bound 15,.bound 16,.bound 17,.bound 18,.bound 19,.bound 20,.bound 21,.bound 22,
    .bound 23,.bound 24,.bound 25,.bound 26,.bound 27⟩

private def bodyData : RelationalData (Project.Term 36) :=
  ⟨.bound 28,.bound 29,.bound 30,.bound 31,.bound 32,.bound 33,.bound 34,.bound 35⟩

private def bodyWitness : StageWitness (Project.Term 36) :=
  ⟨.bound 8,.bound 7,.bound 6,.bound 5,.bound 4,.bound 3,.bound 2,.bound 1,.bound 0⟩

private def defCertificateBody : Project.Formula 1 36 :=
  stageWitnessFormula bodyContext bodyData (.bound 12) (.bound 13) (.bound 14) (.bound 11) (.bound 10) bodyWitness

private theorem defCertificateBody_freeClosed : defCertificateBody.FreeClosed := by
  unfold defCertificateBody stageWitnessFormula
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
    bodyContext,bodyData,bodyWitness,Project.Formula.existsMem,Project.Formula.forallMem,Definitional.Formula.FreeClosed]

def defSuccessorMatrix : KP1Y.WitnessMatrix 24 where
  body := Project.Formula.existsMem (.bound 0) (Project.Formula.existsMem (.bound 1)
    (Project.Formula.existsMem (.bound 2) (Project.Formula.existsMem (.bound 3)
      (Project.Formula.existsMem (.bound 4) (Project.Formula.existsMem (.bound 5)
        (Project.Formula.existsMem (.bound 6) (Project.Formula.existsMem (.bound 7)
          (Project.Formula.existsMem (.bound 8) defCertificateBody))))))))
  freeClosed := by
    simp [Project.Formula.existsMem,Definitional.Formula.FreeClosed,defCertificateBody_freeClosed]
  delta0 := .existsMem _ (.existsMem _ (.existsMem _ (.existsMem _ (.existsMem _
    (.existsMem _ (.existsMem _ (.existsMem _ (.existsMem _ (stageWitnessFormula_delta0 _ _ _ _ _ _ _ _)))))))))

def StageWitness.InBox (M : SetTheory.Structure.{u}) (W : StageWitness M.Domain) (B : M.Domain) : Prop :=
  M.mem W.values B ∧ M.mem W.sequences B ∧ M.mem W.relation B ∧ M.mem W.atomic B ∧
    M.mem W.columns B ∧ M.mem W.table B ∧ M.mem W.raw B ∧ M.mem W.typed B ∧ M.mem W.definitions B

theorem defSuccessorMatrix_iff {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    (env : Env M 24) (A Def B : M.Domain) :
    Project.Formula.satisfies (((env.push A).push Def).push B) defSuccessorMatrix.body ↔
      ∃ W : StageWitness M.Domain, W.InBox M B ∧ W.Valid M (defContext.eval env) (defData.eval env)
        (env.bound 0) (env.bound 1) (env.bound 2) A Def := by
  simp only [defSuccessorMatrix,Project.Formula.satisfies_existsMem_iff,
    defCertificateBody,stageWitnessFormula_iff hM]
  constructor
  · rintro ⟨V,hV,SB,hSB,R,hR,Atom,hAtom,Col,hCol,H,hH,Raw,hRaw,Sat,hSat,F,hF,hValid⟩
    exact ⟨⟨V,SB,R,Atom,Col,H,Raw,Sat,F⟩,⟨hV,hSB,hR,hAtom,hCol,hH,hRaw,hSat,hF⟩,hValid⟩
  · rintro ⟨⟨V,SB,R,Atom,Col,H,Raw,Sat,F⟩,hBox,hValid⟩
    exact ⟨V,hBox.1,SB,hBox.2.1,R,hBox.2.2.1,Atom,hBox.2.2.2.1,Col,hBox.2.2.2.2.1,
      H,hBox.2.2.2.2.2.1,Raw,hBox.2.2.2.2.2.2.1,Sat,hBox.2.2.2.2.2.2.2.1,F,hBox.2.2.2.2.2.2.2.2,hValid⟩

private theorem fixed_list_container_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    (xs : List M.Domain) : ∃ B, ∀ x, x∈xs → M.mem x B := by
  induction xs with
  | nil =>
      obtain ⟨B,_⟩ := SetTheory.KP.exists_empty (KP1Y.models_weakKP hM)
      exact ⟨B,fun x hx => False.elim (List.not_mem_nil hx)⟩
  | cons a xs ih =>
      obtain ⟨B,hB⟩ := ih
      obtain ⟨B',hB'⟩ := SetTheory.KP.exists_insert (KP1Y.models_weakKP hM) B a
      refine ⟨B',?_⟩
      intro x hx
      rcases List.mem_cons.mp hx with he | hx
      · exact (hB' x).mpr (Or.inr he)
      · exact (hB' x).mpr (Or.inl (hB x hx))

theorem stage_witness_box_exists_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    (W : StageWitness M.Domain) : ∃ B, W.InBox M B := by
  obtain ⟨B,hB⟩ := fixed_list_container_d hM
    [W.values,W.sequences,W.relation,W.atomic,W.columns,W.table,W.raw,W.typed,W.definitions]
  refine ⟨B,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩ <;> apply hB <;> simp

theorem def_successor_matrix_total_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    (env : Env M 24) (hS : FixedSyntax M (defContext.eval env) (defData.eval env)
      (env.bound 0) (env.bound 1) (env.bound 2)) (A : M.Domain) :
    ∃ Def B, Project.Formula.satisfies (((env.push A).push Def).push B) defSuccessorMatrix.body := by
  obtain ⟨Def,W,hW⟩ := stage_witness_exists_d hM hS A
  obtain ⟨B,hB⟩ := stage_witness_box_exists_d hM W
  exact ⟨Def,B,(defSuccessorMatrix_iff hM env A Def B).mpr ⟨W,hB,hW⟩⟩

theorem def_successor_matrix_functional_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    (env : Env M 24) (hS : FixedSyntax M (defContext.eval env) (defData.eval env)
      (env.bound 0) (env.bound 1) (env.bound 2)) {A Def Def' B B' : M.Domain}
    (h : Project.Formula.satisfies (((env.push A).push Def).push B) defSuccessorMatrix.body)
    (h' : Project.Formula.satisfies (((env.push A).push Def').push B') defSuccessorMatrix.body) : Def=Def' := by
  obtain ⟨W,_,hW⟩ := (defSuccessorMatrix_iff hM env A Def B).mp h
  obtain ⟨W',_,hW'⟩ := (defSuccessorMatrix_iff hM env A Def' B').mp h'
  exact hW.output_unique_d hM hS.interpretation.spaces.omega hS.spaces.omega hW'

end KP1Y.SetLanguage
