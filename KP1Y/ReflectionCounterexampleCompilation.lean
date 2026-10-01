import KP1Y.ReflectionTemplateTruth

/-! 真正的统一反例公式：∃输入标签 (Demand ∧ ¬∃输出标签 Response)。 -/
namespace KP1Y.ReflectionModel
open YesMetaZFC YesMetaZFC.SetTheory
open KP1Y.Kuratowski KP1Y.Functions KP1Y.Assignments KP1Y.Satisfaction
universe u

def TemplateOutputExists (M : SetTheory.Structure.{u}) (PC : Context M.Domain) (D : RelationalData M.Domain)
    (T : TemplateShape M.Domain) (V : NameFrame M.Domain) (B : TemplateBlocks M.Domain) (s : M.Domain) : Prop :=
  ∃ t, M.mem t PC.assignments ∧ AgreeOutside M V.outputs T.width s t V.scope PC.carrier ∧ OutputTemplate M PC D T B t

def TemplateCounterexample (M : SetTheory.Structure.{u}) (C : ArticleData M.Domain) (PC : Context M.Domain)
    (D : RelationalData M.Domain) (T : TemplateShape M.Domain) (V : NameFrame M.Domain) (B : TemplateBlocks M.Domain) (s : M.Domain) : Prop :=
  ∃ t, M.mem t PC.assignments ∧ AgreeOutside M V.inputs T.width s t V.scope PC.carrier ∧
    InputTemplate M C PC D T B t ∧ ¬TemplateOutputExists M PC D T V B t

structure UniformCounterexampleProgram (M : SetTheory.Structure.{u}) (C : ArticleData M.Domain)
    (S : ArticleStructure M.Domain) (T : TemplateShape M.Domain) (V : NameFrame M.Domain)
    (B : TemplateBlocks M.Domain) (p length head : M.Domain) : Prop where
  result : FormulaResult M S.context S.relations p length head V.scope
  truth : ∀ A Assignments Columns Atom H, EvaluationInstance M S.context A Assignments Columns Atom H →
    ∀ s, Graph M s V.scope A → (NodeTrue M (S.context.withInterpretation A Assignments Columns Atom) H p head s ↔
      TemplateCounterexample M C (S.context.withInterpretation A Assignments Columns Atom) S.relations T V B s)

theorem uniform_counterexample_program_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ArticleData M.Domain} (hC : C.Valid M) {S : ArticleStructure M.Domain} (hS : S.Valid M C)
    {T : TemplateShape M.Domain} (hT : T.Valid M C) {F : M.Domain} {V : NameFrame M.Domain}
    (hV : V.Valid M C F T.width T.edgeLength T.needLength) {K : M.Domain} {B : TemplateBlocks M.Domain}
    (hB : B.Valid M C S.relations T V K) : ∃ p length head, UniformCounterexampleProgram M C S T V B p length head := by
  have hb : M.mem V.scope S.context.omega := Eq.mpr (congrArg (M.mem V.scope) hS.omega) hV.scope
  have hm : M.mem T.width S.context.omega := Eq.mpr (congrArg (M.mem T.width) hS.omega) hV.width
  obtain ⟨seed,ns,js,hSeed⟩ := basic_seed_exists_d hM hC hS hV hB.basic
  obtain ⟨p0,n0,j0,h0,u0⟩ := uniform_input_template_d hM hC hS hT hV hB hSeed
  obtain ⟨p1,n1,j1,h1,u1⟩ := uniform_output_template_d hM hC hS hT hV hB h0.result
  obtain ⟨p2,n2,j2,h2,truth2⟩ := uniform_compile_existential_block_d hM hS.context h1.result hV.outputs.graph hm
  obtain ⟨p3,n3,h3,truth3⟩ := uniform_compile_negation_d hM hS.context h2.wellFormed h2.successor.predecessor_mem
  have hBefore := (h1.trans hM.1 h2).trans hM.1 h3
  have hj0 := prefix_domain_subset hM.1 hBefore.prefixGraph hBefore.wellFormed.graph j0 h0.successor.predecessor_mem
  obtain ⟨p4,n4,j4,h4,truth4⟩ := uniform_compile_conjunction_d hM hS.context h3.wellFormed hj0 h3.successor.predecessor_mem
  have hBody (A Assignments Columns Atom H : M.Domain) (hI : EvaluationInstance M S.context A Assignments Columns Atom H)
      (s : M.Domain) (hAssign : Graph M s V.scope A) :
      NodeTrue M (S.context.withInterpretation A Assignments Columns Atom) H p4 j4 s ↔
        InputTemplate M C (S.context.withInterpretation A Assignments Columns Atom) S.relations T B s ∧
          ¬TemplateOutputExists M (S.context.withInterpretation A Assignments Columns Atom) S.relations T V B s := by
    have hs := (hI.assignments_exact s).mpr ⟨V.scope,hb,hAssign⟩
    have hIn := ((hBefore.withInterpretation A Assignments Columns Atom).old_node hM (hI.contextSpaces hS.context) hI.table
      h0.wellFormed.length_nat h0.successor.predecessor_mem hs).symm.trans (u0.truth A Assignments Columns Atom H hI s hs)
    have hOut : NodeTrue M (S.context.withInterpretation A Assignments Columns Atom) H p2 j2 s ↔
        TemplateOutputExists M (S.context.withInterpretation A Assignments Columns Atom) S.relations T V B s := by
      apply (truth2 A Assignments Columns Atom H hI s hAssign).trans
      exact ⟨fun ⟨t,ht,hFrame,hTrue⟩ => ⟨t,ht,hFrame,(u1.truth A Assignments Columns Atom H hI t ht).mp hTrue⟩,
        fun ⟨t,ht,hFrame,hTrue⟩ => ⟨t,ht,hFrame,(u1.truth A Assignments Columns Atom H hI t ht).mpr hTrue⟩⟩
    exact (truth4 A Assignments Columns Atom H hI s hs).trans
      (and_congr hIn ((truth3 A Assignments Columns Atom H hI s hs).trans (not_congr hOut)))
  obtain ⟨p5,n5,j5,h5,truth5⟩ := uniform_compile_existential_block_d hM hS.context h4.result hV.inputs.graph hm
  refine ⟨p5,n5,j5,h5.result,?_⟩
  intro A Assignments Columns Atom H hI s hAssign
  apply (truth5 A Assignments Columns Atom H hI s hAssign).trans
  exact ⟨fun ⟨t,ht,hFrame,hTrue⟩ => ⟨t,ht,hFrame,(hBody A Assignments Columns Atom H hI t hFrame.target).mp hTrue⟩,
    fun ⟨t,ht,hFrame,hTrue⟩ => ⟨t,ht,hFrame,(hBody A Assignments Columns Atom H hI t hFrame.target).mpr hTrue⟩⟩

theorem UniformCounterexampleProgram.reflect_d {M : SetTheory.Structure.{u}}
    {C : ArticleData M.Domain} {S : ArticleStructure M.Domain} (hS : S.Valid M C)
    {δ : M.Domain} {small : EvaluationData M.Domain} (h : Height M C S δ small)
    {T : TemplateShape M.Domain} {V : NameFrame M.Domain} {B : TemplateBlocks M.Domain} {p length head s : M.Domain}
    (hP : UniformCounterexampleProgram M C S T V B p length head) (hAssign : Graph M s V.scope small.carrier) :
    TemplateCounterexample M C (small.context S.context) S.relations T V B s ↔
      TemplateCounterexample M C (S.large.context S.context) S.relations T V B s :=
  (hP.truth small.carrier small.assignments small.columns small.atomic small.table h.valid s hAssign).symm.trans
    ((h.elementary.truth p length head V.scope hP.result s hAssign).trans
      (hP.truth S.large.carrier S.large.assignments S.large.columns S.large.atomic S.large.table hS.large s
        (hAssign.mono_values h.elementary.carrier_subset)))

end KP1Y.ReflectionModel
