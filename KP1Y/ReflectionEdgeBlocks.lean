import KP1Y.ReflectionRelationCode
import KP1Y.ReflectionGroundParameters

/-! 每条内部图边直接生成四元 R 原子；图边层号没有当前 K 的限制。 -/
namespace KP1Y.ReflectionModel
open YesMetaZFC YesMetaZFC.SetTheory YesMetaZFC.SetTheory.Definitional
open KP1Y.Kuratowski KP1Y.Functions KP1Y.Reflection KP1Y.Satisfaction
universe u

private def edgeCodeTerms : ArticleData (Project.Term 39) := articleTerms.weaken.weaken.weaken.weaken.weaken.weaken.weaken.weaken.weaken.weaken.weaken.weaken.weaken.weaken.weaken

private theorem edgeCodeTerms_closed : edgeCodeTerms.Closed := by
  constructor
  · constructor <;> rfl
  all_goals first | rfl | (intro i; rfl)

private def edgeBlockSchema : Project.Delta0BinarySchema 29 where
  body := Project.Formula.existsMem (.bound 7) (Project.Formula.existsMem (.bound 8)
    (Project.Formula.existsMem (.bound 9) (Project.Formula.existsMem (.bound 10)
      (Project.Formula.existsMem (.bound 9) (Project.Formula.existsMem (.bound 10)
        (Project.Formula.existsMem (.bound 11) (Project.Formula.existsMem (.bound 12)
          (.conj (edgeEntryFormula edgeCodeTerms.reflection (.bound 10) (.bound 9) (.bound 7) (.bound 6) (.bound 5) (.bound 4))
            (.conj (memPairFormula (.bound 11) (.bound 9) (.bound 3))
              (.conj (memPairFormula (.bound 12) (.bound 6) (.bound 2))
                (.conj (memPairFormula (.bound 12) (.bound 5) (.bound 1))
                  (.conj (memPairFormula (.bound 12) (.bound 4) (.bound 0))
                    (relationCodeFormula (edgeCodeTerms.numbers 0) (edgeCodeTerms.numbers 1)
                      (edgeCodeTerms.numbers 2) (edgeCodeTerms.numbers 3) (edgeCodeTerms.numbers 4)
                      (.bound 14) (.bound 13) (.bound 3) (.bound 2) (.bound 1) (.bound 0) (.bound 8))))))))))))))
  freeClosed := by
    have hEntry := edgeEntryFormula_freeClosed edgeCodeTerms_closed.reflection
      (.bound 10) (.bound 9) (.bound 7) (.bound 6) (.bound 5) (.bound 4) rfl rfl rfl rfl rfl rfl
    have hCode := relationCodeFormula_freeClosed (edgeCodeTerms.numbers 0) (edgeCodeTerms.numbers 1)
      (edgeCodeTerms.numbers 2) (edgeCodeTerms.numbers 3) (edgeCodeTerms.numbers 4)
      (.bound 14) (.bound 13) (.bound 3) (.bound 2) (.bound 1) (.bound 0) (.bound 8)
      (edgeCodeTerms_closed.numbers 0) (edgeCodeTerms_closed.numbers 1) (edgeCodeTerms_closed.numbers 2)
      (edgeCodeTerms_closed.numbers 3) (edgeCodeTerms_closed.numbers 4) rfl rfl rfl rfl rfl rfl rfl
    simp [Project.Formula.existsMem,Definitional.Formula.FreeClosed,memPairFormula,codeFormula,pairFormula,
      Project.Formula.forallMem,hEntry,hCode]
  delta0 := .existsMem _ (.existsMem _ (.existsMem _ (.existsMem _ (.existsMem _ (.existsMem _ (.existsMem _ (.existsMem _
    (.conj (edgeEntryFormula_delta0 _ _ _ _ _ _ _) (.conj (memPairFormula_delta0 _ _ _)
      (.conj (memPairFormula_delta0 _ _ _) (.conj (memPairFormula_delta0 _ _ _)
        (.conj (memPairFormula_delta0 _ _ _) (relationCodeFormula_delta0 _ _ _ _ _ _ _ _ _ _ _ _)))))))))))))

def EdgeCode (M : SetTheory.Structure.{u}) (C : ArticleData M.Domain)
    (Variables scope names layers diagram i code : M.Domain) : Prop :=
  ∃ k, M.mem k C.reflection.omega ∧ ∃ q, M.mem q C.reflection.omega ∧
    ∃ p, M.mem p C.reflection.omega ∧ ∃ j, M.mem j C.reflection.omega ∧
      ∃ uk, M.mem uk scope ∧ ∃ uq, M.mem uq scope ∧ ∃ up, M.mem up scope ∧ ∃ uj, M.mem uj scope ∧
        EdgeEntry M C.reflection diagram i k q p j ∧ MemPair M layers i uk ∧
          MemPair M names q uq ∧ MemPair M names p up ∧ MemPair M names j uj ∧
            RelationCode M (C.numbers 0) (C.numbers 1) (C.numbers 2) (C.numbers 3) (C.numbers 4)
              Variables scope uk uq up uj code

private theorem edgeBlockSchema_iff {M : SetTheory.Structure.{u}} (he : Extensional M)
    (C : ArticleData M.Domain) (Variables scope names layers diagram i code : M.Domain) :
    Project.Formula.satisfies ((((((((articleEnv C).push Variables).push scope).push names).push layers).push diagram).push i).push code)
      edgeBlockSchema.body ↔ EdgeCode M C Variables scope names layers diagram i code := by
  simp only [edgeBlockSchema,Project.Formula.satisfies_existsMem_iff,Project.Formula.satisfies_conj_iff,
    edgeEntryFormula_iff he,memPairFormula_iff he,relationCodeFormula_iff he]
  rfl

structure EdgeBlock (M : SetTheory.Structure.{u}) (C : ArticleData M.Domain) (D : RelationalData M.Domain)
    (T : TemplateShape M.Domain) (scope names layers B : M.Domain) : Prop where
  variables : Graph M names T.width scope
  layerVariables : Graph M layers T.edgeLength scope
  graph : Graph M B T.edgeLength D.codes
  rows : ∀ i code, MemPair M B i code ↔ M.mem i T.edgeLength ∧ EdgeCode M C D.variables scope names layers T.diagram i code

theorem edge_block_exists_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ArticleData M.Domain} (hC : C.Valid M) {A : M.Domain} {D : RelationalData M.Domain}
    (hD : ArticleInterpretation M C A D) {T : TemplateShape M.Domain} (hT : T.Valid M C)
    {scope names layers : M.Domain} (hs : M.mem scope D.omega)
    (hNames : Graph M names T.width scope) (hLayers : Graph M layers T.edgeLength scope) :
    ∃ B, EdgeBlock M C D T scope names layers B := by
  let e := (((((articleEnv C).push D.variables).push scope).push names).push layers).push T.diagram
  obtain ⟨B,hSupport,hRaw⟩ := relation_comprehension_d hM edgeBlockSchema e T.edgeLength D.codes
  have hRows (i code : M.Domain) : MemPair M B i code ↔
      M.mem i T.edgeLength ∧ EdgeCode M C D.variables scope names layers T.diagram i code := by
    have h := hRaw i code
    rw [edgeBlockSchema_iff hM.1] at h
    refine h.trans ⟨fun h => ⟨h.1,h.2.2⟩,?_⟩
    rintro ⟨hi,hCode⟩
    obtain ⟨k,hk,q,hq,p,hp,j,hj,uk,huk,uq,huq,up,hup,uj,huj,hEntry,hL,hQ,hP,hJ,hRel⟩ := hCode
    exact ⟨hi,hRel.code_mem_d hM hC hD hs,k,hk,q,hq,p,hp,j,hj,uk,huk,uq,huq,up,hup,uj,huj,hEntry,hL,hQ,hP,hJ,hRel⟩
  refine ⟨B,hNames,hLayers,⟨hSupport,?_,?_⟩,hRows⟩
  · intro i hi
    obtain ⟨k,q,p,j,hEntry⟩ := edge_entry_exists hC.reflection hT.edges hi
    have hiω := (KP1Y.Naturals.omega_isOrdinal_d hM hC.numerals.omega).transitive T.edgeLength hT.edgeLength i hi
    obtain ⟨hk,hq,hp,hj⟩ := (hEntry.occurs hiω).bounds hM.1 hC.reflection
    obtain ⟨hqW,hpW,hjW⟩ := hT.edge_columns_d hM hC hEntry
    obtain ⟨uk,huk,hL⟩ := hLayers.total i hi
    obtain ⟨uq,huq,hQ⟩ := hNames.total q hqW
    obtain ⟨up,hup,hP⟩ := hNames.total p hpW
    obtain ⟨uj,huj,hJ⟩ := hNames.total j hjW
    obtain ⟨code,hRel⟩ := relation_code_exists_d hM hC hD hs huk huq hup huj
    exact ⟨code,hRel.code_mem_d hM hC hD hs,(hRows i code).mpr
      ⟨hi,k,hk,q,hq,p,hp,j,hj,uk,huk,uq,huq,up,hup,uj,huj,hEntry,hL,hQ,hP,hJ,hRel⟩⟩
  · intro i code code' hAt hAt'
    obtain ⟨_,k,_,q,_,p,_,j,_,uk,_,uq,_,up,_,uj,_,hEntry,hL,hQ,hP,hJ,hRel⟩ := (hRows i code).mp hAt
    obtain ⟨_,k',_,q',_,p',_,j',_,uk',_,uq',_,up',_,uj',_,hEntry',hL',hQ',hP',hJ',hRel'⟩ := (hRows i code').mp hAt'
    obtain ⟨hkk,hqq,hpp,hjj⟩ := hEntry.unique hM.1 hT.edges hEntry'
    subst k'
    subst q'
    subst p'
    subst j'
    have hUk := hLayers.unique i uk' uk hL' hL
    have hUq := hNames.unique q uq' uq hQ' hQ
    have hUp := hNames.unique p up' up hP' hP
    have hUj := hNames.unique j uj' uj hJ' hJ
    subst uk'
    subst uq'
    subst up'
    subst uj'
    exact hRel.unique_d hM hC hRel'

theorem EdgeBlock.at_entry_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ArticleData M.Domain} {D : RelationalData M.Domain} {T : TemplateShape M.Domain} (hT : T.Valid M C)
    {scope names layers B i code k q p j : M.Domain} (hB : EdgeBlock M C D T scope names layers B)
    (hAt : MemPair M B i code) (hEntry : EdgeEntry M C.reflection T.diagram i k q p j) :
    ∃ uk, M.mem uk scope ∧ ∃ uq, M.mem uq scope ∧ ∃ up, M.mem up scope ∧ ∃ uj, M.mem uj scope ∧
      MemPair M layers i uk ∧ MemPair M names q uq ∧ MemPair M names p up ∧ MemPair M names j uj ∧
        RelationCode M (C.numbers 0) (C.numbers 1) (C.numbers 2) (C.numbers 3) (C.numbers 4)
          D.variables scope uk uq up uj code := by
  obtain ⟨_,k',_,q',_,p',_,j',_,uk,huk,uq,huq,up,hup,uj,huj,hEntry',hL,hQ,hP,hJ,hRel⟩ := (hB.rows i code).mp hAt
  obtain ⟨hkk,hqq,hpp,hjj⟩ := hEntry.unique hM.1 hT.edges hEntry'
  subst k'
  subst q'
  subst p'
  subst j'
  exact ⟨uk,huk,uq,huq,up,hup,uj,huj,hL,hQ,hP,hJ,hRel⟩

theorem EdgeBlock.scoped_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ArticleData M.Domain} (hC : C.Valid M) {A : M.Domain} {D : RelationalData M.Domain}
    (hD : ArticleInterpretation M C A D) {T : TemplateShape M.Domain}
    {scope names layers B i code : M.Domain} (hs : M.mem scope D.omega)
    (hB : EdgeBlock M C D T scope names layers B) (hAt : MemPair M B i code) : ScopedAtom M D code scope := by
  obtain ⟨_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,hRel⟩ := (hB.rows i code).mp hAt
  exact hRel.scoped_d hM hC hD hs

theorem shape_edge_blocks_exists_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ArticleData M.Domain} (hC : C.Valid M) {A : M.Domain} {D : RelationalData M.Domain}
    (hD : ArticleInterpretation M C A D) {T : TemplateShape M.Domain} (hT : T.Valid M C)
    {F : M.Domain} {V : NameFrame M.Domain} (hV : V.Valid M C F T.width T.edgeLength T.needLength) :
    ∃ BI BO, EdgeBlock M C D T V.scope V.inputs V.edgeLayers BI ∧ EdgeBlock M C D T V.scope V.outputs V.edgeLayers BO := by
  have hs : M.mem V.scope D.omega := Eq.mpr (congrArg (M.mem V.scope) hD.omega) hV.scope
  obtain ⟨BI,hBI⟩ := edge_block_exists_d hM hC hD hT hs hV.inputs.graph hV.edgeLayers.graph
  obtain ⟨BO,hBO⟩ := edge_block_exists_d hM hC hD hT hs hV.outputs.graph hV.edgeLayers.graph
  exact ⟨BI,BO,hBI,hBO⟩

end KP1Y.ReflectionModel
