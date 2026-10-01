import KP1Y.ReflectionRelationCodeTruth
import KP1Y.ReflectionGroundParameters

/-! 端点模板的实际内部有限原子块；top=true 使用 P，top=false 使用 R。 -/
namespace KP1Y.ReflectionModel
open YesMetaZFC YesMetaZFC.SetTheory YesMetaZFC.SetTheory.Definitional
open KP1Y.Kuratowski KP1Y.Functions KP1Y.Satisfaction KP1Y.Reflection KP1Y.Ranking
universe u

def EndpointCode (top : Bool) (M : SetTheory.Structure.{u}) (C : ArticleData M.Domain) (D : RelationalData M.Domain)
    (scope uk uq up point code : M.Domain) : Prop :=
  if top then TopCode M (C.numbers 0) (C.numbers 1) (C.numbers 2) (C.numbers 3) D.variables scope uk uq up code
  else RelationCode M (C.numbers 0) (C.numbers 1) (C.numbers 2) (C.numbers 3) (C.numbers 4) D.variables scope uk uq up point code

private theorem endpoint_code_exists_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory) {C : ArticleData M.Domain} (hC : C.Valid M)
    {A : M.Domain} {D : RelationalData M.Domain} (hD : ArticleInterpretation M C A D) (top : Bool)
    {scope uk uq up point : M.Domain} (hs : M.mem scope D.omega) (hk : M.mem uk scope)
    (hq : M.mem uq scope) (hp : M.mem up scope) (ha : M.mem point scope) :
    ∃ code, EndpointCode top M C D scope uk uq up point code := by
  cases top
  · exact relation_code_exists_d hM hC hD hs hk hq hp ha
  · exact top_code_exists_d hM hC hD hs hk hq hp

theorem EndpointCode.unique_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory) {C : ArticleData M.Domain} (hC : C.Valid M)
    {D : RelationalData M.Domain} {top : Bool} {scope uk uq up point code code' : M.Domain}
    (h : EndpointCode top M C D scope uk uq up point code) (h' : EndpointCode top M C D scope uk uq up point code') : code=code' := by
  cases top
  · exact RelationCode.unique_d hM hC h h'
  · exact TopCode.unique_d hM hC h h'

theorem EndpointCode.scoped_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory) {C : ArticleData M.Domain} (hC : C.Valid M)
    {A : M.Domain} {D : RelationalData M.Domain} (hD : ArticleInterpretation M C A D) {top : Bool}
    {scope uk uq up point code : M.Domain} (hs : M.mem scope D.omega)
    (h : EndpointCode top M C D scope uk uq up point code) : ScopedAtom M D code scope := by
  cases top
  · exact RelationCode.scoped_d hM hC hD hs h
  · exact TopCode.scoped_d hM hC hD hs h

theorem EndpointCode.code_mem_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory) {C : ArticleData M.Domain} (hC : C.Valid M)
    {A : M.Domain} {D : RelationalData M.Domain} (hD : ArticleInterpretation M C A D) {top : Bool}
    {scope uk uq up point code : M.Domain} (hs : M.mem scope D.omega)
    (h : EndpointCode top M C D scope uk uq up point code) : M.mem code D.codes :=
  (h.scoped_d hM hC hD hs).code_mem hD.spaces

structure EndpointBlock (top : Bool) (M : SetTheory.Structure.{u}) (C : ArticleData M.Domain) (D : RelationalData M.Domain)
    (T : TemplateShape M.Domain) (V : NameFrame M.Domain) (names point B : M.Domain) : Prop where
  nameGraph : Graph M names T.width V.scope
  layers : Graph M V.needLayers T.needLength V.scope
  graph : Graph M B T.needLength D.codes
  rows : ∀ i k q p, NeedEntry M C.reflection T.template i k q p → ∀ uk uq up,
    MemPair M V.needLayers i uk → MemPair M names q uq → MemPair M names p up →
    ∀ code, MemPair M B i code ↔ EndpointCode top M C D V.scope uk uq up point code

private def endpointCodeFormula {d : Nat} (top : Bool) (zero one two three four Variables scope uk uq up point code : Project.Term d) : Project.Formula 1 d :=
  if top then topCodeFormula zero one two three Variables scope uk uq up code
  else relationCodeFormula zero one two three four Variables scope uk uq up point code

private theorem endpointCodeFormula_delta0 {d : Nat} (top : Bool)
    (zero one two three four Variables scope uk uq up point code : Project.Term d) :
    (endpointCodeFormula top zero one two three four Variables scope uk uq up point code).IsDelta0 := by
  cases top
  · exact relationCodeFormula_delta0 _ _ _ _ _ _ _ _ _ _ _ _
  · exact topCodeFormula_delta0 _ _ _ _ _ _ _ _ _ _

private def endpointSchema (top : Bool) : Project.Delta0BinarySchema 14 where
  body := Project.Formula.existsMem (.bound 6) (Project.Formula.existsMem (.bound 6)
    (Project.Formula.existsMem (.bound 7) (Project.Formula.existsMem (.bound 12)
      (Project.Formula.existsMem (.bound 13) (Project.Formula.existsMem (.bound 14)
        (.conj (Project.Formula.existsMem (.bound 14) (.conj (memPairFormula (.bound 14) (.bound 8) (.bound 0))
            (packetFormula (.bound 0) (.bound 6) (.bound 5) (.bound 4))))
          (.conj (memPairFormula (.bound 10) (.bound 7) (.bound 2))
            (.conj (memPairFormula (.bound 9) (.bound 4) (.bound 1))
              (.conj (memPairFormula (.bound 9) (.bound 3) (.bound 0))
                (endpointCodeFormula top (.bound 17) (.bound 18) (.bound 19) (.bound 20) (.bound 21)
                  (.bound 16) (.bound 15) (.bound 2) (.bound 1) (.bound 0) (.bound 8) (.bound 6)))))))))))
  freeClosed := by
    cases top <;> simp [endpointCodeFormula,topCodeFormula,relationCodeFormula,memPairFormula,packetFormula,
      codeFormula,pairFormula,graphFormula,Project.Formula.existsMem,Project.Formula.forallMem,Definitional.Formula.FreeClosed]
  delta0 := .existsMem _ (.existsMem _ (.existsMem _ (.existsMem _ (.existsMem _ (.existsMem _
    (.conj (.existsMem _ (.conj (memPairFormula_delta0 _ _ _) (packetFormula_delta0 _ _ _ _)))
      (.conj (memPairFormula_delta0 _ _ _) (.conj (memPairFormula_delta0 _ _ _)
        (.conj (memPairFormula_delta0 _ _ _) (endpointCodeFormula_delta0 _ _ _ _ _ _ _ _ _ _ _ _ _))))))))))

theorem endpoint_block_exists_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory) {C : ArticleData M.Domain} (hC : C.Valid M)
    {A : M.Domain} {D : RelationalData M.Domain} (hD : ArticleInterpretation M C A D) (top : Bool)
    {T : TemplateShape M.Domain} (hT : T.Valid M C) {V : NameFrame M.Domain} {names point : M.Domain}
    (hs : M.mem V.scope D.omega) (hNames : Graph M names T.width V.scope)
    (hLayers : Graph M V.needLayers T.needLength V.scope) (hPoint : M.mem point V.scope) :
    ∃ B, EndpointBlock top M C D T V names point B := by
  let e := (((((((((((((oneEnv (C.numbers 4)).push (C.numbers 3)).push (C.numbers 2)).push (C.numbers 1)).push (C.numbers 0)).push D.variables).push V.scope).push C.reflection.needCodes).push T.template).push C.reflection.omega).push T.width).push V.needLayers).push names).push point
  have hφ (i code : M.Domain) : Project.Formula.satisfies ((e.push i).push code) (endpointSchema top).body ↔
      ∃ k, M.mem k C.reflection.omega ∧ ∃ q, M.mem q T.width ∧ ∃ p, M.mem p T.width ∧
        ∃ uk, M.mem uk V.scope ∧ ∃ uq, M.mem uq V.scope ∧ ∃ up, M.mem up V.scope ∧
          NeedEntry M C.reflection T.template i k q p ∧ MemPair M V.needLayers i uk ∧ MemPair M names q uq ∧ MemPair M names p up ∧
            EndpointCode top M C D V.scope uk uq up point code := by
    cases top <;> simp only [endpointSchema,endpointCodeFormula,EndpointCode,Bool.false_eq_true,↓reduceIte,
      Project.Formula.satisfies_existsMem_iff,Project.Formula.satisfies_conj_iff,memPairFormula_iff hM.1,
      packetFormula_iff hM.1,relationCodeFormula_iff hM.1,topCodeFormula_iff hM.1] <;> rfl
  obtain ⟨B,hSupport,hRaw⟩ := relation_comprehension_d hM (endpointSchema top) e T.needLength D.codes
  have hRows (i code : M.Domain) : MemPair M B i code ↔ M.mem i T.needLength ∧ M.mem code D.codes ∧
      ∃ k, M.mem k C.reflection.omega ∧ ∃ q, M.mem q T.width ∧ ∃ p, M.mem p T.width ∧
        ∃ uk, M.mem uk V.scope ∧ ∃ uq, M.mem uq V.scope ∧ ∃ up, M.mem up V.scope ∧
          NeedEntry M C.reflection T.template i k q p ∧ MemPair M V.needLayers i uk ∧ MemPair M names q uq ∧ MemPair M names p up ∧
            EndpointCode top M C D V.scope uk uq up point code := by
    simpa only [hφ] using hRaw i code
  have hω := KP1Y.Naturals.omega_isOrdinal_d hM hC.numerals.omega
  have readCode (i k q p uk uq up code : M.Domain) (hEntry : NeedEntry M C.reflection T.template i k q p)
      (hk : MemPair M V.needLayers i uk) (hq : MemPair M names q uq) (hp : MemPair M names p up) :
      MemPair M B i code ↔ EndpointCode top M C D V.scope uk uq up point code := by
    constructor
    · intro hAt
      obtain ⟨_,_,k',_,q',_,p',_,uk',_,uq',_,up',_,hEntry',hk',hq',hp',hCode⟩ := (hRows i code).mp hAt
      obtain ⟨rfl,rfl,rfl⟩ := hEntry.unique hM.1 hT.needs hEntry'
      have hkk' := hLayers.unique i uk uk' hk hk'
      have hqq' := hNames.unique q uq uq' hq hq'
      have hpp' := hNames.unique p up up' hp hp'
      subst uk'
      subst uq'
      subst up'
      exact hCode
    · intro hCode
      have hi := hT.need_index hM.1 hEntry
      have hkω := ((hEntry.occurs (hω.transitive T.needLength hT.needLength i hi)).bounds hM.1 hC.reflection).1
      obtain ⟨hqW,hpW⟩ := hT.need_columns_d hM hC hEntry
      exact (hRows i code).mpr ⟨hi,hCode.code_mem_d hM hC hD hs,k,hkω,q,hqW,p,hpW,
        uk,(hLayers.bounds hM.1 hk).2,uq,(hNames.bounds hM.1 hq).2,up,(hNames.bounds hM.1 hp).2,hEntry,hk,hq,hp,hCode⟩
  have hGraph : Graph M B T.needLength D.codes := by
    refine ⟨hSupport,?_,?_⟩
    · intro i hi
      obtain ⟨k,q,p,hEntry⟩ := need_entry_exists hC.reflection hT.needs hi
      obtain ⟨hqW,hpW⟩ := hT.need_columns_d hM hC hEntry
      obtain ⟨uk,huk,hk⟩ := hLayers.total i hi
      obtain ⟨uq,huq,hq⟩ := hNames.total q hqW
      obtain ⟨up,hup,hp⟩ := hNames.total p hpW
      obtain ⟨code,hCode⟩ := endpoint_code_exists_d hM hC hD top hs huk huq hup hPoint
      exact ⟨code,hCode.code_mem_d hM hC hD hs,(readCode i k q p uk uq up code hEntry hk hq hp).mpr hCode⟩
    · intro i code code' hi hi'
      have hIndex := ((hRows i code).mp hi).1
      obtain ⟨k,q,p,hEntry⟩ := need_entry_exists hC.reflection hT.needs hIndex
      obtain ⟨hqW,hpW⟩ := hT.need_columns_d hM hC hEntry
      obtain ⟨uk,_,hk⟩ := hLayers.total i hIndex
      obtain ⟨uq,_,hq⟩ := hNames.total q hqW
      obtain ⟨up,_,hp⟩ := hNames.total p hpW
      exact ((readCode i k q p uk uq up code hEntry hk hq hp).mp hi).unique_d hM hC
        ((readCode i k q p uk uq up code' hEntry hk hq hp).mp hi')
  exact ⟨B,hNames,hLayers,hGraph,fun i k q p hEntry uk uq up hk hq hp code => readCode i k q p uk uq up code hEntry hk hq hp⟩

theorem EndpointBlock.scoped_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory) {C : ArticleData M.Domain} (hC : C.Valid M)
    {A : M.Domain} {D : RelationalData M.Domain} (hD : ArticleInterpretation M C A D)
    {T : TemplateShape M.Domain} (hT : T.Valid M C) {V : NameFrame M.Domain} {top : Bool} {names point B : M.Domain}
    (hs : M.mem V.scope D.omega) (h : EndpointBlock top M C D T V names point B) {i code : M.Domain} (hAt : MemPair M B i code) :
    ScopedAtom M D code V.scope := by
  have hi := (h.graph.bounds hM.1 hAt).1
  obtain ⟨k,q,p,hEntry⟩ := need_entry_exists hC.reflection hT.needs hi
  obtain ⟨hqW,hpW⟩ := hT.need_columns_d hM hC hEntry
  obtain ⟨uk,_,hk⟩ := h.layers.total i hi
  obtain ⟨uq,_,hq⟩ := h.nameGraph.total q hqW
  obtain ⟨up,_,hp⟩ := h.nameGraph.total p hpW
  exact ((h.rows i k q p hEntry uk uq up hk hq hp code).mp hAt).scoped_d hM hC hD hs

structure EndpointBlocks (α : Type u) where
  pointName : α
  inputTop : α
  outputRelation : α
  outputTop : α

structure EndpointBlocks.Valid (M : SetTheory.Structure.{u}) (C : ArticleData M.Domain) (D : RelationalData M.Domain)
    (T : TemplateShape M.Domain) (V : NameFrame M.Domain) (B : EndpointBlocks M.Domain) : Prop where
  pointName : MemPair M V.scalars (C.numbers 1) B.pointName
  inputTop : EndpointBlock true M C D T V V.inputs B.pointName B.inputTop
  outputRelation : EndpointBlock false M C D T V V.outputs B.pointName B.outputRelation
  outputTop : EndpointBlock true M C D T V V.outputs B.pointName B.outputTop

theorem endpoint_blocks_exists_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory) {C : ArticleData M.Domain} (hC : C.Valid M)
    {A : M.Domain} {D : RelationalData M.Domain} (hD : ArticleInterpretation M C A D) {T : TemplateShape M.Domain} (hT : T.Valid M C)
    {F : M.Domain} {V : NameFrame M.Domain} (hV : V.Valid M C F T.width T.edgeLength T.needLength) :
    ∃ B, EndpointBlocks.Valid M C D T V B := by
  have hs : M.mem V.scope D.omega := Eq.mpr (congrArg (M.mem V.scope) hD.omega) hV.scope
  obtain ⟨point,hPoint,hPointRow⟩ := hV.scalars.graph.total (C.numbers 1) (hC.numerals.lt (by decide : (1:Nat)<3))
  obtain ⟨inputTop,hInput⟩ := endpoint_block_exists_d hM hC hD true hT hs hV.inputs.graph hV.needLayers.graph hPoint
  obtain ⟨outputRelation,hOutput⟩ := endpoint_block_exists_d hM hC hD false hT hs hV.outputs.graph hV.needLayers.graph hPoint
  obtain ⟨outputTop,hTop⟩ := endpoint_block_exists_d hM hC hD true hT hs hV.outputs.graph hV.needLayers.graph hPoint
  exact ⟨⟨point,inputTop,outputRelation,outputTop⟩,hPointRow,hInput,hOutput,hTop⟩

end KP1Y.ReflectionModel
