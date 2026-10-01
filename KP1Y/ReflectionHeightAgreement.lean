import KP1Y.ReflectionTopInduction
import KP1Y.ReflectionCounterexampleTransfer
import KP1Y.ReflectionTemplateEnvironment
import KP1Y.OrdinalInduction

/-! 第6引理(7)：对内部 K、再对 θ 作对象序数归纳，得到顶端κ与初等高度δ的双向查询等价。 -/
namespace KP1Y.ReflectionModel
open YesMetaZFC YesMetaZFC.SetTheory YesMetaZFC.SetTheory.Definitional
open KP1Y.Kuratowski KP1Y.Functions KP1Y.Satisfaction KP1Y.Reflection
universe u

def HeightAgreementAt (M : SetTheory.Structure.{u}) (C : IndexData M.Domain) (H κ δ K θ : M.Domain) : Prop :=
  ∀ a, M.mem a δ → (θ=a ∨ M.mem θ a) → (Query M C H K θ a κ ↔ Query M C H K θ a δ)

def heightAgreementAtFormula {d : Nat} (C : IndexData (Project.Term d)) (H κ δ K θ : Project.Term d) : Project.Formula 1 d :=
  Project.Formula.forallMem δ (.imp (.disj (Project.Formula.extensionalEq θ.weaken (.bound 0)) (.mem θ.weaken (.bound 0)))
    (.iff (queryFormula C.weaken H.weaken K.weaken θ.weaken (.bound 0) κ.weaken)
      (queryFormula C.weaken H.weaken K.weaken θ.weaken (.bound 0) δ.weaken)))

theorem heightAgreementAtFormula_delta0 {d : Nat} (C : IndexData (Project.Term d)) (H κ δ K θ : Project.Term d) :
    (heightAgreementAtFormula C H κ δ K θ).IsDelta0 :=
  .forallMem _ (.imp (.disj (.atom _ _ _) (.mem _ _))
    (.iff (queryFormula_delta0 _ _ _ _ _ _) (queryFormula_delta0 _ _ _ _ _ _)))

theorem heightAgreementAtFormula_iff {M : SetTheory.Structure.{u}} (he : Extensional M) {d : Nat}
    (env : Env M d) (C : IndexData (Project.Term d)) (H κ δ K θ : Project.Term d) :
    Project.Formula.satisfies env (heightAgreementAtFormula C H κ δ K θ) ↔
      HeightAgreementAt M (C.eval env) (H.eval env) (κ.eval env) (δ.eval env) (K.eval env) (θ.eval env) := by
  simp only [heightAgreementAtFormula,HeightAgreementAt,Project.Formula.satisfies_forallMem_iff,
    Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_disj_iff,Project.Formula.satisfies_mem_iff,
    Project.Formula.satisfies_extensionalEq_iff_eq he,Project.Formula.satisfies_iff_iff,
    queryFormula_iff he,IndexData.eval_weaken,Term.eval_weaken]
  rfl

private def heightAgreementEnv {M : SetTheory.Structure.{u}} (C : IndexData M.Domain) (H κ δ : M.Domain) : Env M 10 :=
  (((((((((oneEnv C.omega).push C.cap).push C.middle).push C.keys).push C.block).push C.bound).push C.index).push H).push κ).push δ

private def rootAgreementIndex : IndexData (Project.Term 12) :=
  ⟨.bound 11,.bound 10,.bound 9,.bound 8,.bound 7,.bound 6,.bound 5⟩

private def rootAgreementSchema : Project.Delta0UnarySchema 11 where
  body := heightAgreementAtFormula rootAgreementIndex (.bound 4) (.bound 3) (.bound 2) (.bound 1) (.bound 0)
  freeClosed := by
    simp [heightAgreementAtFormula,rootAgreementIndex,queryFormula,validQueryFormula,cursorFormula,
      KP1Y.Ranking.packetFormula,IndexData.weaken,IndexData.map,memPairFormula,codeFormula,pairFormula,
      Project.Formula.forallMem,Project.Formula.existsMem,Definitional.Formula.FreeClosed]
  delta0 := heightAgreementAtFormula_delta0 _ _ _ _ _ _

private theorem rootAgreementSchema_iff {M : SetTheory.Structure.{u}} (he : Extensional M)
    (C : IndexData M.Domain) (H κ δ K θ : M.Domain) :
    Project.Formula.satisfies (((heightAgreementEnv C H κ δ).push K).push θ) rootAgreementSchema.body ↔
      HeightAgreementAt M C H κ δ K θ := by
  simp only [rootAgreementSchema,heightAgreementAtFormula_iff he]
  rfl

private def layerAgreementSchema : Project.Delta0UnarySchema 10 where
  body := .imp (.mem (.bound 0) (.bound 10)) (Project.Formula.forallMem (.bound 9) rootAgreementSchema.body)
  freeClosed := by simp [Project.Formula.forallMem,Definitional.Formula.FreeClosed,rootAgreementSchema.freeClosed]
  delta0 := .imp (.mem _ _) (.forallMem _ rootAgreementSchema.delta0)

private theorem layerAgreementSchema_iff {M : SetTheory.Structure.{u}} (he : Extensional M)
    (C : IndexData M.Domain) (H κ δ K : M.Domain) :
    Project.Formula.satisfies ((heightAgreementEnv C H κ δ).push K) layerAgreementSchema.body ↔
      (M.mem K C.omega → ∀ θ, M.mem θ C.cap → HeightAgreementAt M C H κ δ K θ) := by
  simp only [layerAgreementSchema,Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_mem_iff,
    Project.Formula.satisfies_forallMem_iff,rootAgreementSchema_iff he]
  rfl

private theorem height_to_top_step_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ArticleData M.Domain} (hC : C.Valid M) {S : ArticleStructure M.Domain} (hS : S.Valid M C)
    {δ : M.Domain} {small : EvaluationData M.Domain} (h : Height M C S δ small)
    {K θ a : M.Domain} (haδ : M.mem a δ) (hIH : TopAgreementBefore M C.reflection C.table C.top δ K θ)
    (hSmall : Query M C.reflection.toIndexData C.table K θ a δ) : Query M C.reflection.toIndexData C.table K θ a C.top := by
  classical
  apply Classical.byContradiction
  intro hNot
  have hValid : ValidQuery M C.reflection.toIndexData K θ a C.top :=
    (valid_query_paper_iff hM.1 hC.reflection.cap hC.cap K θ a C.top).mpr
      ⟨hSmall.1.1,hSmall.1.2.2.2.2.1,hC.top.transitive δ h.below a haδ,Or.inl rfl,hSmall.1.2.2.2.2.2.2⟩
  have hθδ : M.mem θ δ := by
    rcases hValid.2.2.2.2.1 with he | hθa
    · exact he ▸ haδ
    · exact h.ordinal.transitive a haδ θ hθa
  obtain ⟨m,hm,A,hA,N,hN,c,hc,f,hf,hDemand,hNone⟩ := hC.table.counterexample_d hM hC.reflection hValid hNot
  obtain ⟨NI,NN,hShape⟩ := template_shape_exists hC hDemand.representation.diagram hDemand.template hc
  let T : TemplateShape M.Domain := ⟨m,A,N,c,NI,NN⟩
  have hT : T.Valid M C := hShape
  obtain ⟨F,_,V,hV,B,hB⟩ := template_environment_exists_d hM hC hS.interpretation hT K
  have hNoneAll : ¬∃ g, Response M C.reflection C.table a m A N c f g := by
    rintro ⟨g,hResponse⟩
    exact hNone g (hResponse.representation.labeling.sequence hC.reflection) hResponse
  obtain ⟨f',hGraph,hDemand',hNone'⟩ := h.localize_counterexample_d hM hC hS hT hV hB haδ hθδ hDemand hNoneAll
  have hBelow : Below M C.reflection m f' δ := fun _ _ _ _ hAt => (hGraph.bounds hM.1 hAt).2
  have hEnd := (end_top_height_agree hM.1 hIH hDemand'.representation.labeling.graph hBelow hDemand'.admissible).mp hDemand'.endpoint
  have hDemandδ : Demand M C.reflection C.table K θ a δ m A N c f' :=
    ⟨hDemand'.template,hDemand'.representation,hDemand'.cut,hBelow,hDemand'.admissible,hEnd⟩
  obtain ⟨g,_,hResponse⟩ := (hC.table.reflect_d hM hC.reflection hSmall) m hm A hA N hN c hc f'
    (hDemand'.representation.labeling.sequence hC.reflection) hDemandδ
  exact hNone' ⟨g,hResponse⟩

/-- 第6引理(7)的完整双向等价；无遗留归纳或反例局部化假设。 -/
theorem Height.query_agreement_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ArticleData M.Domain} (hC : C.Valid M) {S : ArticleStructure M.Domain} (hS : S.Valid M C)
    {δ : M.Domain} {small : EvaluationData M.Domain} (h : Height M C S δ small)
    {K θ a : M.Domain} (hK : M.mem K C.reflection.omega) (haδ : M.mem a δ) (hθa : θ=a ∨ M.mem θ a) :
    Query M C.reflection.toIndexData C.table K θ a C.top ↔ Query M C.reflection.toIndexData C.table K θ a δ := by
  let env := heightAgreementEnv C.reflection.toIndexData C.table C.top δ
  have hLayers := KP1Y.ordinal_induction_d hM layerAgreementSchema.toUnarySchema env (by
    intro K _ ihK
    apply (layerAgreementSchema_iff hM.1 C.reflection.toIndexData C.table C.top δ K).mpr
    intro hK
    have hRoots := KP1Y.ordinal_induction_d hM rootAgreementSchema.toUnarySchema (env.push K) (by
      intro θ _ ihθ
      apply (rootAgreementSchema_iff hM.1 C.reflection.toIndexData C.table C.top δ K θ).mpr
      intro a haδ hθa
      have hIH : TopAgreementBefore M C.reflection C.table C.top δ K θ := by
        intro k hk η hη x _ hEarlier hηx hxδ
        rcases hEarlier with hkK | ⟨he,hηθ⟩
        · exact (layerAgreementSchema_iff hM.1 C.reflection.toIndexData C.table C.top δ k).mp (ihK k hkK) hk η hη x hxδ hηx
        · subst k
          exact (rootAgreementSchema_iff hM.1 C.reflection.toIndexData C.table C.top δ K η).mp (ihθ η hηθ) x hxδ hηx
      exact ⟨top_to_height_d hM hC.reflection hC.table h.below haδ hIH,
        height_to_top_step_d hM hC hS h haδ hIH⟩)
    intro θ hθ
    exact (rootAgreementSchema_iff hM.1 C.reflection.toIndexData C.table C.top δ K θ).mp (hRoots θ (hC.reflection.cap.mem hθ)))
  have hθCap : M.mem θ C.reflection.cap := by
    have haCap := hC.reflection.cap.transitive C.top hC.cap.predecessor_mem a (hC.top.transitive δ h.below a haδ)
    rcases hθa with he | hθa
    · exact he ▸ haCap
    · exact hC.reflection.cap.transitive a haCap θ hθa
  exact (layerAgreementSchema_iff hM.1 C.reflection.toIndexData C.table C.top δ K).mp
    (hLayers K ((KP1Y.Naturals.omega_isOrdinal_d hM hC.numerals.omega).mem hK)) hK θ hθCap a haδ hθa

end KP1Y.ReflectionModel
