import KP1Y.ReflectionModelHeight
import KP1Y.ReflectionAdjacentLabels
import KP1Y.LeastChoice

/-! 用有界 Skolem 封闭谓词选取最小高度，再进行模型内部的确定性迭代。 -/
namespace KP1Y.ReflectionModel
open YesMetaZFC YesMetaZFC.SetTheory YesMetaZFC.SetTheory.Definitional
open KP1Y.Kuratowski KP1Y.Functions KP1Y.Satisfaction KP1Y.Cardinal KP1Y.Closure KP1Y.Iteration
universe u

/-- 把 Skolem 闭包测试的全部量词限制到已构造的大结构集合。 -/
def BoundedSkolemClosed (M : SetTheory.Structure.{u}) (ω programs assignments carrier : M.Domain)
    (K : SkolemBounds M.Domain) (F X : M.Domain) : Prop :=
  ∀ p, M.mem p programs → ∀ j, M.mem j ω → ∀ bound, M.mem bound ω →
    ∀ v, M.mem v ω → ∀ s, M.mem s assignments → ∀ key, M.mem key K.keys →
      ∀ x, M.mem x carrier → Graph M s bound X ∧ KeyCode M K key p j s bound v ∧ MemPair M F key x → M.mem x X

def boundedSkolemClosedFormula {n : Nat} (ω programs assignments carrier : Project.Term n)
    (K : SkolemBounds (Project.Term n)) (F X : Project.Term n) : Project.Formula 1 n :=
  Project.Formula.forallMem programs (Project.Formula.forallMem ω.weaken
    (Project.Formula.forallMem ω.weaken.weaken (Project.Formula.forallMem ω.weaken.weaken.weaken
      (Project.Formula.forallMem assignments.weaken.weaken.weaken.weaken
        (Project.Formula.forallMem K.keys.weaken.weaken.weaken.weaken.weaken
          (Project.Formula.forallMem carrier.weaken.weaken.weaken.weaken.weaken.weaken
            (.imp (.conj (graphFormula (.bound 2) (.bound 4) X.weaken.weaken.weaken.weaken.weaken.weaken.weaken)
              (.conj (keyCodeFormula K.weaken.weaken.weaken.weaken.weaken.weaken.weaken
                (.bound 1) (.bound 6) (.bound 5) (.bound 2) (.bound 4) (.bound 3))
                (memPairFormula F.weaken.weaken.weaken.weaken.weaken.weaken.weaken (.bound 1) (.bound 0))))
              (.mem (.bound 0) X.weaken.weaken.weaken.weaken.weaken.weaken.weaken))))))))

theorem boundedSkolemClosedFormula_delta0 {n : Nat} (ω programs assignments carrier : Project.Term n)
    (K : SkolemBounds (Project.Term n)) (F X : Project.Term n) :
    (boundedSkolemClosedFormula ω programs assignments carrier K F X).IsDelta0 :=
  .forallMem _ (.forallMem _ (.forallMem _ (.forallMem _ (.forallMem _ (.forallMem _ (.forallMem _
    (.imp (.conj (graphFormula_delta0 _ _ _)
      (.conj (keyCodeFormula_delta0 _ _ _ _ _ _ _) (memPairFormula_delta0 _ _ _))) (.mem _ _))))))))

theorem boundedSkolemClosedFormula_iff {M : SetTheory.Structure.{u}} (he : Extensional M) {n : Nat}
    (env : Env M n) (ω programs assignments carrier : Project.Term n)
    (K : SkolemBounds (Project.Term n)) (F X : Project.Term n) :
    Project.Formula.satisfies env (boundedSkolemClosedFormula ω programs assignments carrier K F X) ↔
      BoundedSkolemClosed M (ω.eval env) (programs.eval env) (assignments.eval env) (carrier.eval env)
        (K.eval env) (F.eval env) (X.eval env) := by
  simp only [boundedSkolemClosedFormula,BoundedSkolemClosed,Project.Formula.satisfies_forallMem_iff,
    Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_mem_iff,
    graphFormula_iff he,keyCodeFormula_iff he,memPairFormula_iff he,SkolemBounds.eval_weaken,Term.eval_weaken]
  rfl

theorem bounded_skolem_closed_iff {M : SetTheory.Structure.{u}} (he : Extensional M)
    {C : Context M.Domain} {I : EvaluationData M.Domain} (hI : I.Valid C)
    {K : SkolemBounds M.Domain} (hK : SkolemBoundsValid M C I K) {F X : M.Domain}
    (hF : Graph M F K.keys I.carrier) (hSub : M.MemberSubset X I.carrier) :
    BoundedSkolemClosed M C.omega C.programs I.assignments I.carrier K F X ↔ SkolemClosed M C K F X := by
  constructor
  · intro h p hp j hj bound hb v hv s hS key hKey x hAt
    have hs := (hI.assignments_exact s).mpr ⟨bound,hb,hS.mono_values hSub⟩
    have hk := (key_members hK key).mpr ⟨p,hp,j,hj,s,hs,bound,hb,v,hv,hKey⟩
    exact h p hp j hj bound hb v hv s hs key hk x (hF.bounds he hAt).2 ⟨hS,hKey,hAt⟩
  · intro h p hp j hj bound hb v hv s _ key _ x _ hAnte
    exact h p hp j hj bound hb v hv s hAnte.1 key hAnte.2.1 x hAnte.2.2

def HeightClosed (M : SetTheory.Structure.{u}) (S : ArticleStructure M.Domain) (δ : M.Domain) : Prop :=
  BoundedSkolemClosed M S.context.omega S.context.programs S.large.assignments S.large.carrier S.bounds S.skolem δ

def HeightStep (M : SetTheory.Structure.{u}) (S : ArticleStructure M.Domain) (γ δ : M.Domain) : Prop :=
  M.mem γ δ ∧ M.mem S.context.omega δ ∧ HeightClosed M S δ

def heightClosureEnv {M : SetTheory.Structure.{u}} (S : ArticleStructure M.Domain) : Env M 9 :=
  ((((((((oneEnv S.context.omega).push S.context.programs).push S.large.assignments).push S.large.carrier).push S.bounds.programNodes).push S.bounds.variableSlots).push S.bounds.assignmentSlots).push S.bounds.keys).push S.skolem

def heightStepSchema : Project.Delta0BinarySchema 9 where
  body := .conj (.mem (.bound 1) (.bound 0)) (.conj (.mem (.bound 10) (.bound 0))
    (boundedSkolemClosedFormula (.bound 10) (.bound 9) (.bound 8) (.bound 7)
      ⟨.bound 6,.bound 5,.bound 4,.bound 3⟩ (.bound 2) (.bound 0)))
  freeClosed := by
    simp [boundedSkolemClosedFormula,keyCodeFormula,SkolemBounds.weaken,SkolemBounds.map,
      graphFormula,memPairFormula,codeFormula,pairFormula,Project.Formula.forallMem,
      Project.Formula.existsMem,Definitional.Formula.FreeClosed]
  delta0 := .conj (.mem _ _) (.conj (.mem _ _) (boundedSkolemClosedFormula_delta0 _ _ _ _ _ _ _))

theorem heightStepSchema_iff {M : SetTheory.Structure.{u}} (he : Extensional M)
    (S : ArticleStructure M.Domain) (γ δ : M.Domain) :
    Project.Formula.satisfies (((heightClosureEnv S).push γ).push δ) heightStepSchema.body ↔ HeightStep M S γ δ := by
  simp only [heightStepSchema,Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_mem_iff,
    boundedSkolemClosedFormula_iff he]
  rfl

theorem ArticleStructure.Valid.closed_height_above_exists_d {M : SetTheory.Structure.{u}}
    (hM : M.Models KP1Y.theory) {C : ArticleData M.Domain} (hC : C.Valid M)
    {S : ArticleStructure M.Domain} (hS : S.Valid M C)
    (hκ : UncountableOrdinal M C.reflection.omega C.top) {γ : M.Domain} (hγ : M.mem γ C.top) :
    ∃ δ, M.mem δ C.top ∧ HeightStep M S γ δ := by
  have hUnc : UncountableOrdinal M S.context.omega S.large.carrier := by rw [hS.omega,hS.carrier]; exact hκ
  have hEnum : UniformEnumeration M S.context.omega S.large.carrier C.enumKeys C.enumeration := by
    rw [hS.omega,hS.carrier]
    exact hC.enumeration
  have hγLarge : M.mem γ S.large.carrier := Eq.mpr (congrArg (M.mem γ) hS.carrier) hγ
  obtain ⟨base,hSeed⟩ := height_seed_exists_d hM hS.context.omega hUnc.1 hUnc.2.1 hγLarge
  obtain ⟨zero,_,hz⟩ := hS.context.omega.1.1
  have hDefault := hUnc.1.transitive S.context.omega hUnc.2.1 zero hz
  obtain ⟨δ,E,hSub,hCount,hSeedIn,hClosed,hEnumClosed⟩ := e_closed_skolem_hull_d hM
    hS.context hS.large hS.bounds hS.skolem hS.programs hSeed.graph hEnum hDefault
  obtain ⟨_,hδ⟩ := countable_initial_segment_d hM hUnc hEnum hSub hCount hEnumClosed
  exact ⟨δ,Eq.mp (congrArg (M.mem δ) hS.carrier) hδ,hSeedIn γ hSeed.point,hSeedIn S.context.omega hSeed.omega,
    (bounded_skolem_closed_iff hM.1 hS.large hS.bounds hS.skolem.graph hSub).mpr hClosed⟩

private def ordinalOrderSchema : Project.Delta0BinarySchema 0 where
  body := .mem (.bound 1) (.bound 0)
  freeClosed := by simp [Definitional.Formula.FreeClosed]
  delta0 := .mem _ _

theorem height_order_exists_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {κ : M.Domain} (hκ : M.IsOrdinal κ) :
    ∃ R, KP1Y.InternalWellOrder M R κ ∧ ∀ x y, MemPair M R x y ↔ M.mem x κ ∧ M.mem y κ ∧ M.mem x y := by
  let env : Env M 0 := ⟨Fin.elim0,fun _ => κ⟩
  obtain ⟨R,_,hRaw⟩ := relation_comprehension_d hM ordinalOrderSchema env κ κ
  have hφ (x y : M.Domain) : Project.Formula.satisfies ((env.push x).push y) ordinalOrderSchema.body ↔ M.mem x y := by
    simp only [ordinalOrderSchema,Project.Formula.satisfies_mem_iff]
    rfl
  have hRows (x y : M.Domain) : MemPair M R x y ↔ M.mem x κ ∧ M.mem y κ ∧ M.mem x y := by
    simpa only [hφ] using hRaw x y
  refine ⟨R,⟨?_,?_,?_⟩,hRows⟩
  · intro x hx hxx
    exact hκ.wellOrder.linear.irrefl x hx ((hRows x x).mp hxx).2.2
  · intro x hx y hy z hz hxy hyz
    exact (hRows x z).mpr ⟨hx,hz,hκ.wellOrder.linear.trans x hx y hy z hz ((hRows x y).mp hxy).2.2 ((hRows y z).mp hyz).2.2⟩
  · intro X hSub hNe
    obtain ⟨x,hx,hMin⟩ := hκ.wellOrder.least X hSub hNe
    refine ⟨x,hx,?_⟩
    intro y hy
    rcases hMin y hy with he | hxy
    · exact Or.inl (hM.1.eq_of_same_members x y he)
    · exact Or.inr ((hRows x y).mpr ⟨hSub x hx,hSub y hy,hxy⟩)

structure HeightOperation (M : SetTheory.Structure.{u}) (C : ArticleData M.Domain)
    (S : ArticleStructure M.Domain) (G : M.Domain) : Prop where
  graph : Graph M G C.top C.top
  step : ∀ γ δ, MemPair M G γ δ → HeightStep M S γ δ
  least : ∀ γ δ, MemPair M G γ δ → ∀ η, M.mem η C.top → HeightStep M S γ η → δ=η ∨ M.mem δ η

/-- 对每个 γ 取最小的有界可定义 Skolem 封闭高度，产生真正的集合选择图。 -/
theorem height_operation_exists_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ArticleData M.Domain} (hC : C.Valid M) {S : ArticleStructure M.Domain} (hS : S.Valid M C)
    (hκ : UncountableOrdinal M C.reflection.omega C.top) : ∃ G, HeightOperation M C S G := by
  obtain ⟨R,hOrder,hR⟩ := height_order_exists_d hM hC.top
  let P := fun γ δ => Project.Formula.satisfies (((heightClosureEnv S).push γ).push δ) heightStepSchema.body
  have hExists (γ : M.Domain) (hγ : M.mem γ C.top) : ∃ δ, KP1Y.LeastWitness R C.top P γ δ := by
    apply KP1Y.least_witness_exists_d hM heightStepSchema (heightClosureEnv S) hOrder
    obtain ⟨δ,hδ,hStep⟩ := hS.closed_height_above_exists_d hM hC hκ hγ
    exact ⟨δ,hδ,(heightStepSchema_iff hM.1 S γ δ).mpr hStep⟩
  obtain ⟨G,hSupport,hRaw⟩ := relation_comprehension_d hM (KP1Y.leastSchema heightStepSchema)
    (((heightClosureEnv S).push R).push C.top) C.top C.top
  have hRows (γ δ : M.Domain) : MemPair M G γ δ ↔ M.mem γ C.top ∧ M.mem δ C.top ∧ KP1Y.LeastWitness R C.top P γ δ := by
    simpa only [KP1Y.leastSchema_iff hM.1] using hRaw γ δ
  have hGraph : Graph M G C.top C.top := by
    refine ⟨hSupport,?_,?_⟩
    · intro γ hγ
      obtain ⟨δ,hδ⟩ := hExists γ hγ
      exact ⟨δ,hδ.1,(hRows γ δ).mpr ⟨hγ,hδ.1,hδ⟩⟩
    · intro γ δ η hδ hη
      exact KP1Y.least_witness_unique hOrder ((hRows γ δ).mp hδ).2.2 ((hRows γ η).mp hη).2.2
  have hSpec (γ δ : M.Domain) (hAt : MemPair M G γ δ) : KP1Y.LeastWitness R C.top P γ δ := ((hRows γ δ).mp hAt).2.2
  refine ⟨G,hGraph,?_,?_⟩
  · intro γ δ hAt
    exact (heightStepSchema_iff hM.1 S γ δ).mp (hSpec γ δ hAt).2.1
  · intro γ δ hAt η hη hStep
    rcases (hSpec γ δ hAt).2.2 η hη ((heightStepSchema_iff hM.1 S γ η).mpr hStep) with he | hLess
    · exact Or.inl he
    · exact Or.inr ((hR δ η).mp hLess).2.2

private def heightSectionSchema : Project.Delta0BinarySchema 3 where
  body := Project.Formula.existsMem (.bound 4)
    (.conj (codeFormula (.bound 0) (.bound 3) (.bound 2)) (memPairFormula (.bound 4) (.bound 0) (.bound 1)))
  freeClosed := by
    simp [codeFormula,pairFormula,memPairFormula,Project.Formula.existsMem,Project.Formula.forallMem,Definitional.Formula.FreeClosed]
  delta0 := .existsMem _ (.conj (codeFormula_delta0 _ _ _) (memPairFormula_delta0 _ _ _))

/-- 全局 e 的正初段截面给出实际满射 ω→δ。 -/
theorem height_enumeration_exists_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ArticleData M.Domain} (hC : C.Valid M) {δ : M.Domain}
    (hδ : M.mem δ C.top) (hPos : ∃ z, M.mem z δ) : ∃ E, Onto M E C.reflection.omega δ := by
  let env := ((oneEnv C.enumKeys).push C.enumeration).push δ
  have hφ (n x : M.Domain) : Project.Formula.satisfies ((env.push n).push x) heightSectionSchema.body ↔
      ∃ key, M.mem key C.enumKeys ∧ Codes M key δ n ∧ MemPair M C.enumeration key x := by
    simp only [heightSectionSchema,Project.Formula.satisfies_existsMem_iff,Project.Formula.satisfies_conj_iff,
      codeFormula_iff hM.1,memPairFormula_iff hM.1]
    rfl
  obtain ⟨E,hSupport,hRaw⟩ := relation_comprehension_d hM heightSectionSchema env C.reflection.omega δ
  have hRows (n x : M.Domain) : MemPair M E n x ↔ M.mem n C.reflection.omega ∧ M.mem x δ ∧
      ∃ key, M.mem key C.enumKeys ∧ Codes M key δ n ∧ MemPair M C.enumeration key x := by
    simpa only [hφ] using hRaw n x
  refine ⟨E,hSupport,?_,?_,?_⟩
  · intro n hn
    obtain ⟨key,hCode⟩ := codes_total hM δ n
    have hk := (hC.enumeration.keys key).mpr ⟨δ,hδ,n,hn,hCode⟩
    obtain ⟨x,_,hAt⟩ := hC.enumeration.graph.total key hk
    have hx := hC.enumeration.positive_range δ hδ hPos n hn key hCode x hAt
    exact ⟨x,hx,(hRows n x).mpr ⟨hn,hx,key,hk,hCode,hAt⟩⟩
  · intro n _ x _ y _ hEx hEy
    obtain ⟨_,_,key,_,hCode,hAt⟩ := (hRows n x).mp hEx
    obtain ⟨_,_,key',_,hCode',hAt'⟩ := (hRows n y).mp hEy
    have he := codes_unique hM.1 hCode hCode'
    subst key'
    exact hC.enumeration.graph.unique key x y hAt hAt'
  · intro x hx
    obtain ⟨n,hn,key,hk,hCode,hAt⟩ := hC.enumeration.covers δ hδ x hx
    exact ⟨n,hn,(hRows n x).mpr ⟨hn,hx,key,hk,hCode,hAt⟩⟩

theorem closed_height_is_height_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ArticleData M.Domain} (hC : C.Valid M) {S : ArticleStructure M.Domain} (hS : S.Valid M C)
    {δ : M.Domain} (hδ : M.mem δ C.top) (hωδ : M.mem S.context.omega δ) (hClosed : HeightClosed M S δ) :
    ∃ small, Height M C S δ small := by
  have hSub : M.MemberSubset δ S.large.carrier := by
    intro x hx
    exact Eq.mpr (congrArg (M.mem x) hS.carrier) (hC.top.transitive δ hδ x hx)
  have hSkolem := (bounded_skolem_closed_iff hM.1 hS.large hS.bounds hS.skolem.graph hSub).mp hClosed
  obtain ⟨small,hCarrier,hSmall,hElem⟩ := closed_substructure_exists_d hM hS.context hS.interpretation.spaces
    hS.large hS.relational_carrier hS.atomic hS.bounds hS.skolem hSub hSkolem
  obtain ⟨E,hE⟩ := height_enumeration_exists_d hM hC hδ ⟨S.context.omega,hωδ⟩
  exact ⟨small,hC.top.mem hδ,hδ,Eq.mp (congrArg (fun ω => M.mem ω δ) hS.omega) hωδ,hCarrier,hSmall,hElem,E,hE⟩

/-- 迭代存在性调用的 Δ₀ 全性/唯一性由已经构造的 G 图提供。 -/
theorem HeightOperation.iterate_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ArticleData M.Domain} (hC : C.Valid M) {S : ArticleStructure M.Domain} {G γ : M.Domain}
    (hG : HeightOperation M C S G) (hγ : M.mem γ C.top) :
    ∃ base H, MemPair M G γ base ∧ Graph M H C.reflection.omega C.top ∧
      (∀ zero, M.mem zero C.reflection.omega → (∀ x, ¬M.mem x zero) → MemPair M H zero base) ∧
      (∀ i j x y, M.SuccessorOf j i → MemPair M H i x → MemPair M H j y → MemPair M G x y) ∧
      ∀ i δ, MemPair M H i δ → M.mem S.context.omega δ ∧ HeightClosed M S δ := by
  obtain ⟨base,hBase,hAtBase⟩ := hG.graph.total γ hγ
  have hNext (x y : M.Domain) : nextDenote KP1Y.Recursion.memberSchema (oneEnv G) x y ↔ MemPair M G x y :=
    KP1Y.Recursion.memberSchema_iff hM.1 G x y
  obtain ⟨H,hH⟩ := iterator_exists_d hM KP1Y.Recursion.memberSchema (oneEnv G) hC.numerals.omega hBase
    (by
      intro x hx
      obtain ⟨y,hy,hxy⟩ := hG.graph.total x hx
      exact ⟨y,hy,(hNext x y).mpr hxy⟩)
    (fun x _ y _ z _ hxy hxz => hG.graph.unique x y z ((hNext x y).mp hxy) ((hNext x z).mp hxz))
  have hTransition (i j x y : M.Domain) (hs : M.SuccessorOf j i) (hix : MemPair M H i x) (hjy : MemPair M H j y) :
      MemPair M G x y := (hNext x y).mp (hH.transition i j x y hs hix hjy)
  refine ⟨base,H,hAtBase,hH.graph,hH.initial,hTransition,?_⟩
  intro i δ hAt
  have hi := (hH.graph.bounds hM.1 hAt).1
  rcases KP1Y.Naturals.natural_cases hM hC.numerals.omega hi with hEmpty | ⟨j,hj,hs⟩
  · have hBaseAt := hH.initial i hi hEmpty
    have he := hH.graph.unique i δ base hAt hBaseAt
    subst δ
    exact (hG.step γ base hAtBase).2
  · obtain ⟨x,_,hjx⟩ := hH.graph.total j hj
    exact (hG.step x δ (hTransition j i x δ hs hjx hAt)).2

structure HeightSequence (M : SetTheory.Structure.{u}) (C : ArticleData M.Domain)
    (S : ArticleStructure M.Domain) (γ m f : M.Domain) : Prop where
  graph : Graph M f m C.top
  increasing : KP1Y.Reflection.Increasing M f m C.top
  above : ∀ i δ, MemPair M f i δ → M.mem γ δ
  closed : ∀ i δ, MemPair M f i δ → HeightClosed M S δ
  heights : ∀ i δ, MemPair M f i δ → ∃ small, Height M C S δ small

/-- 任意内部有限长度的递增高度图；所有行高于 γ，且都有实际小结构存在证书。 -/
theorem height_sequence_exists_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ArticleData M.Domain} (hC : C.Valid M) {S : ArticleStructure M.Domain} (hS : S.Valid M C)
    (hκ : UncountableOrdinal M C.reflection.omega C.top) {γ m : M.Domain}
    (hγ : M.mem γ C.top) (hm : M.mem m C.reflection.omega) : ∃ f, HeightSequence M C S γ m f := by
  obtain ⟨G,hG⟩ := height_operation_exists_d hM hC hS hκ
  obtain ⟨base,H,hBase,hH,hInitial,hTransition,hClosed⟩ := hG.iterate_d hM hC hγ
  have hω := KP1Y.Naturals.omega_isOrdinal_d hM hC.numerals.omega
  have hmSub := hω.transitive m hm
  obtain ⟨f,hF,hRows⟩ := restrict_graph_d hM hH hmSub
  have hAdj : KP1Y.Reflection.AdjacentIncreasing M f m C.top := by
    intro i _ j _ hs x _ y _ hix hjy
    exact (hG.step x y (hTransition i j x y hs ((hRows i x).mp hix).2 ((hRows j y).mp hjy).2)).1
  have hInc := KP1Y.Reflection.increasing_of_adjacent_d hM hC.numerals.omega hm hC.top hF hAdj
  have hAbove : ∀ i δ, MemPair M f i δ → M.mem γ δ := by
    intro i δ hAt
    have hi := (hF.bounds hM.1 hAt).1
    have hδ := (hF.bounds hM.1 hAt).2
    obtain ⟨zero,hEmpty,hz⟩ := hC.numerals.omega.1.1
    have hzi : zero=i ∨ M.mem zero i := by
      rcases hω.wellOrder.linear.compare zero hz i (hmSub i hi) with he | hzi | hiz
      · exact Or.inl (hM.1.eq_of_same_members zero i he)
      · exact Or.inr hzi
      · exact False.elim (hEmpty i hiz)
    rcases hzi with he | hzi
    · subst i
      have he := hH.unique zero δ base ((hRows zero δ).mp hAt).2 (hInitial zero hz hEmpty)
      subst δ
      exact (hG.step γ base hBase).1
    · have hzm := (hω.mem hm).transitive i hi zero hzi
      have hzb := (hRows zero base).mpr ⟨hzm,hInitial zero hz hEmpty⟩
      have hBaseδ := hInc zero hzm i hi hzi base (hG.graph.bounds hM.1 hBase).2 δ hδ hzb hAt
      exact (hC.top.mem hδ).transitive base hBaseδ γ (hG.step γ base hBase).1
  refine ⟨f,hF,hInc,hAbove,?_,?_⟩
  · intro i δ hAt
    exact (hClosed i δ ((hRows i δ).mp hAt).2).2
  · intro i δ hAt
    obtain ⟨hωδ,hCl⟩ := hClosed i δ ((hRows i δ).mp hAt).2
    exact closed_height_is_height_d hM hC hS (hF.bounds hM.1 hAt).2 hωδ hCl

end KP1Y.ReflectionModel
