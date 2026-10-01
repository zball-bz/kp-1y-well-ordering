import KP1Y.OneYExpansion
import KP1Y.RankedDescendantOrder

/-! 内部有限展开路径及实际Reach集合。Reach(x,s)的方向是x为s的后代。 -/
namespace KP1Y.OneYFinite.Reachability
open YesMetaZFC YesMetaZFC.SetTheory YesMetaZFC.SetTheory.Definitional
open KP1Y.Kuratowski KP1Y.Functions KP1Y.Naturals KP1Y.Bounded
open KP1Y.OneYFinite
universe u

structure Path (M : SetTheory.Structure.{u}) (C : ExpressionData M.Domain) (Keys EN steps count nodes controls s x : M.Domain) : Prop where
  length : M.mem steps C.omega
  count_succ : M.SuccessorOf count steps
  nodes_graph : Graph M nodes count C.expressions
  controls_graph : Graph M controls steps C.omega
  initial : MemPair M nodes C.zero s
  final : MemPair M nodes steps x
  edges : ∀i j a b N, M.SuccessorOf j i → MemPair M nodes i a → MemPair M nodes j b → MemPair M controls i N → KP1Y.Dynamics.Expansion M Keys EN a N b

def pathFormula {n : Nat} (C : ExpressionData (Project.Term n)) (Keys EN steps count nodes controls s x : Project.Term n) : Project.Formula 1 n :=
  .conj (.mem steps C.omega) (.conj (successorFormula count steps) (.conj (graphFormula nodes count C.expressions)
    (.conj (graphFormula controls steps C.omega) (.conj (memPairFormula nodes C.zero s) (.conj (memPairFormula nodes steps x)
      (Project.Formula.forallMem steps (Project.Formula.forallMem count.weaken (Project.Formula.forallMem C.expressions.weaken.weaken
        (Project.Formula.forallMem C.expressions.weaken.weaken.weaken (Project.Formula.forallMem C.omega.weaken.weaken.weaken.weaken
          (.imp (.conj (successorFormula (.bound 3) (.bound 4)) (.conj (memPairFormula nodes.weaken.weaken.weaken.weaken.weaken (.bound 4) (.bound 2))
            (.conj (memPairFormula nodes.weaken.weaken.weaken.weaken.weaken (.bound 3) (.bound 1)) (memPairFormula controls.weaken.weaken.weaken.weaken.weaken (.bound 4) (.bound 0)))))
            (KP1Y.Dynamics.expansionFormula Keys.weaken.weaken.weaken.weaken.weaken EN.weaken.weaken.weaken.weaken.weaken (.bound 2) (.bound 0) (.bound 1)))))))))))))

theorem pathFormula_delta0 {n : Nat} (C : ExpressionData (Project.Term n)) (Keys EN steps count nodes controls s x : Project.Term n) :
    (pathFormula C Keys EN steps count nodes controls s x).IsDelta0 :=
  .conj (.mem _ _) (.conj (successorFormula_delta0 _ _) (.conj (graphFormula_delta0 _ _ _) (.conj (graphFormula_delta0 _ _ _)
    (.conj (memPairFormula_delta0 _ _ _) (.conj (memPairFormula_delta0 _ _ _) (.forallMem _ (.forallMem _ (.forallMem _ (.forallMem _ (.forallMem _
      (.imp (.conj (successorFormula_delta0 _ _) (.conj (memPairFormula_delta0 _ _ _) (.conj (memPairFormula_delta0 _ _ _) (memPairFormula_delta0 _ _ _))))
        (KP1Y.Dynamics.expansionFormula_delta0 _ _ _ _ _))))))))))))

theorem pathFormula_freeClosed {n : Nat} {C : ExpressionData (Project.Term n)} (hC : C.Closed)
    (Keys EN steps count nodes controls s x : Project.Term n) (hKeys : Keys.freeSupport=[]) (hEN : EN.freeSupport=[])
    (hSteps : steps.freeSupport=[]) (hCount : count.freeSupport=[]) (hNodes : nodes.freeSupport=[]) (hControls : controls.freeSupport=[])
    (hs : s.freeSupport=[]) (hx : x.freeSupport=[]) : (pathFormula C Keys EN steps count nodes controls s x).FreeClosed := by
  simp [pathFormula,KP1Y.Dynamics.expansionFormula,successorFormula,graphFormula,memPairFormula,codeFormula,pairFormula,
    Project.Formula.forallMem,Project.Formula.existsMem,Definitional.Formula.FreeClosed,hC.omega,hC.zero,hC.expressions,hKeys,hEN,hSteps,hCount,hNodes,hControls,hs,hx]

theorem pathFormula_iff {M : SetTheory.Structure.{u}} (he : Extensional M) {n : Nat} (e : Env M n)
    (C : ExpressionData (Project.Term n)) (Keys EN steps count nodes controls s x : Project.Term n) :
    Project.Formula.satisfies e (pathFormula C Keys EN steps count nodes controls s x) ↔
      Path M (C.eval e) (Keys.eval e) (EN.eval e) (steps.eval e) (count.eval e) (nodes.eval e) (controls.eval e) (s.eval e) (x.eval e) := by
  simp only [pathFormula,Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_mem_iff,successorFormula_iff he,
    graphFormula_iff he,memPairFormula_iff he,Project.Formula.satisfies_forallMem_iff,Project.Formula.satisfies_imp_iff,
    KP1Y.Dynamics.expansionFormula_iff he,Term.eval_weaken]
  constructor
  · rintro ⟨hLength,hCount,hNodes,hControls,hInitial,hFinal,hEdges⟩
    exact ⟨hLength,hCount,hNodes,hControls,hInitial,hFinal,fun i j a b N hs hA hB hN => hEdges i (hControls.bounds he hN).1 j (hNodes.bounds he hB).1
      a (hNodes.bounds he hA).2 b (hNodes.bounds he hB).2 N (hControls.bounds he hN).2 ⟨hs,hA,hB,hN⟩⟩
  · exact fun h => ⟨h.length,h.count_succ,h.nodes_graph,h.controls_graph,h.initial,h.final,fun i _ j _ a _ b _ N _ hs => h.edges i j a b N hs.1 hs.2.1 hs.2.2.1 hs.2.2.2⟩

def Reaches (M : SetTheory.Structure.{u}) (C : ExpressionData M.Domain) (Keys EN x s : M.Domain) : Prop :=
  ∃steps count nodes controls, Path M C Keys EN steps count nodes controls s x

def NodeSpace (M : SetTheory.Structure.{u}) (C : ExpressionData M.Domain) (S : M.Domain) : Prop :=
  ∀nodes, M.mem nodes S ↔ ∃count, M.mem count C.omega ∧ Graph M nodes count C.expressions

theorem Path.count_natural_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {Keys EN steps count nodes controls s x : M.Domain}
    (h : Path M C Keys EN steps count nodes controls s x) : M.mem count C.omega := natural_successor_mem_d hM hC h.length h.count_succ

theorem Path.bounds {M : SetTheory.Structure.{u}} (he : Extensional M) {C : ExpressionData M.Domain}
    {Keys EN steps count nodes controls s x : M.Domain} (h : Path M C Keys EN steps count nodes controls s x) : M.mem s C.expressions ∧ M.mem x C.expressions :=
  ⟨(h.nodes_graph.bounds he h.initial).2,(h.nodes_graph.bounds he h.final).2⟩

theorem Path.zero_d {M : SetTheory.Structure.{u}} {C : ExpressionData M.Domain}
    {Keys EN count nodes controls s x : M.Domain} (h : Path M C Keys EN C.zero count nodes controls s x) : s=x :=
  h.nodes_graph.unique C.zero s x h.initial h.final

theorem zero_path_exists_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) (Keys EN : M.Domain) {s : M.Domain} (hs : M.mem s C.expressions) :
    ∃nodes controls, Path M C Keys EN C.zero C.one nodes controls s s := by
  obtain ⟨nodes,hNodes,hRows⟩ := TowerReconstruction.constant_graph_exists_d hM C.one hs
  refine ⟨nodes,C.zero,hC.zero_nat,hC.one_succ,hNodes,empty_graph hC.zero_empty,
    (hRows C.zero s).mpr ⟨hC.one_succ.predecessor_mem,rfl⟩,(hRows C.zero s).mpr ⟨hC.one_succ.predecessor_mem,rfl⟩,?_⟩
  intro i j a b N _ _ _ hN
  exact False.elim (hC.zero_empty i ((empty_graph (V := C.omega) hC.zero_empty).bounds hM.1 hN).1)

theorem Path.append_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {Keys EN steps count nodes controls s x y N : M.Domain}
    (h : Path M C Keys EN steps count nodes controls s x) (hy : M.mem y C.expressions) (hN : M.mem N C.omega)
    (hEdge : KP1Y.Dynamics.Expansion M Keys EN x N y) :
    ∃count' nodes' controls', Path M C Keys EN count count' nodes' controls' s y ∧
      KP1Y.Sequences.Append M nodes' nodes count y ∧ KP1Y.Sequences.Append M controls' controls steps N := by
  obtain ⟨count',hCount',_⟩ := hC.omega.1.2 count (h.count_natural_d hM hC)
  obtain ⟨nodes',hNodesAppend⟩ := KP1Y.Sequences.append_exists_d hM nodes count y
  obtain ⟨controls',hControlsAppend⟩ := KP1Y.Sequences.append_exists_d hM controls steps N
  have hNodes := KP1Y.Sequences.graph_append_d hM h.nodes_graph hCount' hy hNodesAppend
  have hControls := KP1Y.Sequences.graph_append_d hM h.controls_graph h.count_succ hN hControlsAppend
  have hStepsNeCount : steps≠count := fun he => SetTheory.KP.mem_irrefl_d (KP1Y.models_weakKP hM) count (he ▸ h.count_succ.predecessor_mem)
  refine ⟨count',nodes',controls',⟨h.count_natural_d hM hC,hCount',hNodes,hControls,
    (KP1Y.Sequences.append_rows hM.1 hNodesAppend C.zero s).mpr (.inl h.initial),
    (KP1Y.Sequences.append_rows hM.1 hNodesAppend count y).mpr (.inr ⟨rfl,rfl⟩),?_⟩,hNodesAppend,hControlsAppend⟩
  intro i j a b k hSucc hA hB hK
  rcases (KP1Y.Sequences.append_rows hM.1 hControlsAppend i k).mp hK with hOldControl | ⟨hi,hk⟩
  · have hi := (h.controls_graph.bounds hM.1 hOldControl).1
    have hOldA : MemPair M nodes i a := by
      rcases (KP1Y.Sequences.append_rows hM.1 hNodesAppend i a).mp hA with hOld | ⟨he,_⟩
      · exact hOld
      · exact False.elim (SetTheory.KP.mem_irrefl_d (KP1Y.models_weakKP hM) count
          (he ▸ ((h.count_succ i).mpr (.inl hi))))
    have hOldB : MemPair M nodes j b := by
      rcases (KP1Y.Sequences.append_rows hM.1 hNodesAppend j b).mp hB with hOld | ⟨he,_⟩
      · exact hOld
      · subst j
        have hiNat := (omega_isOrdinal_d hM hC.omega).transitive steps h.length i hi
        have he := Structure.SuccessorOf.predecessor_eq hM.1 ((omega_isOrdinal_d hM hC.omega).mem hiNat) hSucc h.count_succ
        exact False.elim (SetTheory.KP.mem_irrefl_d (KP1Y.models_weakKP hM) steps (he ▸ hi))
    exact h.edges i j a b k hSucc hOldA hOldB hOldControl
  · subst i
    subst k
    have hOldA : MemPair M nodes steps a := by
      rcases (KP1Y.Sequences.append_rows hM.1 hNodesAppend steps a).mp hA with hOld | ⟨he,_⟩
      · exact hOld
      · exact False.elim (hStepsNeCount he)
    have hax := h.nodes_graph.unique steps a x hOldA h.final
    have hj := Structure.SuccessorOf.eq hM.1 hSucc h.count_succ
    subst j
    have hby : b=y := by
      rcases (KP1Y.Sequences.append_rows hM.1 hNodesAppend count b).mp hB with hOld | hNew
      · exact False.elim (SetTheory.KP.mem_irrefl_d (KP1Y.models_weakKP hM) count (h.nodes_graph.bounds hM.1 hOld).1)
      · exact hNew.2
    exact hax.symm ▸ hby.symm ▸ hEdge

def reachesFormula {n : Nat} (C : ExpressionData (Project.Term n)) (NodeSeq Keys EN x s : Project.Term n) : Project.Formula 1 n :=
  Project.Formula.existsMem C.omega (Project.Formula.existsMem C.omega.weaken (Project.Formula.existsMem NodeSeq.weaken.weaken
    (Project.Formula.existsMem C.sequences.weaken.weaken.weaken
      (pathFormula C.weaken.weaken.weaken.weaken Keys.weaken.weaken.weaken.weaken EN.weaken.weaken.weaken.weaken
        (.bound 3) (.bound 2) (.bound 1) (.bound 0) s.weaken.weaken.weaken.weaken x.weaken.weaken.weaken.weaken))))

theorem reachesFormula_delta0 {n : Nat} (C : ExpressionData (Project.Term n)) (NodeSeq Keys EN x s : Project.Term n) :
    (reachesFormula C NodeSeq Keys EN x s).IsDelta0 := .existsMem _ (.existsMem _ (.existsMem _ (.existsMem _ (pathFormula_delta0 _ _ _ _ _ _ _ _ _))))

theorem reachesFormula_freeClosed {n : Nat} {C : ExpressionData (Project.Term n)} (hC : C.Closed)
    (NodeSeq Keys EN x s : Project.Term n) (hS : NodeSeq.freeSupport=[]) (hKeys : Keys.freeSupport=[]) (hEN : EN.freeSupport=[]) (hx : x.freeSupport=[]) (hs : s.freeSupport=[]) :
    (reachesFormula C NodeSeq Keys EN x s).FreeClosed := by
  have hPath := pathFormula_freeClosed hC.weaken.weaken.weaken.weaken Keys.weaken.weaken.weaken.weaken EN.weaken.weaken.weaken.weaken
    (.bound 3) (.bound 2) (.bound 1) (.bound 0) s.weaken.weaken.weaken.weaken x.weaken.weaken.weaken.weaken
    (by simpa using hKeys) (by simpa using hEN) rfl rfl rfl rfl (by simpa using hs) (by simpa using hx)
  simp [reachesFormula,Project.Formula.existsMem,Definitional.Formula.FreeClosed,hC.omega,hC.sequences,hS,hPath]

theorem reachesFormula_iff {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory) {n : Nat} (e : Env M n)
    (C : ExpressionData (Project.Term n)) (NodeSeq Keys EN x s : Project.Term n)
    (hC : (C.eval e).Valid M) (hSpace : NodeSpace M (C.eval e) (NodeSeq.eval e)) :
    Project.Formula.satisfies e (reachesFormula C NodeSeq Keys EN x s) ↔ Reaches M (C.eval e) (Keys.eval e) (EN.eval e) (x.eval e) (s.eval e) := by
  simp only [reachesFormula,Project.Formula.satisfies_existsMem_iff,pathFormula_iff hM.1,ExpressionData.eval_weaken,Term.eval_weaken]
  constructor
  · rintro ⟨steps,_,count,_,nodes,_,controls,_,hPath⟩
    exact ⟨steps,count,nodes,controls,hPath⟩
  · rintro ⟨steps,count,nodes,controls,hPath⟩
    exact ⟨steps,hPath.length,count,hPath.count_natural_d hM hC,nodes,(hSpace nodes).mpr ⟨count,hPath.count_natural_d hM hC,hPath.nodes_graph⟩,
      controls,(hC.sequences controls).mpr ⟨steps,hPath.length,hPath.controls_graph⟩,hPath⟩

structure Relation (M : SetTheory.Structure.{u}) (C : ExpressionData M.Domain) (Keys EN Reach : M.Domain) : Prop where
  support : RelationSupport M Reach C.expressions C.expressions
  rows : ∀x s, MemPair M Reach x s ↔ Reaches M C Keys EN x s

private def reachSchema : Project.Delta0BinarySchema 8 where
  body := reachesFormula ⟨.bound 9,.bound 8,.bound 7,.bound 6,.bound 5⟩ (.bound 2) (.bound 4) (.bound 3) (.bound 1) (.bound 0)
  freeClosed := reachesFormula_freeClosed ⟨rfl,rfl,rfl,rfl,rfl⟩ _ _ _ _ _ rfl rfl rfl rfl rfl
  delta0 := reachesFormula_delta0 _ _ _ _ _ _

theorem reach_relation_exists_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) (Keys EN : M.Domain) : ∃Reach, Relation M C Keys EN Reach := by
  obtain ⟨NodeSeq,hSpace⟩ := KP1Y.Sequences.finite_sequences_exist_d hM hC.omega C.expressions
  let e := (((((((oneEnv C.omega).push C.zero).push C.one).push C.sequences).push C.expressions).push Keys).push EN).push NodeSeq
  obtain ⟨Reach,hSupport,hRaw⟩ := relation_comprehension_d hM reachSchema e C.expressions C.expressions
  have hφ (x s : M.Domain) : Project.Formula.satisfies ((e.push x).push s) reachSchema.body ↔ Reaches M C Keys EN x s :=
    reachesFormula_iff hM _ _ _ _ _ _ _ hC hSpace
  refine ⟨Reach,hSupport,fun x s => ?_⟩
  rw [hRaw x s,hφ]
  refine ⟨fun h => h.2.2,fun h => ?_⟩
  obtain ⟨steps,count,nodes,controls,hPath⟩ := h
  have hBounds := hPath.bounds hM.1
  exact ⟨hBounds.2,hBounds.1,steps,count,nodes,controls,hPath⟩

theorem Relation.unique {M : SetTheory.Structure.{u}} (he : Extensional M) {C : ExpressionData M.Domain} {Keys EN R S : M.Domain}
    (hR : Relation M C Keys EN R) (hS : Relation M C Keys EN S) : R=S := relation_ext he hR.support hS.support (fun x s => (hR.rows x s).trans (hS.rows x s).symm)

theorem Relation.reflexive_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {Keys EN Reach s : M.Domain} (h : Relation M C Keys EN Reach) (hs : M.mem s C.expressions) : MemPair M Reach s s := by
  obtain ⟨nodes,controls,hPath⟩ := zero_path_exists_d hM hC Keys EN hs
  exact (h.rows s s).mpr ⟨C.zero,C.one,nodes,controls,hPath⟩

theorem Reaches.append_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {Keys EN x s y N : M.Domain} (h : Reaches M C Keys EN x s)
    (hy : M.mem y C.expressions) (hN : M.mem N C.omega) (hStep : KP1Y.Dynamics.Expansion M Keys EN x N y) : Reaches M C Keys EN y s := by
  obtain ⟨steps,count,nodes,controls,hPath⟩ := h
  obtain ⟨count',nodes',controls',hPath',_,_⟩ := hPath.append_d hM hC hy hN hStep
  exact ⟨count,count',nodes',controls',hPath'⟩

theorem Relation.expansion_reachable_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {Keys EN Reach s N t : M.Domain} (h : Relation M C Keys EN Reach)
    (hs : M.mem s C.expressions) (hN : M.mem N C.omega) (ht : M.mem t C.expressions) (hStep : KP1Y.Dynamics.Expansion M Keys EN s N t) : MemPair M Reach t s :=
  (h.rows t s).mpr (((h.rows s s).mp (h.reflexive_d hM hC hs)).append_d hM hC ht hN hStep)

private def walkSchema : Project.Delta0UnarySchema 4 where
  body := Project.Formula.forallMem (.bound 4) (.imp (memPairFormula (.bound 4) (.bound 1) (.bound 0)) (memPairFormula (.bound 3) (.bound 0) (.bound 2)))
  freeClosed := by simp [memPairFormula,codeFormula,pairFormula,Project.Formula.forallMem,Project.Formula.existsMem,Definitional.Formula.FreeClosed]
  delta0 := .forallMem _ (.imp (memPairFormula_delta0 _ _ _) (memPairFormula_delta0 _ _ _))

private theorem walkSchema_iff {M : SetTheory.Structure.{u}} (he : Extensional M) (E nodes Reach s i : M.Domain) :
    Project.Formula.satisfies (((((oneEnv E).push nodes).push Reach).push s).push i) walkSchema.body ↔
      ∀u, M.mem u E → MemPair M nodes i u → MemPair M Reach u s := by
  simp only [walkSchema,Project.Formula.satisfies_forallMem_iff,Project.Formula.satisfies_imp_iff,memPairFormula_iff he]
  rfl

theorem Relation.walk_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {Keys EN Reach steps count nodes controls s x z : M.Domain}
    (hR : Relation M C Keys EN Reach) (hPath : Path M C Keys EN steps count nodes controls s x) (hStart : MemPair M Reach s z) : MemPair M Reach x z := by
  let e := (((oneEnv C.expressions).push nodes).push Reach).push z
  have hAll := natural_induction_d hM walkSchema.toUnarySchema e hC.omega
    (fun zero hz => (walkSchema_iff hM.1 C.expressions nodes Reach z zero).mpr (by
      have he := hM.1.eq_of_same_members zero C.zero (fun v => iff_of_false (hz v) (hC.zero_empty v))
      subst zero
      intro u _ hAt
      exact (hPath.nodes_graph.unique C.zero u s hAt hPath.initial).symm ▸ hStart))
    (fun i _ ih j hs => (walkSchema_iff hM.1 C.expressions nodes Reach z j).mpr (by
      intro v hv hV
      have hJ := (hPath.nodes_graph.bounds hM.1 hV).1
      have hi : M.mem i steps := by
        rcases (hPath.count_succ j).mp hJ with hj | he
        · exact ((omega_isOrdinal_d hM hC.omega).mem hPath.length).transitive j hj i hs.predecessor_mem
        · exact (hM.1.eq_of_same_members j steps he) ▸ hs.predecessor_mem
      obtain ⟨u,hu,hU⟩ := hPath.nodes_graph.total i ((hPath.count_succ i).mpr (.inl hi))
      obtain ⟨N,hN,hControl⟩ := hPath.controls_graph.total i hi
      have hReach := (walkSchema_iff hM.1 C.expressions nodes Reach z i).mp ih u hu hU
      exact (hR.rows v z).mpr (((hR.rows u z).mp hReach).append_d hM hC hv hN (hPath.edges i j u v N hs hU hV hControl))))
  exact (walkSchema_iff hM.1 C.expressions nodes Reach z steps).mp (hAll steps hPath.length) x (hPath.bounds hM.1).2 hPath.final

theorem Relation.transitive_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {Keys EN Reach x y z : M.Domain} (h : Relation M C Keys EN Reach)
    (hXY : MemPair M Reach x y) (hYZ : MemPair M Reach y z) : MemPair M Reach x z := by
  obtain ⟨steps,count,nodes,controls,hPath⟩ := (h.rows x y).mp hXY
  exact h.walk_d hM hC hPath hYZ

/-- 通过第二条内部路径逐步追加真实节点与控制图，得到实际合成路径。 -/
theorem concatenate_paths_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {Keys EN a ac an av b bc bn bv s t x : M.Domain}
    (hA : Path M C Keys EN a ac an av s t) (hB : Path M C Keys EN b bc bn bv t x) :
    ∃steps count nodes controls, Path M C Keys EN steps count nodes controls s x := by
  obtain ⟨Reach,hR⟩ := reach_relation_exists_d hM hC Keys EN
  have hST := (hR.rows t s).mpr ⟨a,ac,an,av,hA⟩
  have hSX := hR.walk_d hM hC hB hST
  exact (hR.rows x s).mp hSX

private theorem successor_inside_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {n size i j : M.Domain} (hn : M.mem n C.omega)
    (hSize : M.SuccessorOf size n) (hi : M.mem i n) (hs : M.SuccessorOf j i) : M.mem j size := by
  have hOrd := omega_isOrdinal_d hM hC.omega
  have hiω := hOrd.transitive n hn i hi
  have hjω := natural_successor_mem_d hM hC hiω hs
  have hSub : M.MemberSubset j n := by
    intro x hx
    rcases (hs x).mp hx with hxi | he
    · exact (hOrd.mem hn).transitive i hi x hxi
    · exact (hM.1.eq_of_same_members x i he).symm ▸ hi
  rcases ordinal_subset_cases_d hM (hOrd.mem hjω) (hOrd.mem hn) hSub with he | hjn
  · exact he.symm ▸ hSize.predecessor_mem
  · exact (hSize j).mpr (.inl hjn)

private def shiftSchema : Project.Delta0BinarySchema 2 where
  body := Project.Formula.existsMem (.bound 2) (.conj (successorFormula (.bound 0) (.bound 2)) (memPairFormula (.bound 4) (.bound 0) (.bound 1)))
  freeClosed := by simp [successorFormula,memPairFormula,codeFormula,pairFormula,Project.Formula.forallMem,Project.Formula.existsMem,Definitional.Formula.FreeClosed]
  delta0 := .existsMem _ (.conj (successorFormula_delta0 _ _) (memPairFormula_delta0 _ _ _))

theorem shift_graph_exists_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {n size F A : M.Domain}
    (hn : M.mem n C.omega) (hSize : M.SuccessorOf size n) (hF : Graph M F size A) :
    ∃G, Graph M G n A ∧ ∀i j a, M.mem i n → M.SuccessorOf j i → (MemPair M G i a ↔ MemPair M F j a) := by
  obtain ⟨G,hSupport,hRaw⟩ := relation_comprehension_d hM shiftSchema ((oneEnv F).push size) n A
  have hRows (i a : M.Domain) : MemPair M G i a ↔ M.mem i n ∧ ∃j, M.mem j size ∧ M.SuccessorOf j i ∧ MemPair M F j a := by
    have hφ : Project.Formula.satisfies ((((oneEnv F).push size).push i).push a) shiftSchema.body ↔
        ∃j, M.mem j size ∧ M.SuccessorOf j i ∧ MemPair M F j a := by
      simp only [shiftSchema,Project.Formula.satisfies_existsMem_iff,Project.Formula.satisfies_conj_iff,successorFormula_iff hM.1,memPairFormula_iff hM.1]
      rfl
    rw [hRaw i a,hφ]
    exact ⟨fun h => ⟨h.1,h.2.2⟩,fun ⟨hi,j,hj,hs,hA⟩ => ⟨hi,(hF.bounds hM.1 hA).2,j,hj,hs,hA⟩⟩
  have hRead (i j a : M.Domain) (hi : M.mem i n) (hs : M.SuccessorOf j i) : MemPair M G i a ↔ MemPair M F j a := by
    rw [hRows i a]
    exact ⟨fun ⟨_,j',_,hs',hA⟩ => (Structure.SuccessorOf.eq hM.1 hs' hs) ▸ hA,
      fun hA => ⟨hi,j,successor_inside_d hM hC hn hSize hi hs,hs,hA⟩⟩
  refine ⟨G,⟨hSupport,?_,?_⟩,hRead⟩
  · intro i hi
    obtain ⟨j,hs,_⟩ := hC.omega.1.2 i ((omega_isOrdinal_d hM hC.omega).transitive n hn i hi)
    obtain ⟨a,ha,hA⟩ := hF.total j (successor_inside_d hM hC hn hSize hi hs)
    exact ⟨a,ha,(hRead i j a hi hs).mpr hA⟩
  · intro i a b hA hB
    obtain ⟨hi,j,_,hs,_⟩ := (hRows i a).mp hA
    exact hF.unique j a b ((hRead i j a hi hs).mp hA) ((hRead i j b hi hs).mp hB)

/-- 真正移除首个节点与控制项，两个尾图都由后继索引重排构造。 -/
theorem Path.uncons_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {Keys EN steps previous count nodes controls s x : M.Domain}
    (h : Path M C Keys EN steps count nodes controls s x) (hs : M.SuccessorOf steps previous) :
    ∃t N nodes' controls', M.mem t C.expressions ∧ M.mem N C.omega ∧ KP1Y.Dynamics.Expansion M Keys EN s N t ∧
      Path M C Keys EN previous steps nodes' controls' t x := by
  have hpω := (omega_isOrdinal_d hM hC.omega).transitive steps h.length previous hs.predecessor_mem
  have hz : M.mem C.zero steps := (hC.zero_mem_iff hM h.length).mpr (fun he => hC.zero_empty previous (he ▸ hs.predecessor_mem))
  obtain ⟨t,ht,hT⟩ := h.nodes_graph.total C.one (successor_inside_d hM hC h.length h.count_succ hz hC.one_succ)
  obtain ⟨N,hN,hNAt⟩ := h.controls_graph.total C.zero hz
  obtain ⟨nodes',hNodes,hNodeRows⟩ := shift_graph_exists_d hM hC h.length h.count_succ h.nodes_graph
  obtain ⟨controls',hControls,hControlRows⟩ := shift_graph_exists_d hM hC hpω hs h.controls_graph
  refine ⟨t,N,nodes',controls',ht,hN,h.edges C.zero C.one s t N hC.one_succ h.initial hT hNAt,
    ⟨hpω,hs,hNodes,hControls,(hNodeRows C.zero C.one t hz hC.one_succ).mpr hT,
      (hNodeRows previous steps x hs.predecessor_mem hs).mpr h.final,?_⟩⟩
  intro i j a b k hij hA hB hK
  have hi := (hControls.bounds hM.1 hK).1
  have hiSteps := (hs i).mpr (.inl hi)
  have hj := (hNodes.bounds hM.1 hB).1
  obtain ⟨j',hjj',_⟩ := hC.omega.1.2 j ((omega_isOrdinal_d hM hC.omega).transitive steps h.length j hj)
  exact h.edges j j' a b k hjj' ((hNodeRows i j a hiSteps hij).mp hA) ((hNodeRows j j' b hj hjj').mp hB) ((hControlRows i j k hi hij).mp hK)

private def decomposeSchema : Project.Delta0UnarySchema 9 where
  body := Project.Formula.forallMem (.bound 5) (Project.Formula.forallMem (.bound 6) (Project.Formula.forallMem (.bound 11)
    (Project.Formula.forallMem (.bound 5) (Project.Formula.forallMem (.bound 10)
      (.imp (.conj (pathFormula ⟨.bound 14,.bound 13,.bound 12,.bound 11,.bound 10⟩ (.bound 9) (.bound 8)
        (.bound 5) (.bound 2) (.bound 1) (.bound 0) (.bound 4) (.bound 3))
        (.neg (Project.Formula.extensionalEq (.bound 3) (.bound 4))))
        (Project.Formula.existsMem (.bound 14) (Project.Formula.existsMem (.bound 11)
          (.conj (KP1Y.Dynamics.expansionFormula (.bound 11) (.bound 10) (.bound 6) (.bound 1) (.bound 0))
            (.conj (.neg (Project.Formula.extensionalEq (.bound 0) (.bound 6))) (memPairFormula (.bound 8) (.bound 5) (.bound 0)))))))))))
  freeClosed := by
    have hp := pathFormula_freeClosed (n := 15) (C := ⟨.bound 14,.bound 13,.bound 12,.bound 11,.bound 10⟩) ⟨rfl,rfl,rfl,rfl,rfl⟩
      (.bound 9) (.bound 8) (.bound 5) (.bound 2) (.bound 1) (.bound 0) (.bound 4) (.bound 3) rfl rfl rfl rfl rfl rfl rfl rfl
    simp [KP1Y.Dynamics.expansionFormula,memPairFormula,codeFormula,pairFormula,Project.Formula.forallMem,
      Project.Formula.existsMem,Definitional.Formula.FreeClosed,hp]
  delta0 := .forallMem _ (.forallMem _ (.forallMem _ (.forallMem _ (.forallMem _ (.imp
    (.conj (pathFormula_delta0 _ _ _ _ _ _ _ _ _) (.neg (.atom _ _ _)))
      (.existsMem _ (.existsMem _ (.conj (KP1Y.Dynamics.expansionFormula_delta0 _ _ _ _ _) (.conj (.neg (.atom _ _ _)) (memPairFormula_delta0 _ _ _))))))))))

private def decomposeEnv {M : SetTheory.Structure.{u}} (C : ExpressionData M.Domain) (Keys EN NodeSeq Reach : M.Domain) : Env M 9 :=
  ((((((((oneEnv C.omega).push C.zero).push C.one).push C.sequences).push C.expressions).push Keys).push EN).push NodeSeq).push Reach

private theorem decomposeSchema_iff {M : SetTheory.Structure.{u}} (he : Extensional M)
    (C : ExpressionData M.Domain) (Keys EN NodeSeq Reach steps : M.Domain) :
    Project.Formula.satisfies ((decomposeEnv C Keys EN NodeSeq Reach).push steps) decomposeSchema.body ↔
      ∀s, M.mem s C.expressions → ∀x, M.mem x C.expressions → ∀count, M.mem count C.omega →
      ∀nodes, M.mem nodes NodeSeq → ∀controls, M.mem controls C.sequences → Path M C Keys EN steps count nodes controls s x → x≠s →
        ∃N, M.mem N C.omega ∧ ∃t, M.mem t C.expressions ∧ KP1Y.Dynamics.Expansion M Keys EN s N t ∧ t≠s ∧ MemPair M Reach x t := by
  simp only [decomposeSchema,Project.Formula.satisfies_forallMem_iff,Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_conj_iff,
    Project.Formula.satisfies_neg_iff,Project.Formula.satisfies_extensionalEq_iff_eq he,pathFormula_iff he,
    Project.Formula.satisfies_existsMem_iff,KP1Y.Dynamics.expansionFormula_iff he,memPairFormula_iff he]
  exact ⟨fun h s hs x hx count hc nodes hn controls hv hp hne => h s hs x hx count hc nodes hn controls hv ⟨hp,hne⟩,
    fun h s hs x hx count hc nodes hn controls hv hp => h s hs x hx count hc nodes hn controls hv hp.1 hp.2⟩

theorem Relation.first_step_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {Keys EN Reach s x : M.Domain} (hR : Relation M C Keys EN Reach)
    (hReach : MemPair M Reach x s) (hNe : x≠s) :
    ∃N, M.mem N C.omega ∧ ∃t, M.mem t C.expressions ∧ KP1Y.Dynamics.Expansion M Keys EN s N t ∧ t≠s ∧ MemPair M Reach x t := by
  obtain ⟨NodeSeq,hSpace⟩ := KP1Y.Sequences.finite_sequences_exist_d hM hC.omega C.expressions
  have hAll := natural_induction_d hM decomposeSchema.toUnarySchema (decomposeEnv C Keys EN NodeSeq Reach) hC.omega
    (fun zero hz => (decomposeSchema_iff hM.1 C Keys EN NodeSeq Reach zero).mpr (by
      have he := hM.1.eq_of_same_members zero C.zero (fun v => iff_of_false (hz v) (hC.zero_empty v))
      subst zero
      intro s _ x _ count _ nodes _ controls _ hPath hne
      exact False.elim (hne hPath.zero_d.symm)))
    (fun previous _ ih steps hs => (decomposeSchema_iff hM.1 C Keys EN NodeSeq Reach steps).mpr (by
      intro s hS x hX count _ nodes _ controls _ hPath hne
      obtain ⟨t,N,nodes',controls',ht,hN,hStep,hTail⟩ := hPath.uncons_d hM hC hs
      by_cases hts : t=s
      · subst t
        exact (decomposeSchema_iff hM.1 C Keys EN NodeSeq Reach previous).mp ih s hS x hX steps (hTail.count_natural_d hM hC)
          nodes' ((hSpace nodes').mpr ⟨steps,hTail.count_natural_d hM hC,hTail.nodes_graph⟩)
          controls' ((hC.sequences controls').mpr ⟨previous,hTail.length,hTail.controls_graph⟩) hTail hne
      · exact ⟨N,hN,t,ht,hStep,hts,(hR.rows x t).mpr ⟨previous,steps,nodes',controls',hTail⟩⟩))
  obtain ⟨steps,count,nodes,controls,hPath⟩ := (hR.rows x s).mp hReach
  exact (decomposeSchema_iff hM.1 C Keys EN NodeSeq Reach steps).mp (hAll steps hPath.length)
    s (hPath.bounds hM.1).1 x (hPath.bounds hM.1).2 count (hPath.count_natural_d hM hC)
    nodes ((hSpace nodes).mpr ⟨count,hPath.count_natural_d hM hC,hPath.nodes_graph⟩)
    controls ((hC.sequences controls).mpr ⟨steps,hPath.length,hPath.controls_graph⟩) hPath hNe

/-- O02 DescendantSystem所需的四个Reach字段，量词顺序与原接口一致。 -/
structure ReachFields (M : SetTheory.Structure.{u}) (omega E Keys EN Reach : M.Domain) : Prop where
  reflexive : ∀s, M.mem s E → MemPair M Reach s s
  transitive : ∀x, M.mem x E → ∀y, M.mem y E → ∀z, M.mem z E → MemPair M Reach x y → MemPair M Reach y z → MemPair M Reach x z
  expansion_reachable : ∀s, M.mem s E → ∀N, M.mem N omega → ∀t, M.mem t E → KP1Y.Dynamics.Expansion M Keys EN s N t → MemPair M Reach t s
  first_step : ∀s, M.mem s E → ∀x, M.mem x E → MemPair M Reach x s → x≠s →
    ∃N, M.mem N omega ∧ ∃t, M.mem t E ∧ KP1Y.Dynamics.Expansion M Keys EN s N t ∧ t≠s ∧ MemPair M Reach x t

theorem Relation.fields_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {Keys EN Reach : M.Domain} (h : Relation M C Keys EN Reach) :
    ReachFields M C.omega C.expressions Keys EN Reach :=
  ⟨fun _ hs => h.reflexive_d hM hC hs,
    fun _ _ _ _ _ _ hXY hYZ => h.transitive_d hM hC hXY hYZ,
    fun _ hs _ hN _ ht hStep => h.expansion_reachable_d hM hC hs hN ht hStep,
    fun _ _ _ _ hReach hNe => h.first_step_d hM hC hReach hNe⟩

theorem expansion_step_iff_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} {Keys EN s N t : M.Domain}
    (hEN : Expansion.Graph M C T Keys EN) : KP1Y.Dynamics.Expansion M Keys EN s N t ↔ Expansion.Expands M C T s N t := by
  constructor
  · rintro ⟨key,_,hCode,hAt⟩
    exact (hEN.at_iff hM.1 hC hCode).mp hAt
  · intro hExpand
    obtain ⟨key,hCode⟩ := codes_total hM s N
    have hAt := (hEN.at_iff hM.1 hC hCode).mpr hExpand
    exact ⟨key,(hEN.graph.bounds hM.1 hAt).1,hCode,hAt⟩

theorem Relation.actual_expansion_reachable_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} {Keys EN Reach s N t : M.Domain}
    (hEN : Expansion.Graph M C T Keys EN) (hR : Relation M C Keys EN Reach) (h : Expansion.Expands M C T s N t) : MemPair M Reach t s := by
  have hs : M.mem s C.expressions := by
    obtain ⟨_,m,hm,hLegal,_⟩ := h
    exact (hC.expressions s).mpr ⟨m,hm,hLegal⟩
  have hStep := (expansion_step_iff_d hM hC hEN).mpr h
  have ht : M.mem t C.expressions := by
    obtain ⟨_,_,_,hAt⟩ := hStep
    exact (hEN.graph.bounds hM.1 hAt).2
  exact hR.expansion_reachable_d hM hC hs h.1 ht hStep

/-- 对已经实际构造的全局EN形成Reach，并交付O02字段；不附加词序或秩下降假设。 -/
theorem expansion_reachability_exists_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} {Keys EN : M.Domain}
    (hEN : Expansion.Graph M C T Keys EN) :
    ∃Reach, Relation M C Keys EN Reach ∧ ReachFields M C.omega C.expressions Keys EN Reach ∧
      ∀s N t, Expansion.Expands M C T s N t → MemPair M Reach t s := by
  obtain ⟨Reach,hReach⟩ := reach_relation_exists_d hM hC Keys EN
  exact ⟨Reach,hReach,hReach.fields_d hM hC,fun _ _ _ h => hReach.actual_expansion_reachable_d hM hC hEN h⟩

end KP1Y.OneYFinite.Reachability
