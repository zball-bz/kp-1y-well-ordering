import KP1Y.OrdinalRank
import KP1Y.FunctionIteration

/-! 实际序数值函数推出内部关系极小元及集合编码轨迹终止。

`MemPair R y x` 的方向表示从 x 向 y 走一步。秩函数不要求单射。
所有最小元选择只针对模型内部集合；这里没有宿主 membership 良基性、
标准 ω 或 dependent choice 的假设。结论是通用条件定理，尚未实例化到 1-Y。
-/
namespace KP1Y.Dynamics
open YesMetaZFC YesMetaZFC.SetTheory YesMetaZFC.SetTheory.Definitional
open KP1Y.Kuratowski KP1Y.Functions KP1Y.Bounded
universe u

/-- 实际关系的每一步使实际函数 μ 的序数值严格下降。 -/
def Decreases (M : SetTheory.Structure.{u}) (R μ E χ : M.Domain) : Prop :=
  ∀ x, M.mem x E → ∀ y, M.mem y E → ∀ a, M.mem a χ → ∀ b, M.mem b χ →
    MemPair M R y x ∧ MemPair M μ x a ∧ MemPair M μ y b → M.mem b a

def decreasesFormula {n : Nat} (R μ E χ : Project.Term n) : Project.Formula 1 n :=
  Project.Formula.forallMem E (Project.Formula.forallMem E.weaken
    (Project.Formula.forallMem χ.weaken.weaken (Project.Formula.forallMem χ.weaken.weaken.weaken
      (.imp (.conj (memPairFormula R.weaken.weaken.weaken.weaken (.bound 2) (.bound 3))
        (.conj (memPairFormula μ.weaken.weaken.weaken.weaken (.bound 3) (.bound 1))
          (memPairFormula μ.weaken.weaken.weaken.weaken (.bound 2) (.bound 0))))
        (.mem (.bound 0) (.bound 1))))))

theorem decreasesFormula_delta0 {n : Nat} (R μ E χ : Project.Term n) :
    (decreasesFormula R μ E χ).IsDelta0 :=
  .forallMem _ (.forallMem _ (.forallMem _ (.forallMem _
    (.imp (.conj (memPairFormula_delta0 _ _ _)
      (.conj (memPairFormula_delta0 _ _ _) (memPairFormula_delta0 _ _ _))) (.mem _ _)))))

theorem decreasesFormula_iff {M : SetTheory.Structure.{u}} (he : Extensional M) {n : Nat}
    (env : Env M n) (R μ E χ : Project.Term n) :
    Project.Formula.satisfies env (decreasesFormula R μ E χ) ↔
      Decreases M (R.eval env) (μ.eval env) (E.eval env) (χ.eval env) := by
  simp only [decreasesFormula, Decreases, Project.Formula.satisfies_forallMem_iff,
    Project.Formula.satisfies_imp_iff, Project.Formula.satisfies_conj_iff,
    Project.Formula.satisfies_mem_iff, memPairFormula_iff he, Definitional.Term.eval_weaken]
  rfl

structure RankedRelation (M : SetTheory.Structure.{u}) (R μ E χ : M.Domain) : Prop where
  ordinal : M.IsOrdinal χ
  graph : Graph M μ E χ
  decreases : Decreases M R μ E χ

def rankedRelationFormula {n : Nat} (R μ E χ : Project.Term n) : Project.Formula 1 n :=
  .conj (ordinalFormula χ) (.conj (graphFormula μ E χ) (decreasesFormula R μ E χ))

theorem rankedRelationFormula_delta0 {n : Nat} (R μ E χ : Project.Term n) :
    (rankedRelationFormula R μ E χ).IsDelta0 :=
  .conj (ordinalFormula_delta0 _) (.conj (graphFormula_delta0 _ _ _) (decreasesFormula_delta0 _ _ _ _))

theorem rankedRelationFormula_iff {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory) {n : Nat}
    (env : Env M n) (R μ E χ : Project.Term n) :
    Project.Formula.satisfies env (rankedRelationFormula R μ E χ) ↔
      RankedRelation M (R.eval env) (μ.eval env) (E.eval env) (χ.eval env) := by
  simp only [rankedRelationFormula, Project.Formula.satisfies_conj_iff, ordinalFormula_iff hM,
    graphFormula_iff hM.1, decreasesFormula_iff hM.1]
  exact ⟨fun h => ⟨h.1,h.2.1,h.2.2⟩,fun h => ⟨h.ordinal,h.graph,h.decreases⟩⟩

private def imageSchema : Project.Delta0UnarySchema 2 where
  body := Project.Formula.existsMem (.bound 1) (memPairFormula (.bound 3) (.bound 0) (.bound 1))
  freeClosed := by
    simp [memPairFormula,codeFormula,pairFormula,Project.Formula.forallMem,Project.Formula.existsMem,
      Definitional.Formula.FreeClosed]
  delta0 := .existsMem _ (memPairFormula_delta0 _ _ _)

private theorem imageSchema_iff {M : SetTheory.Structure.{u}} (he : Extensional M) (μ S a : M.Domain) :
    Project.Formula.satisfies (((oneEnv μ).push S).push a) imageSchema.body ↔
      ∃ x, M.mem x S ∧ MemPair M μ x a := by
  simp only [imageSchema,Project.Formula.satisfies_existsMem_iff,memPairFormula_iff he]
  rfl

/-- 不要求 μ 单射；最小的是实际像集合中的序数值。 -/
theorem rank_minimum_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {μ E χ S : M.Domain} (hχ : M.IsOrdinal χ) (hμ : Graph M μ E χ)
    (hSE : M.MemberSubset S E) (hNe : ∃ x, M.mem x S) :
    ∃ x, M.mem x S ∧ ∃ a, M.mem a χ ∧ MemPair M μ x a ∧
      ∀ y, M.mem y S → ∀ b, MemPair M μ y b → (a=b ∨ M.mem a b) := by
  obtain ⟨D,hRaw⟩ := SetTheory.KP.separation_exists_d (KP1Y.models_weakKP hM)
    imageSchema ((oneEnv μ).push S) χ
  have hD (a : M.Domain) : M.mem a D ↔ M.mem a χ ∧ ∃ x, M.mem x S ∧ MemPair M μ x a := by
    simpa only [imageSchema_iff hM.1] using hRaw a
  have hDNe : ∃ a, M.mem a D := by
    obtain ⟨x,hx⟩ := hNe
    obtain ⟨a,ha,hxa⟩ := hμ.total x (hSE x hx)
    exact ⟨a,(hD a).mpr ⟨ha,x,hx,hxa⟩⟩
  obtain ⟨a,haD,hMin⟩ := hχ.wellOrder.least D (fun a ha => ((hD a).mp ha).1) hDNe
  obtain ⟨ha,x,hx,hxa⟩ := (hD a).mp haD
  refine ⟨x,hx,a,ha,hxa,?_⟩
  intro y hy b hyb
  rcases hMin b ((hD b).mpr ⟨(hμ.bounds hM.1 hyb).2,y,hy,hyb⟩) with he | hab
  · exact Or.inl (hM.1.eq_of_same_members a b he)
  · exact Or.inr hab

/-- 每个非空内部子集含一个无更低关系后继的元素；并非宿主 `WellFounded`。 -/
theorem RankedRelation.minimal_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {R μ E χ S : M.Domain} (hRank : RankedRelation M R μ E χ)
    (hSE : M.MemberSubset S E) (hNe : ∃ x, M.mem x S) :
    ∃ x, M.mem x S ∧ ∀ y, M.mem y S → ¬MemPair M R y x := by
  obtain ⟨x,hx,a,ha,hxa,hMin⟩ := rank_minimum_d hM hRank.ordinal hRank.graph hSE hNe
  refine ⟨x,hx,?_⟩
  intro y hy hyx
  obtain ⟨b,hb,hyb⟩ := hRank.graph.total y (hSE y hy)
  have hba := hRank.decreases x (hSE x hx) y (hSE y hy) a ha b hb ⟨hyx,hxa,hyb⟩
  rcases hMin y hy b hyb with he | hab
  · subst b
    exact hRank.ordinal.wellOrder.linear.irrefl a ha hba
  · exact hRank.ordinal.wellOrder.linear.irrefl a ha
      (hRank.ordinal.wellOrder.linear.trans a ha b hb a ha hab hba)

/-- 不存在处处严格下降的实际函数 ω→χ；ω 可为非标准 KP 模型的内部 ω。 -/
theorem ordinal_omega_graph_not_descending_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {ω χ F : M.Domain} (hω : M.IsOmega ω) (hχ : M.IsOrdinal χ) (hF : Graph M F ω χ) :
    ¬(∀ i j a b, M.SuccessorOf j i → MemPair M F i a → MemPair M F j b → M.mem b a) := by
  intro hDesc
  obtain ⟨zero,_,hz⟩ := hω.1.1
  obtain ⟨i,hi,a,ha,hia,hMin⟩ := rank_minimum_d hM hχ hF (fun _ h => h) ⟨zero,hz⟩
  obtain ⟨j,hSucc,hj⟩ := hω.1.2 i hi
  obtain ⟨b,hb,hjb⟩ := hF.total j hj
  have hba := hDesc i j a b hSucc hia hjb
  rcases hMin j hj b hjb with he | hab
  · subst b
    exact hχ.wellOrder.linear.irrefl a ha hba
  · exact hχ.wellOrder.linear.irrefl a ha (hχ.wellOrder.linear.trans a ha b hb a ha hab hba)

/-- 下降关系没有实际集合编码的 ω 长轨迹。这里只复合两个给定的实际图。 -/
theorem RankedRelation.no_omega_trajectory_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {R μ E χ ω H : M.Domain} (hRank : RankedRelation M R μ E χ)
    (hω : M.IsOmega ω) (hH : Graph M H ω E) :
    ¬(∀ i j x y, M.SuccessorOf j i → MemPair M H i x → MemPair M H j y → MemPair M R y x) := by
  intro hStep
  obtain ⟨F,hF⟩ := KP1Y.Assignments.tuple_value_exists_d hM hH hRank.graph
  apply ordinal_omega_graph_not_descending_d hM hω hRank.ordinal hF.values
  intro i j a b hSucc hia hjb
  have hi := (hF.values.bounds hM.1 hia).1
  have hj := (hF.values.bounds hM.1 hjb).1
  have ha := (hF.values.bounds hM.1 hia).2
  have hb := (hF.values.bounds hM.1 hjb).2
  obtain ⟨x,hx,hix⟩ := hH.total i hi
  obtain ⟨y,hy,hjy⟩ := hH.total j hj
  exact hRank.decreases x hx y hy a ha b hb
    ⟨hStep i j x y hSucc hix hjy,
      (hF.rows i hi x hx a ha hix).mp hia,(hF.rows j hj y hy b hb hjy).mp hjb⟩

/-- 非终点处遵循下降关系的给定 ω 轨迹必然在某个内部自然数时刻命中终点。 -/
theorem RankedRelation.trajectory_hits_terminal_d {M : SetTheory.Structure.{u}}
    (hM : M.Models KP1Y.theory) {R μ E χ ω H terminal : M.Domain}
    (hRank : RankedRelation M R μ E χ) (hω : M.IsOmega ω) (hH : Graph M H ω E)
    (hStep : ∀ i j x y, M.SuccessorOf j i → MemPair M H i x → MemPair M H j y →
      x≠terminal → MemPair M R y x) :
    ∃ i, M.mem i ω ∧ MemPair M H i terminal := by
  classical
  apply Classical.byContradiction
  intro hNo
  apply hRank.no_omega_trajectory_d hM hω hH
  intro i j x y hSucc hix hjy
  apply hStep i j x y hSucc hix hjy
  intro he
  subst x
  exact hNo ⟨i,(hH.bounds hM.1 hix).1,hix⟩

/-- 对可定义的确定性全函数实际构造迭代图，再由秩证明命中终点。
本定理的全性和唯一性属于给定 Δ₀ 步骤公式，不诉诸对象选择公理。 -/
theorem definable_iteration_hits_terminal_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {n : Nat} (φ : Project.Delta0BinarySchema n) (env : Env M n)
    {R μ E χ ω base terminal : M.Domain} (hRank : RankedRelation M R μ E χ)
    (hω : M.IsOmega ω) (hBase : M.mem base E)
    (hTotal : ∀ x, M.mem x E → ∃ y, M.mem y E ∧ KP1Y.Iteration.nextDenote φ env x y)
    (hUnique : ∀ x, M.mem x E → ∀ y, M.mem y E → ∀ z, M.mem z E →
      KP1Y.Iteration.nextDenote φ env x y → KP1Y.Iteration.nextDenote φ env x z → y=z)
    (hStep : ∀ x, M.mem x E → ∀ y, M.mem y E → x≠terminal →
      KP1Y.Iteration.nextDenote φ env x y → MemPair M R y x) :
    ∃ H, KP1Y.Iteration.Iterator M (KP1Y.Iteration.nextDenote φ env) ω E base H ∧
      ∃ i, M.mem i ω ∧ MemPair M H i terminal := by
  obtain ⟨H,hH⟩ := KP1Y.Iteration.iterator_exists_d hM φ env hω hBase hTotal hUnique
  refine ⟨H,hH,hRank.trajectory_hits_terminal_d hM hω hH.graph ?_⟩
  intro i j x y hSucc hix hjy hNot
  exact hStep x (hH.graph.bounds hM.1 hix).2 y (hH.graph.bounds hM.1 hjy).2 hNot
    (hH.transition i j x y hSucc hix hjy)

/-- 只量化内部集合子集的关系良基性。 -/
def InternalWellFounded (M : SetTheory.Structure.{u}) (R E : M.Domain) : Prop :=
  ∀ S, M.MemberSubset S E → (∃ x, M.mem x S) →
    ∃ x, M.mem x S ∧ ∀ y, M.mem y S → ¬MemPair M R y x

def internalWellFoundedFormula {n : Nat} (R E : Project.Term n) : Project.Formula 1 n :=
  .forallE (.imp (.conj (Project.Formula.subset (.bound 0) E.weaken)
    (Project.Formula.existsMem (.bound 0) (Project.Formula.extensionalEq (.bound 0) (.bound 0))))
    (Project.Formula.existsMem (.bound 0) (Project.Formula.forallMem (.bound 1)
      (.neg (memPairFormula R.weaken.weaken.weaken (.bound 0) (.bound 1))))))

theorem internalWellFoundedFormula_iff {M : SetTheory.Structure.{u}} (he : Extensional M) {n : Nat}
    (env : Env M n) (R E : Project.Term n) :
    Project.Formula.satisfies env (internalWellFoundedFormula R E) ↔
      InternalWellFounded M (R.eval env) (E.eval env) := by
  simp only [internalWellFoundedFormula, InternalWellFounded, Project.Formula.satisfies_forall_iff,
    Project.Formula.satisfies_imp_iff, Project.Formula.satisfies_conj_iff,
    Project.Formula.satisfies_subset_iff, Project.Formula.satisfies_existsMem_iff,
    Project.Formula.satisfies_extensionalEq_iff_eq he, Project.Formula.satisfies_forallMem_iff,
    Project.Formula.satisfies_neg_iff, memPairFormula_iff he, Definitional.Term.eval_weaken]
  simp only [and_true, and_imp]
  rfl

def minimalCore : Project.Formula 1 4 :=
  .imp (rankedRelationFormula (.bound 0) (.bound 1) (.bound 2) (.bound 3))
    (internalWellFoundedFormula (.bound 0) (.bound 2))

def minimalSentence : Project.Sentence := Project.Sentence.forallClosure minimalCore (by
  simp [minimalCore, rankedRelationFormula, ordinalFormula, graphFormula, decreasesFormula,
    internalWellFoundedFormula, memPairFormula, codeFormula, pairFormula,
    Project.Formula.isTransitive, Project.Formula.forallMem, Project.Formula.existsMem,
    Definitional.Formula.FreeClosed])

/-- 无额外对象公理的纯 ∈ Hilbert 推导：实际序数秩蕴含内部关系良基性。 -/
theorem ranked_relation_wellfounded_derivable : KP1Y.Derives minimalSentence := by
  apply KP1Y.derives_of_all_models
  intro M hM free
  apply (Project.Formula.satisfies_forallClosure_iff free minimalCore).mpr
  intro bound
  let env : Env M 4 := ⟨bound,free⟩
  apply (Project.Formula.satisfies_imp_iff env _ _).mpr
  intro hRank
  have h := (rankedRelationFormula_iff hM env (.bound 0) (.bound 1) (.bound 2) (.bound 3)).mp hRank
  apply (internalWellFoundedFormula_iff hM.1 env (.bound 0) (.bound 2)).mpr
  exact fun S hSE hNe => h.minimal_d hM hSE hNe

/-- 给定实际 ω 轨迹；只有在源状态不是指定终点时要求其下一步属于 R。 -/
def TerminalTrajectory (M : SetTheory.Structure.{u}) (R E ω H terminal : M.Domain) : Prop :=
  Graph M H ω E ∧ ∀ i j x y, M.SuccessorOf j i → MemPair M H i x → MemPair M H j y →
    x≠terminal → MemPair M R y x

def terminalTrajectoryFormula {n : Nat} (R E ω H terminal : Project.Term n) : Project.Formula 1 n :=
  .conj (graphFormula H ω E) (Project.Formula.forallMem ω (Project.Formula.forallMem ω.weaken
    (Project.Formula.forallMem E.weaken.weaken (Project.Formula.forallMem E.weaken.weaken.weaken
      (.imp (.conj (successorFormula (.bound 2) (.bound 3))
        (.conj (memPairFormula H.weaken.weaken.weaken.weaken (.bound 3) (.bound 1))
          (.conj (memPairFormula H.weaken.weaken.weaken.weaken (.bound 2) (.bound 0))
            (.neg (Project.Formula.extensionalEq (.bound 1) terminal.weaken.weaken.weaken.weaken)))))
        (memPairFormula R.weaken.weaken.weaken.weaken (.bound 0) (.bound 1)))))))

theorem terminalTrajectoryFormula_delta0 {n : Nat} (R E ω H terminal : Project.Term n) :
    (terminalTrajectoryFormula R E ω H terminal).IsDelta0 :=
  .conj (graphFormula_delta0 _ _ _) (.forallMem _ (.forallMem _ (.forallMem _ (.forallMem _
    (.imp (.conj (successorFormula_delta0 _ _)
      (.conj (memPairFormula_delta0 _ _ _) (.conj (memPairFormula_delta0 _ _ _) (.neg (.atom _ _ _)))))
      (memPairFormula_delta0 _ _ _))))))

theorem terminalTrajectoryFormula_iff {M : SetTheory.Structure.{u}} (he : Extensional M) {n : Nat}
    (env : Env M n) (R E ω H terminal : Project.Term n) :
    Project.Formula.satisfies env (terminalTrajectoryFormula R E ω H terminal) ↔
      TerminalTrajectory M (R.eval env) (E.eval env) (ω.eval env) (H.eval env) (terminal.eval env) := by
  simp only [terminalTrajectoryFormula, Project.Formula.satisfies_conj_iff,
    Project.Formula.satisfies_forallMem_iff, Project.Formula.satisfies_imp_iff,
    Project.Formula.satisfies_neg_iff, Project.Formula.satisfies_extensionalEq_iff_eq he,
    graphFormula_iff he, memPairFormula_iff he, successorFormula_iff he, Definitional.Term.eval_weaken]
  constructor
  · rintro ⟨hH,hStep⟩
    refine ⟨hH,?_⟩
    intro i j x y hSucc hix hjy hNot
    exact hStep i (hH.bounds he hix).1 j (hH.bounds he hjy).1
      x (hH.bounds he hix).2 y (hH.bounds he hjy).2 ⟨hSucc,hix,hjy,hNot⟩
  · rintro ⟨hH,hStep⟩
    exact ⟨hH,fun i _ j _ x _ y _ h => hStep i j x y h.1 h.2.1 h.2.2.1 h.2.2.2⟩

def terminationCore : Project.Formula 1 7 :=
  .imp (.conj (rankedRelationFormula (.bound 0) (.bound 1) (.bound 2) (.bound 3))
    (.conj (Project.Formula.isOmega (.bound 4))
      (terminalTrajectoryFormula (.bound 0) (.bound 2) (.bound 4) (.bound 5) (.bound 6))))
    (Project.Formula.existsMem (.bound 4) (memPairFormula (.bound 6) (.bound 0) (.bound 7)))

def terminationSentence : Project.Sentence := Project.Sentence.forallClosure terminationCore (by
  simp [terminationCore, rankedRelationFormula, ordinalFormula, graphFormula, decreasesFormula,
    terminalTrajectoryFormula, successorFormula, memPairFormula, codeFormula, pairFormula,
    Project.Formula.isTransitive, Project.Formula.isOmega, Project.Formula.isInductive,
    Project.Formula.isEmpty, Project.Formula.isSuccessor, Project.Formula.forallMem,
    Project.Formula.existsMem, Definitional.Formula.FreeClosed])

/-- 无额外对象公理的纯 ∈ Hilbert 推导：每个给定的下降轨迹命中指定终点。 -/
theorem ranked_trajectory_termination_derivable : KP1Y.Derives terminationSentence := by
  apply KP1Y.derives_of_all_models
  intro M hM free
  apply (Project.Formula.satisfies_forallClosure_iff free terminationCore).mpr
  intro bound
  let env : Env M 7 := ⟨bound,free⟩
  apply (Project.Formula.satisfies_imp_iff env _ _).mpr
  intro hAnte
  have hAnte' := (Project.Formula.satisfies_conj_iff env _ _).mp hAnte
  have hRank := (rankedRelationFormula_iff hM env (.bound 0) (.bound 1) (.bound 2) (.bound 3)).mp hAnte'.1
  have hRest := (Project.Formula.satisfies_conj_iff env _ _).mp hAnte'.2
  have hω := (Project.Formula.satisfies_isOmega_iff env (.bound 4)).mp hRest.1
  have hH := (terminalTrajectoryFormula_iff hM.1 env (.bound 0) (.bound 2) (.bound 4) (.bound 5) (.bound 6)).mp hRest.2
  obtain ⟨i,hi,hit⟩ := hRank.trajectory_hits_terminal_d hM hω hH.1 hH.2
  apply (Project.Formula.satisfies_existsMem_iff env _ _).mpr
  exact ⟨i,hi,(memPairFormula_iff hM.1 (env.push i) (.bound 6) (.bound 0) (.bound 7)).mpr hit⟩

end KP1Y.Dynamics
