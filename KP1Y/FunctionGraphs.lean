import KP1Y.HistoryPrefix

/-! KPω 内部的集合函数图及前缀；不存在宿主函数代替内部函数的问题。 -/
namespace KP1Y.Functions
open YesMetaZFC YesMetaZFC.SetTheory YesMetaZFC.SetTheory.Definitional
open KP1Y.Kuratowski
universe u

structure Graph (M : SetTheory.Structure.{u}) (F A V : M.Domain) : Prop where
  support : ∀ p, M.mem p F → ∃ x, M.mem x A ∧ ∃ y, M.mem y V ∧ Codes M p x y
  total : ∀ x, M.mem x A → ∃ y, M.mem y V ∧ MemPair M F x y
  unique : ∀ x y z, MemPair M F x y → MemPair M F x z → y=z

def graphFormula {n : Nat} (F A V : Project.Term n) : Project.Formula 1 n :=
  .conj
    (Project.Formula.forallMem F (Project.Formula.existsMem A.weaken
      (Project.Formula.existsMem V.weaken.weaken (codeFormula (.bound 2) (.bound 1) (.bound 0)))))
    (.conj
      (Project.Formula.forallMem A (Project.Formula.existsMem V.weaken
        (memPairFormula F.weaken.weaken (.bound 1) (.bound 0))))
      (Project.Formula.forallMem A (Project.Formula.forallMem V.weaken
        (Project.Formula.forallMem V.weaken.weaken
          (.imp (.conj (memPairFormula F.weaken.weaken.weaken (.bound 2) (.bound 1))
            (memPairFormula F.weaken.weaken.weaken (.bound 2) (.bound 0)))
            (Project.Formula.extensionalEq (.bound 1) (.bound 0)))))))

theorem graphFormula_delta0 {n : Nat} (F A V : Project.Term n) : (graphFormula F A V).IsDelta0 :=
  .conj (.forallMem _ (.existsMem _ (.existsMem _ (codeFormula_delta0 _ _ _))))
    (.conj (.forallMem _ (.existsMem _ (memPairFormula_delta0 _ _ _)))
      (.forallMem _ (.forallMem _ (.forallMem _
        (.imp (.conj (memPairFormula_delta0 _ _ _) (memPairFormula_delta0 _ _ _)) (.atom _ _ _))))))

theorem Graph.bounds {M : SetTheory.Structure.{u}} (he : Extensional M) {F A V x y : M.Domain}
    (hF : Graph M F A V) (hxy : MemPair M F x y) : M.mem x A ∧ M.mem y V := by
  obtain ⟨p,hp,hcode⟩ := hxy
  obtain ⟨a,ha,b,hb,hcode'⟩ := hF.support p hp
  obtain ⟨hxa,hyb⟩ := codes_injective he hcode hcode'
  cases hxa
  cases hyb
  exact ⟨ha,hb⟩

theorem graphFormula_iff {M : SetTheory.Structure.{u}} (he : Extensional M) {n : Nat}
    (env : Env M n) (F A V : Project.Term n) :
    Project.Formula.satisfies env (graphFormula F A V) ↔
      Graph M (F.eval env) (A.eval env) (V.eval env) := by
  simp only [graphFormula, Project.Formula.satisfies_conj_iff,
    Project.Formula.satisfies_forallMem_iff, Project.Formula.satisfies_existsMem_iff,
    Project.Formula.satisfies_imp_iff, Project.Formula.satisfies_extensionalEq_iff_eq he,
    codeFormula_iff he, memPairFormula_iff he, Definitional.Term.eval_weaken]
  constructor
  · rintro ⟨hSupport,hTotal,hUnique⟩
    refine ⟨hSupport,hTotal,?_⟩
    have bounds : ∀ x y, MemPair M (F.eval env) x y → M.mem x (A.eval env) ∧ M.mem y (V.eval env) := by
      intro x y hxy
      obtain ⟨p,hp,hcode⟩ := hxy
      obtain ⟨a,ha,b,hb,hcode'⟩ := hSupport p hp
      obtain ⟨hxa,hyb⟩ := codes_injective he hcode hcode'
      cases hxa
      cases hyb
      exact ⟨ha,hb⟩
    intro x y z hxy hxz
    exact hUnique x (bounds x y hxy).1 y (bounds x y hxy).2 z (bounds x z hxz).2 ⟨hxy,hxz⟩
  · intro hF
    exact ⟨hF.support,hF.total,fun x _ y _ z _ h => hF.unique x y z h.1 h.2⟩

theorem Graph.mono_values {M : SetTheory.Structure.{u}} {F A V W : M.Domain}
    (hF : Graph M F A V) (hVW : M.MemberSubset V W) : Graph M F A W := by
  refine ⟨?_,?_,hF.unique⟩
  · intro p hp
    obtain ⟨x,hx,y,hy,hcode⟩ := hF.support p hp
    exact ⟨x,hx,y,hVW y hy,hcode⟩
  · intro x hx
    obtain ⟨y,hy,hxy⟩ := hF.total x hx
    exact ⟨y,hVW y hy,hxy⟩

theorem Graph.ext {M : SetTheory.Structure.{u}} (he : Extensional M) {F G A V W : M.Domain}
    (hF : Graph M F A V) (hG : Graph M G A W)
    (hRows : ∀ x, M.mem x A → ∀ y, MemPair M F x y ↔ MemPair M G x y) : F=G := by
  apply he.eq_of_same_members
  intro p
  constructor
  · intro hp
    obtain ⟨x,hx,y,hy,hcode⟩ := hF.support p hp
    obtain ⟨q,hq,hcode'⟩ := (hRows x hx y).mp ⟨p,hp,hcode⟩
    exact (codes_unique he hcode hcode') ▸ hq
  · intro hp
    obtain ⟨x,hx,y,hy,hcode⟩ := hG.support p hp
    obtain ⟨q,hq,hcode'⟩ := (hRows x hx y).mpr ⟨p,hp,hcode⟩
    exact (codes_unique he hcode hcode') ▸ hq

theorem empty_graph {M : SetTheory.Structure.{u}} {e V : M.Domain}
    (he : ∀ x, ¬M.mem x e) : Graph M e e V := by
  refine ⟨fun p hp => False.elim (he p hp),fun x hx => False.elim (he x hx),?_⟩
  intro x y z hxy _
  obtain ⟨p,hp,_⟩ := hxy
  exact False.elim (he p hp)

theorem restrict_graph_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {F A V B : M.Domain} (hF : Graph M F A V) (hBA : M.MemberSubset B A) :
    ∃ G, Graph M G B V ∧ ∀ x y, MemPair M G x y ↔ M.mem x B ∧ MemPair M F x y := by
  obtain ⟨G,hSupport,hG⟩ := relation_comprehension_d hM KP1Y.Recursion.memberSchema (oneEnv F) B V
  have hRows (x y : M.Domain) : MemPair M G x y ↔ M.mem x B ∧ MemPair M F x y := by
    have h := hG x y
    rw [KP1Y.Recursion.memberSchema_iff hM.1] at h
    refine h.trans ⟨fun h => ⟨h.1,h.2.2⟩,fun h => ⟨h.1,(hF.bounds hM.1 h.2).2,h.2⟩⟩
  refine ⟨G,⟨hSupport,?_,?_⟩,hRows⟩
  · intro x hx
    obtain ⟨y,hy,hxy⟩ := hF.total x (hBA x hx)
    exact ⟨y,hy,(hRows x y).mpr ⟨hx,hxy⟩⟩
  · intro x y z hxy hxz
    exact hF.unique x y z ((hRows x y).mp hxy).2 ((hRows x z).mp hxz).2

theorem append_graph_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {F δ γ V W v : M.Domain} (hF : Graph M F δ V) (hSucc : M.SuccessorOf γ δ)
    (hVW : M.MemberSubset V W) (hv : M.mem v W) :
    ∃ G, Graph M G γ W ∧ ∀ x y, MemPair M G x y ↔ MemPair M F x y ∨ (x=δ ∧ y=v) := by
  have hw := KP1Y.models_weakKP hM
  obtain ⟨p,hp⟩ := codes_total hM δ v
  obtain ⟨G,hG⟩ := SetTheory.KP.exists_insert hw F p
  have hRows (x y : M.Domain) : MemPair M G x y ↔ MemPair M F x y ∨ (x=δ ∧ y=v) := by
    constructor
    · rintro ⟨q,hq,hcode⟩
      rcases (hG q).mp hq with hq | he
      · exact Or.inl ⟨q,hq,hcode⟩
      · cases he
        exact Or.inr (codes_injective hM.1 hcode hp)
    · rintro (hxy | ⟨rfl,rfl⟩)
      · obtain ⟨q,hq,hcode⟩ := hxy
        exact ⟨q,(hG q).mpr (Or.inl hq),hcode⟩
      · exact ⟨p,(hG p).mpr (Or.inr rfl),hp⟩
  refine ⟨G,⟨?_,?_,?_⟩,hRows⟩
  · intro q hq
    rcases (hG q).mp hq with hq | he
    · obtain ⟨x,hx,y,hy,hcode⟩ := hF.support q hq
      exact ⟨x,(hSucc x).mpr (Or.inl hx),y,hVW y hy,hcode⟩
    · cases he
      exact ⟨δ,hSucc.predecessor_mem,v,hv,hp⟩
  · intro x hx
    rcases (hSucc x).mp hx with hx | he
    · obtain ⟨y,hy,hxy⟩ := hF.total x hx
      exact ⟨y,hVW y hy,(hRows x y).mpr (Or.inl hxy)⟩
    · have hxδ := hM.1.eq_of_same_members x δ he
      cases hxδ
      exact ⟨v,hv,(hRows δ v).mpr (Or.inr ⟨rfl,rfl⟩)⟩
  · intro x a b hxa hxb
    rcases (hRows x a).mp hxa with ha | ha <;> rcases (hRows x b).mp hxb with hb | hb
    · exact hF.unique x a b ha hb
    · have hxδ := (hF.bounds hM.1 ha).1
      rw [hb.1] at hxδ
      exact False.elim (SetTheory.KP.mem_irrefl_d hw δ hxδ)
    · have hxδ := (hF.bounds hM.1 hb).1
      rw [ha.1] at hxδ
      exact False.elim (SetTheory.KP.mem_irrefl_d hw δ hxδ)
    · exact ha.2.trans hb.2.symm

structure Prefix (M : SetTheory.Structure.{u}) (P H δ V : M.Domain) : Prop where
  graph : Graph M P δ V
  rows : ∀ x, M.mem x δ → ∀ y, M.mem y V → (MemPair M P x y ↔ MemPair M H x y)

def prefixFormula {n : Nat} (P H δ V : Project.Term n) : Project.Formula 1 n :=
  .conj (graphFormula P δ V)
    (Project.Formula.forallMem δ (Project.Formula.forallMem V.weaken
      (.iff (memPairFormula P.weaken.weaken (.bound 1) (.bound 0))
        (memPairFormula H.weaken.weaken (.bound 1) (.bound 0)))))

theorem prefixFormula_delta0 {n : Nat} (P H δ V : Project.Term n) : (prefixFormula P H δ V).IsDelta0 :=
  .conj (graphFormula_delta0 _ _ _) (.forallMem _ (.forallMem _
    (.iff (memPairFormula_delta0 _ _ _) (memPairFormula_delta0 _ _ _))))

theorem prefixFormula_iff {M : SetTheory.Structure.{u}} (he : Extensional M) {n : Nat}
    (env : Env M n) (P H δ V : Project.Term n) :
    Project.Formula.satisfies env (prefixFormula P H δ V) ↔
      Prefix M (P.eval env) (H.eval env) (δ.eval env) (V.eval env) := by
  simp only [prefixFormula, Project.Formula.satisfies_conj_iff, graphFormula_iff he,
    Project.Formula.satisfies_forallMem_iff, Project.Formula.satisfies_iff_iff,
    memPairFormula_iff he, Definitional.Term.eval_weaken]
  exact ⟨fun h => ⟨h.1,h.2⟩,fun h => ⟨h.graph,h.rows⟩⟩

theorem Prefix.all_rows {M : SetTheory.Structure.{u}} (he : Extensional M) {P H δ A V : M.Domain}
    (hP : Prefix M P H δ V) (hH : Graph M H A V) :
    ∀ x, M.mem x δ → ∀ y, MemPair M P x y ↔ MemPair M H x y := by
  intro x hx y
  constructor
  · intro hxy
    exact (hP.rows x hx y (hP.graph.bounds he hxy).2).mp hxy
  · intro hxy
    exact (hP.rows x hx y (hH.bounds he hxy).2).mpr hxy

theorem Prefix.transport {M : SetTheory.Structure.{u}} (he : Extensional M)
    {P H J δ A V W : M.Domain} (hP : Prefix M P H δ V) (hH : Graph M H A V)
    (hVW : M.MemberSubset V W)
    (hRows : ∀ x, M.mem x δ → ∀ y, MemPair M H x y ↔ MemPair M J x y) :
    Prefix M P J δ W :=
  ⟨hP.graph.mono_values hVW,fun x hx y _ => (hP.all_rows he hH x hx y).trans (hRows x hx y)⟩

theorem restrict_prefix_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {H A V δ : M.Domain} (hH : Graph M H A V) (hδA : M.MemberSubset δ A) :
    ∃ P, Prefix M P H δ V := by
  obtain ⟨P,hP,hRows⟩ := restrict_graph_d hM hH hδA
  exact ⟨P,hP,fun x hx y _ => (hRows x y).trans ⟨And.right,fun h => ⟨hx,h⟩⟩⟩

end KP1Y.Functions
