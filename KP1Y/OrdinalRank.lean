import KP1Y.FunctionGraphs
import KP1Y.LeastChoice
import KP1Y.BoundedSets

/-! 显式序数单射排名产生实际内部良序，最小元只在模型内集合像上选择。 -/
namespace KP1Y.Ranking
open YesMetaZFC YesMetaZFC.SetTheory YesMetaZFC.SetTheory.Definitional
open KP1Y.Kuratowski KP1Y.Functions KP1Y.Bounded
universe u

structure OrdinalRank (M : SetTheory.Structure.{u}) (F X Γ : M.Domain) : Prop where
  ordinal : M.IsOrdinal Γ
  graph : Graph M F X Γ
  injective : ∀ x y a, MemPair M F x a → MemPair M F y a → x=y

def rankFormula {n : Nat} (F X Γ : Project.Term n) : Project.Formula 1 n :=
  .conj (ordinalFormula Γ) (.conj (graphFormula F X Γ)
    (Project.Formula.forallMem X (Project.Formula.forallMem X.weaken (Project.Formula.forallMem Γ.weaken.weaken
      (.imp (.conj (memPairFormula F.weaken.weaken.weaken (.bound 2) (.bound 0))
          (memPairFormula F.weaken.weaken.weaken (.bound 1) (.bound 0)))
        (Project.Formula.extensionalEq (.bound 2) (.bound 1)))))))

theorem rankFormula_delta0 {n : Nat} (F X Γ : Project.Term n) : (rankFormula F X Γ).IsDelta0 :=
  .conj (ordinalFormula_delta0 _) (.conj (graphFormula_delta0 _ _ _) (.forallMem _ (.forallMem _ (.forallMem _
    (.imp (.conj (memPairFormula_delta0 _ _ _) (memPairFormula_delta0 _ _ _)) (.atom _ _ _))))))

theorem rankFormula_iff {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory) {n : Nat}
    (e : Env M n) (F X Γ : Project.Term n) :
    Project.Formula.satisfies e (rankFormula F X Γ) ↔ OrdinalRank M (F.eval e) (X.eval e) (Γ.eval e) := by
  simp only [rankFormula,Project.Formula.satisfies_conj_iff,ordinalFormula_iff hM,graphFormula_iff hM.1,
    Project.Formula.satisfies_forallMem_iff,Project.Formula.satisfies_imp_iff,
    Project.Formula.satisfies_extensionalEq_iff_eq hM.1,memPairFormula_iff hM.1,Definitional.Term.eval_weaken]
  constructor
  · rintro ⟨hOrd,hGraph,hInj⟩
    refine ⟨hOrd,hGraph,?_⟩
    intro x y a hx hy
    exact hInj x (hGraph.bounds hM.1 hx).1 y (hGraph.bounds hM.1 hy).1 a (hGraph.bounds hM.1 hx).2 ⟨hx,hy⟩
  · intro h
    exact ⟨h.ordinal,h.graph,fun x _ y _ a _ hp => h.injective x y a hp.1 hp.2⟩

private def orderSchema : Project.Delta0BinarySchema 2 where
  body := Project.Formula.existsMem (.bound 2) (Project.Formula.existsMem (.bound 3)
    (.conj (memPairFormula (.bound 5) (.bound 3) (.bound 1))
      (.conj (memPairFormula (.bound 5) (.bound 2) (.bound 0)) (.mem (.bound 1) (.bound 0)))))
  freeClosed := by
    simp [memPairFormula,codeFormula,pairFormula,Project.Formula.forallMem,Project.Formula.existsMem,Definitional.Formula.FreeClosed]
  delta0 := .existsMem _ (.existsMem _ (.conj (memPairFormula_delta0 _ _ _) (.conj (memPairFormula_delta0 _ _ _) (.mem _ _))))

private theorem orderSchema_iff {M : SetTheory.Structure.{u}} (he : Extensional M) (F Γ x y : M.Domain) :
    Project.Formula.satisfies ((((oneEnv F).push Γ).push x).push y) orderSchema.body ↔
      ∃ a, M.mem a Γ ∧ ∃ b, M.mem b Γ ∧ MemPair M F x a ∧ MemPair M F y b ∧ M.mem a b := by
  simp only [orderSchema,Project.Formula.satisfies_existsMem_iff,Project.Formula.satisfies_conj_iff,
    Project.Formula.satisfies_mem_iff,memPairFormula_iff he]
  rfl

private def imageSchema : Project.Delta0UnarySchema 2 where
  body := Project.Formula.existsMem (.bound 1) (memPairFormula (.bound 3) (.bound 0) (.bound 1))
  freeClosed := by
    simp [memPairFormula,codeFormula,pairFormula,Project.Formula.forallMem,Project.Formula.existsMem,Definitional.Formula.FreeClosed]
  delta0 := .existsMem _ (memPairFormula_delta0 _ _ _)

private theorem imageSchema_iff {M : SetTheory.Structure.{u}} (he : Extensional M) (F S a : M.Domain) :
    Project.Formula.satisfies (((oneEnv F).push S).push a) imageSchema.body ↔ ∃ x, M.mem x S ∧ MemPair M F x a := by
  simp only [imageSchema,Project.Formula.satisfies_existsMem_iff,memPairFormula_iff he]
  rfl

theorem ordinal_rank_wellorder_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory) {F X Γ : M.Domain}
    (hRank : OrdinalRank M F X Γ) : ∃ R, KP1Y.InternalWellOrder M R X ∧
      ∀ x y, MemPair M R x y ↔ M.mem x X ∧ M.mem y X ∧
        ∃ a, M.mem a Γ ∧ ∃ b, M.mem b Γ ∧ MemPair M F x a ∧ MemPair M F y b ∧ M.mem a b := by
  obtain ⟨R,_,hRaw⟩ := relation_comprehension_d hM orderSchema ((oneEnv F).push Γ) X X
  have hRows (x y : M.Domain) : MemPair M R x y ↔ M.mem x X ∧ M.mem y X ∧
      ∃ a, M.mem a Γ ∧ ∃ b, M.mem b Γ ∧ MemPair M F x a ∧ MemPair M F y b ∧ M.mem a b := by
    simpa only [orderSchema_iff hM.1] using hRaw x y
  refine ⟨R,⟨?_,?_,?_⟩,hRows⟩
  · intro x _ hxx
    obtain ⟨_,_,a,ha,b,_,hxa,hxb,hab⟩ := (hRows x x).mp hxx
    have habEq := hRank.graph.unique x a b hxa hxb
    subst b
    exact hRank.ordinal.wellOrder.linear.irrefl a ha hab
  · intro x hx y _ z hz hxy hyz
    obtain ⟨_,_,a,ha,b,hb,hxa,hyb,hab⟩ := (hRows x y).mp hxy
    obtain ⟨_,_,b',_,c,hc,hyb',hzc,hbc⟩ := (hRows y z).mp hyz
    have hbb' := hRank.graph.unique y b b' hyb hyb'
    subst b'
    exact (hRows x z).mpr ⟨hx,hz,a,ha,c,hc,hxa,hzc,hRank.ordinal.wellOrder.linear.trans a ha b hb c hc hab hbc⟩
  · intro S hSX hNe
    obtain ⟨D,hRawD⟩ := SetTheory.KP.separation_exists_d (KP1Y.models_weakKP hM) imageSchema ((oneEnv F).push S) Γ
    have hD (a : M.Domain) : M.mem a D ↔ M.mem a Γ ∧ ∃ x, M.mem x S ∧ MemPair M F x a := by
      simpa only [imageSchema_iff hM.1] using hRawD a
    have hDNe : ∃ a, M.mem a D := by
      obtain ⟨x,hx⟩ := hNe
      obtain ⟨a,ha,hxa⟩ := hRank.graph.total x (hSX x hx)
      exact ⟨a,(hD a).mpr ⟨ha,x,hx,hxa⟩⟩
    obtain ⟨a,haD,hMin⟩ := hRank.ordinal.wellOrder.least D (fun a ha => ((hD a).mp ha).1) hDNe
    obtain ⟨ha,x,hx,hxa⟩ := (hD a).mp haD
    refine ⟨x,hx,?_⟩
    intro y hy
    obtain ⟨b,hb,hyb⟩ := hRank.graph.total y (hSX y hy)
    rcases hMin b ((hD b).mpr ⟨hb,y,hy,hyb⟩) with hSame | hab
    · have habEq := hM.1.eq_of_same_members a b hSame
      subst b
      exact Or.inl (hRank.injective x y a hxa hyb)
    · exact Or.inr ((hRows x y).mpr ⟨hSX x hx,hSX y hy,a,ha,b,hb,hxa,hyb,hab⟩)

end KP1Y.Ranking
