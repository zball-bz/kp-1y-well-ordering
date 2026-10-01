import KP1Y.OrdinalArithmeticTerms

/-! 为有限字词提供统一增长界：Gκ(x)=κ·x+(x+1)，非序数输入显式返回空集。 -/
namespace KP1Y.WordRank
open YesMetaZFC YesMetaZFC.SetTheory YesMetaZFC.SetTheory.Definitional
open KP1Y.Kuratowski KP1Y.Bounded KP1Y.Arithmetic
universe u

def GrowthCertificate (M : SetTheory.Structure.{u}) (κ x y W : M.Domain) : Prop :=
  ((¬M.IsOrdinal x) ∧ ∀ a, ¬M.mem a y) ∨
    (M.IsOrdinal x ∧ ∃ b, M.mem b W ∧ ∃ u, M.mem u W ∧ ∃ P, M.mem P W ∧ ∃ S, M.mem S W ∧
      ProductCertificate M κ x b P ∧ M.SuccessorOf u x ∧ KP1Y.OrdinalIteration.ValueCertificate successorMatrix (oneEnv b) u y S)

private def growthPositive : Project.Formula 1 8 :=
  .conj (productCertificateFormula (.bound 7) (.bound 6) (.bound 3) (.bound 1))
    (.conj (successorFormula (.bound 2) (.bound 6)) (sumCertificateFormula (.bound 3) (.bound 2) (.bound 5) (.bound 0)))

private theorem growthPositive_freeClosed : growthPositive.FreeClosed := by
  simp only [growthPositive,Definitional.Formula.FreeClosed]
  refine ⟨productCertificateFormula_freeClosed _ _ _ _ rfl rfl rfl rfl,?_,
    sumCertificateFormula_freeClosed _ _ _ _ rfl rfl rfl rfl⟩
  simp [successorFormula,Project.Formula.forallMem,Definitional.Formula.FreeClosed]

def growthMatrix : KP1Y.WitnessMatrix 1 where
  body := .disj (.conj (.neg (ordinalFormula (.bound 2))) (emptyFormula (.bound 1)))
    (.conj (ordinalFormula (.bound 2)) (Project.Formula.existsMem (.bound 0) (Project.Formula.existsMem (.bound 1)
      (Project.Formula.existsMem (.bound 2) (Project.Formula.existsMem (.bound 3) growthPositive)))))
  freeClosed := by
    simp [ordinalFormula,Project.Formula.isTransitive,emptyFormula,Project.Formula.existsMem,Project.Formula.forallMem,
      Definitional.Formula.FreeClosed,growthPositive_freeClosed]
  delta0 := .disj (.conj (.neg (ordinalFormula_delta0 _)) (emptyFormula_delta0 _))
    (.conj (ordinalFormula_delta0 _) (.existsMem _ (.existsMem _ (.existsMem _ (.existsMem _
      (.conj (productCertificateFormula_delta0 _ _ _ _) (.conj (successorFormula_delta0 _ _) (sumCertificateFormula_delta0 _ _ _ _))))))))

theorem growthMatrix_iff {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory) (e : Env M 1) (x y W : M.Domain) :
    KP1Y.OrdinalIteration.Next growthMatrix e x y W ↔ GrowthCertificate M (e.bound 0) x y W := by
  simp only [KP1Y.OrdinalIteration.Next,growthMatrix,growthPositive,Project.Formula.satisfies_disj_iff,
    Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_neg_iff,Project.Formula.satisfies_existsMem_iff,
    ordinalFormula_iff hM,emptyFormula_iff,successorFormula_iff hM.1,
    productCertificateFormula_iff hM,sumCertificateFormula_iff hM]
  rfl

theorem growth_total_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory) (e : Env M 1)
    (hκ : M.IsOrdinal (e.bound 0)) : KP1Y.OrdinalIteration.Total growthMatrix e := by
  classical
  intro x
  by_cases hx : M.IsOrdinal x
  · obtain ⟨b,hb⟩ := product_exists_d hM hκ hx
    obtain ⟨u,hu⟩ := SetTheory.KP.exists_successor (KP1Y.models_weakKP hM) x
    obtain ⟨y,hy⟩ := sum_exists_d hM b (SetTheory.KP.successor_isOrdinal (KP1Y.models_weakKP hM) hx hu)
    obtain ⟨P,hP⟩ := (product_sigmaOne_iff_d hM (oneEnv (e.bound 0)) x b).mp hb
    obtain ⟨S,hS⟩ := hy
    obtain ⟨W0,hW0⟩ := SetTheory.KP.exists_pair (KP1Y.models_weakKP hM) b u
    obtain ⟨W1,hW1⟩ := SetTheory.KP.exists_pair (KP1Y.models_weakKP hM) P S
    obtain ⟨W,hW⟩ := SetTheory.KP.exists_unionOfTwo (KP1Y.models_weakKP hM) W0 W1
    exact ⟨y,W,(growthMatrix_iff hM e x y W).mpr (Or.inr ⟨hx,
      b,(hW b).mpr (Or.inl ((hW0 b).mpr (Or.inl rfl))),u,(hW u).mpr (Or.inl ((hW0 u).mpr (Or.inr rfl))),
      P,(hW P).mpr (Or.inr ((hW1 P).mpr (Or.inl rfl))),S,(hW S).mpr (Or.inr ((hW1 S).mpr (Or.inr rfl))),
      (productMatrix_iff hM (oneEnv (e.bound 0)) x b P).mp hP,hu,hS⟩)⟩
  · obtain ⟨zero,hZero⟩ := SetTheory.KP.exists_empty (KP1Y.models_weakKP hM)
    exact ⟨zero,zero,(growthMatrix_iff hM e x zero zero).mpr (Or.inl ⟨hx,hZero⟩)⟩

theorem growth_functional_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory) (e : Env M 1) :
    KP1Y.OrdinalIteration.Functional growthMatrix e := by
  intro x y y' W W' h h'
  rcases (growthMatrix_iff hM e x y W).mp h with ⟨hx,hy⟩ | ⟨hx,b,_,u,_,P,_,S,_,hb,hu,hy⟩
  · rcases (growthMatrix_iff hM e x y' W').mp h' with ⟨_,hy'⟩ | ⟨hx',_⟩
    · exact hM.1.eq_of_same_members y y' (fun a => iff_of_false (hy a) (hy' a))
    · exact False.elim (hx hx')
  · rcases (growthMatrix_iff hM e x y' W').mp h' with ⟨hx',_⟩ | ⟨_,b',_,u',_,P',_,S',_,hb',hu',hy'⟩
    · exact False.elim (hx' hx)
    · have hbb' := product_unique_d hM hb.meaning hb'.meaning
      subst b'
      have huu' := hM.1.eq_of_same_members u u' (fun a => (hu a).trans (hu' a).symm)
      subst u'
      exact sum_unique_d hM ⟨S,hy⟩ ⟨S',hy'⟩

theorem growth_preserves_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory) (e : Env M 1) :
    KP1Y.OrdinalIteration.PreservesOrdinals growthMatrix e := by
  intro x hx y W h
  rcases (growthMatrix_iff hM e x y W).mp h with ⟨hn,_⟩ | ⟨_,b,_,u,_,P,_,S,_,hb,_,hy⟩
  · exact False.elim (hn hx)
  · exact Sum.isOrdinal_d hM (hb.meaning.isOrdinal_d hM) ⟨S,hy⟩

theorem growth_strict_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory) (e : Env M 1) :
    KP1Y.OrdinalIteration.StrictGrowth growthMatrix e := by
  intro x hx y W h
  rcases (growthMatrix_iff hM e x y W).mp h with ⟨hn,_⟩ | ⟨_,b,_,u,_,P,_,S,_,hb,hu,hy⟩
  · exact False.elim (hn hx)
  · exact sum_right_subset_d hM (hb.meaning.isOrdinal_d hM) ⟨S,hy⟩ x hu.predecessor_mem

theorem growth_contains_product_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    (e : Env M 1) {x b y W : M.Domain} (hb : Product M (e.bound 0) x b)
    (h : KP1Y.OrdinalIteration.Next growthMatrix e x y W) : M.MemberSubset b y := by
  rcases (growthMatrix_iff hM e x y W).mp h with ⟨hn,_⟩ | ⟨_,b',_,u,_,P,_,S,_,hb',_,hy⟩
  · exact False.elim (hn hb.right_ordinal)
  · have hbb' := product_unique_d hM hb hb'.meaning
    subst b'
    exact sum_base_subset_d hM (hb.isOrdinal_d hM) ⟨S,hy⟩

end KP1Y.WordRank
