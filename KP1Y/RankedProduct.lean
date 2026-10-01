import KP1Y.RankComposition
import KP1Y.OrdinalRectangleGraph

/-! 两个已排名集合的实际笛卡尔积拥有序数排名。 -/
namespace KP1Y.Ranking
open YesMetaZFC YesMetaZFC.SetTheory YesMetaZFC.SetTheory.Definitional
open KP1Y.Kuratowski KP1Y.Functions
universe u

private def productImageSchema : Project.Delta0BinarySchema 6 where
  body := Project.Formula.existsMem (.bound 2) (Project.Formula.existsMem (.bound 4)
    (Project.Formula.existsMem (.bound 6) (Project.Formula.existsMem (.bound 8)
      (.conj (codeFormula (.bound 5) (.bound 3) (.bound 2))
        (.conj (codeFormula (.bound 4) (.bound 1) (.bound 0))
          (.conj (memPairFormula (.bound 10) (.bound 3) (.bound 1)) (memPairFormula (.bound 11) (.bound 2) (.bound 0))))))))
  freeClosed := by
    simp [codeFormula,pairFormula,memPairFormula,Project.Formula.existsMem,Project.Formula.forallMem,Definitional.Formula.FreeClosed]
  delta0 := .existsMem _ (.existsMem _ (.existsMem _ (.existsMem _ (.conj (codeFormula_delta0 _ _ _)
    (.conj (codeFormula_delta0 _ _ _) (.conj (memPairFormula_delta0 _ _ _) (memPairFormula_delta0 _ _ _)))))))

private theorem productImageSchema_iff {M : SetTheory.Structure.{u}} (he : Extensional M)
    (G F β α Y X p q : M.Domain) :
    Project.Formula.satisfies ((((((((oneEnv G).push F).push β).push α).push Y).push X).push p).push q) productImageSchema.body ↔
      ∃ x, M.mem x X ∧ ∃ y, M.mem y Y ∧ ∃ a, M.mem a α ∧ ∃ b, M.mem b β ∧
        Codes M p x y ∧ Codes M q a b ∧ MemPair M F x a ∧ MemPair M G y b := by
  simp only [productImageSchema,Project.Formula.satisfies_existsMem_iff,Project.Formula.satisfies_conj_iff,
    codeFormula_iff he,memPairFormula_iff he]
  rfl

theorem ranked_product_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory) {F G X Y α β P : M.Domain}
    (hF : OrdinalRank M F X α) (hG : OrdinalRank M G Y β) (hP : IsProduct M P X Y) :
    ∃ Γ R, OrdinalRank M R P Γ := by
  obtain ⟨Q,hQ⟩ := product_exists hM α β
  obtain ⟨Γ,hΓ⟩ := KP1Y.Arithmetic.product_exists_d hM hG.ordinal hF.ordinal
  obtain ⟨Rank,hRank⟩ := KP1Y.Arithmetic.rectangle_ordinal_rank_d hM hF.ordinal hG.ordinal hQ hΓ
  obtain ⟨H,hSupport,hRaw⟩ := relation_comprehension_d hM productImageSchema
    ((((((oneEnv G).push F).push β).push α).push Y).push X) P Q
  have hRows (p q : M.Domain) : MemPair M H p q ↔ M.mem p P ∧ M.mem q Q ∧
      ∃ x, M.mem x X ∧ ∃ y, M.mem y Y ∧ ∃ a, M.mem a α ∧ ∃ b, M.mem b β ∧
        Codes M p x y ∧ Codes M q a b ∧ MemPair M F x a ∧ MemPair M G y b := by
    simpa only [productImageSchema_iff hM.1] using hRaw p q
  have hH : Graph M H P Q := by
    refine ⟨hSupport,?_,?_⟩
    · intro p hp
      obtain ⟨x,hx,y,hy,hpCode⟩ := (hP p).mp hp
      obtain ⟨a,ha,hFa⟩ := hF.graph.total x hx
      obtain ⟨b,hb,hGb⟩ := hG.graph.total y hy
      obtain ⟨q,hqCode⟩ := codes_total hM a b
      have hq := (hQ q).mpr ⟨a,ha,b,hb,hqCode⟩
      exact ⟨q,hq,(hRows p q).mpr ⟨hp,hq,x,hx,y,hy,a,ha,b,hb,hpCode,hqCode,hFa,hGb⟩⟩
    · intro p q q' hpq hpq'
      obtain ⟨_,_,x,_,y,_,a,_,b,_,hpCode,hqCode,hFa,hGb⟩ := (hRows p q).mp hpq
      obtain ⟨_,_,x',_,y',_,a',_,b',_,hpCode',hqCode',hFa',hGb'⟩ := (hRows p q').mp hpq'
      obtain ⟨hxx',hyy'⟩ := codes_injective hM.1 hpCode hpCode'
      subst x'
      subst y'
      have haa' := hF.graph.unique x a a' hFa hFa'
      have hbb' := hG.graph.unique y b b' hGb hGb'
      subst a'
      subst b'
      exact codes_unique hM.1 hqCode hqCode'
  have hInj : ∀ p p' q, MemPair M H p q → MemPair M H p' q → p=p' := by
    intro p p' q hpq hp'q
    obtain ⟨_,_,x,_,y,_,a,_,b,_,hpCode,hqCode,hFa,hGb⟩ := (hRows p q).mp hpq
    obtain ⟨_,_,x',_,y',_,a',_,b',_,hpCode',hqCode',hFa',hGb'⟩ := (hRows p' q).mp hp'q
    obtain ⟨haa',hbb'⟩ := codes_injective hM.1 hqCode hqCode'
    subst a'
    subst b'
    have hxx' := hF.injective x x' a hFa hFa'
    have hyy' := hG.injective y y' b hGb hGb'
    subst x'
    subst y'
    exact codes_unique hM.1 hpCode hpCode'
  obtain ⟨R,hR⟩ := rank_pullback_d hM hH hInj hRank
  exact ⟨Γ,R,hR⟩

end KP1Y.Ranking
