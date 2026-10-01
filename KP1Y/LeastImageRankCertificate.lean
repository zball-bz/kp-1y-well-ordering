import KP1Y.RankedImage

/-! 满射像的最小源排名证书。每行只检查字面Δ₀最小性，整个图由此唯一。 -/
namespace KP1Y.Ranking
open YesMetaZFC YesMetaZFC.SetTheory YesMetaZFC.SetTheory.Definitional
open KP1Y.Kuratowski KP1Y.Functions KP1Y.Cardinal
universe u

structure LeastImageRankCertificate (M : SetTheory.Structure.{u}) (F G X Y Γ R : M.Domain) : Prop where
  graph : Graph M R Y Γ
  rows : ∀ y, M.mem y Y → ∀ a, M.mem a Γ → MemPair M R y a → LeastImage M X F G Γ y a

def leastImageRankCertificateFormula {n : Nat} (F G X Y Γ R : Project.Term n) : Project.Formula 1 n :=
  .conj (graphFormula R Y Γ) (Project.Formula.forallMem Y (Project.Formula.forallMem Γ.weaken
    (.imp (memPairFormula R.weaken.weaken (.bound 1) (.bound 0))
      (leastImageFormula X.weaken.weaken F.weaken.weaken G.weaken.weaken Γ.weaken.weaken (.bound 1) (.bound 0)))))

theorem leastImageRankCertificateFormula_delta0 {n : Nat} (F G X Y Γ R : Project.Term n) :
    (leastImageRankCertificateFormula F G X Y Γ R).IsDelta0 :=
  .conj (graphFormula_delta0 _ _ _) (.forallMem _ (.forallMem _ (.imp (memPairFormula_delta0 _ _ _)
    (leastImageFormula_delta0 _ _ _ _ _ _))))

theorem leastImageRankCertificateFormula_freeClosed {n : Nat} (F G X Y Γ R : Project.Term n)
    (hF : F.freeSupport=[]) (hG : G.freeSupport=[]) (hX : X.freeSupport=[]) (hY : Y.freeSupport=[])
    (hΓ : Γ.freeSupport=[]) (hR : R.freeSupport=[]) : (leastImageRankCertificateFormula F G X Y Γ R).FreeClosed := by
  simp [leastImageRankCertificateFormula,leastImageFormula,fiberRankFormula,graphFormula,memPairFormula,codeFormula,pairFormula,
    Project.Formula.forallMem,Project.Formula.existsMem,Definitional.Formula.FreeClosed,hF,hG,hX,hY,hΓ,hR]

theorem leastImageRankCertificateFormula_iff {M : SetTheory.Structure.{u}} (he : Extensional M) {n : Nat}
    (e : Env M n) (F G X Y Γ R : Project.Term n) :
    Project.Formula.satisfies e (leastImageRankCertificateFormula F G X Y Γ R) ↔
      LeastImageRankCertificate M (F.eval e) (G.eval e) (X.eval e) (Y.eval e) (Γ.eval e) (R.eval e) := by
  simp only [leastImageRankCertificateFormula,Project.Formula.satisfies_conj_iff,graphFormula_iff he,
    Project.Formula.satisfies_forallMem_iff,Project.Formula.satisfies_imp_iff,memPairFormula_iff he,leastImageFormula_iff he,Term.eval_weaken]
  exact ⟨fun h => ⟨h.1,h.2⟩,fun h => ⟨h.graph,h.rows⟩⟩

theorem least_image_rank_certificate_exists_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {F G X Y Γ : M.Domain} (hRank : OrdinalRank M F X Γ) (hG : Onto M G X Y) :
    ∃ R, LeastImageRankCertificate M F G X Y Γ R := by
  obtain ⟨R,hR,hRows⟩ := ranked_image_d hM hRank hG
  exact ⟨R,hR.graph,fun y _ a _ hAt => ((hRows y a).mp hAt).2⟩

theorem LeastImageRankCertificate.rank_d {M : SetTheory.Structure.{u}} (he : Extensional M)
    {F G X Y Γ R : M.Domain} (hRank : OrdinalRank M F X Γ) (hG : Graph M G X Y)
    (h : LeastImageRankCertificate M F G X Y Γ R) : OrdinalRank M R Y Γ := by
  refine ⟨hRank.ordinal,h.graph,?_⟩
  intro y y' a hya hy'a
  have hy := h.graph.bounds he hya
  have hy' := h.graph.bounds he hy'a
  obtain ⟨x,_,hGx,hFx⟩ := (h.rows y hy.1 a hy.2 hya).2.1
  obtain ⟨x',_,hGx',hFx'⟩ := (h.rows y' hy'.1 a hy'.2 hy'a).2.1
  have hxx' := hRank.injective x x' a hFx hFx'
  subst x'
  exact hG.unique x y y' hGx hGx'

theorem LeastImageRankCertificate.unique {M : SetTheory.Structure.{u}} (he : Extensional M)
    {F G X Y Γ R R' : M.Domain} (hΓ : M.IsOrdinal Γ)
    (h : LeastImageRankCertificate M F G X Y Γ R) (h' : LeastImageRankCertificate M F G X Y Γ R') : R=R' := by
  apply h.graph.ext he h'.graph
  intro y hy a
  obtain ⟨b,hb,hyb⟩ := h.graph.total y hy
  obtain ⟨b',hb',hyb'⟩ := h'.graph.total y hy
  have hbb' := least_image_unique hΓ (h.rows y hy b hb hyb) (h'.rows y hy b' hb' hyb')
  subst b'
  constructor
  · intro hya
    exact (h.graph.unique y b a hyb hya) ▸ hyb'
  · intro hya
    exact (h'.graph.unique y b a hyb' hya) ▸ hyb

end KP1Y.Ranking
