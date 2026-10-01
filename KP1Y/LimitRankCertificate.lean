import KP1Y.LimitRankPoint

/-! 序数长已排名历史的并集排名证书，允许旧排名互不相容，最终输出仍唯一。 -/
namespace KP1Y.Ranking
open YesMetaZFC YesMetaZFC.SetTheory YesMetaZFC.SetTheory.Definitional
open KP1Y.Kuratowski KP1Y.Functions KP1Y.Arithmetic
universe u

def limitRankGraphFormula {n : Nat} (H I V κ A Γ R B : Project.Term n) : Project.Formula 1 n :=
  sigmaGraphCertificateFormula limitRankPointMatrix (Fin.cases κ (Fin.cases V (Fin.cases I (fun _ => H)))) R A Γ B

theorem limitRankGraphFormula_delta0 {n : Nat} (H I V κ A Γ R B : Project.Term n) :
    (limitRankGraphFormula H I V κ A Γ R B).IsDelta0 := sigmaGraphCertificateFormula_delta0 _ _ _ _ _ _

theorem limitRankGraphFormula_freeClosed {n : Nat} (H I V κ A Γ R B : Project.Term n)
    (hH : H.freeSupport=[]) (hI : I.freeSupport=[]) (hV : V.freeSupport=[]) (hκ : κ.freeSupport=[])
    (hA : A.freeSupport=[]) (hΓ : Γ.freeSupport=[]) (hR : R.freeSupport=[]) (hB : B.freeSupport=[]) :
    (limitRankGraphFormula H I V κ A Γ R B).FreeClosed :=
  sigmaGraphCertificateFormula_freeClosed _ _ _ _ _ _ (Fin.cases hκ (Fin.cases hV (Fin.cases hI (fun _ => hH)))) hR hA hΓ hB

theorem limitRankGraphFormula_iff {M : SetTheory.Structure.{u}} (he : Extensional M) {n : Nat} (e : Env M n)
    (H I V κ A Γ R B : Project.Term n) : Project.Formula.satisfies e (limitRankGraphFormula H I V κ A Γ R B) ↔
      SigmaGraphCertificate limitRankPointMatrix (limitRankEnv (H.eval e) (I.eval e) (V.eval e) (κ.eval e))
        (R.eval e) (A.eval e) (Γ.eval e) (B.eval e) := by
  apply sigmaGraphCertificateFormula_iff_bound
  · exact he
  · exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun i => Fin.elim0 i))))

structure LimitRankCertificate (M : SetTheory.Structure.{u}) (H I V A κ Γ R BP BG : M.Domain)
    (W : PacketUnionBounds M.Domain) : Prop where
  family : RankedFamily M H I V
  unions : FamilyUnionCertificate M H I V A κ W
  range : ProductCertificate M κ I Γ BP
  values : SigmaGraphCertificate limitRankPointMatrix (limitRankEnv H I V κ) R A Γ BG

def limitRankCertificateFormula {n : Nat} (H I V A κ Γ R BP BG : Project.Term n)
    (W : PacketUnionBounds (Project.Term n)) : Project.Formula 1 n :=
  .conj (rankedFamilyFormula H I V) (.conj (familyUnionCertificateFormula H I V A κ W)
    (.conj (productCertificateFormula κ I Γ BP) (limitRankGraphFormula H I V κ A Γ R BG)))

theorem limitRankCertificateFormula_delta0 {n : Nat} (H I V A κ Γ R BP BG : Project.Term n)
    (W : PacketUnionBounds (Project.Term n)) : (limitRankCertificateFormula H I V A κ Γ R BP BG W).IsDelta0 :=
  .conj (rankedFamilyFormula_delta0 _ _ _) (.conj (familyUnionCertificateFormula_delta0 _ _ _ _ _ _)
    (.conj (productCertificateFormula_delta0 _ _ _ _) (limitRankGraphFormula_delta0 _ _ _ _ _ _ _ _)))

theorem limitRankCertificateFormula_freeClosed {n : Nat} (H I V A κ Γ R BP BG : Project.Term n)
    (W : PacketUnionBounds (Project.Term n)) (hH : H.freeSupport=[]) (hI : I.freeSupport=[]) (hV : V.freeSupport=[])
    (hA : A.freeSupport=[]) (hκ : κ.freeSupport=[]) (hΓ : Γ.freeSupport=[]) (hR : R.freeSupport=[])
    (hBP : BP.freeSupport=[]) (hBG : BG.freeSupport=[]) (h1 : W.first.freeSupport=[]) (h2 : W.second.freeSupport=[])
    (h3 : W.third.freeSupport=[]) (h4 : W.fourth.freeSupport=[]) (h5 : W.fifth.freeSupport=[]) :
    (limitRankCertificateFormula H I V A κ Γ R BP BG W).FreeClosed := by
  simp only [limitRankCertificateFormula,Definitional.Formula.FreeClosed]
  exact ⟨rankedFamilyFormula_freeClosed _ _ _ hH hI hV,
    familyUnionCertificateFormula_freeClosed _ _ _ _ _ _ hH hI hV hA hκ h1 h2 h3 h4 h5,
    productCertificateFormula_freeClosed _ _ _ _ hκ hI hΓ hBP,
    limitRankGraphFormula_freeClosed _ _ _ _ _ _ _ _ hH hI hV hκ hA hΓ hR hBG⟩

theorem limitRankCertificateFormula_iff {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory) {n : Nat}
    (e : Env M n) (H I V A κ Γ R BP BG : Project.Term n) (W : PacketUnionBounds (Project.Term n)) :
    Project.Formula.satisfies e (limitRankCertificateFormula H I V A κ Γ R BP BG W) ↔
      LimitRankCertificate M (H.eval e) (I.eval e) (V.eval e) (A.eval e) (κ.eval e) (Γ.eval e)
        (R.eval e) (BP.eval e) (BG.eval e) (W.eval e) := by
  simp only [limitRankCertificateFormula,Project.Formula.satisfies_conj_iff,rankedFamilyFormula_iff hM,
    familyUnionCertificateFormula_iff hM.1,productCertificateFormula_iff hM,limitRankGraphFormula_iff hM.1]
  exact ⟨fun h => ⟨h.1,h.2.1,h.2.2.1,h.2.2.2⟩,fun h => ⟨h.family,h.unions,h.range,h.values⟩⟩

theorem limit_rank_certificate_exists_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory) {H I V : M.Domain}
    (hI : M.IsOrdinal I) (hH : RankedFamily M H I V) : ∃ A κ Γ R BP BG W, LimitRankCertificate M H I V A κ Γ R BP BG W := by
  obtain ⟨A,κ,W,hUnion⟩ := family_union_certificate_exists_d hM H I V
  have hκ := hUnion.meaning.ceiling_ordinal_d hM hH
  obtain ⟨Γ,hΓ⟩ := product_exists_d hM hκ hI
  obtain ⟨BP,hBP⟩ := (product_sigmaOne_iff_d hM (oneEnv κ) I Γ).mp hΓ
  let e := limitRankEnv H I V κ
  obtain ⟨R,BG,hR⟩ := sigma_graph_certificate_exists_d hM limitRankPointMatrix e A Γ (by
    intro x hx
    obtain ⟨r,B,hB⟩ := limit_rank_point_exists_d hM hI hH hUnion.meaning hx
    exact ⟨r,B,(limitRankPointMatrix_iff hM e x r B).mpr hB⟩) (by
    intro x _ r B hB
    obtain ⟨j,hj,_,_,a,ha,_,_,_,hRect⟩ := ((limitRankPointMatrix_iff hM e x r B).mp hB).meaning_d hM
    exact rectangle_bounded_d hM hΓ hRect hj ha) (by
    intro x _ r r' B B' hB hB'
    exact ((limitRankPointMatrix_iff hM e x r B).mp hB).unique_d hM hI hH
      ((limitRankPointMatrix_iff hM e x r' B').mp hB'))
  exact ⟨A,κ,Γ,R,BP,BG,W,hH,hUnion,(productMatrix_iff hM (oneEnv κ) I Γ BP).mp hBP,hR⟩

theorem LimitRankCertificate.rank_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {H I V A κ Γ R BP BG : M.Domain} {W : PacketUnionBounds M.Domain}
    (h : LimitRankCertificate M H I V A κ Γ R BP BG W) : OrdinalRank M R A Γ := by
  refine ⟨h.range.meaning.isOrdinal_d hM,h.values.graph,?_⟩
  intro x y r hxr hyr
  have hx := h.values.graph.bounds hM.1 hxr
  have hy := h.values.graph.bounds hM.1 hyr
  obtain ⟨B,_,hB⟩ := h.values.rows x hx.1 r hx.2 hxr
  obtain ⟨B',_,hB'⟩ := h.values.rows y hy.1 r hy.2 hyr
  exact ((limitRankPointMatrix_iff hM _ x r B).mp hB).injective_d hM h.family
    ((limitRankPointMatrix_iff hM _ y r B').mp hB')

theorem LimitRankCertificate.unique_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {H I V A κ Γ R BP BG V' A' κ' Γ' R' BP' BG' : M.Domain} {W W' : PacketUnionBounds M.Domain}
    (h : LimitRankCertificate M H I V A κ Γ R BP BG W)
    (h' : LimitRankCertificate M H I V' A' κ' Γ' R' BP' BG' W') : A=A' ∧ κ=κ' ∧ Γ=Γ' ∧ R=R' := by
  obtain ⟨hA,hκ⟩ := h.unions.meaning.unique hM.1 h.family.graph h'.family.graph h'.unions.meaning
  subst A'
  subst κ'
  have hΓ := product_unique_d hM h.range.meaning h'.range.meaning
  subst Γ'
  refine ⟨rfl,rfl,rfl,?_⟩
  apply h.values.graph.ext hM.1 h'.values.graph
  intro x hx r
  obtain ⟨a,ha,hxa⟩ := h.values.graph.total x hx
  obtain ⟨b,hb,hxb⟩ := h'.values.graph.total x hx
  obtain ⟨B,_,hB⟩ := h.values.rows x hx a ha hxa
  obtain ⟨B',_,hB'⟩ := h'.values.rows x hx b hb hxb
  have hPoint := (limitRankPointMatrix_iff hM _ x a B).mp hB
  have hPoint' := ((limitRankPointMatrix_iff hM _ x b B').mp hB').values_congr hM.1 h'.family.graph h.family.graph
  have hab := hPoint.unique_d hM h.range.meaning.right_ordinal h.family hPoint'
  subst b
  constructor
  · intro hxr
    exact (h.values.graph.unique x a r hxa hxr) ▸ hxb
  · intro hxr
    exact (h'.values.graph.unique x a r hxb hxr) ▸ hxa

end KP1Y.Ranking
