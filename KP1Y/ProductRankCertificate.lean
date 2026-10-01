import KP1Y.ProductRankPoint

/-! 积排名的规范图证书。输出界是β·α，排名行由固定乘积点算法决定。 -/
namespace KP1Y.Ranking
open YesMetaZFC YesMetaZFC.SetTheory YesMetaZFC.SetTheory.Definitional
open KP1Y.Kuratowski KP1Y.Functions KP1Y.Arithmetic
universe u

def productRankGraphFormula {n : Nat} (F G X Y α β P Γ R B : Project.Term n) : Project.Formula 1 n :=
  sigmaGraphCertificateFormula productRankPointMatrix
    (Fin.cases α (Fin.cases β (Fin.cases X (Fin.cases Y (Fin.cases F (fun _ => G)))))) R P Γ B

theorem productRankGraphFormula_delta0 {n : Nat} (F G X Y α β P Γ R B : Project.Term n) :
    (productRankGraphFormula F G X Y α β P Γ R B).IsDelta0 := sigmaGraphCertificateFormula_delta0 _ _ _ _ _ _

theorem productRankGraphFormula_freeClosed {n : Nat} (F G X Y α β P Γ R B : Project.Term n)
    (hF : F.freeSupport=[]) (hG : G.freeSupport=[]) (hX : X.freeSupport=[]) (hY : Y.freeSupport=[])
    (hα : α.freeSupport=[]) (hβ : β.freeSupport=[]) (hP : P.freeSupport=[]) (hΓ : Γ.freeSupport=[])
    (hR : R.freeSupport=[]) (hB : B.freeSupport=[]) : (productRankGraphFormula F G X Y α β P Γ R B).FreeClosed :=
  sigmaGraphCertificateFormula_freeClosed _ _ _ _ _ _
    (Fin.cases hα (Fin.cases hβ (Fin.cases hX (Fin.cases hY (Fin.cases hF (fun _ => hG)))))) hR hP hΓ hB

theorem productRankGraphFormula_iff {M : SetTheory.Structure.{u}} (he : Extensional M) {n : Nat} (e : Env M n)
    (F G X Y α β P Γ R B : Project.Term n) :
    Project.Formula.satisfies e (productRankGraphFormula F G X Y α β P Γ R B) ↔
      SigmaGraphCertificate productRankPointMatrix
        (productRankEnv (F.eval e) (G.eval e) (X.eval e) (Y.eval e) (α.eval e) (β.eval e))
        (R.eval e) (P.eval e) (Γ.eval e) (B.eval e) := by
  apply sigmaGraphCertificateFormula_iff_bound
  · exact he
  · exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun i => Fin.elim0 i))))))

structure ProductRankCertificate (M : SetTheory.Structure.{u}) (F G X Y α β P Γ R BP BG : M.Domain) : Prop where
  range : ProductCertificate M β α Γ BP
  values : SigmaGraphCertificate productRankPointMatrix (productRankEnv F G X Y α β) R P Γ BG

def productRankCertificateFormula {n : Nat} (F G X Y α β P Γ R BP BG : Project.Term n) : Project.Formula 1 n :=
  .conj (productCertificateFormula β α Γ BP) (productRankGraphFormula F G X Y α β P Γ R BG)

theorem productRankCertificateFormula_delta0 {n : Nat} (F G X Y α β P Γ R BP BG : Project.Term n) :
    (productRankCertificateFormula F G X Y α β P Γ R BP BG).IsDelta0 :=
  .conj (productCertificateFormula_delta0 _ _ _ _) (productRankGraphFormula_delta0 _ _ _ _ _ _ _ _ _ _)

theorem productRankCertificateFormula_freeClosed {n : Nat} (F G X Y α β P Γ R BP BG : Project.Term n)
    (hF : F.freeSupport=[]) (hG : G.freeSupport=[]) (hX : X.freeSupport=[]) (hY : Y.freeSupport=[])
    (hα : α.freeSupport=[]) (hβ : β.freeSupport=[]) (hP : P.freeSupport=[]) (hΓ : Γ.freeSupport=[])
    (hR : R.freeSupport=[]) (hBP : BP.freeSupport=[]) (hBG : BG.freeSupport=[]) :
    (productRankCertificateFormula F G X Y α β P Γ R BP BG).FreeClosed := by
  simp only [productRankCertificateFormula,Definitional.Formula.FreeClosed]
  exact ⟨productCertificateFormula_freeClosed _ _ _ _ hβ hα hΓ hBP,
    productRankGraphFormula_freeClosed _ _ _ _ _ _ _ _ _ _ hF hG hX hY hα hβ hP hΓ hR hBG⟩

theorem productRankCertificateFormula_iff {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory) {n : Nat}
    (e : Env M n) (F G X Y α β P Γ R BP BG : Project.Term n) :
    Project.Formula.satisfies e (productRankCertificateFormula F G X Y α β P Γ R BP BG) ↔
      ProductRankCertificate M (F.eval e) (G.eval e) (X.eval e) (Y.eval e) (α.eval e) (β.eval e)
        (P.eval e) (Γ.eval e) (R.eval e) (BP.eval e) (BG.eval e) := by
  simp only [productRankCertificateFormula,Project.Formula.satisfies_conj_iff,
    productCertificateFormula_iff hM,productRankGraphFormula_iff hM.1]
  exact ⟨fun h => ⟨h.1,h.2⟩,fun h => ⟨h.range,h.values⟩⟩

theorem product_rank_certificate_exists_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {F G X Y α β P : M.Domain} (hF : OrdinalRank M F X α) (hG : OrdinalRank M G Y β) (hP : IsProduct M P X Y) :
    ∃ Γ R BP BG, ProductRankCertificate M F G X Y α β P Γ R BP BG := by
  obtain ⟨Γ,hΓ⟩ := product_exists_d hM hG.ordinal hF.ordinal
  obtain ⟨BP,hBP⟩ := (product_sigmaOne_iff_d hM (oneEnv β) α Γ).mp hΓ
  let e := productRankEnv F G X Y α β
  obtain ⟨R,BG,hR⟩ := sigma_graph_certificate_exists_d hM productRankPointMatrix e P Γ (by
    intro p hp
    obtain ⟨r,W,hW⟩ := product_rank_point_exists_d hM hF hG hP hp
    exact ⟨r,W,(productRankPointMatrix_iff hM e p r W).mpr hW⟩) (by
    intro p _ r W hW
    obtain ⟨_,_,_,_,a,ha,b,hb,_,_,_,hCode⟩ := ((productRankPointMatrix_iff hM e p r W).mp hW).meaning_d hM
    exact rectangle_bounded_d hM hΓ hCode ha hb) (by
    intro p _ r r' W W' hW hW'
    exact ((productRankPointMatrix_iff hM e p r W).mp hW).unique_d hM hF.graph hG.graph
      ((productRankPointMatrix_iff hM e p r' W').mp hW'))
  exact ⟨Γ,R,BP,BG,(productMatrix_iff hM (oneEnv β) α Γ BP).mp hBP,hR⟩

theorem ProductRankCertificate.rank_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {F G X Y α β P Γ R BP BG : M.Domain} (hF : OrdinalRank M F X α) (hG : OrdinalRank M G Y β)
    (h : ProductRankCertificate M F G X Y α β P Γ R BP BG) : OrdinalRank M R P Γ := by
  refine ⟨h.range.meaning.isOrdinal_d hM,h.values.graph,?_⟩
  intro p p' r hpr hp'r
  have hp := h.values.graph.bounds hM.1 hpr
  have hp' := h.values.graph.bounds hM.1 hp'r
  obtain ⟨W,_,hW⟩ := h.values.rows p hp.1 r hp.2 hpr
  obtain ⟨W',_,hW'⟩ := h.values.rows p' hp'.1 r hp'.2 hp'r
  exact ((productRankPointMatrix_iff hM _ p r W).mp hW).injective_d hM hF hG
    ((productRankPointMatrix_iff hM _ p' r W').mp hW')

theorem ProductRankCertificate.unique_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {F G X Y α β P Γ R BP BG Γ' R' BP' BG' : M.Domain} (hF : Graph M F X α) (hG : Graph M G Y β)
    (h : ProductRankCertificate M F G X Y α β P Γ R BP BG)
    (h' : ProductRankCertificate M F G X Y α β P Γ' R' BP' BG') : Γ=Γ' ∧ R=R' := by
  have hΓ := product_unique_d hM h.range.meaning h'.range.meaning
  subst Γ'
  refine ⟨rfl,h.values.unique hM.1 h'.values ?_⟩
  intro p _ r r' W W' hW hW'
  exact ((productRankPointMatrix_iff hM _ p r W).mp hW).unique_d hM hF hG
    ((productRankPointMatrix_iff hM _ p r' W').mp hW')

end KP1Y.Ranking
