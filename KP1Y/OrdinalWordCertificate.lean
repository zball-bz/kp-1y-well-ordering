import KP1Y.WordCeilingCertificate
import KP1Y.OrdinalWordRank

/-! 固定字词编码算法的有界证书：统一序数界、乘积界及每行计算证书。
证书中的辅助集合可以变化，但输出序数和排名图唯一。 -/
namespace KP1Y.WordRank
open YesMetaZFC YesMetaZFC.SetTheory YesMetaZFC.SetTheory.Definitional
open KP1Y.Kuratowski KP1Y.Functions KP1Y.Arithmetic KP1Y.Ranking
universe u

def codeGraphFormula {n : Nat} (ω κ C R Words Γ B : Project.Term n) : Project.Formula 1 n :=
  sigmaGraphCertificateFormula codeMatrix (Fin.cases ω (Fin.cases κ (fun _ => C))) R Words Γ B

theorem codeGraphFormula_delta0 {n : Nat} (ω κ C R Words Γ B : Project.Term n) :
    (codeGraphFormula ω κ C R Words Γ B).IsDelta0 := sigmaGraphCertificateFormula_delta0 _ _ _ _ _ _

theorem codeGraphFormula_freeClosed {n : Nat} (ω κ C R Words Γ B : Project.Term n)
    (hω : ω.freeSupport=[]) (hκ : κ.freeSupport=[]) (hC : C.freeSupport=[]) (hR : R.freeSupport=[])
    (hWords : Words.freeSupport=[]) (hΓ : Γ.freeSupport=[]) (hB : B.freeSupport=[]) :
    (codeGraphFormula ω κ C R Words Γ B).FreeClosed :=
  sigmaGraphCertificateFormula_freeClosed _ _ _ _ _ _ (Fin.cases hω (Fin.cases hκ (fun _ => hC))) hR hWords hΓ hB

theorem codeGraphFormula_iff {M : SetTheory.Structure.{u}} (he : Extensional M) {n : Nat} (e : Env M n)
    (ω κ C R Words Γ B : Project.Term n) :
    Project.Formula.satisfies e (codeGraphFormula ω κ C R Words Γ B) ↔
      SigmaGraphCertificate codeMatrix (((oneEnv (C.eval e)).push (κ.eval e)).push (ω.eval e))
        (R.eval e) (Words.eval e) (Γ.eval e) (B.eval e) := by
  apply sigmaGraphCertificateFormula_iff_bound
  · exact he
  · exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun i => Fin.elim0 i)))

structure OrdinalWordCertificate (M : SetTheory.Structure.{u}) (ω κ Words Γ R C BC BP BG : M.Domain) : Prop where
  ceiling : CeilingCertificate M κ ω C BC
  range : ProductCertificate M C ω Γ BP
  values : SigmaGraphCertificate codeMatrix (((oneEnv C).push κ).push ω) R Words Γ BG

def ordinalWordCertificateFormula {n : Nat} (ω κ Words Γ R C BC BP BG : Project.Term n) : Project.Formula 1 n :=
  .conj (ceilingCertificateFormula κ ω C BC)
    (.conj (productCertificateFormula C ω Γ BP) (codeGraphFormula ω κ C R Words Γ BG))

theorem ordinalWordCertificateFormula_delta0 {n : Nat} (ω κ Words Γ R C BC BP BG : Project.Term n) :
    (ordinalWordCertificateFormula ω κ Words Γ R C BC BP BG).IsDelta0 :=
  .conj (ceilingCertificateFormula_delta0 _ _ _ _) (.conj (productCertificateFormula_delta0 _ _ _ _)
    (codeGraphFormula_delta0 _ _ _ _ _ _ _))

theorem ordinalWordCertificateFormula_freeClosed {n : Nat} (ω κ Words Γ R C BC BP BG : Project.Term n)
    (hω : ω.freeSupport=[]) (hκ : κ.freeSupport=[]) (hWords : Words.freeSupport=[]) (hΓ : Γ.freeSupport=[])
    (hR : R.freeSupport=[]) (hC : C.freeSupport=[]) (hBC : BC.freeSupport=[])
    (hBP : BP.freeSupport=[]) (hBG : BG.freeSupport=[]) :
    (ordinalWordCertificateFormula ω κ Words Γ R C BC BP BG).FreeClosed := by
  simp only [ordinalWordCertificateFormula,Definitional.Formula.FreeClosed]
  exact ⟨ceilingCertificateFormula_freeClosed _ _ _ _ hκ hω hC hBC,
    productCertificateFormula_freeClosed _ _ _ _ hC hω hΓ hBP,
    codeGraphFormula_freeClosed _ _ _ _ _ _ _ hω hκ hC hR hWords hΓ hBG⟩

theorem ordinalWordCertificateFormula_iff {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory) {n : Nat}
    (e : Env M n) (ω κ Words Γ R C BC BP BG : Project.Term n) :
    Project.Formula.satisfies e (ordinalWordCertificateFormula ω κ Words Γ R C BC BP BG) ↔
      OrdinalWordCertificate M (ω.eval e) (κ.eval e) (Words.eval e) (Γ.eval e) (R.eval e)
        (C.eval e) (BC.eval e) (BP.eval e) (BG.eval e) := by
  simp only [ordinalWordCertificateFormula,Project.Formula.satisfies_conj_iff,
    ceilingCertificateFormula_iff hM,productCertificateFormula_iff hM,codeGraphFormula_iff hM.1]
  exact ⟨fun h => ⟨h.1,h.2.1,h.2.2⟩,fun h => ⟨h.ceiling,h.range,h.values⟩⟩

theorem ordinal_word_certificate_exists_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {ω κ Words : M.Domain} (hω : M.IsOmega ω) (hκ : M.IsOrdinal κ)
    (hWords : ∀ s, M.mem s Words ↔ ∃ n, M.mem n ω ∧ Graph M s n κ) :
    ∃ Γ R C BC BP BG, OrdinalWordCertificate M ω κ Words Γ R C BC BP BG := by
  obtain ⟨zero,one,C,F,hBudget⟩ := budget_exists_d hM hω hκ
  obtain ⟨BC,hBC⟩ := hBudget.limit_value
  obtain ⟨Γ,hΓ⟩ := product_exists_d hM hBudget.ceiling (KP1Y.Naturals.omega_isOrdinal_d hM hω)
  obtain ⟨BP,hBP⟩ := (product_sigmaOne_iff_d hM (oneEnv C) ω Γ).mp hΓ
  let e : Env M 3 := ((oneEnv C).push κ).push ω
  obtain ⟨R,BG,hValues⟩ := sigma_graph_certificate_exists_d hM codeMatrix e Words Γ (by
    intro s hs
    obtain ⟨n,hn,hS⟩ := (hWords s).mp hs
    obtain ⟨r,hr⟩ := code_exists_d hM hBudget hn hS
    exact ⟨r,(code_sigmaOne_iff_d hM e s r).mp hr⟩) (by
    intro s _ r W hW
    obtain ⟨n,hn,c,hc,_,_,hCode⟩ := (code_sigmaOne_iff_d hM e s r).mpr ⟨W,hW⟩
    exact rectangle_bounded_d hM hΓ hCode hn hc) (by
    intro s _ r r' W W' hW hW'
    exact code_unique_d hM hω ((code_sigmaOne_iff_d hM e s r).mpr ⟨W,hW⟩)
      ((code_sigmaOne_iff_d hM e s r').mpr ⟨W',hW'⟩))
  exact ⟨Γ,R,C,BC,BP,BG,⟨zero,hBudget.zero_nat,one,hBudget.one_nat,hBudget.zero_empty,hBudget.one_successor,hBC⟩,
    (productMatrix_iff hM (oneEnv C) ω Γ BP).mp hBP,hValues⟩

theorem OrdinalWordCertificate.rank_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {ω κ Words Γ R C BC BP BG : M.Domain} (hω : M.IsOmega ω) (hκ : M.IsOrdinal κ)
    (h : OrdinalWordCertificate M ω κ Words Γ R C BC BP BG) : OrdinalRank M R Words Γ := by
  obtain ⟨zero,one,F,hBudget⟩ := h.ceiling.budget_d hM hω hκ
  refine ⟨h.range.meaning.isOrdinal_d hM,h.values.graph,?_⟩
  intro s t r hsr htr
  have hS := h.values.graph.bounds hM.1 hsr
  have hT := h.values.graph.bounds hM.1 htr
  obtain ⟨W,_,hW⟩ := h.values.rows s hS.1 r hS.2 hsr
  obtain ⟨W',_,hW'⟩ := h.values.rows t hT.1 r hT.2 htr
  exact code_injective_d hM hBudget
    ((code_sigmaOne_iff_d hM _ s r).mpr ⟨W,hW⟩) ((code_sigmaOne_iff_d hM _ t r).mpr ⟨W',hW'⟩) rfl

theorem OrdinalWordCertificate.unique_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {ω κ Words Γ R C BC BP BG Γ' R' C' BC' BP' BG' : M.Domain} (hω : M.IsOmega ω)
    (h : OrdinalWordCertificate M ω κ Words Γ R C BC BP BG)
    (h' : OrdinalWordCertificate M ω κ Words Γ' R' C' BC' BP' BG') : Γ=Γ' ∧ R=R' := by
  have hCC' := h.ceiling.unique_d hM h'.ceiling
  subst C'
  have hΓΓ' := product_unique_d hM h.range.meaning h'.range.meaning
  subst Γ'
  refine ⟨rfl,h.values.unique hM.1 h'.values ?_⟩
  intro s _ r r' W W' hW hW'
  exact code_unique_d hM hω ((code_sigmaOne_iff_d hM _ s r).mpr ⟨W,hW⟩)
    ((code_sigmaOne_iff_d hM _ s r').mpr ⟨W',hW'⟩)

end KP1Y.WordRank
