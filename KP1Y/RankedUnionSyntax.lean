import KP1Y.LimitRankCertificate

/-! 将历史并集排名打包为单值Σ₁输出；输出采用(A,(Γ,R))，与Def后继一致。 -/
namespace KP1Y.Ranking
open YesMetaZFC YesMetaZFC.SetTheory YesMetaZFC.SetTheory.Definitional
open KP1Y.Kuratowski KP1Y.Functions
universe u

private def bodyBounds : PacketUnionBounds (Project.Term 17) := ⟨.bound 6,.bound 5,.bound 4,.bound 3,.bound 2⟩

private def bodyFormula : Project.Formula 1 17 :=
  .conj (codeFormula (.bound 14) (.bound 11) (.bound 7)) (.conj (codeFormula (.bound 7) (.bound 9) (.bound 8))
    (limitRankCertificateFormula (.bound 15) (.bound 16) (.bound 12) (.bound 11) (.bound 10) (.bound 9) (.bound 8) (.bound 1) (.bound 0) bodyBounds))

private theorem bodyFormula_freeClosed : bodyFormula.FreeClosed := by
  simp only [bodyFormula,Definitional.Formula.FreeClosed]
  refine ⟨?_,?_,limitRankCertificateFormula_freeClosed _ _ _ _ _ _ _ _ _ _
    rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl⟩ <;>
    simp [codeFormula,pairFormula,Project.Formula.existsMem,Project.Formula.forallMem,Definitional.Formula.FreeClosed]

def rankedUnionMatrix : KP1Y.WitnessMatrix 1 where
  body := Project.Formula.existsMem (.bound 0) (
    Project.Formula.existsMem (.bound 1) (
    Project.Formula.existsMem (.bound 2) (
    Project.Formula.existsMem (.bound 3) (
    Project.Formula.existsMem (.bound 4) (
    Project.Formula.existsMem (.bound 5) (
    Project.Formula.existsMem (.bound 6) (
    Project.Formula.existsMem (.bound 7) (
    Project.Formula.existsMem (.bound 8) (
    Project.Formula.existsMem (.bound 9) (
    Project.Formula.existsMem (.bound 10) (
    Project.Formula.existsMem (.bound 11) (
    Project.Formula.existsMem (.bound 12) (bodyFormula)))))))))))))
  freeClosed := by simp [Project.Formula.existsMem,Definitional.Formula.FreeClosed,bodyFormula_freeClosed]
  delta0 := .existsMem _ (.existsMem _ (.existsMem _ (.existsMem _ (.existsMem _ (.existsMem _ (.existsMem _ (.existsMem _ (.existsMem _ (.existsMem _ (.existsMem _ (.existsMem _ (.existsMem _ ((.conj (codeFormula_delta0 _ _ _) (.conj (codeFormula_delta0 _ _ _) (limitRankCertificateFormula_delta0 _ _ _ _ _ _ _ _ _ _))))))))))))))))

def unionBoundsInBox (M : SetTheory.Structure.{u}) (W : PacketUnionBounds M.Domain) (B : M.Domain) : Prop :=
  M.mem W.first B ∧ M.mem W.second B ∧ M.mem W.third B ∧ M.mem W.fourth B ∧ M.mem W.fifth B

def RankedUnionCertificate (M : SetTheory.Structure.{u}) (H I Out B : M.Domain) : Prop :=
  ∃ V, M.mem V B ∧ ∃ A, M.mem A B ∧ ∃ κ, M.mem κ B ∧ ∃ Γ, M.mem Γ B ∧ ∃ R, M.mem R B ∧ ∃ q, M.mem q B ∧
    ∃ W : PacketUnionBounds M.Domain, unionBoundsInBox M W B ∧ ∃ BP, M.mem BP B ∧ ∃ BG, M.mem BG B ∧
      Codes M Out A q ∧ Codes M q Γ R ∧ LimitRankCertificate M H I V A κ Γ R BP BG W

theorem rankedUnionMatrix_iff {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    (e : Env M 1) (H Out B : M.Domain) :
    Project.Formula.satisfies (((e.push H).push Out).push B) rankedUnionMatrix.body ↔ RankedUnionCertificate M H (e.bound 0) Out B := by
  simp only [rankedUnionMatrix,Project.Formula.satisfies_existsMem_iff,bodyFormula,Project.Formula.satisfies_conj_iff,
    codeFormula_iff hM.1,limitRankCertificateFormula_iff hM]
  constructor
  · rintro ⟨V,hV,A,hA,κ,hκ,Γ,hΓ,R,hR,q,hq,U1,h1,U2,h2,U3,h3,U4,h4,U5,h5,BP,hBP,BG,hBG,hOut,hqCode,hCert⟩
    exact ⟨V,hV,A,hA,κ,hκ,Γ,hΓ,R,hR,q,hq,⟨U1,U2,U3,U4,U5⟩,⟨h1,h2,h3,h4,h5⟩,BP,hBP,BG,hBG,hOut,hqCode,hCert⟩
  · rintro ⟨V,hV,A,hA,κ,hκ,Γ,hΓ,R,hR,q,hq,⟨U1,U2,U3,U4,U5⟩,hU,BP,hBP,BG,hBG,hOut,hqCode,hCert⟩
    exact ⟨V,hV,A,hA,κ,hκ,Γ,hΓ,R,hR,q,hq,U1,hU.1,U2,hU.2.1,U3,hU.2.2.1,U4,hU.2.2.2.1,U5,hU.2.2.2.2,
      BP,hBP,BG,hBG,hOut,hqCode,hCert⟩

end KP1Y.Ranking
