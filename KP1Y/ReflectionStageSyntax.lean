import KP1Y.ReflectionStageCode
import KP1Y.ProductRankPoint
import KP1Y.RankedPacketTerms
import KP1Y.RankedUnion

/-! 阶段码(b,(K,θ))到序数编号的统一Σ₁证书，供预先形成实际索引图。 -/
namespace KP1Y.Reflection
open YesMetaZFC YesMetaZFC.SetTheory YesMetaZFC.SetTheory.Definitional
open KP1Y.Kuratowski KP1Y.Functions KP1Y.Ranking KP1Y.Arithmetic
universe u

def StagePoint (M : SetTheory.Structure.{u}) (ω cap L key σ : M.Domain) : Prop :=
  ∃ b, M.mem b cap ∧ ∃ K, M.mem K ω ∧ ∃ θ, M.mem θ cap ∧ Packet M key b K θ ∧ StageCode M cap L b K θ σ

def StageCertificate (M : SetTheory.Structure.{u}) (ω cap L key σ W : M.Domain) : Prop :=
  ∃ b, M.mem b cap ∧ ∃ K, M.mem K ω ∧ ∃ θ, M.mem θ cap ∧ ∃ t, M.mem t L ∧
    ∃ q, M.mem q W ∧ ∃ u, M.mem u W ∧ ∃ C, M.mem C W ∧ ∃ D, M.mem D W ∧
      Packet M key b K θ ∧ Codes M q K θ ∧ Codes M u b t ∧
        RectangleCertificate M ω cap q t C ∧ RectangleCertificate M cap L u σ D

private def stageBody : Project.Formula 1 14 :=
  .conj (packetFormula (.bound 10) (.bound 7) (.bound 6) (.bound 5))
    (.conj (codeFormula (.bound 3) (.bound 6) (.bound 5))
      (.conj (codeFormula (.bound 2) (.bound 7) (.bound 4))
        (.conj (rectangleCertificateFormula (.bound 11) (.bound 12) (.bound 3) (.bound 4) (.bound 1))
          (rectangleCertificateFormula (.bound 12) (.bound 13) (.bound 2) (.bound 9) (.bound 0)))))

private theorem stageBody_freeClosed : stageBody.FreeClosed := by
  simp only [stageBody,Definitional.Formula.FreeClosed]
  refine ⟨packetFormula_freeClosed _ _ _ _ rfl rfl rfl rfl,?_,?_,
    rectangleCertificateFormula_freeClosed _ _ _ _ _ rfl rfl rfl rfl rfl,
    rectangleCertificateFormula_freeClosed _ _ _ _ _ rfl rfl rfl rfl rfl⟩ <;>
    simp [codeFormula,pairFormula,Project.Formula.existsMem,Project.Formula.forallMem,Definitional.Formula.FreeClosed]

def stageMatrix : KP1Y.WitnessMatrix 3 where
  body := Project.Formula.existsMem (.bound 4) (Project.Formula.existsMem (.bound 4)
    (Project.Formula.existsMem (.bound 6) (Project.Formula.existsMem (.bound 8)
      (Project.Formula.existsMem (.bound 4) (Project.Formula.existsMem (.bound 5)
        (Project.Formula.existsMem (.bound 6) (Project.Formula.existsMem (.bound 7) stageBody)))))))
  freeClosed := by simp [Project.Formula.existsMem,Definitional.Formula.FreeClosed,stageBody_freeClosed]
  delta0 := .existsMem _ (.existsMem _ (.existsMem _ (.existsMem _ (.existsMem _ (.existsMem _ (.existsMem _ (.existsMem _
    (.conj (packetFormula_delta0 _ _ _ _) (.conj (codeFormula_delta0 _ _ _) (.conj (codeFormula_delta0 _ _ _)
      (.conj (rectangleCertificateFormula_delta0 _ _ _ _ _) (rectangleCertificateFormula_delta0 _ _ _ _ _))))))))))))

def stageEnv {M : SetTheory.Structure.{u}} (ω cap L : M.Domain) : Env M 3 := ((oneEnv L).push cap).push ω

theorem stageMatrix_iff {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory) (e : Env M 3) (key σ W : M.Domain) :
    Project.Formula.satisfies (((e.push key).push σ).push W) stageMatrix.body ↔
      StageCertificate M (e.bound 0) (e.bound 1) (e.bound 2) key σ W := by
  simp only [stageMatrix,stageBody,Project.Formula.satisfies_existsMem_iff,Project.Formula.satisfies_conj_iff,
    packetFormula_iff hM.1,codeFormula_iff hM.1,rectangleCertificateFormula_iff hM]
  rfl

private theorem rectangle_certificate_meaning_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {I κ q r B i a : M.Domain} (h : RectangleCertificate M I κ q r B) (hq : Codes M q i a) : RectangleCode M κ i a r := by
  obtain ⟨i',_,a',_,d,_,P,_,S,_,hq',hP,hS⟩ := h
  obtain ⟨hii',haa'⟩ := codes_injective hM.1 hq hq'
  subst i'
  subst a'
  exact ⟨d,hP.meaning,⟨S,hS⟩⟩

theorem stage_sigmaOne_iff_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    (e : Env M 3) (hL : Product M (e.bound 1) (e.bound 0) (e.bound 2)) (key σ : M.Domain) :
    StagePoint M (e.bound 0) (e.bound 1) (e.bound 2) key σ ↔
      ∃ W, Project.Formula.satisfies (((e.push key).push σ).push W) stageMatrix.body := by
  constructor
  · rintro ⟨b,hb,K,hK,θ,hθ,hPacket,t,ht,hσ⟩
    have htL := rectangle_bounded_d hM hL ht hK hθ
    obtain ⟨q,hq⟩ := codes_total hM K θ
    obtain ⟨u,hu⟩ := codes_total hM b t
    obtain ⟨C,hC⟩ := (rectangle_sigmaOne_iff_d hM ((oneEnv (e.bound 1)).push (e.bound 0)) q t).mp ⟨K,hK,θ,hθ,hq,ht⟩
    obtain ⟨D,hD⟩ := (rectangle_sigmaOne_iff_d hM ((oneEnv (e.bound 2)).push (e.bound 1)) u σ).mp ⟨b,hb,t,htL,hu,hσ⟩
    obtain ⟨W,hW⟩ := finite_list_container_d hM [q,u,C,D]
    exact ⟨W,(stageMatrix_iff hM e key σ W).mpr ⟨b,hb,K,hK,θ,hθ,t,htL,
      q,hW q (by simp),u,hW u (by simp),C,hW C (by simp),D,hW D (by simp),hPacket,hq,hu,
      (rectangleMatrix_iff hM ((oneEnv (e.bound 1)).push (e.bound 0)) q t C).mp hC,
      (rectangleMatrix_iff hM ((oneEnv (e.bound 2)).push (e.bound 1)) u σ D).mp hD⟩⟩
  · rintro ⟨W,hW⟩
    obtain ⟨b,hb,K,hK,θ,hθ,t,_,q,_,u,_,C,_,D,_,hPacket,hq,hu,hC,hD⟩ := (stageMatrix_iff hM e key σ W).mp hW
    exact ⟨b,hb,K,hK,θ,hθ,hPacket,t,rectangle_certificate_meaning_d hM hC hq,rectangle_certificate_meaning_d hM hD hu⟩

theorem StagePoint.unique_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory) {ω cap L key σ τ : M.Domain}
    (h : StagePoint M ω cap L key σ) (h' : StagePoint M ω cap L key τ) : σ=τ := by
  obtain ⟨b,_,K,_,θ,_,hp,hCode⟩ := h
  obtain ⟨b',_,K',_,θ',_,hp',hCode'⟩ := h'
  obtain ⟨hbb',hKK',hθθ'⟩ := hp.injective hM.1 hp'
  subst b'
  subst K'
  subst θ'
  exact stage_code_unique_d hM hCode hCode'

end KP1Y.Reflection
