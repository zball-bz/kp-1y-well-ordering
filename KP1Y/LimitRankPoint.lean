import KP1Y.FirstRankedStage
import KP1Y.ProductRankPoint

/-! 并集元素按首次出现j和该阶段排名a编码为κ·j+a；包含实际算术证书。 -/
namespace KP1Y.Ranking
open YesMetaZFC YesMetaZFC.SetTheory YesMetaZFC.SetTheory.Definitional
open KP1Y.Kuratowski KP1Y.Functions KP1Y.Arithmetic
universe u

def LimitRankPoint (M : SetTheory.Structure.{u}) (H I V κ x r W : M.Domain) : Prop :=
  ∃ j, M.mem j I ∧ ∃ p, M.mem p V ∧ ∃ a, M.mem a κ ∧ ∃ q, M.mem q W ∧ ∃ B, M.mem B W ∧
    FirstStage M H I V x j ∧ MemPair M H j p ∧ (∃ T γ F, Packet M p T γ F ∧ MemPair M F x a) ∧
      Codes M q j a ∧ RectangleCertificate M I κ q r B

private def pointBody : Project.Formula 1 12 :=
  .conj (firstStageFormula (.bound 11) (.bound 10) (.bound 9) (.bound 7) (.bound 4))
    (.conj (memPairFormula (.bound 11) (.bound 4) (.bound 3))
      (.conj (existsPacketFormula (.bound 3) (memPairFormula (.bound 0) (.bound 10) (.bound 5)))
        (.conj (codeFormula (.bound 1) (.bound 4) (.bound 2))
          (rectangleCertificateFormula (.bound 10) (.bound 8) (.bound 1) (.bound 6) (.bound 0)))))

private theorem pointBody_freeClosed : pointBody.FreeClosed := by
  simp only [pointBody,Definitional.Formula.FreeClosed]
  refine ⟨firstStageFormula_freeClosed _ _ _ _ _ rfl rfl rfl rfl rfl,?_,?_,?_,
    rectangleCertificateFormula_freeClosed _ _ _ _ _ rfl rfl rfl rfl rfl⟩
  · simp [memPairFormula,codeFormula,pairFormula,Project.Formula.existsMem,Project.Formula.forallMem,Definitional.Formula.FreeClosed]
  · apply existsPacketFormula_freeClosed _ rfl
    simp [memPairFormula,codeFormula,pairFormula,Project.Formula.existsMem,Project.Formula.forallMem,Definitional.Formula.FreeClosed]
  · simp [codeFormula,pairFormula,Project.Formula.existsMem,Project.Formula.forallMem,Definitional.Formula.FreeClosed]

def limitRankPointMatrix : KP1Y.WitnessMatrix 4 where
  body := Project.Formula.existsMem (.bound 5) (Project.Formula.existsMem (.bound 5)
    (Project.Formula.existsMem (.bound 5) (Project.Formula.existsMem (.bound 3) (Project.Formula.existsMem (.bound 4) pointBody))))
  freeClosed := by simp [Project.Formula.existsMem,Definitional.Formula.FreeClosed,pointBody_freeClosed]
  delta0 := .existsMem _ (.existsMem _ (.existsMem _ (.existsMem _ (.existsMem _
    (.conj (firstStageFormula_delta0 _ _ _ _ _) (.conj (memPairFormula_delta0 _ _ _)
      (.conj (existsPacketFormula_delta0 _ (memPairFormula_delta0 _ _ _))
        (.conj (codeFormula_delta0 _ _ _) (rectangleCertificateFormula_delta0 _ _ _ _ _)))))))))

def limitRankEnv {M : SetTheory.Structure.{u}} (H I V κ : M.Domain) : Env M 4 :=
  (((oneEnv H).push I).push V).push κ

theorem limitRankPointMatrix_iff {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory) (e : Env M 4) (x r W : M.Domain) :
    Project.Formula.satisfies (((e.push x).push r).push W) limitRankPointMatrix.body ↔
      LimitRankPoint M (e.bound 3) (e.bound 2) (e.bound 1) (e.bound 0) x r W := by
  simp only [limitRankPointMatrix,pointBody,Project.Formula.satisfies_existsMem_iff,Project.Formula.satisfies_conj_iff,
    firstStageFormula_iff hM.1,memPairFormula_iff hM.1,existsPacketFormula_iff hM.1,codeFormula_iff hM.1,rectangleCertificateFormula_iff hM]
  rfl

theorem LimitRankPoint.meaning_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory) {H I V κ x r W : M.Domain}
    (h : LimitRankPoint M H I V κ x r W) :
    ∃ j, M.mem j I ∧ ∃ p, M.mem p V ∧ ∃ a, M.mem a κ ∧ FirstStage M H I V x j ∧ MemPair M H j p ∧
      (∃ T γ F, Packet M p T γ F ∧ MemPair M F x a) ∧ RectangleCode M κ j a r := by
  obtain ⟨j,hj,p,hp,a,ha,q,_,B,_,hFirst,hAt,hSelected,hq,hRect⟩ := h
  obtain ⟨j',_,a',_,d,_,P,_,S,_,hq',hP,hS⟩ := hRect
  obtain ⟨hjj',haa'⟩ := codes_injective hM.1 hq hq'
  subst j'
  subst a'
  exact ⟨j,hj,p,hp,a,ha,hFirst,hAt,hSelected,d,hP.meaning,⟨S,hS⟩⟩

theorem limit_rank_point_exists_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory) {H I V A κ x : M.Domain}
    (hI : M.IsOrdinal I) (hH : RankedFamily M H I V) (hUnion : FamilyUnions M H I V A κ) (hx : M.mem x A) :
    ∃ r W, LimitRankPoint M H I V κ x r W := by
  obtain ⟨j,hFirst⟩ := first_stage_exists_d hM hI hUnion hx
  have hOcc := hFirst.2.1
  obtain ⟨p,hp,hAt,T,γ,F,hPacket,hxT⟩ := hOcc
  have hRank := (hH.ranked j p hAt).rank hM.1 hPacket
  obtain ⟨a,ha,hFa⟩ := hRank.graph.total x hxT
  have haκ : M.mem a κ := (hUnion.ceiling a).mpr ⟨j,hFirst.1,p,hp,hAt,T,γ,F,hPacket,ha⟩
  have hκ := hUnion.ceiling_ordinal_d hM hH
  obtain ⟨r,hr⟩ := rectangle_exists_d hM hκ (hI.mem hFirst.1) (hκ.mem haκ)
  obtain ⟨q,hq⟩ := codes_total hM j a
  obtain ⟨B,hB⟩ := (rectangle_sigmaOne_iff_d hM ((oneEnv κ).push I) q r).mp ⟨j,hFirst.1,a,haκ,hq,hr⟩
  obtain ⟨W,hW⟩ := SetTheory.KP.exists_pair (KP1Y.models_weakKP hM) q B
  exact ⟨r,W,j,hFirst.1,p,hp,a,haκ,q,(hW q).mpr (Or.inl rfl),B,(hW B).mpr (Or.inr rfl),hFirst,hAt,
    ⟨T,γ,F,hPacket,hFa⟩,hq,(rectangleMatrix_iff hM ((oneEnv κ).push I) q r B).mp hB⟩

theorem LimitRankPoint.unique_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {H I V κ x r r' W W' : M.Domain} (hI : M.IsOrdinal I) (hH : RankedFamily M H I V)
    (h : LimitRankPoint M H I V κ x r W) (h' : LimitRankPoint M H I V κ x r' W') : r=r' := by
  obtain ⟨j,_,p,_,a,_,hFirst,hAt,⟨T,γ,F,hPacket,hFa⟩,hr⟩ := h.meaning_d hM
  obtain ⟨j',_,p',_,a',_,hFirst',hAt',⟨T',γ',F',hPacket',hFa'⟩,hr'⟩ := h'.meaning_d hM
  have hjj' := first_stage_unique hI hFirst hFirst'
  subst j'
  have hpp' := hH.graph.unique j p p' hAt hAt'
  subst p'
  obtain ⟨hT,hγ,hF⟩ := hPacket.injective hM.1 hPacket'
  subst T'
  subst γ'
  subst F'
  have haa' := ((hH.ranked j p hAt).rank hM.1 hPacket).graph.unique x a a' hFa hFa'
  subst a'
  exact rectangle_unique_d hM hr hr'

theorem LimitRankPoint.injective_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {H I V κ x y r W W' : M.Domain} (hH : RankedFamily M H I V)
    (h : LimitRankPoint M H I V κ x r W) (h' : LimitRankPoint M H I V κ y r W') : x=y := by
  obtain ⟨j,_,p,_,a,ha,_,hAt,⟨T,γ,F,hPacket,hFa⟩,hr⟩ := h.meaning_d hM
  obtain ⟨j',_,p',_,a',ha',_,hAt',⟨T',γ',F',hPacket',hFa'⟩,hr'⟩ := h'.meaning_d hM
  obtain ⟨hjj',haa'⟩ := rectangle_injective_d hM hr hr' ha ha' rfl
  subst j'
  subst a'
  have hpp' := hH.graph.unique j p p' hAt hAt'
  subst p'
  obtain ⟨hT,hγ,hF⟩ := hPacket.injective hM.1 hPacket'
  subst T'
  subst γ'
  subst F'
  exact ((hH.ranked j p hAt).rank hM.1 hPacket).injective x y a hFa hFa'

theorem LimitRankPoint.values_congr {M : SetTheory.Structure.{u}} (he : Extensional M)
    {H I V V' κ x r W : M.Domain} (hH : Graph M H I V) (hH' : Graph M H I V')
    (h : LimitRankPoint M H I V κ x r W) : LimitRankPoint M H I V' κ x r W := by
  obtain ⟨j,hj,p,_,a,ha,q,hq,B,hB,hFirst,hAt,hSelected,hqCode,hRect⟩ := h
  exact ⟨j,hj,p,(hH'.bounds he hAt).2,a,ha,q,hq,B,hB,(firstStage_values_congr he hH hH' x j).mp hFirst,hAt,hSelected,hqCode,hRect⟩

end KP1Y.Ranking
