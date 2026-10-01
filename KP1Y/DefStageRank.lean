import KP1Y.DefStageWitness
import KP1Y.CanonicalProgramRank
import KP1Y.RankedSequenceSpace
import KP1Y.RankedProduct
import KP1Y.RankedImage

/-! 已排名载域的纯集合语言Def后继拥有实际序数排名。
这里保留给定程序排名；规范跨层递归的唯一性另由证书验证，不能由存在性代替。 -/
namespace KP1Y.SetLanguage
open YesMetaZFC YesMetaZFC.SetTheory
open KP1Y.Kuratowski KP1Y.Functions KP1Y.Satisfaction KP1Y.Definability KP1Y.Ranking
universe u

theorem DefStage.ranked_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : Context M.Domain} {D : RelationalData M.Domain}
    {zero one two H Raw Sat Def FA FP α π : M.Domain}
    (h : DefStage M C D zero one two H Raw Sat Def)
    (hA : OrdinalRank M FA C.carrier α) (hP : OrdinalRank M FP C.programs π) :
    ∃ Γ R, OrdinalRank M R Def Γ := by
  obtain ⟨β,FV,hV⟩ := ranked_sequence_space_d hM h.spaces.omega hA h.spaces.assignments
  obtain ⟨Γ,FC,hC⟩ := ranked_product_d hM hP hV h.spaces.columns
  obtain ⟨G,hG⟩ := def_certificate_exists_d hM h.subsets
  obtain ⟨R,hR,_⟩ := ranked_image_d hM hC hG.onto
  exact ⟨Γ,R,hR⟩

theorem StageWitness.Valid.ranked_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : Context M.Domain} {D : RelationalData M.Domain}
    {zero one two A Def FA FP α π : M.Domain} {W : StageWitness M.Domain}
    (hS : FixedSyntax M C D zero one two) (hW : W.Valid M C D zero one two A Def)
    (hA : OrdinalRank M FA A α) (hP : OrdinalRank M FP C.programs π) :
    ∃ Γ R, OrdinalRank M R Def Γ :=
  (hW.stage_d hM hS).ranked_d hM hA hP

theorem canonical_def_ranked_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : Context M.Domain} {D : RelationalData M.Domain}
    {zero one two A Def FA α : M.Domain} {W : StageWitness M.Domain}
    (hS : CanonicalSyntax M C D zero one two) (hW : W.Valid M C D zero one two A Def)
    (hA : OrdinalRank M FA A α) : ∃ Γ R, OrdinalRank M R Def Γ := by
  obtain ⟨FP,hP⟩ := canonical_program_rank_d hM hS
  exact hW.ranked_d hM hS.toFixedSyntax hA hP

end KP1Y.SetLanguage
