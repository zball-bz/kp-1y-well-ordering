import KP1Y.OneYReconstructionRecovery
import KP1Y.OneYGraphPseudo

/-! 图层伪父与真实数值提取的读取桥；不用预设目标提取父图正确。 -/
namespace KP1Y.OneYFinite.ReconstructionExtraction
open YesMetaZFC YesMetaZFC.SetTheory YesMetaZFC.SetTheory.Definitional
open KP1Y.Kuratowski KP1Y.Functions KP1Y.Naturals KP1Y.Bounded
open CopiedMountain
universe u

theorem pseudo_candidate_iff_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {m V P H : M.Domain} {R : RowStateSpace M.Domain}
    (hRun : RowRun M C m R V P H) {X : Data M.Domain} (hX : X.Valid M C) (hFrom : FromRun M C m R V H X)
    (c p : M.Domain) : GraphPseudoCandidate M C X c p ↔ PseudoCandidate M C m R H X.heights c p := by
  constructor
  · rintro ⟨hc,hhc,hp,hhp,r,hr,hHC,hHP,hSucc,F,_,hF,hAnc,hRel⟩
    obtain ⟨W,hAt⟩ := (hFrom.parents r F).mp hF
    have hNumeric := hRun.at_numeric_d hM hC hAt
    refine ⟨hc,hhc,hp,hhp,r,hr,hHC,hHP,⟨hr,Or.inr hSucc⟩,W,(hRun.space.values W).mpr hNumeric.values,
      F,(hRun.space.forests F).mpr hNumeric.forest,hAt,hFrom.width ▸ hAnc,?_⟩
    exact hRel.elim Or.inl (fun he => Or.inr (he.symm ▸ hSucc))
  · rintro ⟨hc,hhc,hp,hhp,r,hr,hHC,hHP,hPrev,W,_,F,_,hAt,hAnc,hRel⟩
    have hF := (hFrom.parents r F).mpr ⟨W,hAt⟩
    have hSucc : M.SuccessorOf hc r := by
      rcases hPrev.2 with ⟨he,_⟩ | hSucc
      · obtain ⟨q,hCQ,_⟩ := ancestor_parent_cases_d hM hC (hRun.at_numeric_d hM hC hAt).forest hAnc
        have hRH := (hX.source r c hc hHC).mp ⟨q,F,(hX.parents.bounds hM.1 hF).2,hF,hCQ⟩
        exact False.elim (hC.zero_empty r (he ▸ hRH))
      · exact hSucc
    refine ⟨hc,hhc,hp,hhp,r,hr,hHC,hHP,hSucc,F,(hX.parents.bounds hM.1 hF).2,hF,hFrom.width.symm ▸ hAnc,?_⟩
    rcases hRel with he | hOther
    · exact Or.inl he
    · exact Or.inr (Structure.SuccessorOf.predecessor_eq hM.1 ((omega_isOrdinal_d hM hC.omega).mem hr) hSucc hOther).symm

theorem pseudo_parent_iff_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {m V P H : M.Domain} {R : RowStateSpace M.Domain}
    (hRun : RowRun M C m R V P H) {X : Data M.Domain} (hX : X.Valid M C) (hFrom : FromRun M C m R V H X)
    (c p : M.Domain) : GraphPseudoParent M C X c p ↔ PseudoParent M C m R H X.heights c p := by
  have hCandidates := pseudo_candidate_iff_d hM hC hRun hX hFrom c
  constructor
  · intro h
    obtain ⟨height,hh,hHeight⟩ := hX.heights.total c (h.1.bounds hM.1).2.1
    exact ⟨⟨height,hh,hHeight,h.1.positive_d hM hC hX hHeight⟩,(hCandidates p).mp h.1,
      fun q hq hQ => h.2 q hq ((hCandidates q).mpr hQ)⟩
  · rintro ⟨_,hCand,hMax⟩
    exact ⟨(hCandidates p).mpr hCand,fun q hq hQ => hMax q hq ((hCandidates q).mp hQ)⟩

theorem pseudo_forest_iff_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {m V P H F : M.Domain} {R : RowStateSpace M.Domain}
    (hRun : RowRun M C m R V P H) {X : Data M.Domain} (hX : X.Valid M C) (hFrom : FromRun M C m R V H X) :
    GraphPseudoForest M C X F ↔ PseudoForest M C m R H X.heights F := by
  constructor
  · intro h
    exact ⟨hFrom.width ▸ h.forest,fun c p => (h.rows c p).trans (pseudo_parent_iff_d hM hC hRun hX hFrom c p)⟩
  · intro h
    exact ⟨hFrom.width.symm ▸ h.forest,fun c p => (h.parents c p).trans (pseudo_parent_iff_d hM hC hRun hX hFrom c p).symm⟩

theorem extraction_from_graph_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {m V P H Top F Q : M.Domain} {R : RowStateSpace M.Domain}
    (hRun : RowRun M C m R V P H) {X : Data M.Domain} (hX : X.Valid M C) (hFrom : FromRun M C m R V H X)
    (hTop : TopValueGraph M C m R H X.heights Top) (hF : GraphPseudoForest M C X F)
    (hSelect : Selects true M C m F Top Q) : Extraction M C m V P Top Q :=
  ⟨R,H,X.heights,F,hRun,hFrom.heights,hTop,(pseudo_forest_iff_d hM hC hRun hX hFrom).mp hF,hSelect⟩

theorem extraction_graph_exists_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {m V P H Top : M.Domain} {R : RowStateSpace M.Domain}
    (hRun : RowRun M C m R V P H) {X : Data M.Domain} (hX : X.Valid M C) (hFrom : FromRun M C m R V H X)
    (hTop : TopValueGraph M C m R H X.heights Top) :
    ∃ F Q, GraphPseudoForest M C X F ∧ Selects true M C m F Top Q ∧ Extraction M C m V P Top Q := by
  obtain ⟨F,hF⟩ := graph_pseudo_forest_exists_d hM hC hX
  obtain ⟨Q,hQ⟩ := select_forest_exists_d hM true hC (hFrom.width ▸ hF.forest) hTop.graph
  exact ⟨F,Q,hF,hQ,extraction_from_graph_d hM hC hRun hX hFrom hTop hF hQ⟩

end KP1Y.OneYFinite.ReconstructionExtraction
