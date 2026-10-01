import KP1Y.ReflectionTemplateCompilation

/-! 任意实际反射形状均有变量名基底、共同作用域与全部代码块，供两个反射观察使用。 -/
namespace KP1Y.ReflectionModel
open YesMetaZFC YesMetaZFC.SetTheory
open KP1Y.Ranking
universe u

theorem template_environment_exists_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ArticleData M.Domain} (hC : C.Valid M) {A : M.Domain} {D : KP1Y.Satisfaction.RelationalData M.Domain}
    (hD : ArticleInterpretation M C A D) {T : TemplateShape M.Domain} (hT : T.Valid M C) (K : M.Domain) :
    ∃ F, OrdinalRank M F C.reflection.pairs C.reflection.omega ∧
      ∃ V, V.Valid M C F T.width T.edgeLength T.needLength ∧
        ∃ B, TemplateBlocks.Valid M C D T V K B := by
  obtain ⟨F,hF⟩ := pair_name_basis_exists_d hM hC.numerals.omega hC.reflection.pairs
  obtain ⟨V,hV⟩ := name_frame_exists_d hM hC hF hT.diagram.1 hT.edgeLength hT.needLength
  obtain ⟨B,hB⟩ := template_blocks_exists_d hM hC hD hT hV K
  exact ⟨F,hF,V,hV,B,hB⟩

end KP1Y.ReflectionModel
