import KP1Y.FormulaResult

/-! 程序保留可用字面有界的集合包含表达，并从函数性恢复精确前缀。 -/
namespace KP1Y.Satisfaction
open YesMetaZFC YesMetaZFC.SetTheory
open KP1Y.Kuratowski KP1Y.Functions
universe u

theorem memPair_mono {M : SetTheory.Structure.{u}} {p q i a : M.Domain}
    (h : M.MemberSubset p q) (hAt : MemPair M p i a) : MemPair M q i a := by
  obtain ⟨r,hr,hCode⟩ := hAt
  exact ⟨r,h r hr,hCode⟩

theorem prefix_to_subset {M : SetTheory.Structure.{u}} (he : Extensional M)
    {p q n I : M.Domain} (h : Prefix M p q n I) : M.MemberSubset p q := by
  intro r hr
  obtain ⟨i,hi,a,ha,hCode⟩ := h.graph.support r hr
  obtain ⟨t,ht,hCode'⟩ := (h.rows i hi a ha).mp ⟨r,hr,hCode⟩
  exact (codes_unique he hCode hCode') ▸ ht

theorem subset_to_prefix {M : SetTheory.Structure.{u}} (_he : Extensional M)
    {p q n m I : M.Domain} (hP : Graph M p n I) (hQ : Graph M q m I)
    (hSub : M.MemberSubset p q) : Prefix M p q n I := by
  refine ⟨hP,?_⟩
  intro i hi a _
  constructor
  · exact memPair_mono hSub
  · intro hQa
    obtain ⟨b,_,hPb⟩ := hP.total i hi
    have hab := hQ.unique i a b hQa (memPair_mono hSub hPb)
    subst a
    exact hPb

theorem CompiledExtension.to_subset {M : SetTheory.Structure.{u}} (he : Extensional M)
    {C : Context M.Domain} {D : RelationalData M.Domain} {p n bound q length head : M.Domain}
    (h : CompiledExtension M C D p n bound q length head) : M.MemberSubset p q :=
  prefix_to_subset he h.prefixGraph

theorem subset_result_extension {M : SetTheory.Structure.{u}} (he : Extensional M)
    {C : Context M.Domain} {D : RelationalData M.Domain} {p n bound q length head : M.Domain}
    (hP : Graph M p n C.instructions) (hQ : FormulaResult M C D q length head bound)
    (hSub : M.MemberSubset p q) : CompiledExtension M C D p n bound q length head :=
  ⟨hQ.successor,hQ.head_nat,hQ.wellFormed,subset_to_prefix he hP hQ.wellFormed.graph hSub⟩

end KP1Y.Satisfaction
