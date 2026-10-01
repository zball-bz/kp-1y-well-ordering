import KP1Y.WellFormedPrograms

/-! 程序前缀的组合、定义域包含，以及合法节点在前缀和追加中的保持。 -/
namespace KP1Y.Satisfaction
open YesMetaZFC YesMetaZFC.SetTheory
open KP1Y.Kuratowski KP1Y.Functions
universe u

theorem prefix_domain_subset {M : SetTheory.Structure.{u}} (he : Extensional M)
    {p q n m I : M.Domain} (hP : Prefix M p q n I) (hQ : Graph M q m I) : M.MemberSubset n m := by
  intro i hi
  obtain ⟨instr,hInstr,hPi⟩ := hP.graph.total i hi
  exact (hQ.bounds he ((hP.rows i hi instr hInstr).mp hPi)).1

theorem prefix_trans {M : SetTheory.Structure.{u}} (he : Extensional M)
    {p q r n m I : M.Domain} (hP : Prefix M p q n I) (hQ : Prefix M q r m I) : Prefix M p r n I := by
  refine ⟨hP.graph,?_⟩
  intro i hi instr hInstr
  exact (hP.rows i hi instr hInstr).trans (hQ.rows i (prefix_domain_subset he hP hQ.graph i hi) instr hInstr)

theorem wellFormed_prefix {M : SetTheory.Structure.{u}} (he : Extensional M)
    {C : Context M.Domain} {D : RelationalData M.Domain} {p q n m bound : M.Domain}
    (hQ : WellFormedProgram M C D q m bound) (hn : M.mem n C.omega)
    (hP : Prefix M p q n C.instructions) : WellFormedProgram M C D p n bound := by
  refine ⟨hP.graph,hn,hQ.bound_nat,?_⟩
  intro i hi
  exact (wellFormedAt_transport (hP.rows i hi)).mpr (hQ.nodes i (prefix_domain_subset he hP hQ.graph i hi))

theorem wellFormed_extend {M : SetTheory.Structure.{u}} (he : Extensional M)
    {C : Context M.Domain} {D : RelationalData M.Domain} {p q n m bound : M.Domain}
    (hP : WellFormedProgram M C D p n bound) (hQ : Graph M q m C.instructions)
    (hm : M.mem m C.omega) (hSucc : M.SuccessorOf m n) (hPrefix : Prefix M p q n C.instructions)
    (hNode : WellFormedAt M C D q n bound) : WellFormedProgram M C D q m bound := by
  refine ⟨hQ,hm,hP.bound_nat,?_⟩
  intro i hi
  rcases (hSucc i).mp hi with hi | hi
  · exact (wellFormedAt_transport (hPrefix.rows i hi)).mp (hP.nodes i hi)
  · exact (he.eq_of_same_members i n hi) ▸ hNode

end KP1Y.Satisfaction
