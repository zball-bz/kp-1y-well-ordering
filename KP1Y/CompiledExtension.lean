import KP1Y.NodeTruth

/-! 编译结果记录实际程序、末节点、合法性和保留的输入前缀。 -/
namespace KP1Y.Satisfaction
open YesMetaZFC YesMetaZFC.SetTheory
open KP1Y.Kuratowski KP1Y.Functions
universe u

structure CompiledExtension (M : SetTheory.Structure.{u}) (C : Context M.Domain) (D : RelationalData M.Domain)
    (p n bound q length head : M.Domain) : Prop where
  successor : M.SuccessorOf length head
  head_nat : M.mem head C.omega
  wellFormed : WellFormedProgram M C D q length bound
  prefixGraph : Prefix M p q n C.instructions

theorem CompiledExtension.formula {M : SetTheory.Structure.{u}} {C : Context M.Domain} {D : RelationalData M.Domain}
    {p n bound q length head : M.Domain} (h : CompiledExtension M C D p n bound q length head) :
    FormulaProgram M C D q length bound := ⟨h.wellFormed,head,h.successor.predecessor_mem⟩

theorem CompiledExtension.program_mem {M : SetTheory.Structure.{u}} {C : Context M.Domain} (hC : ContextSpaces M C)
    {D : RelationalData M.Domain} {p n bound q length head : M.Domain}
    (h : CompiledExtension M C D p n bound q length head) : M.mem q C.programs :=
  (hC.programs q).mpr ⟨length,h.wellFormed.length_nat,h.wellFormed.graph⟩

theorem CompiledExtension.trans {M : SetTheory.Structure.{u}} (he : Extensional M)
    {C : Context M.Domain} {D : RelationalData M.Domain} {p n bound q m j r length head : M.Domain}
    (h1 : CompiledExtension M C D p n bound q m j) (h2 : CompiledExtension M C D q m bound r length head) :
    CompiledExtension M C D p n bound r length head :=
  ⟨h2.successor,h2.head_nat,h2.wellFormed,prefix_trans he h1.prefixGraph h2.prefixGraph⟩

theorem CompiledExtension.old_node {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : Context M.Domain} (hC : ContextSpaces M C) {D : RelationalData M.Domain}
    {H p n bound q length head i s : M.Domain} (hH : Evaluation M C H)
    (h : CompiledExtension M C D p n bound q length head) (hn : M.mem n C.omega)
    (hi : M.mem i n) (hs : M.mem s C.assignments) : NodeTrue M C H p i s ↔ NodeTrue M C H q i s :=
  nodeTrue_prefix_d hM hC hH hn (h.program_mem hC) h.prefixGraph hi hs

end KP1Y.Satisfaction
