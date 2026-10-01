import KP1Y.SatisfactionPrefix

/-! 内部公式程序的空程序和指令追加；旧节点的真值保持不变。 -/
namespace KP1Y.Satisfaction
open YesMetaZFC YesMetaZFC.SetTheory
open KP1Y.Kuratowski KP1Y.Functions KP1Y.Sequences
universe u

theorem empty_program_d {M : SetTheory.Structure.{u}} {C : Context M.Domain} (hC : ContextSpaces M C) :
    ∃ e, (∀ x, ¬M.mem x e) ∧ M.mem e C.omega ∧ M.mem e C.programs ∧ Graph M e e C.instructions := by
  obtain ⟨e,he,heω⟩ := hC.omega.1.1
  exact ⟨e,he,heω,(hC.programs e).mpr ⟨e,heω,empty_graph he⟩,empty_graph he⟩

theorem append_instruction_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : Context M.Domain} (hC : ContextSpaces M C) {p n op x y : M.Domain}
    (hP : Graph M p n C.instructions) (hn : M.mem n C.omega)
    (hop : op=C.atomTag ∨ op=C.negTag ∨ op=C.impTag ∨ op=C.allTag)
    (hx : M.mem x C.operands) (hy : M.mem y C.operands) :
    ∃ q m, M.SuccessorOf m n ∧ M.mem m C.omega ∧ Graph M q m C.instructions ∧ M.mem q C.programs ∧
      Prefix M p q n C.instructions ∧ InstructionAt M C.instructions C.pairs q n op x y := by
  obtain ⟨instr,hInstr,args,hArgs,hFields,hCode⟩ := instruction_exists_d hM hC hop hx hy
  obtain ⟨m,hm,hmω⟩ := hC.omega.1.2 n hn
  obtain ⟨q,hApp⟩ := append_exists_d hM p n instr
  have hQ := graph_append_d hM hP hm hInstr hApp
  have hPrefix : Prefix M p q n C.instructions := by
    refine ⟨hP,?_⟩
    intro i hi value _
    have hne : i≠n := by
      intro he
      subst i
      exact SetTheory.KP.mem_irrefl_d (KP1Y.models_weakKP hM) n hi
    simpa only [hne,false_and,or_false] using (append_rows hM.1 hApp i value).symm
  exact ⟨q,m,hm,hmω,hQ,(hC.programs q).mpr ⟨m,hmω,hQ⟩,hPrefix,
    instr,hInstr,args,hArgs,(append_rows hM.1 hApp n instr).mpr (Or.inr ⟨rfl,rfl⟩),hCode,hFields⟩

theorem append_instruction_preserves_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : Context M.Domain} (hC : ContextSpaces M C) {H p n op x y : M.Domain} (hH : Evaluation M C H)
    (hP : Graph M p n C.instructions) (hn : M.mem n C.omega)
    (hop : op=C.atomTag ∨ op=C.negTag ∨ op=C.impTag ∨ op=C.allTag)
    (hx : M.mem x C.operands) (hy : M.mem y C.operands) :
    ∃ q m, M.SuccessorOf m n ∧ M.mem m C.omega ∧ Graph M q m C.instructions ∧ M.mem q C.programs ∧
      InstructionAt M C.instructions C.pairs q n op x y ∧
      ∀ i, M.mem i n → NodeAgreement M C H p q i := by
  obtain ⟨q,m,hm,hmω,hQ,hq,hPrefix,hInstr⟩ := append_instruction_d hM hC hP hn hop hx hy
  exact ⟨q,m,hm,hmω,hQ,hq,hInstr,evaluation_prefix_d hM hC hH hn hq hPrefix⟩

end KP1Y.Satisfaction
