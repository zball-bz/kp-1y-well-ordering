import KP1Y.RelationalSpaces
import KP1Y.SatisfactionTags

/-! 从关系结构构造全部实际语法空间及列界，并保留原子解释的来源。 -/
namespace KP1Y.Satisfaction
open YesMetaZFC YesMetaZFC.SetTheory YesMetaZFC.SetTheory.Definitional
open KP1Y.Kuratowski KP1Y.Functions
universe u

structure ContextSpaces (M : SetTheory.Structure.{u}) (C : Context M.Domain) : Prop where
  omega : M.IsOmega C.omega
  distinct : DistinctTags M.Domain C.atomTag C.negTag C.impTag C.allTag
  tag_naturals : M.mem C.atomTag C.omega ∧ M.mem C.negTag C.omega ∧
    M.mem C.impTag C.omega ∧ M.mem C.allTag C.omega
  omega_operands : M.MemberSubset C.omega C.operands
  pairs : ∀ args, M.mem args C.pairs ↔
    ∃ x, M.mem x C.operands ∧ ∃ y, M.mem y C.operands ∧ Codes M args x y
  instructions : ∀ instr, M.mem instr C.instructions ↔ ∃ args, M.mem args C.pairs ∧
    (Codes M instr C.atomTag args ∨ Codes M instr C.negTag args ∨
      Codes M instr C.impTag args ∨ Codes M instr C.allTag args)
  programs : ∀ p, M.mem p C.programs ↔ ∃ n, M.mem n C.omega ∧ Graph M p n C.instructions
  assignments : ∀ s, M.mem s C.assignments ↔ ∃ n, M.mem n C.omega ∧ Graph M s n C.carrier
  columns : ∀ c, M.mem c C.columns ↔
    ∃ p, M.mem p C.programs ∧ ∃ s, M.mem s C.assignments ∧ Codes M c p s

structure RelationalContext (M : SetTheory.Structure.{u}) (D : RelationalData M.Domain)
    (Atom : M.Domain) (C : Context M.Domain) : Prop where
  omega_eq : C.omega=D.omega
  carrier_eq : C.carrier=D.carrier
  assignments_eq : C.assignments=D.values
  atomic_eq : C.atomic=Atom
  codes_bound : M.MemberSubset D.codes C.operands

theorem context_spaces_exists_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {D : RelationalData M.Domain} (hD : DataSpaces M D) (Atom : M.Domain) :
    ∃ C, RelationalContext M D Atom C ∧ ContextSpaces M C := by
  have hw := KP1Y.models_weakKP hM
  obtain ⟨Tags,a,n,i,q,hDistinct,ha,hn,hi,hq,hTags⟩ := opcode_set_exists_d hM hD.omega
  obtain ⟨O,hO⟩ := SetTheory.KP.exists_unionOfTwo hw D.omega D.codes
  obtain ⟨Pairs,hPairs⟩ := product_exists hM O O
  obtain ⟨Instructions,hInstructions⟩ := product_exists hM Tags Pairs
  obtain ⟨Programs,hPrograms⟩ := KP1Y.Sequences.finite_sequences_exist_d hM hD.omega Instructions
  obtain ⟨Columns,hColumns⟩ := product_exists hM Programs D.values
  let C : Context M.Domain := ⟨D.omega,D.carrier,O,Pairs,Instructions,Programs,D.values,Columns,Atom,a,n,i,q⟩
  refine ⟨C,⟨rfl,rfl,rfl,rfl,fun x hx => (hO x).mpr (Or.inr hx)⟩,
    ⟨hD.omega,hDistinct,⟨ha,hn,hi,hq⟩,fun x hx => (hO x).mpr (Or.inl hx),
      hPairs,?_,hPrograms,hD.values,hColumns⟩⟩
  intro instr
  constructor
  · intro hInstr
    obtain ⟨op,hop,args,hArgs,hCode⟩ := (hInstructions instr).mp hInstr
    refine ⟨args,hArgs,?_⟩
    rcases (hTags op).mp hop with he | he | he | he
    · subst op
      exact Or.inl hCode
    · subst op
      exact Or.inr (Or.inl hCode)
    · subst op
      exact Or.inr (Or.inr (Or.inl hCode))
    · subst op
      exact Or.inr (Or.inr (Or.inr hCode))
  · rintro ⟨args,hArgs,hCode⟩
    rcases hCode with hCode | hCode | hCode | hCode
    · exact (hInstructions instr).mpr ⟨a,(hTags a).mpr (Or.inl rfl),args,hArgs,hCode⟩
    · exact (hInstructions instr).mpr ⟨n,(hTags n).mpr (Or.inr (Or.inl rfl)),args,hArgs,hCode⟩
    · exact (hInstructions instr).mpr ⟨i,(hTags i).mpr (Or.inr (Or.inr (Or.inl rfl))),args,hArgs,hCode⟩
    · exact (hInstructions instr).mpr ⟨q,(hTags q).mpr (Or.inr (Or.inr (Or.inr rfl))),args,hArgs,hCode⟩

theorem column_exists_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : Context M.Domain} (hC : ContextSpaces M C) {p s : M.Domain}
    (hp : M.mem p C.programs) (hs : M.mem s C.assignments) :
    ∃ c, M.mem c C.columns ∧ Codes M c p s := by
  obtain ⟨c,hCode⟩ := codes_total hM p s
  exact ⟨c,(hC.columns c).mpr ⟨p,hp,s,hs,hCode⟩,hCode⟩

theorem instruction_exists_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : Context M.Domain} (hC : ContextSpaces M C) {op x y : M.Domain}
    (hop : op=C.atomTag ∨ op=C.negTag ∨ op=C.impTag ∨ op=C.allTag)
    (hx : M.mem x C.operands) (hy : M.mem y C.operands) :
    ∃ instr, M.mem instr C.instructions ∧ ∃ args, M.mem args C.pairs ∧
      Codes M args x y ∧ Codes M instr op args := by
  obtain ⟨args,hArgs⟩ := codes_total hM x y
  have hArgsMem := (hC.pairs args).mpr ⟨x,hx,y,hy,hArgs⟩
  obtain ⟨instr,hCode⟩ := codes_total hM op args
  refine ⟨instr,(hC.instructions instr).mpr ⟨args,hArgsMem,?_⟩,args,hArgsMem,hArgs,hCode⟩
  rcases hop with he | he | he | he
  · subst op
    exact Or.inl hCode
  · subst op
    exact Or.inr (Or.inl hCode)
  · subst op
    exact Or.inr (Or.inr (Or.inl hCode))
  · subst op
    exact Or.inr (Or.inr (Or.inr hCode))

end KP1Y.Satisfaction
