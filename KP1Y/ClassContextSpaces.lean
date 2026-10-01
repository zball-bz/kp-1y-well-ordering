import KP1Y.ClassRelationalData
import KP1Y.CanonicalSetSyntax

/-! 已在传递类中的整套语法参数满足同样的程序空间与FixedSyntax合同。 -/
namespace KP1Y.Classes
open YesMetaZFC YesMetaZFC.SetTheory
open KP1Y.Kuratowski KP1Y.Satisfaction KP1Y.SetLanguage
universe u

theorem context_spaces_into_class_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {P : M.Domain → Prop} {hNe : ∃ x, P x} (hP : TransitiveClass M P) (hInner : (classModel M P hNe).Models KP1Y.theory)
    (C : Context (classModel M P hNe).Domain) (hC : ContextSpaces M (C.map Subtype.val)) : ContextSpaces (classModel M P hNe) C := by
  refine ⟨omega_into_class hM.1 hP C.omega hC.omega,
    ⟨fun h => hC.distinct.atom_neg (congrArg Subtype.val h),
      fun h => hC.distinct.atom_imp (congrArg Subtype.val h),
      fun h => hC.distinct.atom_all (congrArg Subtype.val h),
      fun h => hC.distinct.neg_imp (congrArg Subtype.val h),
      fun h => hC.distinct.neg_all (congrArg Subtype.val h),
      fun h => hC.distinct.imp_all (congrArg Subtype.val h)⟩,
    hC.tag_naturals,fun x hx => hC.omega_operands x.val hx,
    (product_class_absolute_d hM hP hInner C.pairs C.operands C.operands).mpr hC.pairs,?_,
    sequence_space_into_class hM.1 hP C.programs C.omega C.instructions hC.programs,
    sequence_space_into_class hM.1 hP C.assignments C.omega C.carrier hC.assignments,
    (product_class_absolute_d hM hP hInner C.columns C.programs C.assignments).mpr hC.columns⟩
  intro instr
  constructor
  · intro hInstr
    obtain ⟨args,hArgs,hCode⟩ := (hC.instructions instr.val).mp hInstr
    let args0 : (classModel M P hNe).Domain := ⟨args,hP C.pairs.val C.pairs.property args hArgs⟩
    refine ⟨args0,hArgs,?_⟩
    rcases hCode with hCode | hCode | hCode | hCode
    · exact Or.inl ((codes_class_absolute hM.1 hP instr C.atomTag args0).mpr hCode)
    · exact Or.inr (Or.inl ((codes_class_absolute hM.1 hP instr C.negTag args0).mpr hCode))
    · exact Or.inr (Or.inr (Or.inl ((codes_class_absolute hM.1 hP instr C.impTag args0).mpr hCode)))
    · exact Or.inr (Or.inr (Or.inr ((codes_class_absolute hM.1 hP instr C.allTag args0).mpr hCode)))
  · rintro ⟨args,hArgs,hCode⟩
    apply (hC.instructions instr.val).mpr
    refine ⟨args.val,hArgs,?_⟩
    rcases hCode with hCode | hCode | hCode | hCode
    · exact Or.inl ((codes_class_absolute hM.1 hP instr C.atomTag args).mp hCode)
    · exact Or.inr (Or.inl ((codes_class_absolute hM.1 hP instr C.negTag args).mp hCode))
    · exact Or.inr (Or.inr (Or.inl ((codes_class_absolute hM.1 hP instr C.impTag args).mp hCode)))
    · exact Or.inr (Or.inr (Or.inr ((codes_class_absolute hM.1 hP instr C.allTag args).mp hCode)))

theorem fixed_syntax_into_class_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {P : M.Domain → Prop} {hNe : ∃ x, P x} (hP : TransitiveClass M P) (hInner : (classModel M P hNe).Models KP1Y.theory)
    (C : Context (classModel M P hNe).Domain) (D : RelationalData (classModel M P hNe).Domain)
    (zero one two : (classModel M P hNe).Domain)
    (hS : FixedSyntax M (C.map Subtype.val) (D.map Subtype.val) zero.val one.val two.val) :
    FixedSyntax (classModel M P hNe) C D zero one two := by
  exact ⟨interpretation_into_class hM.1 hP D zero one two hS.interpretation,
    context_spaces_into_class_d hM hP hInner C hS.spaces,
    ⟨Subtype.ext hS.link.omega_eq,Subtype.ext hS.link.carrier_eq,Subtype.ext hS.link.assignments_eq,rfl,
      fun x hx => hS.link.codes_bound x.val hx⟩⟩

end KP1Y.Classes
