import KP1Y.ClassSetAbsoluteness
import KP1Y.ClassOrdinals
import KP1Y.Countability

/-! 满射图是Δ₀绝对的；外部不可数序数向传递内模型下降。没有声称不可数性向外绝对。 -/
namespace KP1Y.Classes
open YesMetaZFC YesMetaZFC.SetTheory YesMetaZFC.SetTheory.Definitional
open KP1Y.Kuratowski KP1Y.Cardinal
universe u

theorem onto_class_absolute {M : SetTheory.Structure.{u}} (he : Extensional M)
    {P : M.Domain → Prop} {hNe : ∃ x, P x} (hP : TransitiveClass M P) (F X Y : (classModel M P hNe).Domain) :
    Onto (classModel M P hNe) F X Y ↔ Onto M F.val X.val Y.val := by
  let e := ((oneEnv F).push X).push Y
  exact (ontoFormula_iff (class_extensional he hP) e (.bound 2) (.bound 1) (.bound 0)).symm.trans
    ((delta0_class_absolute hP (ontoFormula_delta0 (.bound 2) (.bound 1) (.bound 0)) e).trans
      (ontoFormula_iff he (forgetEnv e) (.bound 2) (.bound 1) (.bound 0)))

theorem uncountable_into_class {M : SetTheory.Structure.{u}} (he : Extensional M)
    {P : M.Domain → Prop} {hNe : ∃ x, P x} (hP : TransitiveClass M P) (ω ν : (classModel M P hNe).Domain)
    (hν : UncountableOrdinal M ω.val ν.val) : UncountableOrdinal (classModel M P hNe) ω ν := by
  refine ⟨ordinal_into_class hP ν hν.1,hν.2.1,?_⟩
  rintro ⟨F,hF⟩
  exact hν.2.2 ⟨F.val,(onto_class_absolute he hP F ω ν).mp hF⟩

end KP1Y.Classes
