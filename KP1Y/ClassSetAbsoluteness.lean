import KP1Y.ClassBoundedTruth
import KP1Y.RelationTables
import KP1Y.FunctionGraphs

/-! 传递类中的实际有序对、关系、函数和积，通过已有字面Δ₀公式逐项绝对。 -/
namespace KP1Y.Classes
open YesMetaZFC YesMetaZFC.SetTheory YesMetaZFC.SetTheory.Definitional
open KP1Y.Kuratowski KP1Y.Functions
universe u

theorem pair_class_absolute {M : SetTheory.Structure.{u}} (he : Extensional M)
    {P : M.Domain → Prop} {hNe : ∃ x, P x} (hP : TransitiveClass M P) (p x y : (classModel M P hNe).Domain) :
    PairSet (classModel M P hNe) p x y ↔ PairSet M p.val x.val y.val := by
  let e := ((oneEnv p).push x).push y
  exact (pairFormula_iff (class_extensional he hP) e (.bound 2) (.bound 1) (.bound 0)).symm.trans
    ((delta0_class_absolute hP (pairFormula_delta0 (.bound 2) (.bound 1) (.bound 0)) e).trans
      (pairFormula_iff he (forgetEnv e) (.bound 2) (.bound 1) (.bound 0)))

theorem codes_class_absolute {M : SetTheory.Structure.{u}} (he : Extensional M)
    {P : M.Domain → Prop} {hNe : ∃ x, P x} (hP : TransitiveClass M P) (p x y : (classModel M P hNe).Domain) :
    Codes (classModel M P hNe) p x y ↔ Codes M p.val x.val y.val := by
  let e := ((oneEnv p).push x).push y
  exact (codeFormula_iff (class_extensional he hP) e (.bound 2) (.bound 1) (.bound 0)).symm.trans
    ((delta0_class_absolute hP (codeFormula_delta0 (.bound 2) (.bound 1) (.bound 0)) e).trans
      (codeFormula_iff he (forgetEnv e) (.bound 2) (.bound 1) (.bound 0)))

theorem memPair_class_absolute {M : SetTheory.Structure.{u}} (he : Extensional M)
    {P : M.Domain → Prop} {hNe : ∃ x, P x} (hP : TransitiveClass M P) (R x y : (classModel M P hNe).Domain) :
    MemPair (classModel M P hNe) R x y ↔ MemPair M R.val x.val y.val := by
  let e := ((oneEnv R).push x).push y
  exact (memPairFormula_iff (class_extensional he hP) e (.bound 2) (.bound 1) (.bound 0)).symm.trans
    ((delta0_class_absolute hP (memPairFormula_delta0 (.bound 2) (.bound 1) (.bound 0)) e).trans
      (memPairFormula_iff he (forgetEnv e) (.bound 2) (.bound 1) (.bound 0)))

theorem graph_class_absolute {M : SetTheory.Structure.{u}} (he : Extensional M)
    {P : M.Domain → Prop} {hNe : ∃ x, P x} (hP : TransitiveClass M P) (F A V : (classModel M P hNe).Domain) :
    Graph (classModel M P hNe) F A V ↔ Graph M F.val A.val V.val := by
  let e := ((oneEnv F).push A).push V
  exact (graphFormula_iff (class_extensional he hP) e (.bound 2) (.bound 1) (.bound 0)).symm.trans
    ((delta0_class_absolute hP (graphFormula_delta0 (.bound 2) (.bound 1) (.bound 0)) e).trans
      (graphFormula_iff he (forgetEnv e) (.bound 2) (.bound 1) (.bound 0)))

theorem relationSupport_class_absolute {M : SetTheory.Structure.{u}} (he : Extensional M)
    {P : M.Domain → Prop} {hNe : ∃ x, P x} (hP : TransitiveClass M P) (R X Y : (classModel M P hNe).Domain) :
    RelationSupport (classModel M P hNe) R X Y ↔ RelationSupport M R.val X.val Y.val := by
  let e := ((oneEnv R).push X).push Y
  exact (relationSupportFormula_iff (class_extensional he hP) e (.bound 2) (.bound 1) (.bound 0)).symm.trans
    ((delta0_class_absolute hP (relationSupportFormula_delta0 (.bound 2) (.bound 1) (.bound 0)) e).trans
      (relationSupportFormula_iff he (forgetEnv e) (.bound 2) (.bound 1) (.bound 0)))

theorem product_class_absolute_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {P : M.Domain → Prop} {hNe : ∃ x, P x} (hP : TransitiveClass M P) (hInner : (classModel M P hNe).Models KP1Y.theory)
    (R X Y : (classModel M P hNe).Domain) : IsProduct (classModel M P hNe) R X Y ↔ IsProduct M R.val X.val Y.val := by
  let e := ((oneEnv R).push X).push Y
  exact (productBoundedFormula_iff hInner e (.bound 2) (.bound 1) (.bound 0)).symm.trans
    ((delta0_class_absolute hP (productBoundedFormula_delta0 (.bound 2) (.bound 1) (.bound 0)) e).trans
      (productBoundedFormula_iff hM (forgetEnv e) (.bound 2) (.bound 1) (.bound 0)))

end KP1Y.Classes
