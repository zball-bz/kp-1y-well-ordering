import KP1Y.UniformFiniteTemplates

/-! 共享语法下的初等性接口及真正使用同一份代码的有限模板反射。 -/
namespace KP1Y.Satisfaction
open YesMetaZFC YesMetaZFC.SetTheory
open KP1Y.Kuratowski KP1Y.Functions
universe u

structure EvaluationData (α : Type u) where
  carrier : α
  assignments : α
  columns : α
  atomic : α
  table : α

def EvaluationData.context {α : Type u} (I : EvaluationData α) (C : Context α) : Context α :=
  C.withInterpretation I.carrier I.assignments I.columns I.atomic

def EvaluationData.Valid {M : SetTheory.Structure.{u}} (I : EvaluationData M.Domain) (C : Context M.Domain) : Prop :=
  EvaluationInstance M C I.carrier I.assignments I.columns I.atomic I.table

/-- 明确的待构造初等性性质，不是 KP1Y.theory 中的新公理。 -/
structure ProgramElementary (M : SetTheory.Structure.{u}) (C : Context M.Domain) (D : RelationalData M.Domain)
    (small large : EvaluationData M.Domain) : Prop where
  carrier_subset : M.MemberSubset small.carrier large.carrier
  truth : ∀ p length head bound, FormulaResult M C D p length head bound →
    ∀ s, Graph M s bound small.carrier →
      (NodeTrue M (small.context C) small.table p head s ↔ NodeTrue M (large.context C) large.table p head s)

theorem reflect_exists_constraints_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : Context M.Domain} (hC : ContextSpaces M C) {D : RelationalData M.Domain}
    {small large : EvaluationData M.Domain} (hSmall : small.Valid C) (hLarge : large.Valid C)
    (hElem : ProgramElementary M C D small large) {seq N vars NV bound seed s : M.Domain}
    (hSeq : Graph M seq N D.codes) (hN : M.mem N C.omega) (hb : M.mem bound C.omega)
    (hVars : Graph M vars NV bound) (hNV : M.mem NV C.omega)
    (hCodes : M.MemberSubset D.codes C.operands)
    (hScoped : ∀ i, M.mem i N → ∀ a, MemPair M seq i a → ScopedAtom M D a bound)
    (hSeed : M.mem seed D.codes) (hSeedScope : ScopedAtom M D seed bound)
    (hS : Graph M s bound small.carrier) :
    ExistsConstraints M (small.context C) D seq N vars NV s bound ↔
      ExistsConstraints M (large.context C) D seq N vars NV s bound := by
  obtain ⟨p,length,head,hP,hMeaning⟩ := uniform_compile_exists_constraints_d hM hC hSeq hN hb hVars hNV hCodes hScoped hSeed hSeedScope
  exact (hMeaning small.carrier small.assignments small.columns small.atomic small.table hSmall s hS).symm.trans
    ((hElem.truth p length head bound hP s hS).trans
      (hMeaning large.carrier large.assignments large.columns large.atomic large.table hLarge s (hS.mono_values hElem.carrier_subset)))

theorem reflect_counterexample_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : Context M.Domain} (hC : ContextSpaces M C) {D : RelationalData M.Domain}
    {small large : EvaluationData M.Domain} (hSmall : small.Valid C) (hLarge : large.Valid C)
    (hElem : ProgramElementary M C D small large)
    {input NI output NO inputVars NVI outputVars NVO bound seed s : M.Domain}
    (hInput : Graph M input NI D.codes) (hNI : M.mem NI C.omega)
    (hOutput : Graph M output NO D.codes) (hNO : M.mem NO C.omega) (hb : M.mem bound C.omega)
    (hInputVars : Graph M inputVars NVI bound) (hNVI : M.mem NVI C.omega)
    (hOutputVars : Graph M outputVars NVO bound) (hNVO : M.mem NVO C.omega)
    (hCodes : M.MemberSubset D.codes C.operands)
    (hScopedInput : ∀ i, M.mem i NI → ∀ a, MemPair M input i a → ScopedAtom M D a bound)
    (hScopedOutput : ∀ i, M.mem i NO → ∀ a, MemPair M output i a → ScopedAtom M D a bound)
    (hSeed : M.mem seed D.codes) (hSeedScope : ScopedAtom M D seed bound)
    (hS : Graph M s bound small.carrier) :
    Counterexample M (small.context C) D input NI output NO inputVars NVI outputVars NVO s bound ↔
      Counterexample M (large.context C) D input NI output NO inputVars NVI outputVars NVO s bound := by
  obtain ⟨p,length,head,hP,hMeaning⟩ := uniform_compile_counterexample_d hM hC hInput hNI hOutput hNO hb
    hInputVars hNVI hOutputVars hNVO hCodes hScopedInput hScopedOutput hSeed hSeedScope
  exact (hMeaning small.carrier small.assignments small.columns small.atomic small.table hSmall s hS).symm.trans
    ((hElem.truth p length head bound hP s hS).trans
      (hMeaning large.carrier large.assignments large.columns large.atomic large.table hLarge s (hS.mono_values hElem.carrier_subset)))

end KP1Y.Satisfaction
