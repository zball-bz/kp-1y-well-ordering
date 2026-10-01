import KP1Y.CompiledExtension

/-! 一个完整公式结果：合法程序及其真正的最后节点，验证仍为 Δ₀。 -/
namespace KP1Y.Satisfaction
open YesMetaZFC YesMetaZFC.SetTheory YesMetaZFC.SetTheory.Definitional
open KP1Y.Kuratowski KP1Y.Functions KP1Y.Bounded
universe u

structure FormulaResult (M : SetTheory.Structure.{u}) (C : Context M.Domain) (D : RelationalData M.Domain)
    (p length head bound : M.Domain) : Prop where
  wellFormed : WellFormedProgram M C D p length bound
  successor : M.SuccessorOf length head
  head_nat : M.mem head C.omega

def resultFormula {n : Nat} (C : Context (Project.Term n)) (D : RelationalData (Project.Term n))
    (p length head bound : Project.Term n) : Project.Formula 1 n :=
  .conj (wellFormedProgramFormula C D p length bound)
    (.conj (successorFormula length head) (.mem head C.omega))

theorem resultFormula_delta0 {n : Nat} (C : Context (Project.Term n)) (D : RelationalData (Project.Term n))
    (p length head bound : Project.Term n) : (resultFormula C D p length head bound).IsDelta0 :=
  .conj (wellFormedProgramFormula_delta0 _ _ _ _ _) (.conj (successorFormula_delta0 _ _) (.mem _ _))

theorem resultFormula_iff {M : SetTheory.Structure.{u}} (he : Extensional M) {n : Nat}
    (env : Env M n) (C : Context (Project.Term n)) (D : RelationalData (Project.Term n))
    (p length head bound : Project.Term n) :
    Project.Formula.satisfies env (resultFormula C D p length head bound) ↔
      FormulaResult M (C.eval env) (D.eval env) (p.eval env) (length.eval env) (head.eval env) (bound.eval env) := by
  simp only [resultFormula, Project.Formula.satisfies_conj_iff, wellFormedProgramFormula_iff he,
    successorFormula_iff he, Project.Formula.satisfies_mem_iff]
  exact ⟨fun h => ⟨h.1,h.2.1,h.2.2⟩,fun h => ⟨h.wellFormed,h.successor,h.head_nat⟩⟩

theorem CompiledExtension.result {M : SetTheory.Structure.{u}} {C : Context M.Domain} {D : RelationalData M.Domain}
    {p n bound q length head : M.Domain} (h : CompiledExtension M C D p n bound q length head) :
    FormulaResult M C D q length head bound := ⟨h.wellFormed,h.successor,h.head_nat⟩

theorem FormulaResult.formula {M : SetTheory.Structure.{u}} {C : Context M.Domain} {D : RelationalData M.Domain}
    {p length head bound : M.Domain} (h : FormulaResult M C D p length head bound) :
    FormulaProgram M C D p length bound := ⟨h.wellFormed,head,h.successor.predecessor_mem⟩

theorem FormulaResult.program_mem {M : SetTheory.Structure.{u}} {C : Context M.Domain} (hC : ContextSpaces M C)
    {D : RelationalData M.Domain} {p length head bound : M.Domain} (h : FormulaResult M C D p length head bound) :
    M.mem p C.programs := (hC.programs p).mpr ⟨length,h.wellFormed.length_nat,h.wellFormed.graph⟩

end KP1Y.Satisfaction
