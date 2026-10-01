import KP1Y.ProjectNamingCorrectness
import KP1Y.CompileNamedFormula
import KP1Y.FiniteVariableNames

/-! 普通自由闭合集合公式编译成实际KP程序，并构造读取任意参数环境的对象赋值图。 -/
namespace KP1Y.Named
open YesMetaZFC YesMetaZFC.SetTheory YesMetaZFC.SetTheory.Definitional
open KP1Y.Kuratowski KP1Y.Functions KP1Y.Classes KP1Y.Satisfaction KP1Y.SetLanguage
universe u

def variableCount {n : Nat} (φ : Project.Formula 1 n) : Nat := n+extraDepth φ+1

def initialName {n : Nat} (φ : Project.Formula 1 n) (i : Fin n) : Fin (variableCount φ) :=
  ⟨i.val,by have hi := i.isLt; dsimp [variableCount]; omega⟩

def fallbackName {n : Nat} (φ : Project.Formula 1 n) : Fin (variableCount φ) :=
  ⟨0,by dsimp [variableCount]; omega⟩

def initialEncoding {n : Nat} (φ : Project.Formula 1 n) : Formula (variableCount φ) :=
  encode (fallbackName φ) φ (initialName φ) n (by dsimp [variableCount]; omega)

theorem initialEncoding_correct {M : SetTheory.Structure.{u}} (he : Extensional M) {A : M.Domain}
    (hA : M.TransitiveSet A) {hNe : ∃ x, M.mem x A} {n : Nat} (φ : Project.Formula 1 n) (hClosed : φ.FreeClosed)
    (vals : Fin (variableCount φ) → M.Domain) (s : Env (classModel M (fun x => M.mem x A) hNe) n)
    (hMatch : ValueMatch (initialName φ) vals s) :
    Holds M A vals (initialEncoding φ) ↔ Project.Formula.satisfies s φ :=
  encode_correct he hA φ hClosed (fallbackName φ) (initialName φ) n
    (by dsimp [variableCount]; omega) (fun i => i.isLt) vals s hMatch

theorem graph_reads_exist {M : SetTheory.Structure.{u}} {k : Nat} {s bound A : M.Domain}
    (names : Fin k → M.Domain) (hNames : ∀ i, M.mem (names i) bound) (hS : Graph M s bound A) :
    ∃ vals, Reads M s names vals := by
  classical
  let vals (i : Fin k) := Classical.choose (hS.total (names i) (hNames i))
  exact ⟨vals,fun i => (Classical.choose_spec (hS.total (names i) (hNames i))).2⟩

theorem project_formula_program_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : Context M.Domain} {D : RelationalData M.Domain} {zero one two H Raw Sat Def : M.Domain}
    (h : DefStage M C D zero one two H Raw Sat Def) (hTrans : M.TransitiveSet C.carrier)
    (hNe : ∃ x, M.mem x C.carrier) {n : Nat} (φ : Project.Formula 1 n) (hClosed : φ.FreeClosed) :
    ∃ p length head, FormulaResult M C D p length head (natValue h.spaces.omega (variableCount φ)) ∧
      ∀ s (e : Env (classModel M (fun x => M.mem x C.carrier) hNe) n),
        Graph M s (natValue h.spaces.omega (variableCount φ)) C.carrier →
        (∀ i, MemPair M s (natValue h.spaces.omega i.val) (e.bound i).val) →
        (NodeTrue M C H p head s ↔ Project.Formula.satisfies e φ) := by
  have hEmpty : WellFormedProgram M C D zero zero (natValue h.spaces.omega (variableCount φ)) :=
    ⟨empty_graph h.naturals.zero_empty,h.naturals.zero_nat,natValue_nat h.spaces.omega _,
      fun i hi => False.elim (h.naturals.zero_empty i hi)⟩
  obtain ⟨p,length,head,hP,hTruth⟩ := compile_named_formula_d hM h (natNames h.spaces.omega)
    (natNames_bounded h.spaces.omega) (natNames_injective_d hM h.spaces.omega (variableCount φ)) (initialEncoding φ) hEmpty
  refine ⟨p,length,head,hP.result,?_⟩
  intro s e hS hRows
  obtain ⟨vals,hReads⟩ := graph_reads_exist (natNames h.spaces.omega) (natNames_bounded h.spaces.omega) hS
  have hMatch : ValueMatch (initialName φ) vals e := by
    intro i
    exact hS.unique (natValue h.spaces.omega i.val) _ _ (hReads (initialName φ i)) (hRows i)
  exact (hTruth s vals hS hReads).trans (initialEncoding_correct hM.1 hTrans φ hClosed vals e hMatch)

theorem project_assignment_exists_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {ω A : M.Domain} (hω : M.IsOmega ω) (hNe : ∃ x, M.mem x A) {n : Nat} (φ : Project.Formula 1 n)
    (e : Env (classModel M (fun x => M.mem x A) hNe) n) :
    ∃ s, Graph M s (natValue hω (variableCount φ)) A ∧ ∀ i, MemPair M s (natValue hω i.val) (e.bound i).val := by
  obtain ⟨a,ha⟩ := hNe
  let vals (j : Fin (variableCount φ)) : M.Domain := if hj : j.val<n then (e.bound ⟨j.val,hj⟩).val else a
  have hVals : ∀ j, M.mem (vals j) A := by
    intro j
    by_cases hj : j.val<n
    · simpa only [vals,dif_pos hj] using (e.bound ⟨j.val,hj⟩).property
    · simpa only [vals,dif_neg hj] using ha
  obtain ⟨s,hS,hReads⟩ := finite_assignment_exists_d hM hω vals hVals
  refine ⟨s,hS,?_⟩
  intro i
  have hAt : vals (initialName φ i)=(e.bound i).val := by simp [vals,initialName,i.isLt]
  have hRow := hReads (initialName φ i)
  rw [hAt] at hRow
  exact hRow

end KP1Y.Named
