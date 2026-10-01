import KP1Y.ClassStructures

/-! 任意非空传递类与原模型之间的全部Δ₀公式绝对性，逐有界语法构造证明。 -/
namespace KP1Y.Classes
open YesMetaZFC YesMetaZFC.SetTheory YesMetaZFC.SetTheory.Definitional
universe u

theorem delta0_class_absolute {M : SetTheory.Structure.{u}} {P : M.Domain → Prop} {hNe : ∃ x, P x}
    (hP : TransitiveClass M P) {n : Nat} {φ : Project.Formula 1 n} (hφ : φ.IsDelta0)
    (env : Env (classModel M P hNe) n) :
    Project.Formula.satisfies env φ ↔ Project.Formula.satisfies (forgetEnv env) φ := by
  induction hφ with
  | falsum => simp only [Project.Formula.satisfies_falsum_iff]
  | truth => simp only [Project.Formula.satisfies_truth_iff]
  | mem a b =>
      simp only [Project.Formula.satisfies_mem_iff]
      change M.mem (a.eval env).val (b.eval env).val ↔ _
      rw [term_value_forget,term_value_forget]
  | atom symbol hs args =>
      cases symbol with
      | extensionalEq =>
          rw [Project.Formula.satisfies_atom_extensionalEq_iff,Project.Formula.satisfies_atom_extensionalEq_iff]
          simpa only [Structure.SameMembers,term_value_forget] using
            (same_members_absolute hP ((args 0).eval env) ((args 1).eval env))
      | subset =>
          rw [Project.Formula.satisfies_atom_subset_iff,Project.Formula.satisfies_atom_subset_iff]
          simpa only [Structure.MemberSubset,term_value_forget] using
            (subset_absolute hP ((args 0).eval env) ((args 1).eval env))
  | neg h ih =>
      simp only [Project.Formula.satisfies_neg_iff]
      exact not_congr (ih env)
  | conj h1 h2 ih1 ih2 =>
      simp only [Project.Formula.satisfies_conj_iff]
      exact and_congr (ih1 env) (ih2 env)
  | disj h1 h2 ih1 ih2 =>
      simp only [Project.Formula.satisfies_disj_iff]
      exact or_congr (ih1 env) (ih2 env)
  | imp h1 h2 ih1 ih2 =>
      simp only [Project.Formula.satisfies_imp_iff]
      exact imp_congr (ih1 env) (ih2 env)
  | iff h1 h2 ih1 ih2 =>
      simp only [Project.Formula.satisfies_iff_iff]
      exact iff_congr (ih1 env) (ih2 env)
  | forallMem t h ih =>
      simp only [Project.Formula.satisfies_forallMem_iff]
      constructor
      · intro hAll x hx
        have hx' : M.mem x (t.eval env).val := by simpa only [term_value_forget] using hx
        let a : (classModel M P hNe).Domain := ⟨x,hP _ (t.eval env).property x hx'⟩
        have hBody := (ih (env.push a)).mp (hAll a hx')
        simpa only [forgetEnv_push] using hBody
      · intro hAll a ha
        have ha' : M.mem a.val (t.eval (forgetEnv env)) := by
          change M.mem a.val (t.eval env).val at ha
          simpa only [term_value_forget] using ha
        apply (ih (env.push a)).mpr
        simpa only [forgetEnv_push] using hAll a.val ha'
  | existsMem t h ih =>
      simp only [Project.Formula.satisfies_existsMem_iff]
      constructor
      · rintro ⟨a,ha,hBody⟩
        have ha' : M.mem a.val (t.eval (forgetEnv env)) := by
          change M.mem a.val (t.eval env).val at ha
          simpa only [term_value_forget] using ha
        refine ⟨a.val,ha',?_⟩
        simpa only [forgetEnv_push] using (ih (env.push a)).mp hBody
      · rintro ⟨x,hx,hBody⟩
        have hx' : M.mem x (t.eval env).val := by simpa only [term_value_forget] using hx
        let a : (classModel M P hNe).Domain := ⟨x,hP _ (t.eval env).property x hx'⟩
        refine ⟨a,hx',(ih (env.push a)).mpr ?_⟩
        simpa only [forgetEnv_push] using hBody

end KP1Y.Classes
