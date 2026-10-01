import KP1Y.NamedAssignments
import KP1Y.SetRelationExtensions
import KP1Y.CompileQuantifier

/-! 任意有限命名公式编译成KP模型中的真实程序，完整保留前缀并核验全部赋值。 -/
namespace KP1Y.Named
open YesMetaZFC YesMetaZFC.SetTheory
open KP1Y.Kuratowski KP1Y.Functions KP1Y.Assignments KP1Y.Satisfaction KP1Y.SetLanguage
universe u

theorem compile_named_formula_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : Context M.Domain} {D : RelationalData M.Domain} {zero one two H Raw Sat Def bound : M.Domain}
    (h : DefStage M C D zero one two H Raw Sat Def) {k : Nat} (names : Fin k → M.Domain)
    (hNames : ∀ i, M.mem (names i) bound) (hInj : InjectiveNames names) (φ : Formula k)
    {p n : M.Domain} (hP : WellFormedProgram M C D p n bound) :
    ∃ q length head, CompiledExtension M C D p n bound q length head ∧
      ∀ s vals, Graph M s bound C.carrier → Reads M s names vals →
        (NodeTrue M C H q head s ↔ Holds M C.carrier vals φ) := by
  induction φ generalizing p n with
  | equal i j =>
      obtain ⟨q,length,hQ,hTruth⟩ := compile_equality_extension_d hM h hP (hNames i) (hNames j)
      exact ⟨q,length,n,hQ,fun s vals hS hR => hTruth s (vals i) (vals j) hS (hR i) (hR j)⟩
  | member i j =>
      obtain ⟨q,length,hQ,hTruth⟩ := compile_membership_extension_d hM h hP (hNames i) (hNames j)
      exact ⟨q,length,n,hQ,fun s vals hS hR => hTruth s (vals i) (vals j) hS (hR i) (hR j)⟩
  | neg φ ih =>
      obtain ⟨p1,n1,j1,h1,truth1⟩ := ih hP
      obtain ⟨p2,n2,h2,truth2⟩ := compile_negation_d hM h.spaces h.evaluation h1.wellFormed h1.successor.predecessor_mem
      refine ⟨p2,n2,n1,h1.trans hM.1 h2,?_⟩
      intro s vals hS hR
      have hs := (h.spaces.assignments s).mpr ⟨bound,hP.bound_nat,hS⟩
      exact (truth2 s hs).trans (not_congr (truth1 s vals hS hR))
  | imp φ ψ ihφ ihψ =>
      obtain ⟨p1,n1,j1,h1,truth1⟩ := ihφ hP
      obtain ⟨p2,n2,j2,h2,truth2⟩ := ihψ h1.wellFormed
      have hj1 := prefix_domain_subset hM.1 h2.prefixGraph h2.wellFormed.graph j1 h1.successor.predecessor_mem
      obtain ⟨p3,n3,h3,truth3⟩ := compile_implication_d hM h.spaces h.evaluation h2.wellFormed hj1 h2.successor.predecessor_mem
      refine ⟨p3,n3,n2,(h1.trans hM.1 h2).trans hM.1 h3,?_⟩
      intro s vals hS hR
      have hs := (h.spaces.assignments s).mpr ⟨bound,hP.bound_nat,hS⟩
      have hOld := (h2.old_node hM h.spaces h.evaluation h1.wellFormed.length_nat h1.successor.predecessor_mem hs).symm
      exact (truth3 s hs).trans (imp_congr (hOld.trans (truth1 s vals hS hR)) (truth2 s vals hS hR))
  | all v φ ih =>
      obtain ⟨p1,n1,j1,h1,truth1⟩ := ih hP
      obtain ⟨p2,n2,h2,truth2⟩ := compile_universal_d hM h.spaces h.evaluation h1.wellFormed h1.successor.predecessor_mem (hNames v)
      refine ⟨p2,n2,n1,h1.trans hM.1 h2,?_⟩
      intro s vals hS hR
      apply (truth2 s hS).trans
      constructor
      · intro hAll x hx
        obtain ⟨t,hU⟩ := update_exists_d hM (i := names v) hS hx
        have hReads := reads_updated hM.1 hNames hInj hS hR v hx hU
        exact (truth1 t (setValue vals v x) hU.graph hReads).mp (hAll x hx t hU)
      · intro hAll x hx t hU
        have hReads := reads_updated hM.1 hNames hInj hS hR v hx hU
        exact (truth1 t (setValue vals v x) hU.graph hReads).mpr (hAll x hx)

end KP1Y.Named
