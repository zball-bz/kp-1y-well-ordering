import KP1Y.NaturalPairing
import KP1Y.SequenceSpaces
import KP1Y.AssignmentUpdate

/-! 自然数字词追加的全定义版本，供内部字词解码递归使用。 -/
namespace KP1Y.Naturals
open YesMetaZFC YesMetaZFC.SetTheory YesMetaZFC.SetTheory.Definitional
open KP1Y.Kuratowski KP1Y.Functions KP1Y.Sequences
universe u

def WordExtension (M : SetTheory.Structure.{u}) (ω Words zero old a value : M.Domain) : Prop :=
  (M.mem old Words ∧ ∃ length, M.mem length ω ∧ Graph M old length ω ∧ Append M value old length a) ∨
    (¬M.mem old Words ∧ value=zero)

def wordExtensionFormula {n : Nat} (ω Words zero old a value : Project.Term n) : Project.Formula 1 n :=
  .disj (.conj (.mem old Words) (Project.Formula.existsMem ω
      (.conj (graphFormula old.weaken (.bound 0) ω.weaken)
        (appendFormula value.weaken old.weaken (.bound 0) a.weaken))))
    (.conj (.neg (.mem old Words)) (Project.Formula.extensionalEq value zero))

theorem wordExtensionFormula_delta0 {n : Nat} (ω Words zero old a value : Project.Term n) :
    (wordExtensionFormula ω Words zero old a value).IsDelta0 :=
  .disj (.conj (.mem _ _) (.existsMem _ (.conj (graphFormula_delta0 _ _ _) (appendFormula_delta0 _ _ _ _))))
    (.conj (.neg (.mem _ _)) (.atom _ _ _))

theorem wordExtensionFormula_iff {M : SetTheory.Structure.{u}} (he : Extensional M) {n : Nat}
    (env : Env M n) (ω Words zero old a value : Project.Term n) :
    Project.Formula.satisfies env (wordExtensionFormula ω Words zero old a value) ↔
      WordExtension M (ω.eval env) (Words.eval env) (zero.eval env) (old.eval env) (a.eval env) (value.eval env) := by
  simp only [wordExtensionFormula, Project.Formula.satisfies_disj_iff, Project.Formula.satisfies_conj_iff,
    Project.Formula.satisfies_mem_iff, Project.Formula.satisfies_existsMem_iff, Project.Formula.satisfies_neg_iff,
    Project.Formula.satisfies_extensionalEq_iff_eq he, graphFormula_iff he, appendFormula_iff he,
    Definitional.Term.eval_weaken]
  rfl

theorem word_extension_total_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {ω Words zero old a : M.Domain} (hω : M.IsOmega ω)
    (hWords : ∀ w, M.mem w Words ↔ ∃ n, M.mem n ω ∧ Graph M w n ω)
    (hZeroWord : M.mem zero Words) (ha : M.mem a ω) :
    ∃ value, M.mem value Words ∧ WordExtension M ω Words zero old a value := by
  classical
  by_cases hOld : M.mem old Words
  · obtain ⟨length,hLength,hGraph⟩ := (hWords old).mp hOld
    obtain ⟨next,hSucc,hNext⟩ := hω.1.2 length hLength
    obtain ⟨value,hAppend⟩ := append_exists_d hM old length a
    have hValue := graph_append_d hM hGraph hSucc ha hAppend
    exact ⟨value,(hWords value).mpr ⟨next,hNext,hValue⟩,Or.inl ⟨hOld,length,hLength,hGraph,hAppend⟩⟩
  · exact ⟨zero,hZeroWord,Or.inr ⟨hOld,rfl⟩⟩

theorem word_extension_unique {M : SetTheory.Structure.{u}} (he : Extensional M)
    {ω Words zero old a v v' : M.Domain}
    (h : WordExtension M ω Words zero old a v) (h' : WordExtension M ω Words zero old a v') : v=v' := by
  rcases h with ⟨hOld,n,_,hGraph,hAppend⟩ | ⟨hOld,hv⟩
  · rcases h' with ⟨_,n',_,hGraph',hAppend'⟩ | ⟨hOld',_⟩
    · have hnn' := KP1Y.Assignments.domain_unique he hGraph hGraph'
      subst n'
      exact append_unique he hAppend hAppend'
    · exact False.elim (hOld' hOld)
  · rcases h' with ⟨hOld',_⟩ | ⟨_,hv'⟩
    · exact False.elim (hOld hOld')
    · exact hv.trans hv'.symm

end KP1Y.Naturals
