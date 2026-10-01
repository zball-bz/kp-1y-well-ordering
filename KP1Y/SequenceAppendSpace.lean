import KP1Y.SequenceAppend

/-! 一个实际序列族追加所有 A 中的项，所得精确像仍是 KPω 中的集合。 -/
namespace KP1Y.Sequences
open YesMetaZFC YesMetaZFC.SetTheory YesMetaZFC.SetTheory.Definitional
open KP1Y.Kuratowski KP1Y.Functions KP1Y.Bounded
universe u

def AppendSpace (M : SetTheory.Structure.{u}) (T B A i : M.Domain) : Prop :=
  ∀ G, M.mem G T ↔ ∃ F, M.mem F B ∧ ∃ a, M.mem a A ∧ Append M G F i a

def appendSpaceFormula {n : Nat} (T B A i : Project.Term n) : Project.Formula 1 n :=
  .conj
    (Project.Formula.forallMem T (Project.Formula.existsMem B.weaken
      (Project.Formula.existsMem A.weaken.weaken
        (appendFormula (.bound 2) (.bound 1) i.weaken.weaken.weaken (.bound 0)))))
    (Project.Formula.forallMem B (Project.Formula.forallMem A.weaken
      (Project.Formula.existsMem T.weaken.weaken
        (appendFormula (.bound 0) (.bound 2) i.weaken.weaken.weaken (.bound 1)))))

theorem appendSpaceFormula_delta0 {n : Nat} (T B A i : Project.Term n) :
    (appendSpaceFormula T B A i).IsDelta0 :=
  .conj (.forallMem _ (.existsMem _ (.existsMem _ (appendFormula_delta0 _ _ _ _))))
    (.forallMem _ (.forallMem _ (.existsMem _ (appendFormula_delta0 _ _ _ _))))

theorem appendSpaceFormula_iff {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory) {n : Nat}
    (env : Env M n) (T B A i : Project.Term n) :
    Project.Formula.satisfies env (appendSpaceFormula T B A i) ↔
      AppendSpace M (T.eval env) (B.eval env) (A.eval env) (i.eval env) := by
  simp only [appendSpaceFormula, Project.Formula.satisfies_conj_iff,
    Project.Formula.satisfies_forallMem_iff, Project.Formula.satisfies_existsMem_iff,
    appendFormula_iff hM.1, Definitional.Term.eval_weaken]
  constructor
  · rintro ⟨hSound,hTotal⟩ G
    refine ⟨hSound G,?_⟩
    rintro ⟨F,hF,a,ha,hApp⟩
    obtain ⟨J,hJ,hAppJ⟩ := hTotal F hF a ha
    exact (append_unique hM.1 hApp hAppJ) ▸ hJ
  · intro h
    refine ⟨fun G => (h G).mp,?_⟩
    intro F hF a ha
    obtain ⟨G,hApp⟩ := append_exists_d hM F (i.eval env) a
    exact ⟨G,(h G).mpr ⟨F,hF,a,ha,hApp⟩,hApp⟩

theorem appendSpace_unique {M : SetTheory.Structure.{u}} (he : Extensional M)
    {T T' B A i : M.Domain} (hT : AppendSpace M T B A i) (hT' : AppendSpace M T' B A i) : T=T' :=
  he.eq_of_same_members T T' (fun G => (hT G).trans (hT' G).symm)

private def appendImageSchema : Project.Delta0BinarySchema 3 where
  body := Project.Formula.existsMem (.bound 3) (Project.Formula.existsMem (.bound 5)
    (.conj (codeFormula (.bound 3) (.bound 1) (.bound 0))
      (appendFormula (.bound 2) (.bound 1) (.bound 4) (.bound 0))))
  freeClosed := by
    simp [appendFormula, insertFormula, codeFormula, pairFormula,
      Project.Formula.existsMem, Project.Formula.forallMem, Definitional.Formula.FreeClosed]
  delta0 := .existsMem _ (.existsMem _
    (.conj (codeFormula_delta0 _ _ _) (appendFormula_delta0 _ _ _ _)))

private def appendEnv {M : SetTheory.Structure.{u}} (i B A : M.Domain) : Env M 3 :=
  ⟨Fin.cases i (Fin.cases B (fun _ => A)),fun _ => i⟩

private theorem appendImageSchema_iff {M : SetTheory.Structure.{u}} (he : Extensional M)
    (i B A q G : M.Domain) :
    Project.Formula.satisfies (((appendEnv i B A).push q).push G) appendImageSchema.body ↔
      ∃ F, M.mem F B ∧ ∃ a, M.mem a A ∧ Codes M q F a ∧ Append M G F i a := by
  simp only [appendImageSchema, Project.Formula.satisfies_existsMem_iff,
    Project.Formula.satisfies_conj_iff, codeFormula_iff he, appendFormula_iff he]
  rfl

theorem appendSpace_exists_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    (B A i : M.Domain) : ∃ T, AppendSpace M T B A i := by
  obtain ⟨P,hP⟩ := product_exists hM B A
  obtain ⟨T,hT⟩ := KP1Y.functional_image_d hM appendImageSchema (appendEnv i B A) P
    (fun q hq => by
      obtain ⟨F,hF,a,ha,hcode⟩ := (hP q).mp hq
      obtain ⟨G,hApp⟩ := append_exists_d hM F i a
      exact ⟨G,(appendImageSchema_iff hM.1 i B A q G).mpr ⟨F,hF,a,ha,hcode,hApp⟩⟩)
    (fun q _ G J hG hJ => by
      obtain ⟨F,_,a,_,hcode,hApp⟩ := (appendImageSchema_iff hM.1 i B A q G).mp hG
      obtain ⟨F',_,a',_,hcode',hApp'⟩ := (appendImageSchema_iff hM.1 i B A q J).mp hJ
      obtain ⟨hF,ha⟩ := codes_injective hM.1 hcode hcode'
      subst F'
      subst a'
      exact append_unique hM.1 hApp hApp')
  refine ⟨T,fun G => ?_⟩
  constructor
  · intro hGT
    obtain ⟨q,_,hφ⟩ := (hT G).mp hGT
    obtain ⟨F,hF,a,ha,_,hApp⟩ := (appendImageSchema_iff hM.1 i B A q G).mp hφ
    exact ⟨F,hF,a,ha,hApp⟩
  · rintro ⟨F,hF,a,ha,hApp⟩
    obtain ⟨q,hcode⟩ := codes_total hM F a
    exact (hT G).mpr ⟨q,(hP q).mpr ⟨F,hF,a,ha,hcode⟩,
      (appendImageSchema_iff hM.1 i B A q G).mpr ⟨F,hF,a,ha,hcode,hApp⟩⟩

end KP1Y.Sequences
