import KP1Y.SequenceSpaceStep

/-! 对所有内部自然数长度，构造恰好包含全部集合函数的序列空间 A^{<ω}。 -/
namespace KP1Y.Sequences
open YesMetaZFC YesMetaZFC.SetTheory YesMetaZFC.SetTheory.Definitional
open KP1Y.Kuratowski KP1Y.Functions KP1Y.Bounded KP1Y.Naturals
universe u

def Space (M : SetTheory.Structure.{u}) (T i A : M.Domain) : Prop :=
  ∀ F, M.mem F T ↔ Graph M F i A

def spaceFormula {n : Nat} (T i A : Project.Term n) : Project.Formula 1 n :=
  .forallE (.iff (.mem (.bound 0) T.weaken) (graphFormula (.bound 0) i.weaken A.weaken))

theorem spaceFormula_iff {M : SetTheory.Structure.{u}} (he : Extensional M) {n : Nat}
    (env : Env M n) (T i A : Project.Term n) :
    Project.Formula.satisfies env (spaceFormula T i A) ↔ Space M (T.eval env) (i.eval env) (A.eval env) := by
  simp only [spaceFormula, Project.Formula.satisfies_forall_iff,
    Project.Formula.satisfies_iff_iff, Project.Formula.satisfies_mem_iff,
    graphFormula_iff he, Definitional.Term.eval_weaken]
  rfl

theorem append_space_correct_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {T B A i s : M.Domain} (hB : Space M B i A) (hs : M.SuccessorOf s i)
    (hT : AppendSpace M T B A i) : Space M T s A := by
  intro G
  constructor
  · intro hGT
    obtain ⟨F,hF,a,ha,hApp⟩ := (hT G).mp hGT
    exact graph_append_d hM ((hB F).mp hF) hs ha hApp
  · intro hG
    obtain ⟨F,a,hF,ha,hApp⟩ := graph_decompose_d hM hG hs
    exact (hT G).mpr ⟨F,(hB F).mpr hF,a,ha,hApp⟩

private def rowSpaceSchema : Project.UnarySchema 2 where
  body := .forallE (.imp (memPairFormula (.bound 3) (.bound 1) (.bound 0))
    (spaceFormula (.bound 0) (.bound 1) (.bound 2)))
  freeClosed := by
    simp [spaceFormula, graphFormula, memPairFormula, codeFormula, pairFormula,
      Project.Formula.forallMem, Project.Formula.existsMem, Definitional.Formula.FreeClosed]

private theorem rowSpaceSchema_iff {M : SetTheory.Structure.{u}} (he : Extensional M)
    (H A i : M.Domain) :
    Project.Formula.satisfies (((oneEnv H).push A).push i) rowSpaceSchema.body ↔
      ∀ T, MemPair M H i T → Space M T i A := by
  simp only [rowSpaceSchema, Project.Formula.satisfies_forall_iff,
    Project.Formula.satisfies_imp_iff, memPairFormula_iff he, spaceFormula_iff he]
  rfl

theorem space_history_row {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {A H ω V Q i T : M.Domain}
    (hH : KP1Y.SigmaRecursion.ValueHistory M (spaceStep.denote (oneEnv A)) H ω V Q)
    (hi : M.mem i ω) (hHi : MemPair M H i T) :
    ((∀ x, ¬M.mem x i) ∧ PairSet M T i i) ∨
      ∃ p, M.mem p i ∧ ∃ B, M.SuccessorOf i p ∧ MemPair M H p B ∧ AppendSpace M T B A p := by
  obtain ⟨P,hPV,hQi⟩ := hH.prefixes.total i hi
  obtain ⟨hPref,w,_,hStep⟩ := hH.obeys i hi P hPV T (hH.values.bounds hM.1 hHi).2 hQi hHi
  obtain ⟨_,hCases⟩ := (spaceStep_iff hM A i P T w).mp hStep
  rcases hCases with hZero | ⟨p,hp,B,_,hs,hPB,hSpace⟩
  · exact Or.inl hZero
  · exact Or.inr ⟨p,hp,B,hs,(hPref.all_rows hM.1 hH.values p hp B).mp hPB,hSpace⟩

theorem space_history_exact_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {A H ω V Q : M.Domain} (hω : M.IsOmega ω)
    (hH : KP1Y.SigmaRecursion.ValueHistory M (spaceStep.denote (oneEnv A)) H ω V Q) :
    ∀ i, M.mem i ω → ∀ T, MemPair M H i T → Space M T i A := by
  have hAll := natural_induction_d hM rowSpaceSchema ((oneEnv H).push A) hω
    (fun e he => (rowSpaceSchema_iff hM.1 H A e).mpr (by
      intro T hT
      obtain ⟨zero,hzero,hzeroω⟩ := hω.1.1
      have hezero := hM.1.eq_of_same_members e zero (fun x => iff_of_false (he x) (hzero x))
      have heω : M.mem e ω := hezero ▸ hzeroω
      rcases space_history_row hM hH heω hT with ⟨_,hPair⟩ | ⟨p,hp,_,_,_,_⟩
      · intro F
        constructor
        · intro hF
          have hFe : F=e := (hPair F).mp hF |>.elim id id
          subst F
          exact empty_graph he
        · intro hF
          have hFe : F=e := hF.ext hM.1 (empty_graph (V := A) he) (fun x hx => False.elim (he x hx))
          exact (hPair F).mpr (Or.inl hFe)
      · exact False.elim (he p hp)))
    (fun p hp ih s hs => (rowSpaceSchema_iff hM.1 H A s).mpr (by
      intro T hT
      obtain ⟨s',hs',hs'ω⟩ := hω.1.2 p hp
      have hsω : M.mem s ω := (Structure.SuccessorOf.eq hM.1 hs hs') ▸ hs'ω
      rcases space_history_row hM hH hsω hT with ⟨hEmpty,_⟩ | ⟨q,_,B,hsq,hPB,hSpace⟩
      · exact False.elim (hEmpty p hs.predecessor_mem)
      · have hpq := Structure.SuccessorOf.predecessor_eq hM.1 ((omega_isOrdinal_d hM hω).mem hp) hs hsq
        subst q
        exact append_space_correct_d hM ((rowSpaceSchema_iff hM.1 H A p).mp ih B hPB) hs hSpace))
  exact fun i hi => (rowSpaceSchema_iff hM.1 H A i).mp (hAll i hi)

theorem finite_sequences_exist_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {ω : M.Domain} (hω : M.IsOmega ω) (A : M.Domain) :
    ∃ S, ∀ F, M.mem F S ↔ ∃ i, M.mem i ω ∧ Graph M F i A := by
  obtain ⟨H,V,Q,hH⟩ := space_history_exists_d hM hω A
  have hExact := space_history_exact_d hM hω hH
  obtain ⟨D,hD⟩ := KP1Y.functional_image_d hM KP1Y.Recursion.memberSchema (oneEnv H) ω
    (fun i hi => by
      obtain ⟨T,_,hT⟩ := hH.values.total i hi
      exact ⟨T,(KP1Y.Recursion.memberSchema_iff hM.1 H i T).mpr hT⟩)
    (fun i _ T U hT hU => hH.values.unique i T U
      ((KP1Y.Recursion.memberSchema_iff hM.1 H i T).mp hT)
      ((KP1Y.Recursion.memberSchema_iff hM.1 H i U).mp hU))
  have hRange : ∀ T, M.mem T D ↔ ∃ i, M.mem i ω ∧ MemPair M H i T := by
    intro T
    simpa only [KP1Y.Recursion.memberSchema_iff hM.1] using hD T
  obtain ⟨S,hS⟩ := SetTheory.KP.exists_union (KP1Y.models_weakKP hM) D
  refine ⟨S,fun F => ?_⟩
  constructor
  · intro hFS
    obtain ⟨T,hTD,hFT⟩ := (hS F).mp hFS
    obtain ⟨i,hi,hT⟩ := (hRange T).mp hTD
    exact ⟨i,hi,(hExact i hi T hT F).mp hFT⟩
  · rintro ⟨i,hi,hF⟩
    obtain ⟨T,_,hT⟩ := hH.values.total i hi
    exact (hS F).mpr ⟨T,(hRange T).mpr ⟨i,hi,hT⟩,(hExact i hi T hT F).mpr hF⟩

def finiteSequenceSpaceFormula {n : Nat} (S ω A : Project.Term n) : Project.Formula 1 n :=
  .forallE (.iff (.mem (.bound 0) S.weaken)
    (Project.Formula.existsMem ω.weaken (graphFormula (.bound 1) (.bound 0) A.weaken.weaken)))

theorem finiteSequenceSpaceFormula_iff {M : SetTheory.Structure.{u}} (he : Extensional M) {n : Nat}
    (env : Env M n) (S ω A : Project.Term n) :
    Project.Formula.satisfies env (finiteSequenceSpaceFormula S ω A) ↔
      ∀ F, M.mem F (S.eval env) ↔ ∃ i, M.mem i (ω.eval env) ∧ Graph M F i (A.eval env) := by
  simp only [finiteSequenceSpaceFormula, Project.Formula.satisfies_forall_iff,
    Project.Formula.satisfies_iff_iff, Project.Formula.satisfies_mem_iff,
    Project.Formula.satisfies_existsMem_iff, graphFormula_iff he, Definitional.Term.eval_weaken]
  rfl

def sequencesCore : Project.Formula 1 2 :=
  .imp (Project.Formula.isOmega (.bound 1))
    (.existsE (finiteSequenceSpaceFormula (.bound 0) (.bound 2) (.bound 1)))

def sequencesSentence : Project.Sentence :=
  Project.Sentence.forallClosure sequencesCore (by
    simp [sequencesCore, finiteSequenceSpaceFormula, graphFormula, memPairFormula,
      codeFormula, pairFormula, Project.Formula.isOmega, Project.Formula.isInductive,
      Project.Formula.isEmpty, Project.Formula.isSuccessor, Project.Formula.forallMem,
      Project.Formula.existsMem, Definitional.Formula.FreeClosed])

theorem sequencesCore_iff {M : SetTheory.Structure.{u}} (he : Extensional M) (env : Env M 2) :
    Project.Formula.satisfies env sequencesCore ↔
      (M.IsOmega (env.bound 1) → ∃ S, ∀ F, M.mem F S ↔
        ∃ i, M.mem i (env.bound 1) ∧ Graph M F i (env.bound 0)) := by
  simp only [sequencesCore, Project.Formula.satisfies_imp_iff,
    Project.Formula.satisfies_isOmega_iff, Project.Formula.satisfies_exists_iff,
    finiteSequenceSpaceFormula_iff he]
  rfl

theorem finite_sequences_derivable : KP1Y.Derives sequencesSentence := by
  apply KP1Y.derives_of_all_models
  intro M hM free
  apply (Project.Formula.satisfies_forallClosure_iff free sequencesCore).mpr
  intro bound
  exact (sequencesCore_iff hM.1 ⟨bound,free⟩).mpr (fun hω => finite_sequences_exist_d hM hω (bound 0))

end KP1Y.Sequences
