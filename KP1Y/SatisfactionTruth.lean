import KP1Y.SatisfactionProgram

/-! 抽取非空程序末节点的真值，得到实际满意度集合及有界验证公式。 -/
namespace KP1Y.Satisfaction
open YesMetaZFC YesMetaZFC.SetTheory YesMetaZFC.SetTheory.Definitional
open KP1Y.Kuratowski KP1Y.Functions KP1Y.Bounded
universe u

def FinalTrue (M : SetTheory.Structure.{u}) (C : Context M.Domain) (H c : M.Domain) : Prop :=
  ∃ p, M.mem p C.programs ∧ ∃ s, M.mem s C.assignments ∧ Codes M c p s ∧
    ∃ i, M.mem i C.omega ∧ ∃ m, M.mem m C.omega ∧
      M.SuccessorOf m i ∧ Graph M p m C.instructions ∧ MemPair M H i c

def finalTrueFormula {n : Nat} (C : Context (Project.Term n)) (H c : Project.Term n) : Project.Formula 1 n :=
  Project.Formula.existsMem C.programs (Project.Formula.existsMem C.assignments.weaken
    (.conj (codeFormula c.weaken.weaken (.bound 1) (.bound 0))
      (Project.Formula.existsMem C.omega.weaken.weaken (Project.Formula.existsMem C.omega.weaken.weaken.weaken
        (.conj (successorFormula (.bound 0) (.bound 1))
          (.conj (graphFormula (.bound 3) (.bound 0) C.instructions.weaken.weaken.weaken.weaken)
            (memPairFormula H.weaken.weaken.weaken.weaken (.bound 1) c.weaken.weaken.weaken.weaken)))))))

theorem finalTrueFormula_delta0 {n : Nat} (C : Context (Project.Term n)) (H c : Project.Term n) :
    (finalTrueFormula C H c).IsDelta0 :=
  .existsMem _ (.existsMem _ (.conj (codeFormula_delta0 _ _ _)
    (.existsMem _ (.existsMem _ (.conj (successorFormula_delta0 _ _)
      (.conj (graphFormula_delta0 _ _ _) (memPairFormula_delta0 _ _ _)))))))

theorem finalTrueFormula_iff {M : SetTheory.Structure.{u}} (he : Extensional M) {n : Nat}
    (env : Env M n) (C : Context (Project.Term n)) (H c : Project.Term n) :
    Project.Formula.satisfies env (finalTrueFormula C H c) ↔
      FinalTrue M (C.eval env) (H.eval env) (c.eval env) := by
  simp only [finalTrueFormula, Project.Formula.satisfies_existsMem_iff,
    Project.Formula.satisfies_conj_iff, codeFormula_iff he, successorFormula_iff he,
    graphFormula_iff he, memPairFormula_iff he, Definitional.Term.eval_weaken]
  rfl

def TruthSet (M : SetTheory.Structure.{u}) (C : Context M.Domain) (H Sat : M.Domain) : Prop :=
  ∀ c, M.mem c Sat ↔ M.mem c C.columns ∧ FinalTrue M C H c

def truthFormula {n : Nat} (C : Context (Project.Term n)) (H Sat : Project.Term n) : Project.Formula 1 n :=
  .conj (Project.Formula.subset Sat C.columns)
    (Project.Formula.forallMem C.columns (.iff (.mem (.bound 0) Sat.weaken)
      (finalTrueFormula C.weaken H.weaken (.bound 0))))

theorem truthFormula_delta0 {n : Nat} (C : Context (Project.Term n)) (H Sat : Project.Term n) :
    (truthFormula C H Sat).IsDelta0 :=
  .conj (.atom _ _ _) (.forallMem _ (.iff (.mem _ _) (finalTrueFormula_delta0 _ _ _)))

theorem truthFormula_iff {M : SetTheory.Structure.{u}} (he : Extensional M) {n : Nat}
    (env : Env M n) (C : Context (Project.Term n)) (H Sat : Project.Term n) :
    Project.Formula.satisfies env (truthFormula C H Sat) ↔
      TruthSet M (C.eval env) (H.eval env) (Sat.eval env) := by
  simp only [truthFormula, Project.Formula.satisfies_conj_iff, Project.Formula.satisfies_subset_iff,
    Project.Formula.satisfies_forallMem_iff, Project.Formula.satisfies_iff_iff,
    Project.Formula.satisfies_mem_iff, finalTrueFormula_iff he,
    Context.eval_weaken, Definitional.Term.eval_weaken]
  constructor
  · rintro ⟨hSub,hRows⟩ c
    exact ⟨fun hc => ⟨hSub c hc,(hRows c (hSub c hc)).mp hc⟩,
      fun hc => (hRows c hc.1).mpr hc.2⟩
  · intro h
    exact ⟨fun c hc => ((h c).mp hc).1,
      fun c hc => ⟨fun hSat => ((h c).mp hSat).2,fun hTrue => (h c).mpr ⟨hc,hTrue⟩⟩⟩

private def truthParameters : Context (Project.Term 15) :=
  ⟨.bound 2,.bound 3,.bound 4,.bound 5,.bound 6,.bound 7,.bound 8,
    .bound 9,.bound 10,.bound 11,.bound 12,.bound 13,.bound 14⟩

private def truthSchema : Project.Delta0UnarySchema 14 where
  body := finalTrueFormula truthParameters (.bound 1) (.bound 0)
  freeClosed := by
    simp [finalTrueFormula, truthParameters, graphFormula, successorFormula,
      memPairFormula, codeFormula, pairFormula, Project.Formula.existsMem,
      Project.Formula.forallMem, Definitional.Formula.FreeClosed]
  delta0 := finalTrueFormula_delta0 _ _ _

private theorem truthSchema_iff {M : SetTheory.Structure.{u}} (he : Extensional M)
    (C : Context M.Domain) (H c : M.Domain) :
    Project.Formula.satisfies (((contextEnv C).push H).push c) truthSchema.body ↔ FinalTrue M C H c := by
  simp only [truthSchema, finalTrueFormula_iff he]
  rfl

theorem truth_set_exists_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    (C : Context M.Domain) (H : M.Domain) : ∃ Sat, TruthSet M C H Sat := by
  obtain ⟨Sat,hSat⟩ := SetTheory.KP.separation_exists_d (KP1Y.models_weakKP hM)
    truthSchema ((contextEnv C).push H) C.columns
  refine ⟨Sat,fun c => ?_⟩
  simpa only [truthSchema_iff hM.1] using hSat c

theorem truth_at_last {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : Context M.Domain} (hC : ContextSpaces M C) {H Sat p s i m c : M.Domain}
    (hSat : TruthSet M C H Sat) (hP : Graph M p m C.instructions) (hs : M.mem s C.assignments)
    (hi : M.mem i C.omega) (hm : M.mem m C.omega) (hSucc : M.SuccessorOf m i)
    (hCode : Codes M c p s) : M.mem c Sat ↔ MemPair M H i c := by
  constructor
  · intro hc
    obtain ⟨_,p',_,s',_,hCode',j,_,n,_,hSucc',hP',hTrue⟩ := (hSat c).mp hc
    obtain ⟨hpp',hss'⟩ := codes_injective hM.1 hCode hCode'
    subst p'
    subst s'
    have hnm := KP1Y.Assignments.domain_unique hM.1 hP' hP
    subst n
    have hij := Structure.SuccessorOf.predecessor_eq hM.1
      ((KP1Y.Naturals.omega_isOrdinal_d hM hC.omega).mem hi) hSucc hSucc'
    subst j
    exact hTrue
  · intro hTrue
    have hp := (hC.programs p).mpr ⟨m,hm,hP⟩
    exact (hSat c).mpr ⟨(hC.columns c).mpr ⟨p,hp,s,hs,hCode⟩,
      p,hp,s,hs,hCode,i,hi,m,hm,hSucc,hP,hTrue⟩

theorem relational_truth_exists_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {ω : M.Domain} (hω : M.IsOmega ω) (A symbols arity interpretation : M.Domain) :
    ∃ variables values codes Atom C H Sat,
      let D : RelationalData M.Domain := ⟨ω,A,symbols,arity,interpretation,variables,values,codes⟩
      DataSpaces M D ∧ AtomicTable M D Atom ∧ RelationalContext M D Atom C ∧
        ContextSpaces M C ∧ Evaluation M C H ∧ TruthSet M C H Sat := by
  obtain ⟨variables,values,codes,Atom,C,H,hD,hAtom,hRel,hC,hH⟩ :=
    relational_evaluation_exists_d hM hω A symbols arity interpretation
  obtain ⟨Sat,hSat⟩ := truth_set_exists_d hM C H
  exact ⟨variables,values,codes,Atom,C,H,Sat,hD,hAtom,hRel,hC,hH,hSat⟩

end KP1Y.Satisfaction
