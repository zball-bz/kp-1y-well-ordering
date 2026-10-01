import KP1Y.OrdinalIterationExistence

/-! 单个连续Σ₁迭代值的统一集合证书、存在、唯一及历史相容。 -/
namespace KP1Y.OrdinalIteration
open YesMetaZFC YesMetaZFC.SetTheory YesMetaZFC.SetTheory.Definitional
open KP1Y.Kuratowski KP1Y.Functions KP1Y.Bounded
universe u

def ValueCertificate {M : SetTheory.Structure.{u}} {n : Nat} (φ : KP1Y.WitnessMatrix n) (e : Env M (n+1))
    (i T B : M.Domain) : Prop :=
  M.IsOrdinal i ∧ ∃ δ, M.mem δ B ∧ ∃ H, M.mem H B ∧ ∃ C, M.mem C B ∧
    M.SuccessorOf δ i ∧ KP1Y.SigmaRecursion.Certificate M ((iterationMatrix φ).denote e) δ H C ∧ MemPair M H i T

private def valueHistorySlots {n : Nat} : Fin (n+4) → Fin (n+7) :=
  Fin.cases 0 (Fin.cases 1 (Fin.cases 2 (fun i => ⟨i.val+6,by omega⟩)))

def valueMatrix {n : Nat} (φ : KP1Y.WitnessMatrix n) : KP1Y.WitnessMatrix (n+1) where
  body := .conj (ordinalFormula (.bound 2))
    (Project.Formula.existsMem (.bound 0) (Project.Formula.existsMem (.bound 1) (Project.Formula.existsMem (.bound 2)
      (.conj (successorFormula (.bound 2) (.bound 5))
        (.conj ((KP1Y.SigmaRecursion.certificateMatrix (iterationMatrix φ)).body.rename valueHistorySlots)
          (memPairFormula (.bound 1) (.bound 5) (.bound 4)))))))
  freeClosed := by
    simp [ordinalFormula,Project.Formula.isTransitive,successorFormula,memPairFormula,codeFormula,pairFormula,
      Project.Formula.existsMem,Project.Formula.forallMem,Definitional.Formula.FreeClosed,
      (KP1Y.SigmaRecursion.certificateMatrix (iterationMatrix φ)).freeClosed]
  delta0 := .conj (ordinalFormula_delta0 _) (.existsMem _ (.existsMem _ (.existsMem _
    (.conj (successorFormula_delta0 _ _)
      (.conj (KP1Y.delta0_rename (KP1Y.SigmaRecursion.certificateMatrix (iterationMatrix φ)).delta0 _)
        (memPairFormula_delta0 _ _ _))))))

private theorem valueHistorySlots_env {M : SetTheory.Structure.{u}} {n : Nat} (e : Env M (n+1)) (i T B δ H C : M.Domain) :
    ((((((e.push i).push T).push B).push δ).push H).push C).reindex valueHistorySlots = ((e.push δ).push H).push C := by
  rw [Env.mk.injEq]
  constructor
  · funext k
    refine Fin.cases ?_ (fun k => ?_) k
    · rfl
    · refine Fin.cases ?_ (fun k => ?_) k
      · rfl
      · refine Fin.cases ?_ (fun _ => ?_) k <;> rfl
  · rfl

theorem valueMatrix_iff {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory) {n : Nat}
    (φ : KP1Y.WitnessMatrix n) (e : Env M (n+1)) (i T B : M.Domain) :
    Project.Formula.satisfies (((e.push i).push T).push B) (valueMatrix φ).body ↔ ValueCertificate φ e i T B := by
  simp only [valueMatrix,Project.Formula.satisfies_conj_iff,ordinalFormula_iff hM,
    Project.Formula.satisfies_existsMem_iff,successorFormula_iff hM.1,
    Project.Formula.satisfies_rename,valueHistorySlots_env,
    KP1Y.SigmaRecursion.certificateMatrix_iff hM.1,memPairFormula_iff hM.1]
  rfl

def Value {M : SetTheory.Structure.{u}} {n : Nat} (φ : KP1Y.WitnessMatrix n) (e : Env M (n+1)) (i T : M.Domain) : Prop :=
  ∃ B, ValueCertificate φ e i T B

theorem Value.ordinal {M : SetTheory.Structure.{u}} {n : Nat} {φ : KP1Y.WitnessMatrix n} {e : Env M (n+1)}
    {i T : M.Domain} (h : Value φ e i T) : M.IsOrdinal i := by
  obtain ⟨_,hi,_⟩ := h
  exact hi

theorem Value.history {M : SetTheory.Structure.{u}} {n : Nat} {φ : KP1Y.WitnessMatrix n} {e : Env M (n+1)}
    {i T : M.Domain} (h : Value φ e i T) : ∃ δ H V Q, M.SuccessorOf δ i ∧
      KP1Y.SigmaRecursion.ValueHistory M ((iterationMatrix φ).denote e) H δ V Q ∧ MemPair M H i T := by
  obtain ⟨_,_,δ,_,H,_,_,_,hs,hCert,hAt⟩ := h
  obtain ⟨V,_,Q,_,hH⟩ := hCert
  exact ⟨δ,H,V,Q,hs,hH,hAt⟩

theorem value_from_successor_history_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory) {n : Nat}
    {φ : KP1Y.WitnessMatrix n} {e : Env M (n+1)} {i T δ H V Q : M.Domain} (hi : M.IsOrdinal i) (hs : M.SuccessorOf δ i)
    (hH : KP1Y.SigmaRecursion.ValueHistory M ((iterationMatrix φ).denote e) H δ V Q) (hAt : MemPair M H i T) : Value φ e i T := by
  obtain ⟨C,hC⟩ := KP1Y.SigmaRecursion.certificate_exists hM hH
  obtain ⟨B0,hB0⟩ := SetTheory.KP.exists_pair (KP1Y.models_weakKP hM) δ H
  obtain ⟨B,hB⟩ := SetTheory.KP.exists_insert (KP1Y.models_weakKP hM) B0 C
  exact ⟨B,hi,δ,(hB δ).mpr (Or.inl ((hB0 δ).mpr (Or.inl rfl))),
    H,(hB H).mpr (Or.inl ((hB0 H).mpr (Or.inr rfl))),C,(hB C).mpr (Or.inr rfl),hs,hC,hAt⟩

theorem value_from_history_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory) {n : Nat}
    {φ : KP1Y.WitnessMatrix n} {e : Env M (n+1)} {i T Γ H V Q : M.Domain} (hΓ : M.IsOrdinal Γ)
    (hH : KP1Y.SigmaRecursion.ValueHistory M ((iterationMatrix φ).denote e) H Γ V Q) (hiΓ : M.mem i Γ) (hAt : MemPair M H i T) :
    Value φ e i T := by
  have hi := hΓ.mem hiΓ
  obtain ⟨δ,hs⟩ := SetTheory.KP.exists_successor (KP1Y.models_weakKP hM) i
  have hδ := SetTheory.KP.successor_isOrdinal (KP1Y.models_weakKP hM) hi hs
  have hSub : M.MemberSubset δ Γ := by
    intro x hx
    rcases (hs x).mp hx with hx | hSame
    · exact hΓ.transitive i hiΓ x hx
    · exact (hM.1.eq_of_same_members x i hSame) ▸ hiΓ
  obtain ⟨J,R,hJ,hRows⟩ := KP1Y.SigmaRecursion.history_prefix_d hM hδ hSub hH
  exact value_from_successor_history_d hM hi hs hJ ((hRows i T).mpr ⟨hs.predecessor_mem,hAt⟩)

theorem value_exists_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory) {n : Nat}
    (φ : KP1Y.WitnessMatrix n) (e : Env M (n+1)) (hTotal : Total φ (tailEnv e)) (hFun : Functional φ (tailEnv e))
    {i : M.Domain} (hi : M.IsOrdinal i) : ∃ T, Value φ e i T := by
  obtain ⟨δ,hs⟩ := SetTheory.KP.exists_successor (KP1Y.models_weakKP hM) i
  have hδ := SetTheory.KP.successor_isOrdinal (KP1Y.models_weakKP hM) hi hs
  obtain ⟨H,V,Q,hH⟩ := iteration_history_exists_d hM φ e hTotal hFun hδ
  obtain ⟨T,_,hAt⟩ := hH.values.total i hs.predecessor_mem
  exact ⟨T,value_from_successor_history_d hM hi hs hH hAt⟩

theorem value_unique_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory) {n : Nat}
    (φ : KP1Y.WitnessMatrix n) (e : Env M (n+1)) (hFun : Functional φ (tailEnv e))
    {i T T' : M.Domain} (h : Value φ e i T) (h' : Value φ e i T') : T=T' := by
  obtain ⟨δ,H,V,Q,hs,hH,hAt⟩ := h.history
  obtain ⟨δ',H',V',Q',hs',hH',hAt'⟩ := h'.history
  have hδδ' := hM.1.eq_of_same_members δ δ' (fun x => (hs x).trans (hs' x).symm)
  subst δ'
  have hδ := SetTheory.KP.successor_isOrdinal (KP1Y.models_weakKP hM) h.ordinal hs
  have hEq := KP1Y.SigmaRecursion.history_unique hM hδ (fun _ hx => hx) (iteration_functional_d hM φ e hFun hδ) hH hH'
  subst H'
  exact hH.values.unique i T T' hAt hAt'

end KP1Y.OrdinalIteration
