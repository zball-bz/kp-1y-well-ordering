import KP1Y.WordExtension

/-! word(n+1)=word(first(decode n)) 追加 second(decode n) 的字面 Σ₁ 递归矩阵。 -/
namespace KP1Y.Naturals
open YesMetaZFC YesMetaZFC.SetTheory YesMetaZFC.SetTheory.Definitional
open KP1Y.Kuratowski KP1Y.Functions KP1Y.Bounded
universe u

def WordStep (M : SetTheory.Structure.{u}) (ω Words Pairs decode zero i Pref value w : M.Domain) : Prop :=
  M.mem value Words ∧ Graph M Pref i w ∧
    (((∀ x, ¬M.mem x i) ∧ value=zero) ∨
      ∃ n, M.mem n i ∧ ∃ pair, M.mem pair Pairs ∧ ∃ j, M.mem j i ∧ ∃ a, M.mem a ω ∧
        ∃ old, M.mem old w ∧ M.SuccessorOf i n ∧ MemPair M decode n pair ∧ Codes M pair j a ∧
          MemPair M Pref j old ∧ WordExtension M ω Words zero old a value)

def wordEnv {M : SetTheory.Structure.{u}} (ω Words Pairs decode zero : M.Domain) : Env M 5 where
  bound k := match k.val with | 0 => ω | 1 => Words | 2 => Pairs | 3 => decode | _ => zero
  free _ := ω

def wordMatrix : KP1Y.SigmaRecursion.StepMatrix 5 where
  body := .conj (.mem (.bound 1) (.bound 5)) (.conj (graphFormula (.bound 2) (.bound 3) (.bound 0))
    (.disj (.conj (emptyFormula (.bound 3)) (Project.Formula.extensionalEq (.bound 1) (.bound 8)))
      (Project.Formula.existsMem (.bound 3) (Project.Formula.existsMem (.bound 7)
        (Project.Formula.existsMem (.bound 5) (Project.Formula.existsMem (.bound 7)
          (Project.Formula.existsMem (.bound 4)
            (.conj (successorFormula (.bound 8) (.bound 4))
              (.conj (memPairFormula (.bound 12) (.bound 4) (.bound 3))
                (.conj (codeFormula (.bound 3) (.bound 2) (.bound 1))
                  (.conj (memPairFormula (.bound 7) (.bound 2) (.bound 0))
                    (wordExtensionFormula (.bound 9) (.bound 10) (.bound 13) (.bound 0) (.bound 1) (.bound 6)))))))))))))
  freeClosed := by
    simp [wordExtensionFormula, graphFormula, Sequences.appendFormula, Sequences.insertFormula,
      emptyFormula, successorFormula, memPairFormula, codeFormula, pairFormula,
      Project.Formula.existsMem, Project.Formula.forallMem, Definitional.Formula.FreeClosed]
  delta0 := .conj (.mem _ _) (.conj (graphFormula_delta0 _ _ _)
    (.disj (.conj (emptyFormula_delta0 _) (.atom _ _ _))
      (.existsMem _ (.existsMem _ (.existsMem _ (.existsMem _ (.existsMem _
        (.conj (successorFormula_delta0 _ _) (.conj (memPairFormula_delta0 _ _ _)
          (.conj (codeFormula_delta0 _ _ _) (.conj (memPairFormula_delta0 _ _ _)
            (wordExtensionFormula_delta0 _ _ _ _ _ _))))))))))))

theorem wordMatrix_iff {M : SetTheory.Structure.{u}} (he : Extensional M)
    (ω Words Pairs decode zero i Pref value w : M.Domain) :
    wordMatrix.denote (wordEnv ω Words Pairs decode zero) i Pref value w ↔
      WordStep M ω Words Pairs decode zero i Pref value w := by
  simp only [KP1Y.SigmaRecursion.StepMatrix.denote, wordMatrix, Project.Formula.satisfies_conj_iff,
    Project.Formula.satisfies_disj_iff, Project.Formula.satisfies_existsMem_iff,
    Project.Formula.satisfies_mem_iff, Project.Formula.satisfies_extensionalEq_iff_eq he,
    graphFormula_iff he, emptyFormula_iff, successorFormula_iff he, memPairFormula_iff he,
    codeFormula_iff he, wordExtensionFormula_iff he]
  rfl

theorem wordMatrix_total_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {ω Words Pairs decode zero : M.Domain} (hω : M.IsOmega ω) (hDecode : NaturalPairing M ω Pairs decode)
    (hWords : ∀ w, M.mem w Words ↔ ∃ n, M.mem n ω ∧ Graph M w n ω) (hZeroWord : M.mem zero Words) :
    KP1Y.SigmaRecursion.Total M ω (wordMatrix.denote (wordEnv ω Words Pairs decode zero)) := by
  intro i hi Pref V hPref
  rcases natural_cases hM hω hi with hEmpty | ⟨n,hn,hSucc⟩
  · exact ⟨zero,V,(wordMatrix_iff hM.1 ω Words Pairs decode zero i Pref zero V).mpr ⟨hZeroWord,hPref,Or.inl ⟨hEmpty,rfl⟩⟩⟩
  · obtain ⟨pair,hPair,hAt⟩ := hDecode.graph.total n hn
    obtain ⟨j,hj,a,ha,hCode⟩ := (hDecode.product pair).mp hPair
    have hji := hDecode.decode_before hM hω hn hSucc hAt hCode
    obtain ⟨old,hOld,hOldAt⟩ := hPref.total j hji
    obtain ⟨value,hValue,hExt⟩ := word_extension_total_d hM hω hWords hZeroWord ha
    exact ⟨value,V,(wordMatrix_iff hM.1 ω Words Pairs decode zero i Pref value V).mpr
      ⟨hValue,hPref,Or.inr ⟨n,hSucc.predecessor_mem,pair,hPair,j,hji,a,ha,old,hOld,hSucc,hAt,hCode,hOldAt,hExt⟩⟩⟩

theorem wordMatrix_functional_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {ω Words Pairs decode zero : M.Domain} (hω : M.IsOmega ω) (hDecode : NaturalPairing M ω Pairs decode) :
    KP1Y.SigmaRecursion.Functional M ω (wordMatrix.denote (wordEnv ω Words Pairs decode zero)) := by
  intro i hi Pref value value' w w' h h'
  obtain ⟨_,hPref,hCases⟩ := (wordMatrix_iff hM.1 ω Words Pairs decode zero i Pref value w).mp h
  obtain ⟨_,_,hCases'⟩ := (wordMatrix_iff hM.1 ω Words Pairs decode zero i Pref value' w').mp h'
  rcases hCases with ⟨hEmpty,hValue⟩ | ⟨n,hn,pair,_,j,_,a,_,old,_,hSucc,hAt,hCode,hOld,hExt⟩
  · rcases hCases' with ⟨_,hValue'⟩ | ⟨n,hn,_⟩
    · exact hValue.trans hValue'.symm
    · exact False.elim (hEmpty n hn)
  · rcases hCases' with ⟨hEmpty,_⟩ | ⟨n',_,pair',_,j',_,a',_,old',_,hSucc',hAt',hCode',hOld',hExt'⟩
    · exact False.elim (hEmpty n hn)
    · have hnn' := Structure.SuccessorOf.predecessor_eq hM.1 (((omega_isOrdinal_d hM hω).mem hi).mem hn) hSucc hSucc'
      subst n'
      have hPairs := hDecode.graph.unique n pair pair' hAt hAt'
      subst pair'
      obtain ⟨hjj',haa'⟩ := codes_injective hM.1 hCode hCode'
      subst j'
      subst a'
      have hOldEq := hPref.unique j old old' hOld hOld'
      subst old'
      exact word_extension_unique hM.1 hExt hExt'

end KP1Y.Naturals
