import KP1Y.OneYFiniteComputation

/-! 供山形与矩阵帧共同使用的实际全局截断差表及自然数差值性质。 -/
namespace KP1Y.OneYFinite
open YesMetaZFC YesMetaZFC.SetTheory YesMetaZFC.SetTheory.Definitional
open KP1Y.Kuratowski KP1Y.Functions KP1Y.Naturals KP1Y.Bounded
universe u

private def iteratorFamilySchema : Project.Delta0BinarySchema 2 where
  body := predecessorIteratorFormula (.bound 3) (.bound 2) (.bound 1) (.bound 0)
  freeClosed := predecessorIteratorFormula_freeClosed _ _ _ _ rfl rfl rfl rfl
  delta0 := predecessorIteratorFormula_delta0 _ _ _ _

theorem predecessor_iterator_family_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) :
    ∃ Family Lookup, Graph M Lookup C.omega Family ∧
      ∀ a H, MemPair M Lookup a H → PredecessorIterator M C.omega C.zero a H := by
  let e := (oneEnv C.omega).push C.zero
  have hφ (a H : M.Domain) : Project.Formula.satisfies ((e.push a).push H) iteratorFamilySchema.body ↔
      PredecessorIterator M C.omega C.zero a H := by
    simp only [iteratorFamilySchema,predecessorIteratorFormula_iff hM.1]
    rfl
  obtain ⟨Family,hFamily⟩ := SetTheory.KP.collection_exists_d (KP1Y.models_weakKP hM) iteratorFamilySchema e C.omega (by
    intro a ha
    obtain ⟨H,hH⟩ := predecessor_iterator_exists_d hM hC ha
    exact ⟨H,(hφ a H).mpr hH⟩)
  obtain ⟨Lookup,hSupport,hRaw⟩ := relation_comprehension_d hM iteratorFamilySchema e C.omega Family
  have hRows (a H : M.Domain) : MemPair M Lookup a H ↔
      M.mem a C.omega ∧ M.mem H Family ∧ PredecessorIterator M C.omega C.zero a H := by
    simpa only [hφ] using hRaw a H
  refine ⟨Family,Lookup,⟨hSupport,?_,?_⟩,fun a H hAt => ((hRows a H).mp hAt).2.2⟩
  · intro a ha
    obtain ⟨H,hH,hPred⟩ := hFamily a ha
    exact ⟨H,hH,(hRows a H).mpr ⟨ha,hH,(hφ a H).mp hPred⟩⟩
  · intro a H J hH hJ
    exact predecessor_iterator_unique_d hM hC ((hRows a H).mp hH).2.2 ((hRows a J).mp hJ).2.2

private def differenceTableSchema : Project.Delta0BinarySchema 3 where
  body := Project.Formula.existsMem (.bound 4) (Project.Formula.existsMem (.bound 5)
    (Project.Formula.existsMem (.bound 5) (.conj (codeFormula (.bound 4) (.bound 2) (.bound 1))
      (.conj (memPairFormula (.bound 5) (.bound 2) (.bound 0)) (memPairFormula (.bound 0) (.bound 1) (.bound 3))))))
  freeClosed := by
    simp [codeFormula,pairFormula,memPairFormula,Project.Formula.existsMem,Project.Formula.forallMem,Definitional.Formula.FreeClosed]
  delta0 := .existsMem _ (.existsMem _ (.existsMem _ (.conj (codeFormula_delta0 _ _ _)
    (.conj (memPairFormula_delta0 _ _ _) (memPairFormula_delta0 _ _ _)))))

structure DifferenceTable (M : SetTheory.Structure.{u}) (C : ExpressionData M.Domain) (Pairs D : M.Domain) : Prop where
  pairs : IsProduct M Pairs C.omega C.omega
  graph : Graph M D Pairs C.omega
  rows : ∀ a, M.mem a C.omega → ∀ b, M.mem b C.omega → ∀ key, Codes M key a b →
    ∀ d, MemPair M D key d ↔ TruncatedDifference M C.omega C.zero a b d

theorem difference_table_exists_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) : ∃ Pairs D, DifferenceTable M C Pairs D := by
  obtain ⟨Pairs,hPairs⟩ := product_exists hM C.omega C.omega
  obtain ⟨Family,Lookup,hLookup,hLookupRows⟩ := predecessor_iterator_family_d hM hC
  let e := ((oneEnv C.omega).push Family).push Lookup
  have hφ (key d : M.Domain) : Project.Formula.satisfies ((e.push key).push d) differenceTableSchema.body ↔
      ∃ a, M.mem a C.omega ∧ ∃ b, M.mem b C.omega ∧ ∃ H, M.mem H Family ∧
        Codes M key a b ∧ MemPair M Lookup a H ∧ MemPair M H b d := by
    simp only [differenceTableSchema,Project.Formula.satisfies_existsMem_iff,Project.Formula.satisfies_conj_iff,
      codeFormula_iff hM.1,memPairFormula_iff hM.1]
    rfl
  obtain ⟨D,hSupport,hRaw⟩ := relation_comprehension_d hM differenceTableSchema e Pairs C.omega
  have hRows (key d : M.Domain) : MemPair M D key d ↔ M.mem key Pairs ∧ M.mem d C.omega ∧
      ∃ a, M.mem a C.omega ∧ ∃ b, M.mem b C.omega ∧ ∃ H, M.mem H Family ∧
        Codes M key a b ∧ MemPair M Lookup a H ∧ MemPair M H b d := by
    simpa only [hφ] using hRaw key d
  refine ⟨Pairs,D,hPairs,⟨hSupport,?_,?_⟩,?_⟩
  · intro key hk
    obtain ⟨a,ha,b,hb,hCode⟩ := (hPairs key).mp hk
    obtain ⟨H,hH,hAt⟩ := hLookup.total a ha
    obtain ⟨d,hd,hValue⟩ := (hLookupRows a H hAt).1.total b hb
    exact ⟨d,hd,(hRows key d).mpr ⟨hk,hd,a,ha,b,hb,H,hH,hCode,hAt,hValue⟩⟩
  · intro key d d' hd hd'
    obtain ⟨_,_,a,_,b,_,H,_,hCode,hL,hValue⟩ := (hRows key d).mp hd
    obtain ⟨_,_,a',_,b',_,H',_,hCode',hL',hValue'⟩ := (hRows key d').mp hd'
    obtain ⟨haa,hbb⟩ := codes_injective hM.1 hCode hCode'
    subst a'
    subst b'
    have hHH := hLookup.unique a H' H hL' hL
    subst H'
    exact (hLookupRows a H hL).1.unique b d d' hValue hValue'
  · intro a ha b hb key hCode d
    constructor
    · intro hAt
      obtain ⟨_,_,a',_,b',_,H,_,hCode',hL,hValue⟩ := (hRows key d).mp hAt
      obtain ⟨haa,hbb⟩ := codes_injective hM.1 hCode hCode'
      subst a'
      subst b'
      exact ⟨ha,hb,H,hLookupRows a H hL,hValue⟩
    · rintro ⟨_,_,H,hH,hValue⟩
      obtain ⟨H',hH',hL⟩ := hLookup.total a ha
      have hHH := predecessor_iterator_unique_d hM hC hH (hLookupRows a H' hL)
      subst H'
      exact (hRows key d).mpr ⟨(hPairs key).mpr ⟨a,ha,b,hb,hCode⟩,(hH.1.bounds hM.1 hValue).2,
        a,ha,b,hb,H,hH',hCode,hL,hValue⟩

end KP1Y.OneYFinite
