import KP1Y.ReflectionShapeEntries
import KP1Y.ReflectionRow

/-! 从实际有限边表/模板抽取层号函数，供反例公式的自然数参数赋值。 -/
namespace KP1Y.ReflectionModel
open YesMetaZFC YesMetaZFC.SetTheory YesMetaZFC.SetTheory.Definitional
open KP1Y.Kuratowski KP1Y.Functions KP1Y.Reflection
universe u

private theorem data_closed : dataTerms.Closed := by constructor <;> rfl

private def edgeLayerSchema : Project.Delta0BinarySchema 14 where
  body := Project.Formula.existsMem (.bound 3) (Project.Formula.existsMem (.bound 4) (Project.Formula.existsMem (.bound 5)
    (edgeEntryFormula dataTerms.weaken.weaken.weaken.weaken.weaken.weaken (.bound 5) (.bound 4) (.bound 3) (.bound 2) (.bound 1) (.bound 0))))
  freeClosed := by
    have hEntry := edgeEntryFormula_freeClosed data_closed.weaken.weaken.weaken.weaken.weaken.weaken
      (.bound 5) (.bound 4) (.bound 3) (.bound 2) (.bound 1) (.bound 0) rfl rfl rfl rfl rfl rfl
    simp [Project.Formula.existsMem,Definitional.Formula.FreeClosed,hEntry]
  delta0 := .existsMem _ (.existsMem _ (.existsMem _ (edgeEntryFormula_delta0 _ _ _ _ _ _ _)))

private def needLayerSchema : Project.Delta0BinarySchema 14 where
  body := Project.Formula.existsMem (.bound 3) (Project.Formula.existsMem (.bound 4)
    (needEntryFormula dataTerms.weaken.weaken.weaken.weaken.weaken (.bound 4) (.bound 3) (.bound 2) (.bound 1) (.bound 0)))
  freeClosed := by
    have hEntry := needEntryFormula_freeClosed data_closed.weaken.weaken.weaken.weaken.weaken
      (.bound 4) (.bound 3) (.bound 2) (.bound 1) (.bound 0) rfl rfl rfl rfl rfl
    simp [Project.Formula.existsMem,Definitional.Formula.FreeClosed,hEntry]
  delta0 := .existsMem _ (.existsMem _ (needEntryFormula_delta0 _ _ _ _ _ _))

theorem edge_layers_exists_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory) {C : Data M.Domain} (hC : C.Valid M)
    {A n : M.Domain} (hn : M.mem n C.omega) (hA : Graph M A n C.edgeCodes) :
    ∃ L, Graph M L n C.omega ∧ ∀ i k q p j, EdgeEntry M C A i k q p j → MemPair M L i k := by
  have hφ (i k : M.Domain) : Project.Formula.satisfies ((((dataEnv C).push A).push i).push k) edgeLayerSchema.body ↔
      ∃ q, M.mem q C.omega ∧ ∃ p, M.mem p C.omega ∧ ∃ j, M.mem j C.omega ∧ EdgeEntry M C A i k q p j := by
    simp only [edgeLayerSchema,Project.Formula.satisfies_existsMem_iff,edgeEntryFormula_iff hM.1,Data.eval_weaken,dataTerms_dataEnv]
    rfl
  obtain ⟨L,hSupport,hRaw⟩ := relation_comprehension_d hM edgeLayerSchema ((dataEnv C).push A) n C.omega
  have hRows (i k : M.Domain) : MemPair M L i k ↔ M.mem i n ∧ M.mem k C.omega ∧
      ∃ q, M.mem q C.omega ∧ ∃ p, M.mem p C.omega ∧ ∃ j, M.mem j C.omega ∧ EdgeEntry M C A i k q p j := by
    simpa only [hφ] using hRaw i k
  have hGraph : Graph M L n C.omega := by
    refine ⟨hSupport,?_,?_⟩
    · intro i hi
      obtain ⟨k,q,p,j,hEntry⟩ := edge_entry_exists hC hA hi
      have hiω := (KP1Y.Naturals.omega_isOrdinal_d hM hC.omega).transitive n hn i hi
      obtain ⟨hk,hq,hp,hj⟩ := (hEntry.occurs hiω).bounds hM.1 hC
      exact ⟨k,hk,(hRows i k).mpr ⟨hi,hk,q,hq,p,hp,j,hj,hEntry⟩⟩
    · intro i k k' hAt hAt'
      obtain ⟨_,_,q,_,p,_,j,_,hEntry⟩ := (hRows i k).mp hAt
      obtain ⟨_,_,q',_,p',_,j',_,hEntry'⟩ := (hRows i k').mp hAt'
      exact (hEntry.unique hM.1 hA hEntry').1
  refine ⟨L,hGraph,?_⟩
  intro i k q p j hEntry
  obtain ⟨e,he,hAt,hQuad⟩ := hEntry
  have hi := (hA.bounds hM.1 hAt).1
  obtain ⟨hk,hq,hp,hj⟩ := hQuad.bounds hM.1 hC.pairs
  exact (hRows i k).mpr ⟨hi,hk,q,hq,p,hp,j,hj,e,he,hAt,hQuad⟩

theorem need_layers_exists_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory) {C : Data M.Domain} (hC : C.Valid M)
    {N n : M.Domain} (hn : M.mem n C.omega) (hN : Graph M N n C.needCodes) :
    ∃ L, Graph M L n C.omega ∧ ∀ i k q p, NeedEntry M C N i k q p → MemPair M L i k := by
  have hφ (i k : M.Domain) : Project.Formula.satisfies ((((dataEnv C).push N).push i).push k) needLayerSchema.body ↔
      ∃ q, M.mem q C.omega ∧ ∃ p, M.mem p C.omega ∧ NeedEntry M C N i k q p := by
    simp only [needLayerSchema,Project.Formula.satisfies_existsMem_iff,needEntryFormula_iff hM.1,Data.eval_weaken,dataTerms_dataEnv]
    rfl
  obtain ⟨L,hSupport,hRaw⟩ := relation_comprehension_d hM needLayerSchema ((dataEnv C).push N) n C.omega
  have hRows (i k : M.Domain) : MemPair M L i k ↔ M.mem i n ∧ M.mem k C.omega ∧
      ∃ q, M.mem q C.omega ∧ ∃ p, M.mem p C.omega ∧ NeedEntry M C N i k q p := by
    simpa only [hφ] using hRaw i k
  have hGraph : Graph M L n C.omega := by
    refine ⟨hSupport,?_,?_⟩
    · intro i hi
      obtain ⟨k,q,p,hEntry⟩ := need_entry_exists hC hN hi
      have hiω := (KP1Y.Naturals.omega_isOrdinal_d hM hC.omega).transitive n hn i hi
      obtain ⟨hk,hq,hp⟩ := (hEntry.occurs hiω).bounds hM.1 hC
      exact ⟨k,hk,(hRows i k).mpr ⟨hi,hk,q,hq,p,hp,hEntry⟩⟩
    · intro i k k' hAt hAt'
      obtain ⟨_,_,q,_,p,_,hEntry⟩ := (hRows i k).mp hAt
      obtain ⟨_,_,q',_,p',_,hEntry'⟩ := (hRows i k').mp hAt'
      exact (hEntry.unique hM.1 hN hEntry').1
  refine ⟨L,hGraph,?_⟩
  intro i k q p hEntry
  have hi : M.mem i n := by
    obtain ⟨_,_,hAt,_⟩ := hEntry
    exact (hN.bounds hM.1 hAt).1
  have hiω := (KP1Y.Naturals.omega_isOrdinal_d hM hC.omega).transitive n hn i hi
  obtain ⟨hk,hq,hp⟩ := (hEntry.occurs hiω).bounds hM.1 hC
  exact (hRows i k).mpr ⟨hi,hk,q,hq,p,hp,hEntry⟩

end KP1Y.ReflectionModel
