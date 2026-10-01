import KP1Y.ReflectionBinaryBlockTruth
import KP1Y.ReflectionTemplateShape
import KP1Y.ReflectionNameFrame

/-! 逐列前缀等式代码：cut以前比较f/g，之后使用g=g恒真原子。 -/
namespace KP1Y.ReflectionModel
open YesMetaZFC YesMetaZFC.SetTheory YesMetaZFC.SetTheory.Definitional
open KP1Y.Kuratowski KP1Y.Functions KP1Y.Assignments KP1Y.Satisfaction
universe u

private def selectSchema : Project.Delta0BinarySchema 3 where
  body := .disj (.conj (.mem (.bound 1) (.bound 2)) (memPairFormula (.bound 3) (.bound 1) (.bound 0)))
    (.conj (.neg (.mem (.bound 1) (.bound 2))) (memPairFormula (.bound 4) (.bound 1) (.bound 0)))
  freeClosed := by
    simp [memPairFormula,codeFormula,pairFormula,Project.Formula.existsMem,Project.Formula.forallMem,Definitional.Formula.FreeClosed]
  delta0 := .disj (.conj (.mem _ _) (memPairFormula_delta0 _ _ _)) (.conj (.neg (.mem _ _)) (memPairFormula_delta0 _ _ _))

theorem select_name_graph_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory) {X Y n scope : M.Domain}
    (hX : Graph M X n scope) (hY : Graph M Y n scope) (cut : M.Domain) :
    ∃ Z, Graph M Z n scope ∧ ∀ i v, MemPair M Z i v ↔ (M.mem i cut ∧ MemPair M X i v) ∨ (¬M.mem i cut ∧ MemPair M Y i v) := by
  have hφ (i v : M.Domain) : Project.Formula.satisfies (((((oneEnv Y).push X).push cut).push i).push v) selectSchema.body ↔
      (M.mem i cut ∧ MemPair M X i v) ∨ (¬M.mem i cut ∧ MemPair M Y i v) := by
    simp only [selectSchema,Project.Formula.satisfies_disj_iff,Project.Formula.satisfies_conj_iff,
      Project.Formula.satisfies_mem_iff,Project.Formula.satisfies_neg_iff,memPairFormula_iff hM.1]
    rfl
  obtain ⟨Z,hSupport,hRaw⟩ := relation_comprehension_d hM selectSchema (((oneEnv Y).push X).push cut) n scope
  have hRows (i v : M.Domain) : MemPair M Z i v ↔ (M.mem i cut ∧ MemPair M X i v) ∨ (¬M.mem i cut ∧ MemPair M Y i v) := by
    have h := hRaw i v
    rw [hφ] at h
    refine h.trans ⟨fun h => h.2.2,?_⟩
    intro hCases
    rcases hCases with ⟨hi,hAt⟩ | ⟨hi,hAt⟩
    · exact ⟨(hX.bounds hM.1 hAt).1,(hX.bounds hM.1 hAt).2,Or.inl ⟨hi,hAt⟩⟩
    · exact ⟨(hY.bounds hM.1 hAt).1,(hY.bounds hM.1 hAt).2,Or.inr ⟨hi,hAt⟩⟩
  refine ⟨Z,⟨hSupport,?_,?_⟩,hRows⟩
  · intro i hi
    classical
    by_cases hc : M.mem i cut
    · obtain ⟨v,hv,hAt⟩ := hX.total i hi
      exact ⟨v,hv,(hRows i v).mpr (Or.inl ⟨hc,hAt⟩)⟩
    · obtain ⟨v,hv,hAt⟩ := hY.total i hi
      exact ⟨v,hv,(hRows i v).mpr (Or.inr ⟨hc,hAt⟩)⟩
  · intro i v w hiv hiw
    rcases (hRows i v).mp hiv with ⟨hi,hv⟩ | ⟨hi,hv⟩ <;> rcases (hRows i w).mp hiw with ⟨hi',hw⟩ | ⟨hi',hw⟩
    · exact hX.unique i v w hv hw
    · exact False.elim (hi' hi)
    · exact False.elim (hi hi')
    · exact hY.unique i v w hv hw

def PrefixValues (M : SetTheory.Structure.{u}) (f g cut A : M.Domain) : Prop :=
  ∀ i, M.mem i cut → ∀ x, M.mem x A → (MemPair M f i x ↔ MemPair M g i x)

theorem prefix_selector_iff {M : SetTheory.Structure.{u}} {inputs outputs Z n scope cut A s f g : M.Domain}
    (hI : Graph M inputs n scope) (hO : Graph M outputs n scope) (hSub : M.MemberSubset cut n)
    (hZ : ∀ i v, MemPair M Z i v ↔ (M.mem i cut ∧ MemPair M inputs i v) ∨ (¬M.mem i cut ∧ MemPair M outputs i v))
    (hF : TupleValue M f inputs s n scope A) (hG : TupleValue M g outputs s n scope A) :
    CompareSelectors false M outputs Z n scope A s ↔ PrefixValues M f g cut A := by
  constructor
  · intro hCmp i hi x hx
    have hin := hSub i hi
    obtain ⟨u,hu,hOu⟩ := hO.total i hin
    obtain ⟨v,hv,hIv⟩ := hI.total i hin
    have hZv := (hZ i v).mpr (Or.inl ⟨hi,hIv⟩)
    obtain ⟨y,hy,hsy⟩ := hG.source.total u hu
    obtain ⟨z,hz,hsz⟩ := hF.source.total v hv
    have hyz := hCmp i hin u hu v hv hOu hZv y hy z hz hsy hsz
    subst z
    have hfy := (hF.rows i hin v hv y hy hIv).mpr hsz
    have hgy := (hG.rows i hin u hu y hy hOu).mpr hsy
    constructor
    · intro hfx
      exact (hF.values.unique i y x hfy hfx) ▸ hgy
    · intro hgx
      exact (hG.values.unique i y x hgy hgx) ▸ hfy
  · intro hPrefix i hi u hu v hv hOu hZv x hx y hy hsx hsy
    rcases (hZ i v).mp hZv with ⟨hic,hIv⟩ | ⟨_,hOv⟩
    · have hgx := (hG.rows i hi u hu x hx hOu).mpr hsx
      have hfy := (hF.rows i hi v hv y hy hIv).mpr hsy
      exact hG.values.unique i x y hgx ((hPrefix i hic y hy).mp hfy)
    · have huv := hO.unique i u v hOu hOv
      subst v
      exact hG.source.unique u x y hsx hsy

theorem prefix_block_exists_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory) {C : ArticleData M.Domain} (hC : C.Valid M)
    {A : M.Domain} {D : RelationalData M.Domain} (hD : ArticleInterpretation M C A D) {T : TemplateShape M.Domain}
    {F : M.Domain} {V : NameFrame M.Domain} (hV : V.Valid M C F T.width T.edgeLength T.needLength) :
    ∃ Z B, BinaryBlock M C D false V.scope T.width V.outputs Z B ∧
      ∀ i v, MemPair M Z i v ↔ (M.mem i T.cut ∧ MemPair M V.inputs i v) ∨ (¬M.mem i T.cut ∧ MemPair M V.outputs i v) := by
  obtain ⟨Z,hZ,hRows⟩ := select_name_graph_d hM hV.inputs.graph hV.outputs.graph T.cut
  have hb : M.mem V.scope D.omega := Eq.mpr (congrArg (M.mem V.scope) hD.omega) hV.scope
  obtain ⟨B,hB⟩ := binary_block_exists_d hM hC hD false hb hV.outputs.graph hZ
  exact ⟨Z,B,hB,hRows⟩

theorem prefix_values_enlarge {M : SetTheory.Structure.{u}} (he : Extensional M) {f g n cut A B : M.Domain}
    (hF : Graph M f n A) (hG : Graph M g n A) (h : PrefixValues M f g cut A) : PrefixValues M f g cut B := by
  intro i hi x _
  classical
  by_cases hx : M.mem x A
  · exact h i hi x hx
  · exact iff_of_false (fun hAt => hx (hF.bounds he hAt).2) (fun hAt => hx (hG.bounds he hAt).2)

end KP1Y.ReflectionModel
