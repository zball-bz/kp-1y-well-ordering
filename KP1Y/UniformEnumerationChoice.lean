import KP1Y.SurjectionFamily

/-! 将正初段满射选择图展平为 e:(κ×ω)→κ；候选良序仍为明确前提。 -/
namespace KP1Y.Cardinal
open YesMetaZFC YesMetaZFC.SetTheory YesMetaZFC.SetTheory.Definitional
open KP1Y.Kuratowski KP1Y.Functions KP1Y.Bounded KP1Y.Closure
universe u

def EnumerationPoint (M : SetTheory.Structure.{u}) (ω κ W F zero key x : M.Domain) : Prop :=
  ∃ a, M.mem a κ ∧ ∃ n, M.mem n ω ∧ Codes M key a n ∧
    (((∀ z, ¬M.mem z a) ∧ x=zero) ∨ ∃ f, M.mem f W ∧ MemPair M F a f ∧ MemPair M f n x)

private def enumerationPointSchema : Project.Delta0BinarySchema 5 where
  body := Project.Formula.existsMem (.bound 5) (Project.Formula.existsMem (.bound 7)
    (.conj (codeFormula (.bound 3) (.bound 1) (.bound 0))
      (.disj (.conj (emptyFormula (.bound 1)) (Project.Formula.extensionalEq (.bound 2) (.bound 4)))
        (Project.Formula.existsMem (.bound 6) (.conj (memPairFormula (.bound 6) (.bound 2) (.bound 0))
          (memPairFormula (.bound 0) (.bound 1) (.bound 3)))))))
  freeClosed := by
    simp [emptyFormula, memPairFormula, codeFormula, pairFormula, Project.Formula.existsMem,
      Project.Formula.forallMem, Definitional.Formula.FreeClosed]
  delta0 := .existsMem _ (.existsMem _ (.conj (codeFormula_delta0 _ _ _)
    (.disj (.conj (emptyFormula_delta0 _) (.atom _ _ _))
      (.existsMem _ (.conj (memPairFormula_delta0 _ _ _) (memPairFormula_delta0 _ _ _))))))

private def enumerationEnv {M : SetTheory.Structure.{u}} (ω κ W F zero : M.Domain) : Env M 5 :=
  ((((oneEnv ω).push κ).push W).push F).push zero

private theorem enumerationPointSchema_iff {M : SetTheory.Structure.{u}} (he : Extensional M)
    (ω κ W F zero key x : M.Domain) :
    Project.Formula.satisfies (((enumerationEnv ω κ W F zero).push key).push x) enumerationPointSchema.body ↔
      EnumerationPoint M ω κ W F zero key x := by
  simp only [enumerationPointSchema, Project.Formula.satisfies_existsMem_iff,
    Project.Formula.satisfies_conj_iff, Project.Formula.satisfies_disj_iff,
    Project.Formula.satisfies_extensionalEq_iff_eq he, emptyFormula_iff, codeFormula_iff he, memPairFormula_iff he]
  rfl

theorem uniform_enumeration_from_family_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {ω κ W Pos F zero : M.Domain} (hκ : M.IsOrdinal κ) (hZero : M.mem zero κ)
    (hFamily : SurjectionFamily M ω κ W Pos F) : ∃ Keys e, UniformEnumeration M ω κ Keys e := by
  classical
  obtain ⟨Keys,hKeys⟩ := product_exists hM κ ω
  obtain ⟨e,hSupport,hRaw⟩ := relation_comprehension_d hM enumerationPointSchema (enumerationEnv ω κ W F zero) Keys κ
  have hRows (key x : M.Domain) : MemPair M e key x ↔ M.mem key Keys ∧ M.mem x κ ∧ EnumerationPoint M ω κ W F zero key x := by
    simpa only [enumerationPointSchema_iff hM.1] using hRaw key x
  have hGraph : Graph M e Keys κ := by
    refine ⟨hSupport,?_,?_⟩
    · intro key hKey
      obtain ⟨a,ha,n,hn,hCode⟩ := (hKeys key).mp hKey
      by_cases hPos : ∃ z, M.mem z a
      · obtain ⟨f,hf,hAf⟩ := hFamily.graph.total a ((hFamily.positive a).mpr ⟨ha,hPos⟩)
        obtain ⟨x,hx,hAt⟩ := (hFamily.values a f hAf).2.1 n hn
        have hxκ := hκ.transitive a ha x hx
        exact ⟨x,hxκ,(hRows key x).mpr ⟨hKey,hxκ,a,ha,n,hn,hCode,Or.inr ⟨f,hf,hAf,hAt⟩⟩⟩
      · exact ⟨zero,hZero,(hRows key zero).mpr ⟨hKey,hZero,a,ha,n,hn,hCode,
          Or.inl ⟨fun z hz => hPos ⟨z,hz⟩,rfl⟩⟩⟩
    · intro key x y hX hY
      obtain ⟨_,_,a,_,n,_,hCode,hCase⟩ := (hRows key x).mp hX
      obtain ⟨_,_,a',_,n',_,hCode',hCase'⟩ := (hRows key y).mp hY
      obtain ⟨hAs,hNs⟩ := codes_injective hM.1 hCode hCode'
      subst a'
      subst n'
      rcases hCase with ⟨hEmpty,hx⟩ | ⟨f,_,hAf,hAt⟩
      · rcases hCase' with ⟨_,hy⟩ | ⟨f,_,hAf,_⟩
        · exact hx.trans hy.symm
        · obtain ⟨z,hz⟩ := ((hFamily.positive a).mp (hFamily.graph.bounds hM.1 hAf).1).2
          exact False.elim (hEmpty z hz)
      · rcases hCase' with ⟨hEmpty,_⟩ | ⟨f',_,hAf',hAt'⟩
        · obtain ⟨z,hz⟩ := ((hFamily.positive a).mp (hFamily.graph.bounds hM.1 hAf).1).2
          exact False.elim (hEmpty z hz)
        · have hFs := hFamily.graph.unique a f f' hAf hAf'
          subst f'
          exact ((hFamily.values a f hAf).toGraph hM.1).unique n x y hAt hAt'
  refine ⟨Keys,e,hKeys,hGraph,?_,?_⟩
  · intro a _ hPos n _ key hCode x hAt
    obtain ⟨_,_,a',_,n',_,hCode',hCase⟩ := (hRows key x).mp hAt
    obtain ⟨hAs,hNs⟩ := codes_injective hM.1 hCode hCode'
    subst a'
    subst n'
    rcases hCase with ⟨hEmpty,_⟩ | ⟨f,_,hAf,hfx⟩
    · obtain ⟨z,hz⟩ := hPos
      exact False.elim (hEmpty z hz)
    · exact ((hFamily.values a f hAf).bounds hM.1 hfx).2
  · intro a ha x hx
    obtain ⟨f,hf,hAf⟩ := hFamily.graph.total a ((hFamily.positive a).mpr ⟨ha,x,hx⟩)
    obtain ⟨n,hn,hfx⟩ := (hFamily.values a f hAf).2.2.2 x hx
    obtain ⟨key,hCode⟩ := codes_total hM a n
    have hKey := (hKeys key).mpr ⟨a,ha,n,hn,hCode⟩
    have hxκ := hκ.transitive a ha x hx
    exact ⟨n,hn,key,hKey,hCode,(hRows key x).mpr ⟨hKey,hxκ,a,ha,n,hn,hCode,Or.inr ⟨f,hf,hAf,hfx⟩⟩⟩

theorem uniform_enumeration_from_wellorder_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {ω κ W order zero : M.Domain} (hκ : M.IsOrdinal κ) (hZero : M.mem zero κ)
    (hOrder : KP1Y.InternalWellOrder M order W)
    (hCandidates : ∀ a, M.mem a κ → (∃ x, M.mem x a) → ∃ f, M.mem f W ∧ Onto M f ω a) :
    ∃ Keys e, UniformEnumeration M ω κ Keys e := by
  obtain ⟨Pos,F,hFamily⟩ := surjection_family_from_wellorder_d hM hOrder hCandidates
  exact uniform_enumeration_from_family_d hM hκ hZero hFamily

end KP1Y.Cardinal
