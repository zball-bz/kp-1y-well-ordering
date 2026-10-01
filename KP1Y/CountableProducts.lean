import KP1Y.CountableFunctions

/-! 从两个实际 ω 满射构造积的实际 ω 满射，不调用宿主可数性。 -/
namespace KP1Y.Cardinal
open YesMetaZFC YesMetaZFC.SetTheory YesMetaZFC.SetTheory.Definitional
open KP1Y.Kuratowski KP1Y.Functions
universe u

private def productLiftSchema : Project.Delta0BinarySchema 5 where
  body := Project.Formula.existsMem (.bound 2) (Project.Formula.existsMem (.bound 3)
    (.conj (codeFormula (.bound 3) (.bound 1) (.bound 0))
      (Project.Formula.existsMem (.bound 5) (Project.Formula.existsMem (.bound 7)
        (.conj (memPairFormula (.bound 9) (.bound 3) (.bound 1))
          (.conj (memPairFormula (.bound 10) (.bound 2) (.bound 0))
            (codeFormula (.bound 4) (.bound 1) (.bound 0))))))))
  freeClosed := by
    simp [memPairFormula, codeFormula, pairFormula, Project.Formula.existsMem,
      Project.Formula.forallMem, Definitional.Formula.FreeClosed]
  delta0 := .existsMem _ (.existsMem _ (.conj (codeFormula_delta0 _ _ _)
    (.existsMem _ (.existsMem _ (.conj (memPairFormula_delta0 _ _ _)
      (.conj (memPairFormula_delta0 _ _ _) (codeFormula_delta0 _ _ _)))))))

private def productLiftEnv {M : SetTheory.Structure.{u}} (ω X Y f g : M.Domain) : Env M 5 where
  bound k := match k.val with | 0 => ω | 1 => X | 2 => Y | 3 => f | _ => g
  free _ := ω

private theorem productLiftSchema_iff {M : SetTheory.Structure.{u}} (he : Extensional M) (ω X Y f g q p : M.Domain) :
    Project.Formula.satisfies (((productLiftEnv ω X Y f g).push q).push p) productLiftSchema.body ↔
      ∃ i, M.mem i ω ∧ ∃ j, M.mem j ω ∧ Codes M q i j ∧
        ∃ x, M.mem x X ∧ ∃ y, M.mem y Y ∧ MemPair M f i x ∧ MemPair M g j y ∧ Codes M p x y := by
  simp only [productLiftSchema, Project.Formula.satisfies_existsMem_iff,
    Project.Formula.satisfies_conj_iff, codeFormula_iff he, memPairFormula_iff he]
  rfl

theorem product_surjection_lift_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {ω X Y f g NP XY : M.Domain} (hf : Onto M f ω X) (hg : Onto M g ω Y)
    (hNP : IsProduct M NP ω ω) (hXY : IsProduct M XY X Y) : ∃ lift, Onto M lift NP XY := by
  obtain ⟨lift,hSupport,hRaw⟩ := relation_comprehension_d hM productLiftSchema (productLiftEnv ω X Y f g) NP XY
  have hRows (q p : M.Domain) : MemPair M lift q p ↔ M.mem q NP ∧ M.mem p XY ∧
      ∃ i, M.mem i ω ∧ ∃ j, M.mem j ω ∧ Codes M q i j ∧
        ∃ x, M.mem x X ∧ ∃ y, M.mem y Y ∧ MemPair M f i x ∧ MemPair M g j y ∧ Codes M p x y := by
    simpa only [productLiftSchema_iff hM.1] using hRaw q p
  refine ⟨lift,hSupport,?_,?_,?_⟩
  · intro q hq
    obtain ⟨i,hi,j,hj,hQ⟩ := (hNP q).mp hq
    obtain ⟨x,hx,hFx⟩ := hf.2.1 i hi
    obtain ⟨y,hy,hGy⟩ := hg.2.1 j hj
    obtain ⟨p,hP⟩ := codes_total hM x y
    have hp := (hXY p).mpr ⟨x,hx,y,hy,hP⟩
    exact ⟨p,hp,(hRows q p).mpr ⟨hq,hp,i,hi,j,hj,hQ,x,hx,y,hy,hFx,hGy,hP⟩⟩
  · intro q _ p _ p' _ hqp hqp'
    obtain ⟨_,_,i,_,j,_,hQ,x,_,y,_,hFx,hGy,hP⟩ := (hRows q p).mp hqp
    obtain ⟨_,_,i',_,j',_,hQ',x',_,y',_,hFx',hGy',hP'⟩ := (hRows q p').mp hqp'
    obtain ⟨hii',hjj'⟩ := codes_injective hM.1 hQ hQ'
    subst i'
    subst j'
    have hxx' := (hf.toGraph hM.1).unique i x x' hFx hFx'
    have hyy' := (hg.toGraph hM.1).unique j y y' hGy hGy'
    subst x'
    subst y'
    exact codes_unique hM.1 hP hP'
  · intro p hp
    obtain ⟨x,hx,y,hy,hP⟩ := (hXY p).mp hp
    obtain ⟨i,hi,hFx⟩ := hf.2.2.2 x hx
    obtain ⟨j,hj,hGy⟩ := hg.2.2.2 y hy
    obtain ⟨q,hQ⟩ := codes_total hM i j
    have hq := (hNP q).mpr ⟨i,hi,j,hj,hQ⟩
    exact ⟨q,hq,(hRows q p).mpr ⟨hq,hp,i,hi,j,hj,hQ,x,hx,y,hy,hFx,hGy,hP⟩⟩

theorem countable_product_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {ω X Y f g : M.Domain} (hω : M.IsOmega ω) (hf : Onto M f ω X) (hg : Onto M g ω Y) :
    ∃ P E, IsProduct M P X Y ∧ Onto M E ω P := by
  obtain ⟨NP,decode,hDecode⟩ := KP1Y.Naturals.natural_pairing_exists_d hM hω
  obtain ⟨P,hP⟩ := product_exists hM X Y
  obtain ⟨lift,hLift⟩ := product_surjection_lift_d hM hf hg hDecode.product hP
  obtain ⟨E,hE⟩ := onto_compose_d hM hDecode.onto hLift
  exact ⟨P,E,hP,hE⟩

end KP1Y.Cardinal
