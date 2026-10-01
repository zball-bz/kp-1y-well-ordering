import KP1Y.SquareCoverage

/-! 第 n 个配对的两个坐标不超过 n，保证后续字词编码的递归严格向前。 -/
namespace KP1Y.Naturals
open YesMetaZFC YesMetaZFC.SetTheory YesMetaZFC.SetTheory.Definitional
open KP1Y.Kuratowski
universe u

theorem ordinal_le_mem_successor_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {a b c : M.Domain} (ha : M.IsOrdinal a) (hb : M.IsOrdinal b) (hSub : M.MemberSubset a b)
    (hs : M.SuccessorOf c b) : M.mem a c := by
  rcases ordinal_subset_cases_d hM ha hb hSub with he | hab
  · subst a
    exact hs.predecessor_mem
  · exact (hs a).mpr (Or.inl hab)

theorem ordinal_successor_mono_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {a b a' b' : M.Domain} (ha : M.IsOrdinal a) (hb : M.IsOrdinal b) (hSub : M.MemberSubset a b)
    (ha' : M.SuccessorOf a' a) (hb' : M.SuccessorOf b' b) : M.MemberSubset a' b' := by
  intro x hx
  rcases (ha' x).mp hx with hxa | he
  · exact (hb' x).mpr (Or.inl (hSub x hxa))
  · have hxa := hM.1.eq_of_same_members x a he
    exact hxa ▸ ordinal_le_mem_successor_d hM ha hb hSub hb'

theorem square_move_bound_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {ω zero n next x y u v : M.Domain} (hω : M.IsOmega ω) (hEmpty : ∀ z, ¬M.mem z zero)
    (hn : M.mem n ω) (hx : M.mem x ω) (hy : M.mem y ω) (hX : M.MemberSubset x n) (hY : M.MemberSubset y n)
    (hSucc : M.SuccessorOf next n) (hMove : SquareMove M zero x y u v) :
    M.MemberSubset u next ∧ M.MemberSubset v next := by
  have hωOrd := omega_isOrdinal_d hM hω
  have hN := hωOrd.mem hn
  have hI : M.MemberSubset n next := fun z hz => (hSucc z).mpr (Or.inl hz)
  rcases hMove with ⟨_,hu,hv⟩ | ⟨_,hRest⟩
  · subst u
    exact ⟨fun z hz => hI z (hX z hz),ordinal_successor_mono_d hM (hωOrd.mem hy) hN hY hv hSucc⟩
  · rcases hRest with ⟨_,hu,hv⟩ | ⟨p,hp,_,hu,hv⟩
    · subst v
      exact ⟨ordinal_successor_mono_d hM (hωOrd.mem hy) hN hY hu hSucc,fun z hz => False.elim (hEmpty z hz)⟩
    · subst u
      subst v
      exact ⟨fun z hz => hI z (hX z ((hωOrd.mem hx).transitive p hp z hz)),fun z hz => hI z (hY z hz)⟩

private def boundsSchema : Project.Delta0UnarySchema 3 where
  body := Project.Formula.forallMem (.bound 2) (.imp (memPairFormula (.bound 2) (.bound 1) (.bound 0))
    (Project.Formula.forallMem (.bound 4) (Project.Formula.forallMem (.bound 5)
      (.imp (codeFormula (.bound 2) (.bound 1) (.bound 0))
        (.conj (Project.Formula.subset (.bound 1) (.bound 3)) (Project.Formula.subset (.bound 0) (.bound 3)))))))
  freeClosed := by
    simp [memPairFormula, codeFormula, pairFormula, Project.Formula.existsMem,
      Project.Formula.forallMem, Definitional.Formula.FreeClosed]
  delta0 := .forallMem _ (.imp (memPairFormula_delta0 _ _ _) (.forallMem _ (.forallMem _
    (.imp (codeFormula_delta0 _ _ _) (.conj (.atom _ _ _) (.atom _ _ _))))))

private theorem boundsSchema_iff {M : SetTheory.Structure.{u}} (he : Extensional M) (ω P H n : M.Domain) :
    Project.Formula.satisfies ((((oneEnv ω).push P).push H).push n) boundsSchema.body ↔
      ∀ p, M.mem p P → MemPair M H n p → ∀ x, M.mem x ω → ∀ y, M.mem y ω →
        Codes M p x y → M.MemberSubset x n ∧ M.MemberSubset y n := by
  simp only [boundsSchema, Project.Formula.satisfies_forallMem_iff, Project.Formula.satisfies_imp_iff,
    Project.Formula.satisfies_conj_iff, Project.Formula.satisfies_subset_iff, memPairFormula_iff he, codeFormula_iff he]
  rfl

theorem square_coordinate_bounds_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {ω zero P base H : M.Domain} (hω : M.IsOmega ω) (hT : SquareTrace M ω zero P base H)
    (hEmpty : ∀ z, ¬M.mem z zero) :
    ∀ n, M.mem n ω → ∀ p, M.mem p P → MemPair M H n p → ∀ x, M.mem x ω → ∀ y, M.mem y ω →
      Codes M p x y → M.MemberSubset x n ∧ M.MemberSubset y n := by
  have hAll := natural_induction_d hM boundsSchema.toUnarySchema (((oneEnv ω).push P).push H) hω
    (fun e he => (boundsSchema_iff hM.1 ω P H e).mpr (by
      intro p _ hep x _ y _ hCode
      have heω := (hT.iterator.graph.bounds hM.1 hep).1
      have heBase := hT.iterator.initial e heω he
      have hpBase := hT.iterator.graph.unique e p base hep heBase
      subst p
      obtain ⟨hxz,hyz⟩ := codes_injective hM.1 hCode hT.start
      subst x
      subst y
      exact ⟨fun z hz => False.elim (hEmpty z hz),fun z hz => False.elim (hEmpty z hz)⟩))
    (fun n hn ih next hSucc => (boundsSchema_iff hM.1 ω P H next).mpr (by
      intro p _ hNext x _ y _ hCode
      obtain ⟨q,hq,hnq⟩ := hT.iterator.graph.total n hn
      obtain ⟨a,ha,b,hb,hQ⟩ := (hT.pairs q).mp hq
      have hBounds := (boundsSchema_iff hM.1 ω P H n).mp ih q hq hnq a ha b hb hQ
      obtain ⟨a',_,b',_,x',_,y',_,hQ',hP',hMove⟩ := hT.iterator.transition n next q p hSucc hnq hNext
      obtain ⟨haa',hbb'⟩ := codes_injective hM.1 hQ hQ'
      obtain ⟨hxx',hyy'⟩ := codes_injective hM.1 hCode hP'
      subst a'
      subst b'
      subst x'
      subst y'
      exact square_move_bound_d hM hω hEmpty hn ha hb hBounds.1 hBounds.2 hSucc hMove))
  exact fun n hn => (boundsSchema_iff hM.1 ω P H n).mp (hAll n hn)

end KP1Y.Naturals
