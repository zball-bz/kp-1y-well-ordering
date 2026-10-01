import KP1Y.PacketUnionBounds

/-! 已编码历史的载域并集和序数界并集：实际集合构造、精确性及值域界无关的唯一性。 -/
namespace KP1Y.Ranking
open YesMetaZFC YesMetaZFC.SetTheory YesMetaZFC.SetTheory.Definitional
open KP1Y.Kuratowski KP1Y.Functions
universe u

structure FamilyUnions (M : SetTheory.Structure.{u}) (H I V A κ : M.Domain) : Prop where
  carrier : ∀ x, M.mem x A ↔ ∃ j, M.mem j I ∧ FamilyMember M H V j x
  ceiling : ∀ x, M.mem x κ ↔ ∃ j, M.mem j I ∧ FamilyOrdinalMember M H V j x

def carrierUnionFormula {n : Nat} (H I V U A : Project.Term n) : Project.Formula 1 n :=
  .conj (Project.Formula.subset A U) (Project.Formula.forallMem U
    (.iff (.mem (.bound 0) A.weaken) (Project.Formula.existsMem I.weaken
      (familyMemberFormula H.weaken.weaken V.weaken.weaken (.bound 0) (.bound 1)))))

def ordinalUnionFormula {n : Nat} (H I V U κ : Project.Term n) : Project.Formula 1 n :=
  .conj (Project.Formula.subset κ U) (Project.Formula.forallMem U
    (.iff (.mem (.bound 0) κ.weaken) (Project.Formula.existsMem I.weaken
      (familyOrdinalMemberFormula H.weaken.weaken V.weaken.weaken (.bound 0) (.bound 1)))))

theorem carrierUnionFormula_delta0 {n : Nat} (H I V U A : Project.Term n) : (carrierUnionFormula H I V U A).IsDelta0 :=
  .conj (.atom _ _ _) (.forallMem _ (.iff (.mem _ _) (.existsMem _ (familyMemberFormula_delta0 _ _ _ _))))

theorem ordinalUnionFormula_delta0 {n : Nat} (H I V U κ : Project.Term n) : (ordinalUnionFormula H I V U κ).IsDelta0 :=
  .conj (.atom _ _ _) (.forallMem _ (.iff (.mem _ _) (.existsMem _ (familyOrdinalMemberFormula_delta0 _ _ _ _))))

theorem carrierUnionFormula_freeClosed {n : Nat} (H I V U A : Project.Term n)
    (hH : H.freeSupport=[]) (hI : I.freeSupport=[]) (hV : V.freeSupport=[])
    (hU : U.freeSupport=[]) (hA : A.freeSupport=[]) : (carrierUnionFormula H I V U A).FreeClosed := by
  simp only [carrierUnionFormula,Project.Formula.forallMem,Project.Formula.existsMem,Definitional.Formula.FreeClosed]
  refine ⟨?_,?_,?_,?_,?_⟩
  · simp [hA,hU]
  · simp [hU]
  · simp [hA]
  · simp [hI]
  · apply familyMemberFormula_freeClosed <;> simp [hH,hV]

theorem ordinalUnionFormula_freeClosed {n : Nat} (H I V U κ : Project.Term n)
    (hH : H.freeSupport=[]) (hI : I.freeSupport=[]) (hV : V.freeSupport=[])
    (hU : U.freeSupport=[]) (hκ : κ.freeSupport=[]) : (ordinalUnionFormula H I V U κ).FreeClosed := by
  simp only [ordinalUnionFormula,Project.Formula.forallMem,Project.Formula.existsMem,Definitional.Formula.FreeClosed]
  refine ⟨?_,?_,?_,?_,?_⟩
  · simp [hκ,hU]
  · simp [hU]
  · simp [hκ]
  · simp [hI]
  · apply familyOrdinalMemberFormula_freeClosed <;> simp [hH,hV]

theorem carrierUnionFormula_iff {M : SetTheory.Structure.{u}} (he : Extensional M) {n : Nat}
    (e : Env M n) (H I V U A : Project.Term n) : Project.Formula.satisfies e (carrierUnionFormula H I V U A) ↔
      M.MemberSubset (A.eval e) (U.eval e) ∧ ∀ x, M.mem x (U.eval e) →
        (M.mem x (A.eval e) ↔ ∃ j, M.mem j (I.eval e) ∧ FamilyMember M (H.eval e) (V.eval e) j x) := by
  simp only [carrierUnionFormula,Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_subset_iff,
    Project.Formula.satisfies_forallMem_iff,Project.Formula.satisfies_iff_iff,Project.Formula.satisfies_mem_iff,
    Project.Formula.satisfies_existsMem_iff,familyMemberFormula_iff he,Term.eval_weaken]
  rfl

theorem ordinalUnionFormula_iff {M : SetTheory.Structure.{u}} (he : Extensional M) {n : Nat}
    (e : Env M n) (H I V U κ : Project.Term n) : Project.Formula.satisfies e (ordinalUnionFormula H I V U κ) ↔
      M.MemberSubset (κ.eval e) (U.eval e) ∧ ∀ x, M.mem x (U.eval e) →
        (M.mem x (κ.eval e) ↔ ∃ j, M.mem j (I.eval e) ∧ FamilyOrdinalMember M (H.eval e) (V.eval e) j x) := by
  simp only [ordinalUnionFormula,Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_subset_iff,
    Project.Formula.satisfies_forallMem_iff,Project.Formula.satisfies_iff_iff,Project.Formula.satisfies_mem_iff,
    Project.Formula.satisfies_existsMem_iff,familyOrdinalMemberFormula_iff he,Term.eval_weaken]
  rfl

structure FamilyUnionCertificate (M : SetTheory.Structure.{u}) (H I V A κ : M.Domain) (W : PacketUnionBounds M.Domain) : Prop where
  bounds : W.Valid M V
  carrier_subset : M.MemberSubset A W.third
  carrier : ∀ x, M.mem x W.third → (M.mem x A ↔ ∃ j, M.mem j I ∧ FamilyMember M H V j x)
  ceiling_subset : M.MemberSubset κ W.fifth
  ceiling : ∀ x, M.mem x W.fifth → (M.mem x κ ↔ ∃ j, M.mem j I ∧ FamilyOrdinalMember M H V j x)

def familyUnionCertificateFormula {n : Nat} (H I V A κ : Project.Term n) (W : PacketUnionBounds (Project.Term n)) : Project.Formula 1 n :=
  .conj (packetUnionBoundsFormula V W) (.conj (carrierUnionFormula H I V W.third A) (ordinalUnionFormula H I V W.fifth κ))

theorem familyUnionCertificateFormula_delta0 {n : Nat} (H I V A κ : Project.Term n) (W : PacketUnionBounds (Project.Term n)) :
    (familyUnionCertificateFormula H I V A κ W).IsDelta0 :=
  .conj (packetUnionBoundsFormula_delta0 _ _) (.conj (carrierUnionFormula_delta0 _ _ _ _ _) (ordinalUnionFormula_delta0 _ _ _ _ _))

theorem familyUnionCertificateFormula_freeClosed {n : Nat} (H I V A κ : Project.Term n) (W : PacketUnionBounds (Project.Term n))
    (hH : H.freeSupport=[]) (hI : I.freeSupport=[]) (hV : V.freeSupport=[]) (hA : A.freeSupport=[]) (hκ : κ.freeSupport=[])
    (h1 : W.first.freeSupport=[]) (h2 : W.second.freeSupport=[]) (h3 : W.third.freeSupport=[])
    (h4 : W.fourth.freeSupport=[]) (h5 : W.fifth.freeSupport=[]) : (familyUnionCertificateFormula H I V A κ W).FreeClosed := by
  simp only [familyUnionCertificateFormula,Definitional.Formula.FreeClosed]
  exact ⟨packetUnionBoundsFormula_freeClosed _ _ hV h1 h2 h3 h4 h5,
    carrierUnionFormula_freeClosed _ _ _ _ _ hH hI hV h3 hA,ordinalUnionFormula_freeClosed _ _ _ _ _ hH hI hV h5 hκ⟩

theorem familyUnionCertificateFormula_iff {M : SetTheory.Structure.{u}} (he : Extensional M) {n : Nat}
    (e : Env M n) (H I V A κ : Project.Term n) (W : PacketUnionBounds (Project.Term n)) :
    Project.Formula.satisfies e (familyUnionCertificateFormula H I V A κ W) ↔
      FamilyUnionCertificate M (H.eval e) (I.eval e) (V.eval e) (A.eval e) (κ.eval e) (W.eval e) := by
  simp only [familyUnionCertificateFormula,Project.Formula.satisfies_conj_iff,packetUnionBoundsFormula_iff,
    carrierUnionFormula_iff he,ordinalUnionFormula_iff he]
  exact ⟨fun h => ⟨h.1,h.2.1.1,h.2.1.2,h.2.2.1,h.2.2.2⟩,
    fun h => ⟨h.bounds,⟨h.carrier_subset,h.carrier⟩,⟨h.ceiling_subset,h.ceiling⟩⟩⟩

theorem FamilyUnionCertificate.meaning {M : SetTheory.Structure.{u}} {H I V A κ : M.Domain}
    {W : PacketUnionBounds M.Domain} (h : FamilyUnionCertificate M H I V A κ W) : FamilyUnions M H I V A κ := by
  constructor
  · intro x
    constructor
    · intro hx
      exact (h.carrier x (h.carrier_subset x hx)).mp hx
    · rintro ⟨j,hj,p,hp,hAt,hxP⟩
      exact (h.carrier x (h.bounds.carrier_bound hp hxP)).mpr ⟨j,hj,p,hp,hAt,hxP⟩
  · intro x
    constructor
    · intro hx
      exact (h.ceiling x (h.ceiling_subset x hx)).mp hx
    · rintro ⟨j,hj,p,hp,hAt,hxP⟩
      exact (h.ceiling x (h.bounds.ordinal_bound hp hxP)).mpr ⟨j,hj,p,hp,hAt,hxP⟩

private def carrierSchema : Project.Delta0UnarySchema 3 where
  body := Project.Formula.existsMem (.bound 1) (familyMemberFormula (.bound 4) (.bound 3) (.bound 0) (.bound 1))
  freeClosed := by
    simp only [Project.Formula.existsMem,Definitional.Formula.FreeClosed]
    exact ⟨by simp,familyMemberFormula_freeClosed _ _ _ _ rfl rfl rfl rfl⟩
  delta0 := .existsMem _ (familyMemberFormula_delta0 _ _ _ _)

private def ceilingSchema : Project.Delta0UnarySchema 3 where
  body := Project.Formula.existsMem (.bound 1) (familyOrdinalMemberFormula (.bound 4) (.bound 3) (.bound 0) (.bound 1))
  freeClosed := by
    simp only [Project.Formula.existsMem,Definitional.Formula.FreeClosed]
    exact ⟨by simp,familyOrdinalMemberFormula_freeClosed _ _ _ _ rfl rfl rfl rfl⟩
  delta0 := .existsMem _ (familyOrdinalMemberFormula_delta0 _ _ _ _)

theorem family_union_certificate_exists_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory) (H I V : M.Domain) :
    ∃ A κ W, FamilyUnionCertificate M H I V A κ W := by
  obtain ⟨W,hW⟩ := packet_union_bounds_exists_d hM V
  have hCar (x : M.Domain) : Project.Formula.satisfies ((((oneEnv H).push V).push I).push x) carrierSchema.body ↔
      ∃ j, M.mem j I ∧ FamilyMember M H V j x := by
    simp only [carrierSchema,Project.Formula.satisfies_existsMem_iff,familyMemberFormula_iff hM.1]
    rfl
  have hOrd (x : M.Domain) : Project.Formula.satisfies ((((oneEnv H).push V).push I).push x) ceilingSchema.body ↔
      ∃ j, M.mem j I ∧ FamilyOrdinalMember M H V j x := by
    simp only [ceilingSchema,Project.Formula.satisfies_existsMem_iff,familyOrdinalMemberFormula_iff hM.1]
    rfl
  obtain ⟨A,hA⟩ := SetTheory.KP.separation_exists_d (KP1Y.models_weakKP hM) carrierSchema (((oneEnv H).push V).push I) W.third
  obtain ⟨κ,hκ⟩ := SetTheory.KP.separation_exists_d (KP1Y.models_weakKP hM) ceilingSchema (((oneEnv H).push V).push I) W.fifth
  have hA' (x : M.Domain) : M.mem x A ↔ M.mem x W.third ∧ ∃ j, M.mem j I ∧ FamilyMember M H V j x := by
    simpa only [hCar] using hA x
  have hκ' (x : M.Domain) : M.mem x κ ↔ M.mem x W.fifth ∧ ∃ j, M.mem j I ∧ FamilyOrdinalMember M H V j x := by
    simpa only [hOrd] using hκ x
  exact ⟨A,κ,W,hW,fun x hx => ((hA' x).mp hx).1,
    fun x hx => (hA' x).trans ⟨And.right,fun h => ⟨hx,h⟩⟩,
    fun x hx => ((hκ' x).mp hx).1,fun x hx => (hκ' x).trans ⟨And.right,fun h => ⟨hx,h⟩⟩⟩

theorem FamilyUnions.unique {M : SetTheory.Structure.{u}} (he : Extensional M) {H I V V' A κ A' κ' : M.Domain}
    (hH : Graph M H I V) (hH' : Graph M H I V') (h : FamilyUnions M H I V A κ) (h' : FamilyUnions M H I V' A' κ') :
    A=A' ∧ κ=κ' := by
  constructor
  · apply he.eq_of_same_members
    intro x
    rw [h.carrier x,h'.carrier x]
    exact exists_congr (fun j => and_congr Iff.rfl (familyMember_values_congr he hH hH' j x))
  · apply he.eq_of_same_members
    intro x
    rw [h.ceiling x,h'.ceiling x]
    exact exists_congr (fun j => and_congr Iff.rfl (familyOrdinalMember_values_congr he hH hH' j x))

theorem FamilyUnions.ceiling_ordinal_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory) {H I V A κ : M.Domain}
    (hH : RankedFamily M H I V) (h : FamilyUnions M H I V A κ) : M.IsOrdinal κ := by
  apply KP1Y.Bounded.ordinal_of_transitive_members_d hM
  · intro y hy x hxy
    obtain ⟨j,hj,p,hp,hAt,T,Γ,F,hPacket,hyΓ⟩ := (h.ceiling y).mp hy
    have hRank := (hH.ranked j p hAt).rank hM.1 hPacket
    exact (h.ceiling x).mpr ⟨j,hj,p,hp,hAt,T,Γ,F,hPacket,hRank.ordinal.transitive y hyΓ x hxy⟩
  · intro x hx
    obtain ⟨j,_,p,_,hAt,T,Γ,F,hPacket,hxΓ⟩ := (h.ceiling x).mp hx
    exact ((hH.ranked j p hAt).rank hM.1 hPacket).ordinal.mem hxΓ

end KP1Y.Ranking
