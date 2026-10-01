import KP1Y.OneYForestClosure

/-! 同一严格候选链上的最右较小值比较；所有链归纳均作用于明确对象公式。 -/
namespace KP1Y.OneYFinite
open YesMetaZFC YesMetaZFC.SetTheory YesMetaZFC.SetTheory.Definitional
open KP1Y.Kuratowski KP1Y.Functions KP1Y.Naturals
universe u

private def chainEnv {M : SetTheory.Structure.{u}} (C : ExpressionData M.Domain) (m F : M.Domain) : Env M 7 :=
  ((((((oneEnv C.omega).push C.zero).push C.one).push C.sequences).push C.expressions).push m).push F

private def chainComparisonSchema : Project.UnarySchema 7 where
  body := .forallE (.forallE (.imp
    (.conj (ancestorFormula ⟨.bound 9,.bound 8,.bound 7,.bound 6,.bound 5⟩ (.bound 4) (.bound 3) (.bound 1) (.bound 2))
      (ancestorFormula ⟨.bound 9,.bound 8,.bound 7,.bound 6,.bound 5⟩ (.bound 4) (.bound 3) (.bound 0) (.bound 2)))
    (.disj (Project.Formula.extensionalEq (.bound 1) (.bound 0))
      (.disj (ancestorFormula ⟨.bound 9,.bound 8,.bound 7,.bound 6,.bound 5⟩ (.bound 4) (.bound 3) (.bound 1) (.bound 0))
        (ancestorFormula ⟨.bound 9,.bound 8,.bound 7,.bound 6,.bound 5⟩ (.bound 4) (.bound 3) (.bound 0) (.bound 1))))))
  freeClosed := by
    have hC : (⟨.bound 9,.bound 8,.bound 7,.bound 6,.bound 5⟩ : ExpressionData (Project.Term 10)).Closed := ⟨rfl,rfl,rfl,rfl,rfl⟩
    have h1 := ancestorFormula_freeClosed hC (.bound 4) (.bound 3) (.bound 1) (.bound 2) rfl rfl rfl rfl
    have h2 := ancestorFormula_freeClosed hC (.bound 4) (.bound 3) (.bound 0) (.bound 2) rfl rfl rfl rfl
    have h3 := ancestorFormula_freeClosed hC (.bound 4) (.bound 3) (.bound 1) (.bound 0) rfl rfl rfl rfl
    have h4 := ancestorFormula_freeClosed hC (.bound 4) (.bound 3) (.bound 0) (.bound 1) rfl rfl rfl rfl
    simp [Definitional.Formula.FreeClosed,h1,h2,h3,h4]

private theorem chainComparisonSchema_iff {M : SetTheory.Structure.{u}} (he : Extensional M)
    (C : ExpressionData M.Domain) (m F c : M.Domain) :
    Project.Formula.satisfies ((chainEnv C m F).push c) chainComparisonSchema.body ↔
      ∀ a b, Ancestor M C m F a c → Ancestor M C m F b c →
        a=b ∨ Ancestor M C m F a b ∨ Ancestor M C m F b a := by
  simp only [chainComparisonSchema,Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_imp_iff,
    Project.Formula.satisfies_conj_iff,ancestorFormula_iff he,Project.Formula.satisfies_disj_iff,
    Project.Formula.satisfies_extensionalEq_iff_eq he,and_imp]
  rfl

theorem ancestor_common_target_compare_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {m F a b c : M.Domain}
    (hF : Forest M C.omega m F) (ha : Ancestor M C m F a c) (hb : Ancestor M C m F b c) :
    a=b ∨ Ancestor M C m F a b ∨ Ancestor M C m F b a := by
  have hAll := KP1Y.induction_d hM chainComparisonSchema (chainEnv C m F) (by
    intro c ih
    apply (chainComparisonSchema_iff hM.1 C m F c).mpr
    intro a b ha hb
    obtain ⟨p,hP,hA⟩ := ancestor_parent_cases_d hM hC hF ha
    obtain ⟨q,hQ,hB⟩ := ancestor_parent_cases_d hM hC hF hb
    have hpq := hF.unique c q p hQ hP
    subst q
    rcases hA with hA | hA <;> rcases hB with hB | hB
    · exact Or.inl (hA.trans hB.symm)
    · exact Or.inr (Or.inr (hA.symm ▸ hB))
    · exact Or.inr (Or.inl (hB.symm ▸ hA))
    · exact (chainComparisonSchema_iff hM.1 C m F p).mp (ih p (hF.left c p hP)) a b hA hB)
  exact (chainComparisonSchema_iff hM.1 C m F c).mp (hAll c) a b ha hb

theorem ancestor_between_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {m F a b c : M.Domain}
    (hF : Forest M C.omega m F) (ha : Ancestor M C m F a c) (hb : Ancestor M C m F b c)
    (hab : M.mem a b) : Ancestor M C m F a b := by
  rcases ancestor_common_target_compare_d hM hC hF ha hb with he | h | h
  · exact False.elim (SetTheory.KP.mem_irrefl_d (KP1Y.models_weakKP hM) b (he ▸ hab))
  · exact h
  · have hOrd := (omega_isOrdinal_d hM hC.omega).mem hF.width
    exact False.elim (hOrd.wellOrder.linear.irrefl a (ha.bounds hM.1).1
      (hOrd.wellOrder.linear.trans a (ha.bounds hM.1).1 b (hb.bounds hM.1).1 a (ha.bounds hM.1).1 hab h.1))

theorem ancestor_iff_of_parent_rows_eq_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {m F c d : M.Domain} (hF : Forest M C.omega m F)
    (hRows : ∀ p, MemPair M F c p ↔ MemPair M F d p) (a : M.Domain) :
    Ancestor M C m F a c ↔ Ancestor M C m F a d := by
  constructor
  · intro h
    obtain ⟨p,hP,hA⟩ := ancestor_parent_cases_d hM hC hF h
    rcases hA with he | hA
    · subst a
      exact ancestor_direct_d hM hC hF ((hRows p).mp hP)
    · exact ancestor_step_d hM hC hF hA ((hRows p).mp hP)
  · intro h
    obtain ⟨p,hP,hA⟩ := ancestor_parent_cases_d hM hC hF h
    rcases hA with he | hA
    · subst a
      exact ancestor_direct_d hM hC hF ((hRows p).mpr hP)
    · exact ancestor_step_d hM hC hF hA ((hRows p).mpr hP)

def RecordMinimum (M : SetTheory.Structure.{u}) (C : ExpressionData M.Domain) (m F V a c : M.Domain) : Prop :=
  Ancestor M C m F a c ∧ ∃ x, M.mem x C.omega ∧ ∃ y, M.mem y C.omega ∧
    MemPair M V a x ∧ MemPair M V c y ∧ M.mem x y ∧
      ∀ b, M.mem b m → Ancestor M C m F b c → M.mem a b →
        ∀ v, M.mem v C.omega → MemPair M V b v → M.mem x v

def recordMinimumFormula {n : Nat} (C : ExpressionData (Project.Term n)) (m F V a c : Project.Term n) : Project.Formula 1 n :=
  .conj (ancestorFormula C m F a c)
    (Project.Formula.existsMem C.omega (Project.Formula.existsMem C.omega.weaken
      (.conj (memPairFormula V.weaken.weaken a.weaken.weaken (.bound 1))
        (.conj (memPairFormula V.weaken.weaken c.weaken.weaken (.bound 0)) (.conj (.mem (.bound 1) (.bound 0))
          (Project.Formula.forallMem m.weaken.weaken (Project.Formula.forallMem C.omega.weaken.weaken.weaken
            (.imp (.conj (ancestorFormula C.weaken.weaken.weaken.weaken m.weaken.weaken.weaken.weaken F.weaken.weaken.weaken.weaken
              (.bound 1) c.weaken.weaken.weaken.weaken)
              (.conj (.mem a.weaken.weaken.weaken.weaken (.bound 1))
                (memPairFormula V.weaken.weaken.weaken.weaken (.bound 1) (.bound 0)))) (.mem (.bound 3) (.bound 0))))))))))

theorem recordMinimumFormula_delta0 {n : Nat} (C : ExpressionData (Project.Term n)) (m F V a c : Project.Term n) :
    (recordMinimumFormula C m F V a c).IsDelta0 := .conj (ancestorFormula_delta0 _ _ _ _ _)
      (.existsMem _ (.existsMem _ (.conj (memPairFormula_delta0 _ _ _) (.conj (memPairFormula_delta0 _ _ _)
        (.conj (.mem _ _) (.forallMem _ (.forallMem _ (.imp
          (.conj (ancestorFormula_delta0 _ _ _ _ _) (.conj (.mem _ _) (memPairFormula_delta0 _ _ _))) (.mem _ _)))))))))

theorem recordMinimumFormula_freeClosed {n : Nat} {C : ExpressionData (Project.Term n)} (hC : C.Closed)
    (m F V a c : Project.Term n) (hm : m.freeSupport=[]) (hF : F.freeSupport=[])
    (hV : V.freeSupport=[]) (ha : a.freeSupport=[]) (hc : c.freeSupport=[]) : (recordMinimumFormula C m F V a c).FreeClosed := by
  have hAnc := ancestorFormula_freeClosed hC m F a c hm hF ha hc
  have hInner := ancestorFormula_freeClosed hC.weaken.weaken.weaken.weaken
    m.weaken.weaken.weaken.weaken F.weaken.weaken.weaken.weaken (.bound 1) c.weaken.weaken.weaken.weaken
    (by simpa using hm) (by simpa using hF) rfl (by simpa using hc)
  simp [recordMinimumFormula,memPairFormula,codeFormula,pairFormula,Project.Formula.existsMem,
    Project.Formula.forallMem,Definitional.Formula.FreeClosed,hC.omega,hm,hV,ha,hc,hAnc,hInner]

theorem recordMinimumFormula_iff {M : SetTheory.Structure.{u}} (he : Extensional M) {n : Nat} (e : Env M n)
    (C : ExpressionData (Project.Term n)) (m F V a c : Project.Term n) :
    Project.Formula.satisfies e (recordMinimumFormula C m F V a c) ↔
      RecordMinimum M (C.eval e) (m.eval e) (F.eval e) (V.eval e) (a.eval e) (c.eval e) := by
  simp only [recordMinimumFormula,RecordMinimum,Project.Formula.satisfies_conj_iff,ancestorFormula_iff he,
    Project.Formula.satisfies_existsMem_iff,memPairFormula_iff he,Project.Formula.satisfies_mem_iff,
    Project.Formula.satisfies_forallMem_iff,Project.Formula.satisfies_imp_iff,Term.eval_weaken,ExpressionData.eval_weaken]
  constructor
  · rintro ⟨hA,x,hx,y,hy,hX,hY,hxy,hAll⟩
    exact ⟨hA,x,hx,y,hy,hX,hY,hxy,fun b hb hB hab v hv hV => hAll b hb v hv ⟨hB,hab,hV⟩⟩
  · rintro ⟨hA,x,hx,y,hy,hX,hY,hxy,hAll⟩
    exact ⟨hA,x,hx,y,hy,hX,hY,hxy,fun b hb v hv h => hAll b hb h.1 h.2.1 v hv h.2.2⟩

private def recordSchema : Project.UnarySchema 9 where
  body := .forallE (.imp
    (recordMinimumFormula ⟨.bound 10,.bound 9,.bound 8,.bound 7,.bound 6⟩ (.bound 5) (.bound 4) (.bound 3) (.bound 0) (.bound 1))
    (ancestorFormula ⟨.bound 10,.bound 9,.bound 8,.bound 7,.bound 6⟩ (.bound 5) (.bound 2) (.bound 0) (.bound 1)))
  freeClosed := by
    have hC : (⟨.bound 10,.bound 9,.bound 8,.bound 7,.bound 6⟩ : ExpressionData (Project.Term 11)).Closed := ⟨rfl,rfl,rfl,rfl,rfl⟩
    have hR := recordMinimumFormula_freeClosed hC (.bound 5) (.bound 4) (.bound 3) (.bound 0) (.bound 1) rfl rfl rfl rfl rfl
    have hA := ancestorFormula_freeClosed hC (.bound 5) (.bound 2) (.bound 0) (.bound 1) rfl rfl rfl rfl
    simp [Definitional.Formula.FreeClosed,hR,hA]

private theorem recordSchema_iff {M : SetTheory.Structure.{u}} (he : Extensional M)
    (C : ExpressionData M.Domain) (m F V P c : M.Domain) :
    Project.Formula.satisfies ((((chainEnv C m F).push V).push P).push c) recordSchema.body ↔
      ∀ a, RecordMinimum M C m F V a c → Ancestor M C m P a c := by
  simp only [recordSchema,Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_imp_iff,
    recordMinimumFormula_iff he,ancestorFormula_iff he]
  rfl

theorem Selects.record_minimum_ancestor_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {m F V P a c : M.Domain}
    (hS : Selects false M C m F V P) (hRecord : RecordMinimum M C m F V a c) : Ancestor M C m P a c := by
  have hAll := KP1Y.induction_d hM recordSchema (((chainEnv C m F).push V).push P) (by
    intro c ih
    apply (recordSchema_iff hM.1 C m F V P c).mpr
    rintro a ⟨hAnc,x,hx,y,hy,hX,hY,hxy,hRecord⟩
    have hCand : ParentCandidate false M C m F V c a := ⟨hAnc,x,hx,y,hy,hX,hY,hxy,trivial⟩
    obtain ⟨p,hParent⟩ := restricted_parent_exists_d hM false hC hS.inherited ⟨a,hCand⟩
    have hP := (hS.parents c p).mpr hParent
    rcases hParent.2 a hAnc.1 hCand with he | hap
    · subst a
      exact ancestor_direct_d hM hC hS.forest hP
    · have hAp := ancestor_between_d hM hC hS.inherited hAnc hParent.1.1 hap
      obtain ⟨v,hv,hV⟩ := hS.values.total p (hParent.1.1.bounds hM.1).1
      have hBelow : RecordMinimum M C m F V a p := by
        refine ⟨hAp,x,hx,v,hv,hX,hV,hRecord p (hParent.1.1.bounds hM.1).1 hParent.1.1 hap v hv hV,?_⟩
        intro b hb hbp hab w hw hBW
        exact hRecord b hb (ancestor_trans_d hM hC hS.inherited hbp hParent.1.1) hab w hw hBW
      have hA := (recordSchema_iff hM.1 C m F V P p).mp (ih p (hS.forest.left c p hP)) a hBelow
      exact ancestor_step_d hM hC hS.forest hA hP)
  exact (recordSchema_iff hM.1 C m F V P c).mp (hAll c) a hRecord

theorem Selects.value_ge_after_parent_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {m F V P c p b x y : M.Domain}
    (hS : Selects false M C m F V P) (hP : MemPair M P c p) (hB : Ancestor M C m F b c)
    (hpb : M.mem p b) (hX : MemPair M V c x) (hY : MemPair M V b y) : x=y ∨ M.mem x y := by
  have hParent := (hS.parents c p).mp hP
  have hx := (hS.values.bounds hM.1 hX).2
  have hy := (hS.values.bounds hM.1 hY).2
  have hω := omega_isOrdinal_d hM hC.omega
  rcases hω.wellOrder.linear.compare x hx y hy with he | hxy | hyx
  · exact Or.inl (hM.1.eq_of_same_members x y he)
  · exact Or.inr hxy
  · have hCand : ParentCandidate false M C m F V c b := ⟨hB,y,hy,x,hx,hY,hX,hyx,trivial⟩
    rcases hParent.2 b hB.1 hCand with hEq | hbp
    · exact False.elim (SetTheory.KP.mem_irrefl_d (KP1Y.models_weakKP hM) p (hEq ▸ hpb))
    · have hOrd := hω.mem hS.forest.width
      exact False.elim (hOrd.wellOrder.linear.irrefl p (hS.forest.bounds hM.1 hP).2
        (hOrd.wellOrder.linear.trans p (hS.forest.bounds hM.1 hP).2 b (hB.bounds hM.1).1 p
          (hS.forest.bounds hM.1 hP).2 hpb hbp))

theorem Selects.ancestor_of_between_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {m F V P c p q : M.Domain}
    (hS : Selects false M C m F V P) (hP : MemPair M P c p) (hQ : Ancestor M C m F q c)
    (hpq : M.mem p q) : Ancestor M C m P p q := by
  have hParent := (hS.parents c p).mp hP
  obtain ⟨x,hx,y,hy,hX,hY,hxy,_⟩ := hParent.1.2
  obtain ⟨v,hv,hV⟩ := hS.values.total q (hQ.bounds hM.1).1
  have lift (b : M.Domain) (hB : Ancestor M C m F b c) (hpb : M.mem p b)
      (w : M.Domain) (hw : M.mem w C.omega) (hW : MemPair M V b w) : M.mem x w := by
    rcases hS.value_ge_after_parent_d hM hC hP hB hpb hY hW with he | hyw
    · exact he ▸ hxy
    · exact (omega_isOrdinal_d hM hC.omega).wellOrder.linear.trans x hx y hy w hw hxy hyw
  apply hS.record_minimum_ancestor_d hM hC
  refine ⟨ancestor_between_d hM hC hS.inherited hParent.1.1 hQ hpq,x,hx,v,hv,hX,hV,lift q hQ hpq v hv hV,?_⟩
  intro b _ hB hpb w hw hW
  exact lift b (ancestor_trans_d hM hC hS.inherited hB hQ) hpb w hw hW

theorem Selects.ancestor_mono_of_common_chain_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {m F V P c d a x y : M.Domain}
    (hS : Selects false M C m F V P)
    (hCommon : ∀ p, Ancestor M C m F p c ↔ Ancestor M C m F p d)
    (hX : MemPair M V c x) (hY : MemPair M V d y) (hXY : x=y ∨ M.mem x y)
    (hAnc : Ancestor M C m P a c) : Ancestor M C m P a d := by
  obtain ⟨p,hP,hTail⟩ := ancestor_parent_cases_d hM hC hS.forest hAnc
  have hParent := (hS.parents c p).mp hP
  obtain ⟨v,hv,x',hx',hV,hX',hvx,_⟩ := hParent.1.2
  have hxx := hS.values.unique c x' x hX' hX
  subst x'
  have hvy : M.mem v y := by
    rcases hXY with he | hxy
    · exact he ▸ hvx
    · exact (omega_isOrdinal_d hM hC.omega).wellOrder.linear.trans v hv x hx' y (hS.values.bounds hM.1 hY).2 hvx hxy
  have hCand : ParentCandidate false M C m F V d p :=
    ⟨(hCommon p).mp hParent.1.1,v,hv,y,(hS.values.bounds hM.1 hY).2,hV,hY,hvy,trivial⟩
  obtain ⟨q,hQ⟩ := restricted_parent_exists_d hM false hC hS.inherited ⟨p,hCand⟩
  have hQP := (hS.parents d q).mpr hQ
  have hPD : Ancestor M C m P p d := by
    rcases hQ.2 p hCand.1.1 hCand with he | hpq
    · subst p
      exact ancestor_direct_d hM hC hS.forest hQP
    · have hPQ := hS.ancestor_of_between_d hM hC hP ((hCommon q).mpr hQ.1.1) hpq
      exact ancestor_step_d hM hC hS.forest hPQ hQP
  rcases hTail with he | hAP
  · exact he.symm ▸ hPD
  · exact ancestor_trans_d hM hC hS.forest hAP hPD

theorem Selects.ancestor_mono_of_common_parent_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {m F V P c d a x y : M.Domain}
    (hS : Selects false M C m F V P) (hRows : ∀ p, MemPair M F c p ↔ MemPair M F d p)
    (hX : MemPair M V c x) (hY : MemPair M V d y) (hXY : x=y ∨ M.mem x y)
    (hAnc : Ancestor M C m P a c) : Ancestor M C m P a d :=
  hS.ancestor_mono_of_common_chain_d hM hC (ancestor_iff_of_parent_rows_eq_d hM hC hS.inherited hRows) hX hY hXY hAnc

private def depthAncestorSchema : Project.UnarySchema 7 where
  body := .forallE (.forallE (.forallE (.imp
    (.conj (ancestorFormula ⟨.bound 10,.bound 9,.bound 8,.bound 7,.bound 6⟩ (.bound 5) (.bound 4) (.bound 2) (.bound 3))
      (.conj (depthFormula ⟨.bound 10,.bound 9,.bound 8,.bound 7,.bound 6⟩ (.bound 5) (.bound 4) (.bound 2) (.bound 1))
        (depthFormula ⟨.bound 10,.bound 9,.bound 8,.bound 7,.bound 6⟩ (.bound 5) (.bound 4) (.bound 3) (.bound 0))))
    (.mem (.bound 1) (.bound 0)))))
  freeClosed := by
    have hC : (⟨.bound 10,.bound 9,.bound 8,.bound 7,.bound 6⟩ : ExpressionData (Project.Term 11)).Closed := ⟨rfl,rfl,rfl,rfl,rfl⟩
    have hA := ancestorFormula_freeClosed hC (.bound 5) (.bound 4) (.bound 2) (.bound 3) rfl rfl rfl rfl
    have hD := depthFormula_freeClosed hC (.bound 5) (.bound 4) (.bound 2) (.bound 1) rfl rfl rfl rfl
    have hD' := depthFormula_freeClosed hC (.bound 5) (.bound 4) (.bound 3) (.bound 0) rfl rfl rfl rfl
    simp [Definitional.Formula.FreeClosed,hA,hD,hD']

private theorem depthAncestorSchema_iff {M : SetTheory.Structure.{u}} (he : Extensional M)
    (C : ExpressionData M.Domain) (m P c : M.Domain) :
    Project.Formula.satisfies ((chainEnv C m P).push c) depthAncestorSchema.body ↔
      ∀ a da dc, Ancestor M C m P a c → Depth M C m P a da → Depth M C m P c dc → M.mem da dc := by
  simp only [depthAncestorSchema,Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_imp_iff,
    Project.Formula.satisfies_conj_iff,ancestorFormula_iff he,depthFormula_iff he,Project.Formula.satisfies_mem_iff,and_imp]
  rfl

theorem ancestor_depth_lt_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {m P a c da dc : M.Domain}
    (hP : Forest M C.omega m P) (hAnc : Ancestor M C m P a c)
    (hDA : Depth M C m P a da) (hDC : Depth M C m P c dc) : M.mem da dc := by
  have hAll := KP1Y.induction_d hM depthAncestorSchema (chainEnv C m P) (by
    intro c ih
    apply (depthAncestorSchema_iff hM.1 C m P c).mpr
    intro a da dc hAnc hDA hDC
    obtain ⟨p,hParent,hTail⟩ := ancestor_parent_cases_d hM hC hP hAnc
    obtain ⟨dp,hDP,hSucc⟩ := depth_parent_predecessor_d hM hC hP hParent hDC
    rcases hTail with he | hAP
    · subst a
      exact (depth_unique_d hM hC hP hDA hDP).symm ▸ hSucc.predecessor_mem
    · have hLt := (depthAncestorSchema_iff hM.1 C m P p).mp (ih p (hP.left c p hParent)) a da dp hAP hDA hDP
      exact ((omega_isOrdinal_d hM hC.omega).mem hDC.1).transitive dp hSucc.predecessor_mem da hLt)
  exact (depthAncestorSchema_iff hM.1 C m P c).mp (hAll c) a da dc hAnc hDA hDC

theorem parent_of_ancestor_equal_depth_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {m P c d p depth : M.Domain}
    (hP : Forest M C.omega m P) (hCP : MemPair M P c p)
    (hCDepth : Depth M C m P c depth) (hDDepth : Depth M C m P d depth)
    (hAnc : Ancestor M C m P p d) : MemPair M P d p := by
  obtain ⟨q,hDQ,hTail⟩ := ancestor_parent_cases_d hM hC hP hAnc
  rcases hTail with he | hPQ
  · exact he.symm ▸ hDQ
  · obtain ⟨dp,hDP,hDPs⟩ := depth_parent_predecessor_d hM hC hP hCP hCDepth
    obtain ⟨dq,hDQDepth,hDQs⟩ := depth_parent_predecessor_d hM hC hP hDQ hDDepth
    have he := Structure.SuccessorOf.predecessor_eq hM.1 ((omega_isOrdinal_d hM hC.omega).mem hDP.1) hDPs hDQs
    have hLt := ancestor_depth_lt_d hM hC hP hPQ hDP hDQDepth
    exact False.elim (SetTheory.KP.mem_irrefl_d (KP1Y.models_weakKP hM) dq (he ▸ hLt))

theorem parent_rows_eq_of_forward_ancestors_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {m P c d depth : M.Domain}
    (hP : Forest M C.omega m P) (hCDepth : Depth M C m P c depth) (hDDepth : Depth M C m P d depth)
    (hForward : ∀ p, MemPair M P c p → Ancestor M C m P p d) :
    ∀ p, MemPair M P c p ↔ MemPair M P d p := by
  have forward (p : M.Domain) (hcp : MemPair M P c p) : MemPair M P d p :=
    parent_of_ancestor_equal_depth_d hM hC hP hcp hCDepth hDDepth (hForward p hcp)
  intro p
  constructor
  · exact forward p
  · intro hdp
    classical
    by_cases hNo : NoParent M m P c
    · have hZero := depth_of_no_parent_d hM hC hP hNo hCDepth
      exact False.elim (((depth_zero_iff_d hM hC hP hDDepth).mp hZero) p (hP.bounds hM.1 hdp).2 hdp)
    · have hSome : ∃ q, M.mem q m ∧ MemPair M P c q := by
        apply Classical.byContradiction
        intro hNone
        exact hNo (fun q hq hcq => hNone ⟨q,hq,hcq⟩)
      obtain ⟨q,_,hcq⟩ := hSome
      have hpq := hP.unique d p q hdp (forward q hcq)
      exact hpq.symm ▸ hcq

theorem Selects.parent_rows_eq_of_common_chain_depth_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {m F V P c d depth : M.Domain}
    (hS : Selects false M C m F V P)
    (hCommon : ∀ p, Ancestor M C m F p c ↔ Ancestor M C m F p d)
    (hCDepth : Depth M C m P c depth) (hDDepth : Depth M C m P d depth) :
    ∀ p, MemPair M P c p ↔ MemPair M P d p := by
  obtain ⟨x,hx,hX⟩ := hS.values.total c (hCDepth.column_bound hM.1)
  obtain ⟨y,hy,hY⟩ := hS.values.total d (hDDepth.column_bound hM.1)
  have forward (hxy : x=y ∨ M.mem x y) : ∀ p, MemPair M P c p ↔ MemPair M P d p :=
    parent_rows_eq_of_forward_ancestors_d hM hC hS.forest hCDepth hDDepth
      (fun p hP => hS.ancestor_mono_of_common_chain_d hM hC hCommon hX hY hxy (ancestor_direct_d hM hC hS.forest hP))
  rcases (omega_isOrdinal_d hM hC.omega).wellOrder.linear.compare x hx y hy with he | hxy | hyx
  · exact forward (Or.inl (hM.1.eq_of_same_members x y he))
  · exact forward (Or.inr hxy)
  · have hReverse := parent_rows_eq_of_forward_ancestors_d hM hC hS.forest hDDepth hCDepth
      (fun p hP => hS.ancestor_mono_of_common_chain_d hM hC (fun p => (hCommon p).symm) hY hX (Or.inr hyx)
        (ancestor_direct_d hM hC hS.forest hP))
    exact fun p => (hReverse p).symm

theorem Selects.parent_rows_eq_of_common_parent_depth_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {m F V P c d depth : M.Domain}
    (hS : Selects false M C m F V P) (hRows : ∀ p, MemPair M F c p ↔ MemPair M F d p)
    (hCDepth : Depth M C m P c depth) (hDDepth : Depth M C m P d depth) :
    ∀ p, MemPair M P c p ↔ MemPair M P d p :=
  hS.parent_rows_eq_of_common_chain_depth_d hM hC (ancestor_iff_of_parent_rows_eq_d hM hC hS.inherited hRows) hCDepth hDDepth

end KP1Y.OneYFinite
