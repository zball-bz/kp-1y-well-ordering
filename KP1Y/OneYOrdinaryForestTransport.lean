import KP1Y.OneYOrdinaryCopyNesting
import KP1Y.OneYForestSelection

/-! 普通复制的祖先逆像与实际最近较小候选运输。所有归纳长度均是对象自然数。 -/
namespace KP1Y.OneYFinite
open YesMetaZFC YesMetaZFC.SetTheory YesMetaZFC.SetTheory.Definitional
open KP1Y.Kuratowski KP1Y.Functions KP1Y.Assignments KP1Y.Naturals
universe u

private def inverseAncestorCore {d : Nat} (C : ExpressionData (Project.Term d))
    (m n P Q J limit bound : Project.Term d) : Project.Formula 1 d :=
  Project.Formula.forallMem bound (Project.Formula.forallMem n.weaken
    (Project.Formula.forallMem n.weaken.weaken
      (.imp (.conj (.mem (.bound 2) limit.weaken.weaken.weaken)
        (.conj (memPairFormula J.weaken.weaken.weaken (.bound 2) (.bound 1))
          (ancestorFormula C.weaken.weaken.weaken n.weaken.weaken.weaken Q.weaken.weaken.weaken (.bound 0) (.bound 1))))
        (Project.Formula.existsMem m.weaken.weaken.weaken
          (.conj (ancestorFormula C.weaken.weaken.weaken.weaken m.weaken.weaken.weaken.weaken
            P.weaken.weaken.weaken.weaken (.bound 0) (.bound 3))
            (memPairFormula J.weaken.weaken.weaken.weaken (.bound 0) (.bound 1)))))))

private def inverseAncestorEnv {M : SetTheory.Structure.{u}} (C : ExpressionData M.Domain)
    (m n P Q J limit : M.Domain) : Env M 11 :=
  ((((((((((oneEnv C.omega).push C.zero).push C.one).push C.sequences).push C.expressions).push m).push n).push P).push Q).push J).push limit

private def inverseAncestorSchema : Project.UnarySchema 11 where
  body := inverseAncestorCore ⟨.bound 11,.bound 10,.bound 9,.bound 8,.bound 7⟩
    (.bound 6) (.bound 5) (.bound 4) (.bound 3) (.bound 2) (.bound 1) (.bound 0)
  freeClosed := by
    simp [inverseAncestorCore,ancestorFormula,parentPathFormula,ExpressionData.weaken,ExpressionData.map,
      graphFormula,KP1Y.Bounded.successorFormula,memPairFormula,codeFormula,pairFormula,
      Project.Formula.forallMem,Project.Formula.existsMem,Definitional.Formula.FreeClosed]

private theorem inverseAncestorSchema_iff {M : SetTheory.Structure.{u}} (he : Extensional M)
    (C : ExpressionData M.Domain) (m n P Q J limit bound : M.Domain) :
    Project.Formula.satisfies ((inverseAncestorEnv C m n P Q J limit).push bound) inverseAncestorSchema.body ↔
      ∀s, M.mem s bound → ∀c, M.mem c n → ∀a, M.mem a n →
        M.mem s limit ∧ MemPair M J s c ∧ Ancestor M C n Q a c →
          ∃q, M.mem q m ∧ Ancestor M C m P q s ∧ MemPair M J q a := by
  simp only [inverseAncestorSchema,inverseAncestorCore,Project.Formula.satisfies_forallMem_iff,
    Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_mem_iff,
    Project.Formula.satisfies_existsMem_iff,memPairFormula_iff he,ancestorFormula_iff he,
    ExpressionData.eval_weaken,Term.eval_weaken]
  rfl

/-- 父行在像上封闭，就能实际追溯任何目标祖先的源；不预设该祖先已经在像中。 -/
theorem ancestor_pullback_below_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {m n P Q J limit s c a : M.Domain}
    (hP : Forest M C.omega m P) (hQ : Forest M C.omega n Q) (hLimit : M.mem limit C.omega)
    (hCorr : ∀s, M.mem s limit → ∀c, M.mem c n → MemPair M J s c → ∀a,
      MemPair M Q c a ↔ ∃p, MemPair M P s p ∧ MemPair M J p a)
    (hSource : M.mem s limit) (hMap : MemPair M J s c) (hAnc : Ancestor M C n Q a c) :
    ∃q, Ancestor M C m P q s ∧ MemPair M J q a := by
  have hAll := natural_induction_d hM inverseAncestorSchema (inverseAncestorEnv C m n P Q J limit) hC.omega
    (fun z hz => (inverseAncestorSchema_iff hM.1 C m n P Q J limit z).mpr (by
      intro s hs
      exact False.elim (hz s hs)))
    (fun k _ ih next hSucc => (inverseAncestorSchema_iff hM.1 C m n P Q J limit next).mpr (by
      intro s hs c hc a ha hAnte
      rcases (hSucc s).mp hs with hs | he
      · exact (inverseAncestorSchema_iff hM.1 C m n P Q J limit k).mp ih s hs c hc a ha hAnte
      · have hsk := hM.1.eq_of_same_members s k he
        subst s
        obtain ⟨pNew,hParent,hTail⟩ := ancestor_parent_cases_d hM hC hQ hAnte.2.2
        obtain ⟨p,hOld,hMapP⟩ := (hCorr k hAnte.1 c hc hAnte.2.1 pNew).mp hParent
        rcases hTail with he | hTail
        · exact ⟨p,(hP.bounds hM.1 hOld).2,ancestor_direct_d hM hC hP hOld,he.symm ▸ hMapP⟩
        · have hpLimit := ((omega_isOrdinal_d hM hC.omega).mem hLimit).transitive k hAnte.1 p (hP.left k p hOld)
          obtain ⟨q,hq,hSourceAnc,hMapQ⟩ := (inverseAncestorSchema_iff hM.1 C m n P Q J limit k).mp ih
            p (hP.left k p hOld) pNew (hQ.bounds hM.1 hParent).2 a ha ⟨hpLimit,hMapP,hTail⟩
          exact ⟨q,hq,ancestor_step_d hM hC hP hSourceAnc hOld,hMapQ⟩))
  obtain ⟨q,_,hq⟩ := (inverseAncestorSchema_iff hM.1 C m n P Q J limit limit).mp (hAll limit hLimit)
    s hSource c (hAnc.bounds hM.1).2 a (hAnc.bounds hM.1).1 ⟨hSource,hMap,hAnc⟩
  exact ⟨q,hq⟩

namespace CopiedMountain.Ordinary
open KP1Y.OneYFinite.CopyCoordinates

theorem Copies.ancestor_parent_copy_iff_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {A : Context M.Domain} (hA : A.Valid M C) {X Y : Data M.Domain} (hX : X.Valid M C) (hY : Y.Valid M C)
    {n r F G s c a b : M.Domain} (hCopy : Copies M C T A X n Y)
    (hF : MemPair M X.parents r F) (hG : MemPair M Y.parents r G)
    (hSource : M.mem s A.last) (hMap : ParentCopy M C T A b s c) (hChild : M.mem c Y.width) :
    Ancestor M C Y.width G a c ↔ ∃q, Ancestor M C X.width F q s ∧ ParentCopy M C T A b q a := by
  obtain ⟨J,hJ,hRows⟩ := parent_copy_graph_exists_d hM hC hT hA hMap.2.1
  constructor
  · intro hAnc
    obtain ⟨q,hq,hQa⟩ := ancestor_pullback_below_d hM hC (hX.forest r F hF) (hY.forest r G hG) hA.last
      (J := J) (fun d hd u hu hDU v => by
        have hMapD := (hRows d u).mp hDU
        have hTarget : MemPair M G u v ↔ ParentAt M Y r u v := by
          constructor
          · exact fun h => ⟨G,(hY.parents.bounds hM.1 hG).2,hG,h⟩
          · rintro ⟨G',_,hG',h⟩
            exact hY.parents.unique r G' G hG' hG ▸ h
        rw [hTarget,hCopy.parents r u v]
        have huN : M.mem u n := hCopy.width ▸ hu
        simp only [huN,true_and]
        rw [parent_parent_copy_iff_d hM hC hT hA hX hd hMapD]
        constructor
        · rintro ⟨p,_,hOld,hMapP⟩
          obtain ⟨F',_,hF',hP⟩ := hOld
          exact ⟨p,hX.parents.unique r F' F hF' hF ▸ hP,(hRows p v).mpr hMapP⟩
        · rintro ⟨p,hP,hPv⟩
          exact ⟨p,(hJ.graph.bounds hM.1 hPv).1,⟨F,(hX.parents.bounds hM.1 hF).2,hF,hP⟩,(hRows p v).mp hPv⟩)
      hSource ((hRows s c).mpr hMap) hAnc
    exact ⟨q,hq,(hRows q a).mp hQa⟩
  · rintro ⟨q,hq,hMapQ⟩
    exact hCopy.ancestor_parent_copy_d hM hC hT hA hX hY hF hG hq hSource hMapQ hMap hChild


/-- 实际源数值图按普通 source0 读取的复制图，源图的值域不限于自然数。 -/
structure ValueCopies (M : SetTheory.Structure.{u}) (C : ExpressionData M.Domain)
    (T : MatrixArithmetic M.Domain) (A : Context M.Domain) (V n Range W : M.Domain) : Prop where
  graph : Graph M W n Range
  rows : ∀c s b, OrdinaryCoordinates.Decoded M C T A c s b → ∀v,
    MemPair M W c v ↔ M.mem c n ∧ MemPair M V s v

theorem ValueCopies.parent_copy_iff_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {A : Context M.Domain} (hA : A.Valid M C) {V n Range W s b c v : M.Domain}
    (h : ValueCopies M C T A V n Range W) (hs : M.mem s A.last) (hMap : ParentCopy M C T A b s c) :
    MemPair M W c v ↔ M.mem c n ∧ MemPair M V s v := by
  obtain ⟨block,hDec⟩ := OrdinaryCoordinates.decoded_parent_copy_d hM hC hT hA hs hMap
  exact h.rows c s block hDec v

theorem parent_copy_le_iff_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {A : Context M.Domain} (hA : A.Valid M C) {b p q x y : M.Domain}
    (hP : ParentCopy M C T A b p x) (hQ : ParentCopy M C T A b q y) :
    x=y ∨ M.mem x y ↔ p=q ∨ M.mem p q := by
  obtain ⟨J,hJ,hRows⟩ := parent_copy_graph_exists_d hM hC hT hA hP.2.1
  have hPX := (hRows p x).mpr hP
  have hQY := (hRows q y).mpr hQ
  constructor
  · intro hXY
    rcases (omega_isOrdinal_d hM hC.omega).wellOrder.linear.compare p hP.1 q hQ.1 with he | hpq | hqp
    · exact .inl (hM.1.eq_of_same_members p q he)
    · exact .inr hpq
    · have hYX := hJ.strict q hQ.1 p hP.1 hqp y x hQY hPX
      rcases hXY with he | hXY
      · exact False.elim (SetTheory.KP.mem_irrefl_d (KP1Y.models_weakKP hM) y (he ▸ hYX))
      · exact False.elim (SetTheory.KP.mem_irrefl_d (KP1Y.models_weakKP hM) x
          (((omega_isOrdinal_d hM hC.omega).mem (hJ.graph.bounds hM.1 hPX).2).transitive y hYX x hXY))
  · rintro (he | hpq)
    · subst q
      exact .inl (hJ.graph.unique p x y hPX hQY)
    · exact .inr (hJ.strict p hP.1 q hQ.1 hpq x y hPX hQY)

theorem Copies.candidate_parent_copy_iff_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    (positive : Bool) {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {A : Context M.Domain} (hA : A.Valid M C) {X Y : Data M.Domain} (hX : X.Valid M C) (hY : Y.Valid M C)
    {n r F G V W s c a b : M.Domain} (hCopy : Copies M C T A X n Y)
    (hF : MemPair M X.parents r F) (hG : MemPair M Y.parents r G)
    (hValues : ValueCopies M C T A V n C.omega W)
    (hSource : M.mem s A.last) (hMap : ParentCopy M C T A b s c) (hChild : M.mem c Y.width) :
    ParentCandidate positive M C Y.width G W c a ↔
      ∃p, ParentCandidate positive M C X.width F V s p ∧ ParentCopy M C T A b p a := by
  have hAnc := hCopy.ancestor_parent_copy_iff_d hM hC hT hA hX hY hF hG hSource hMap hChild (a := a)
  have hCValue := fun v => hValues.parent_copy_iff_d hM hC hT hA hSource hMap (v := v)
  constructor
  · rintro ⟨ha,x,hx,y,hy,hAX,hCY,hXY,hPos⟩
    obtain ⟨p,hp,hMapP⟩ := hAnc.mp ha
    have hpLast := ((omega_isOrdinal_d hM hC.omega).mem hA.last).transitive s hSource p hp.1
    exact ⟨p,⟨hp,x,hx,y,hy,((hValues.parent_copy_iff_d hM hC hT hA hpLast hMapP).mp hAX).2,
      ((hCValue y).mp hCY).2,hXY,hPos⟩,hMapP⟩
  · rintro ⟨p,⟨hp,x,hx,y,hy,hPX,hSY,hXY,hPos⟩,hMapP⟩
    have ha := hAnc.mpr ⟨p,hp,hMapP⟩
    have hpLast := ((omega_isOrdinal_d hM hC.omega).mem hA.last).transitive s hSource p hp.1
    exact ⟨ha,x,hx,y,hy,(hValues.parent_copy_iff_d hM hC hT hA hpLast hMapP).mpr
      ⟨hCopy.width ▸ (ha.bounds hM.1).1,hPX⟩,(hCValue y).mpr ⟨hCopy.width ▸ hChild,hSY⟩,hXY,hPos⟩

theorem Copies.restricted_parent_copy_iff_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    (positive : Bool) {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {A : Context M.Domain} (hA : A.Valid M C) {X Y : Data M.Domain} (hX : X.Valid M C) (hY : Y.Valid M C)
    {n r F G V W s c a b : M.Domain} (hCopy : Copies M C T A X n Y)
    (hF : MemPair M X.parents r F) (hG : MemPair M Y.parents r G)
    (hValues : ValueCopies M C T A V n C.omega W)
    (hSource : M.mem s A.last) (hMap : ParentCopy M C T A b s c) (hChild : M.mem c Y.width) :
    RestrictedParent positive M C Y.width G W c a ↔
      ∃p, RestrictedParent positive M C X.width F V s p ∧ ParentCopy M C T A b p a := by
  have hCandidate := fun a => hCopy.candidate_parent_copy_iff_d hM positive hC hT hA hX hY hF hG hValues hSource hMap hChild (a := a)
  constructor
  · rintro ⟨hCand,hMax⟩
    obtain ⟨p,hp,hMapP⟩ := (hCandidate a).mp hCand
    refine ⟨p,⟨hp,?_⟩,hMapP⟩
    intro q hqs hq
    obtain ⟨J,hJ,hRows⟩ := parent_copy_graph_exists_d hM hC hT hA hMap.2.1
    have hqω := (omega_isOrdinal_d hM hC.omega).transitive X.width hX.width q (hq.1.bounds hM.1).1
    obtain ⟨x,_,hQX⟩ := hJ.graph.total q hqω
    have hMapQ := (hRows q x).mp hQX
    have hNew := (hCandidate x).mpr ⟨q,hq,hMapQ⟩
    exact (parent_copy_le_iff_d hM hC hT hA hMapQ hMapP).mp (hMax x hNew.1.1 hNew)
  · rintro ⟨p,⟨hp,hMax⟩,hMapP⟩
    refine ⟨(hCandidate a).mpr ⟨p,hp,hMapP⟩,?_⟩
    intro x _ hx
    obtain ⟨q,hq,hMapQ⟩ := (hCandidate x).mp hx
    exact (parent_copy_le_iff_d hM hC hT hA hMapQ hMapP).mpr (hMax q hq.1.1 hq)

/-- 实际普通复制父行与逐项复制值交换最近较小父选择，两个模式都适用。 -/
theorem Copies.selects_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    (positive : Bool) {C : ExpressionData M.Domain} (hC : C.Valid M) {T : MatrixArithmetic M.Domain} (hT : T.Valid M C)
    {A : Context M.Domain} (hA : A.Valid M C) {X Y : Data M.Domain} (hX : X.Valid M C) (hY : Y.Valid M C)
    {n r next F G P Q V W : M.Domain} (hCopy : Copies M C T A X n Y)
    (hF : MemPair M X.parents r F) (hG : MemPair M Y.parents r G)
    (hP : MemPair M X.parents next P) (hQ : MemPair M Y.parents next Q)
    (hValues : ValueCopies M C T A V n C.omega W) (hSelect : Selects positive M C X.width F V P) :
    Selects positive M C Y.width G W Q := by
  refine ⟨hY.forest r G hG,hCopy.width.symm ▸ hValues.graph,hY.forest next Q hQ,?_⟩
  intro c a
  have hParent : MemPair M Q c a ↔ ParentAt M Y next c a := by
    constructor
    · exact fun h => ⟨Q,(hY.parents.bounds hM.1 hQ).2,hQ,h⟩
    · rintro ⟨Q',_,hQ',h⟩
      exact hY.parents.unique next Q' Q hQ' hQ ▸ h
  by_cases hc : M.mem c Y.width
  · have hcω := (omega_isOrdinal_d hM hC.omega).transitive Y.width hY.width c hc
    obtain ⟨s,b,hDec⟩ := OrdinaryCoordinates.decoded_exists_d hM hC hT hA hcω
    have hs := hDec.source_lt_last_d hM hC hT hA
    have hMap := hDec.parent_copy_reconstruct_d hM hC hT hA
    rw [hParent,hCopy.parents next c a]
    have hcN := hCopy.width ▸ hc
    simp only [hcN,true_and]
    rw [parent_parent_copy_iff_d hM hC hT hA hX hs hMap,
      hCopy.restricted_parent_copy_iff_d hM positive hC hT hA hX hY hF hG hValues hs hMap hc]
    constructor
    · rintro ⟨p,_,hOld,hMapP⟩
      obtain ⟨P',_,hP',hEdge⟩ := hOld
      exact ⟨p,(hSelect.parents s p).mp (hX.parents.unique next P' P hP' hP ▸ hEdge),hMapP⟩
    · rintro ⟨p,hRestricted,hMapP⟩
      exact ⟨p,hMapP.1,⟨P,(hX.parents.bounds hM.1 hP).2,hP,(hSelect.parents s p).mpr hRestricted⟩,hMapP⟩
  · exact ⟨fun h => False.elim (hc ((hY.forest next Q hQ).bounds hM.1 h).1),
      fun h => False.elim (hc (h.1.1.bounds hM.1).2)⟩

end CopiedMountain.Ordinary
end KP1Y.OneYFinite
