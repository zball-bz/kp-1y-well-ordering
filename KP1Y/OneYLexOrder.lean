import KP1Y.OneYExpression
import KP1Y.RelationTables

/-! 全部合法内部有限表达式上的严格字典序。这里只证明严格全序，不声称良序。 -/
namespace KP1Y.OneYFinite
open YesMetaZFC YesMetaZFC.SetTheory YesMetaZFC.SetTheory.Definitional
open KP1Y.Kuratowski KP1Y.Functions KP1Y.Naturals KP1Y.Bounded
universe u

def ValuesAgreeBelow (M : SetTheory.Structure.{u}) (w s t cut : M.Domain) : Prop :=
  ∀i, M.mem i cut → ∀a, M.mem a w → (MemPair M s i a ↔ MemPair M t i a)

def LexAt (M : SetTheory.Structure.{u}) (w s m t n : M.Domain) : Prop :=
  ∃i, M.mem i n ∧ ValuesAgreeBelow M w s t i ∧
    (i=m ∨ (M.mem i m ∧ ∃a, M.mem a w ∧ ∃b, M.mem b w ∧ MemPair M s i a ∧ MemPair M t i b ∧ M.mem a b))

def Lex (M : SetTheory.Structure.{u}) (C : ExpressionData M.Domain) (s t : M.Domain) : Prop :=
  ∃m, M.mem m C.omega ∧ LegalAt M C.omega C.zero C.one s m ∧
    ∃n, M.mem n C.omega ∧ LegalAt M C.omega C.zero C.one t n ∧ LexAt M C.omega s m t n

def valuesAgreeBelowFormula {n : Nat} (w s t cut : Project.Term n) : Project.Formula 1 n :=
  Project.Formula.forallMem cut (Project.Formula.forallMem w.weaken
    (.iff (memPairFormula s.weaken.weaken (.bound 1) (.bound 0)) (memPairFormula t.weaken.weaken (.bound 1) (.bound 0))))

def lexAtFormula {n : Nat} (w s m t size : Project.Term n) : Project.Formula 1 n :=
  Project.Formula.existsMem size (.conj (valuesAgreeBelowFormula w.weaken s.weaken t.weaken (.bound 0))
    (.disj (Project.Formula.extensionalEq (.bound 0) m.weaken)
      (.conj (.mem (.bound 0) m.weaken) (Project.Formula.existsMem w.weaken (Project.Formula.existsMem w.weaken.weaken
        (.conj (memPairFormula s.weaken.weaken.weaken (.bound 2) (.bound 1))
          (.conj (memPairFormula t.weaken.weaken.weaken (.bound 2) (.bound 0)) (.mem (.bound 1) (.bound 0)))))))))

def lexFormula {n : Nat} (C : ExpressionData (Project.Term n)) (s t : Project.Term n) : Project.Formula 1 n :=
  Project.Formula.existsMem C.omega (.conj (legalAtFormula C.omega.weaken C.zero.weaken C.one.weaken s.weaken (.bound 0))
    (Project.Formula.existsMem C.omega.weaken (.conj (legalAtFormula C.omega.weaken.weaken C.zero.weaken.weaken C.one.weaken.weaken t.weaken.weaken (.bound 0))
      (lexAtFormula C.omega.weaken.weaken s.weaken.weaken (.bound 1) t.weaken.weaken (.bound 0)))))

theorem valuesAgreeBelowFormula_delta0 {n : Nat} (w s t cut : Project.Term n) : (valuesAgreeBelowFormula w s t cut).IsDelta0 :=
  .forallMem _ (.forallMem _ (.iff (memPairFormula_delta0 _ _ _) (memPairFormula_delta0 _ _ _)))

theorem lexAtFormula_delta0 {n : Nat} (w s m t size : Project.Term n) : (lexAtFormula w s m t size).IsDelta0 :=
  .existsMem _ (.conj (valuesAgreeBelowFormula_delta0 _ _ _ _) (.disj (.atom _ _ _) (.conj (.mem _ _)
    (.existsMem _ (.existsMem _ (.conj (memPairFormula_delta0 _ _ _) (.conj (memPairFormula_delta0 _ _ _) (.mem _ _))))))))

theorem lexFormula_delta0 {n : Nat} (C : ExpressionData (Project.Term n)) (s t : Project.Term n) : (lexFormula C s t).IsDelta0 :=
  .existsMem _ (.conj (legalAtFormula_delta0 _ _ _ _ _) (.existsMem _ (.conj (legalAtFormula_delta0 _ _ _ _ _) (lexAtFormula_delta0 _ _ _ _ _))))

theorem valuesAgreeBelowFormula_freeClosed {n : Nat} (w s t cut : Project.Term n)
    (hw : w.freeSupport=[]) (hs : s.freeSupport=[]) (ht : t.freeSupport=[]) (hc : cut.freeSupport=[]) :
    (valuesAgreeBelowFormula w s t cut).FreeClosed := by
  simp [valuesAgreeBelowFormula,memPairFormula,codeFormula,pairFormula,Project.Formula.forallMem,Project.Formula.existsMem,
    Definitional.Formula.FreeClosed,hw,hs,ht,hc]

theorem lexAtFormula_freeClosed {n : Nat} (w s m t size : Project.Term n)
    (hw : w.freeSupport=[]) (hs : s.freeSupport=[]) (hm : m.freeSupport=[]) (ht : t.freeSupport=[]) (hn : size.freeSupport=[]) :
    (lexAtFormula w s m t size).FreeClosed := by
  simp [lexAtFormula,valuesAgreeBelowFormula,memPairFormula,codeFormula,pairFormula,Project.Formula.forallMem,Project.Formula.existsMem,
    Definitional.Formula.FreeClosed,hw,hs,hm,ht,hn]

theorem lexFormula_freeClosed {n : Nat} {C : ExpressionData (Project.Term n)} (hC : C.Closed)
    (s t : Project.Term n) (hs : s.freeSupport=[]) (ht : t.freeSupport=[]) : (lexFormula C s t).FreeClosed := by
  have hS := legalAtFormula_freeClosed C.omega.weaken C.zero.weaken C.one.weaken s.weaken (.bound 0)
    (by simpa using hC.omega) (by simpa using hC.zero) (by simpa using hC.one) (by simpa using hs) rfl
  have hT := legalAtFormula_freeClosed C.omega.weaken.weaken C.zero.weaken.weaken C.one.weaken.weaken t.weaken.weaken (.bound 0)
    (by simpa using hC.omega) (by simpa using hC.zero) (by simpa using hC.one) (by simpa using ht) rfl
  have hLex := lexAtFormula_freeClosed C.omega.weaken.weaken s.weaken.weaken (.bound 1) t.weaken.weaken (.bound 0)
    (by simpa using hC.omega) (by simpa using hs) rfl (by simpa using ht) rfl
  simp [lexFormula,Project.Formula.existsMem,Definitional.Formula.FreeClosed,hC.omega,hS,hT,hLex]

theorem valuesAgreeBelowFormula_iff {M : SetTheory.Structure.{u}} (he : Extensional M) {n : Nat} (e : Env M n)
    (w s t cut : Project.Term n) : Project.Formula.satisfies e (valuesAgreeBelowFormula w s t cut) ↔
      ValuesAgreeBelow M (w.eval e) (s.eval e) (t.eval e) (cut.eval e) := by
  simp only [valuesAgreeBelowFormula,Project.Formula.satisfies_forallMem_iff,Project.Formula.satisfies_iff_iff,memPairFormula_iff he,Term.eval_weaken]
  rfl

theorem lexAtFormula_iff {M : SetTheory.Structure.{u}} (he : Extensional M) {n : Nat} (e : Env M n)
    (w s m t size : Project.Term n) : Project.Formula.satisfies e (lexAtFormula w s m t size) ↔
      LexAt M (w.eval e) (s.eval e) (m.eval e) (t.eval e) (size.eval e) := by
  simp only [lexAtFormula,Project.Formula.satisfies_existsMem_iff,Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_disj_iff,
    Project.Formula.satisfies_extensionalEq_iff_eq he,Project.Formula.satisfies_mem_iff,valuesAgreeBelowFormula_iff he,memPairFormula_iff he,Term.eval_weaken]
  rfl

theorem lexFormula_iff {M : SetTheory.Structure.{u}} (he : Extensional M) {n : Nat} (e : Env M n)
    (C : ExpressionData (Project.Term n)) (s t : Project.Term n) : Project.Formula.satisfies e (lexFormula C s t) ↔
      Lex M (C.eval e) (s.eval e) (t.eval e) := by
  simp only [lexFormula,Project.Formula.satisfies_existsMem_iff,Project.Formula.satisfies_conj_iff,
    legalAtFormula_iff he,lexAtFormula_iff he,Term.eval_weaken]
  rfl

theorem ValuesAgreeBelow.symm {M : SetTheory.Structure.{u}} {w s t cut : M.Domain} (h : ValuesAgreeBelow M w s t cut) :
    ValuesAgreeBelow M w t s cut := fun i hi a ha => (h i hi a ha).symm

theorem ValuesAgreeBelow.trans {M : SetTheory.Structure.{u}} {w s t u cut : M.Domain}
    (h : ValuesAgreeBelow M w s t cut) (h' : ValuesAgreeBelow M w t u cut) : ValuesAgreeBelow M w s u cut :=
  fun i hi a ha => (h i hi a ha).trans (h' i hi a ha)

theorem ValuesAgreeBelow.restrict {M : SetTheory.Structure.{u}} {w s t cut cut' : M.Domain}
    (h : ValuesAgreeBelow M w s t cut) (hSub : M.MemberSubset cut' cut) : ValuesAgreeBelow M w s t cut' :=
  fun i hi a ha => h i (hSub i hi) a ha

theorem LexAt.irrefl_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory) {w s m : M.Domain}
    (hS : Graph M s m w) : ¬LexAt M w s m s m := by
  rintro ⟨i,hi,_,rfl | ⟨_,a,_,b,_,hA,hB,hab⟩⟩
  · exact SetTheory.KP.mem_irrefl_d (KP1Y.models_weakKP hM) i hi
  · have he := hS.unique i a b hA hB
    exact SetTheory.KP.mem_irrefl_d (KP1Y.models_weakKP hM) b (he ▸ hab)

theorem LexAt.trans_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory) {w s t u m n p : M.Domain}
    (hw : M.IsOmega w) (hm : M.mem m w) (hn : M.mem n w) (hp : M.mem p w)
    (hT : Graph M t n w) (h : LexAt M w s m t n) (h' : LexAt M w t n u p) : LexAt M w s m u p := by
  obtain ⟨i,hin,hAgree,hCase⟩ := h
  obtain ⟨j,hjp,hAgree',hCase'⟩ := h'
  have hOrd := omega_isOrdinal_d hM hw
  have hi := hOrd.transitive n hn i hin
  have hj := hOrd.transitive p hp j hjp
  have hiBound : i=m ∨ M.mem i m := hCase.imp id And.left
  rcases hOrd.wellOrder.linear.compare i hi j hj with he | hij | hji
  · have hij := hM.1.eq_of_same_members i j he
    subst j
    refine ⟨i,hjp,hAgree.trans hAgree',?_⟩
    rcases hCase with he | ⟨him,a,ha,b,hb,hA,hB,hab⟩
    · exact .inl he
    · rcases hCase' with he | ⟨_,b',_,c,hc,hB',hC,hbc⟩
      · exact False.elim (SetTheory.KP.mem_irrefl_d (KP1Y.models_weakKP hM) n (he ▸ hin))
      · have hbb := hT.unique i b b' hB hB'
        subst b'
        exact .inr ⟨him,a,ha,c,hc,hA,hC,(hOrd.mem hc).transitive b hbc a hab⟩
  · have hip := (hOrd.mem hp).transitive j hjp i hij
    refine ⟨i,hip,hAgree.trans (hAgree'.restrict (fun x hx => (hOrd.mem hj).transitive i hij x hx)),?_⟩
    rcases hCase with he | ⟨him,a,ha,b,hb,hA,hB,hab⟩
    · exact .inl he
    · exact .inr ⟨him,a,ha,b,hb,hA,(hAgree' i hij b hb).mp hB,hab⟩
  · have hjm : M.mem j m := hiBound.elim (fun he => he ▸ hji) (fun him => (hOrd.mem hm).transitive i him j hji)
    refine ⟨j,hjp,(hAgree.restrict (fun x hx => (hOrd.mem hi).transitive j hji x hx)).trans hAgree',?_⟩
    rcases hCase' with he | ⟨_,a,ha,b,hb,hA,hB,hab⟩
    · subst j
      exact False.elim (SetTheory.KP.mem_irrefl_d (KP1Y.models_weakKP hM) n ((hOrd.mem hn).transitive i hin n hji))
    · exact .inr ⟨hjm,a,ha,b,hb,(hAgree j hji a ha).mpr hA,hB,hab⟩

theorem Lex.bounds {M : SetTheory.Structure.{u}} {C : ExpressionData M.Domain} (hC : C.Valid M) {s t : M.Domain}
    (h : Lex M C s t) : M.mem s C.expressions ∧ M.mem t C.expressions := by
  obtain ⟨m,hm,hS,n,hn,hT,_⟩ := h
  exact ⟨(hC.expressions s).mpr ⟨m,hm,hS⟩,(hC.expressions t).mpr ⟨n,hn,hT⟩⟩

theorem Lex.at_iff {M : SetTheory.Structure.{u}} (he : Extensional M) {C : ExpressionData M.Domain} {s t m n : M.Domain}
    (hS : LegalAt M C.omega C.zero C.one s m) (hT : LegalAt M C.omega C.zero C.one t n) :
    Lex M C s t ↔ LexAt M C.omega s m t n := by
  constructor
  · rintro ⟨m',_,hS',n',_,hT',hLex⟩
    have hms := legal_length_unique he hS' hS
    have hnt := legal_length_unique he hT' hT
    subst m'
    subst n'
    exact hLex
  · intro hLex
    exact ⟨m,hS.1.1,hS,n,hT.1.1,hT,hLex⟩

theorem Lex.irrefl_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory) {C : ExpressionData M.Domain} {s : M.Domain} : ¬Lex M C s s := by
  intro h
  obtain ⟨m,_,hS,n,_,hS',hLex⟩ := h
  have hmn := legal_length_unique hM.1 hS hS'
  subst n
  exact LexAt.irrefl_d hM hS.1.2 hLex

theorem Lex.trans_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory) {C : ExpressionData M.Domain} (hC : C.Valid M)
    {s t u : M.Domain} (h : Lex M C s t) (h' : Lex M C t u) : Lex M C s u := by
  obtain ⟨m,hm,hS,n,hn,hT,hLex⟩ := h
  obtain ⟨n',_,hT',p,hp,hU,hLex'⟩ := h'
  have hnn := legal_length_unique hM.1 hT' hT
  subst n'
  exact ⟨m,hm,hS,p,hp,hU,hLex.trans_d hM hC.omega hm hn hp hT.1.2 hLex'⟩

def DifferentAt (M : SetTheory.Structure.{u}) (w s t i : M.Domain) : Prop :=
  ∃a, M.mem a w ∧ ∃b, M.mem b w ∧ MemPair M s i a ∧ MemPair M t i b ∧ a≠b

def FirstDifference (M : SetTheory.Structure.{u}) (w s t cut i : M.Domain) : Prop :=
  M.mem i cut ∧ DifferentAt M w s t i ∧ ValuesAgreeBelow M w s t i

def differentAtFormula {n : Nat} (w s t i : Project.Term n) : Project.Formula 1 n :=
  Project.Formula.existsMem w (Project.Formula.existsMem w.weaken
    (.conj (memPairFormula s.weaken.weaken i.weaken.weaken (.bound 1))
      (.conj (memPairFormula t.weaken.weaken i.weaken.weaken (.bound 0)) (.neg (Project.Formula.extensionalEq (.bound 1) (.bound 0))))))

def firstDifferenceFormula {n : Nat} (w s t cut i : Project.Term n) : Project.Formula 1 n :=
  .conj (.mem i cut) (.conj (differentAtFormula w s t i) (valuesAgreeBelowFormula w s t i))

theorem differentAtFormula_delta0 {n : Nat} (w s t i : Project.Term n) : (differentAtFormula w s t i).IsDelta0 :=
  .existsMem _ (.existsMem _ (.conj (memPairFormula_delta0 _ _ _) (.conj (memPairFormula_delta0 _ _ _) (.neg (.atom _ _ _)))))

theorem firstDifferenceFormula_delta0 {n : Nat} (w s t cut i : Project.Term n) : (firstDifferenceFormula w s t cut i).IsDelta0 :=
  .conj (.mem _ _) (.conj (differentAtFormula_delta0 _ _ _ _) (valuesAgreeBelowFormula_delta0 _ _ _ _))

theorem differentAtFormula_freeClosed {n : Nat} (w s t i : Project.Term n)
    (hw : w.freeSupport=[]) (hs : s.freeSupport=[]) (ht : t.freeSupport=[]) (hi : i.freeSupport=[]) :
    (differentAtFormula w s t i).FreeClosed := by
  simp [differentAtFormula,memPairFormula,codeFormula,pairFormula,Project.Formula.forallMem,Project.Formula.existsMem,
    Definitional.Formula.FreeClosed,hw,hs,ht,hi]

theorem firstDifferenceFormula_freeClosed {n : Nat} (w s t cut i : Project.Term n)
    (hw : w.freeSupport=[]) (hs : s.freeSupport=[]) (ht : t.freeSupport=[]) (hc : cut.freeSupport=[]) (hi : i.freeSupport=[]) :
    (firstDifferenceFormula w s t cut i).FreeClosed := by
  have hd := differentAtFormula_freeClosed w s t i hw hs ht hi
  have ha := valuesAgreeBelowFormula_freeClosed w s t i hw hs ht hi
  simp [firstDifferenceFormula,Definitional.Formula.FreeClosed,hc,hi,hd,ha]

theorem differentAtFormula_iff {M : SetTheory.Structure.{u}} (he : Extensional M) {n : Nat} (e : Env M n)
    (w s t i : Project.Term n) : Project.Formula.satisfies e (differentAtFormula w s t i) ↔ DifferentAt M (w.eval e) (s.eval e) (t.eval e) (i.eval e) := by
  simp only [differentAtFormula,Project.Formula.satisfies_existsMem_iff,Project.Formula.satisfies_conj_iff,
    Project.Formula.satisfies_neg_iff,Project.Formula.satisfies_extensionalEq_iff_eq he,memPairFormula_iff he,Term.eval_weaken]
  rfl

theorem firstDifferenceFormula_iff {M : SetTheory.Structure.{u}} (he : Extensional M) {n : Nat} (e : Env M n)
    (w s t cut i : Project.Term n) : Project.Formula.satisfies e (firstDifferenceFormula w s t cut i) ↔
      FirstDifference M (w.eval e) (s.eval e) (t.eval e) (cut.eval e) (i.eval e) := by
  simp only [firstDifferenceFormula,Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_mem_iff,
    differentAtFormula_iff he,valuesAgreeBelowFormula_iff he]
  rfl

theorem not_different_at_iff {M : SetTheory.Structure.{u}} {w s t m n i : M.Domain}
    (hS : Graph M s m w) (hT : Graph M t n w) (his : M.mem i m) (hit : M.mem i n) :
    ¬DifferentAt M w s t i ↔ ∀a, M.mem a w → (MemPair M s i a ↔ MemPair M t i a) := by
  constructor
  · intro hNo a ha
    constructor
    · intro hA
      obtain ⟨b,hb,hB⟩ := hT.total i hit
      have he : a=b := Classical.byContradiction (fun hne => hNo ⟨a,ha,b,hb,hA,hB,hne⟩)
      exact he.symm ▸ hB
    · intro hA
      obtain ⟨b,hb,hB⟩ := hS.total i his
      have he : b=a := Classical.byContradiction (fun hne => hNo ⟨b,hb,a,ha,hB,hA,hne⟩)
      exact he ▸ hB
  · rintro hAgree ⟨a,ha,b,_,hA,hB,hne⟩
    exact hne (hT.unique i a b ((hAgree a ha).mp hA) hB)

private def differentSchema : Project.Delta0UnarySchema 3 where
  body := differentAtFormula (.bound 3) (.bound 2) (.bound 1) (.bound 0)
  freeClosed := differentAtFormula_freeClosed _ _ _ _ rfl rfl rfl rfl
  delta0 := differentAtFormula_delta0 _ _ _ _

/-- 先实际分离差异位置集，再取该内部有限序数中的最小差异。 -/
theorem first_difference_or_agree_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory) {w s t m n cut : M.Domain}
    (hw : M.IsOmega w) (hc : M.mem cut w) (hS : Graph M s m w) (hT : Graph M t n w)
    (hCutS : M.MemberSubset cut m) (hCutT : M.MemberSubset cut n) :
    ValuesAgreeBelow M w s t cut ∨ ∃i, FirstDifference M w s t cut i := by
  let e := ((oneEnv w).push s).push t
  obtain ⟨D,hD⟩ := SetTheory.KP.separation_exists_d (KP1Y.models_weakKP hM) differentSchema e cut
  have hRows (i : M.Domain) : M.mem i D ↔ M.mem i cut ∧ DifferentAt M w s t i := by
    have hr := hD i
    rw [show Project.Formula.satisfies (e.push i) differentSchema.body ↔ DifferentAt M w s t i from differentAtFormula_iff hM.1 _ _ _ _ _] at hr
    exact hr
  by_cases hSome : ∃i, M.mem i D
  · have hOrd := (omega_isOrdinal_d hM hw).mem hc
    obtain ⟨i,hi,hLeast⟩ := hOrd.wellOrder.least D (fun j hj => ((hRows j).mp hj).1) hSome
    obtain ⟨hiCut,hDiff⟩ := (hRows i).mp hi
    refine .inr ⟨i,hiCut,hDiff,?_⟩
    intro j hji
    have hjCut := hOrd.transitive i hiCut j hji
    apply (not_different_at_iff hS hT (hCutS j hjCut) (hCutT j hjCut)).mp
    intro hDiffJ
    rcases hLeast j ((hRows j).mpr ⟨hjCut,hDiffJ⟩) with he | hij
    · have hij := hM.1.eq_of_same_members i j he
      exact SetTheory.KP.mem_irrefl_d (KP1Y.models_weakKP hM) i (hij.symm ▸ hji)
    · exact SetTheory.KP.mem_irrefl_d (KP1Y.models_weakKP hM) i ((hOrd.mem hiCut).transitive j hji i hij)
  · refine .inl (fun i hi => (not_different_at_iff hS hT (hCutS i hi) (hCutT i hi)).mp ?_)
    exact fun hDiff => hSome ⟨i,(hRows i).mpr ⟨hi,hDiff⟩⟩

theorem FirstDifference.unique_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory) {w s t m n cut i j : M.Domain}
    (hw : M.IsOmega w) (hc : M.mem cut w) (_hS : Graph M s m w) (hT : Graph M t n w)
    (h : FirstDifference M w s t cut i) (h' : FirstDifference M w s t cut j) : i=j := by
  have hOrd := (omega_isOrdinal_d hM hw).mem hc
  have hNo (a b : M.Domain) (hab : M.mem a b) (hDiff : DifferentAt M w s t a) (hAgree : ValuesAgreeBelow M w s t b) : False := by
    obtain ⟨x,hx,y,_,hX,hY,hne⟩ := hDiff
    exact hne (hT.unique a x y ((hAgree a hab x hx).mp hX) hY)
  rcases hOrd.wellOrder.linear.compare i h.1 j h'.1 with he | hij | hji
  · exact hM.1.eq_of_same_members i j he
  · exact False.elim (hNo i j hij h.2.1 h'.2.2)
  · exact False.elim (hNo j i hji h'.2.1 h.2.2)

theorem first_difference_lex_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory) {w s t m n cut i : M.Domain}
    (hw : M.IsOmega w) (hCutS : M.MemberSubset cut m) (hCutT : M.MemberSubset cut n)
    (h : FirstDifference M w s t cut i) : LexAt M w s m t n ∨ LexAt M w t n s m := by
  obtain ⟨hi,⟨a,ha,b,hb,hA,hB,hne⟩,hAgree⟩ := h
  rcases (omega_isOrdinal_d hM hw).wellOrder.linear.compare a ha b hb with he | hab | hba
  · exact False.elim (hne (hM.1.eq_of_same_members a b he))
  · exact .inl ⟨i,hCutT i hi,hAgree,.inr ⟨hCutS i hi,a,ha,b,hb,hA,hB,hab⟩⟩
  · exact .inr ⟨i,hCutS i hi,hAgree.symm,.inr ⟨hCutT i hi,b,hb,a,ha,hB,hA,hba⟩⟩

theorem ValuesAgreeBelow.graph_eq {M : SetTheory.Structure.{u}} (he : Extensional M) {w s t m : M.Domain}
    (hS : Graph M s m w) (hT : Graph M t m w) (h : ValuesAgreeBelow M w s t m) : s=t := by
  apply hS.ext he hT
  intro i hi a
  exact ⟨fun hA => (h i hi a (hS.bounds he hA).2).mp hA,fun hA => (h i hi a (hT.bounds he hA).2).mpr hA⟩

theorem LexAt.trichotomy_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory) {w s t m n : M.Domain}
    (hw : M.IsOmega w) (hm : M.mem m w) (hn : M.mem n w) (hS : Graph M s m w) (hT : Graph M t n w) :
    s=t ∨ LexAt M w s m t n ∨ LexAt M w t n s m := by
  have hOrd := omega_isOrdinal_d hM hw
  rcases hOrd.wellOrder.linear.compare m hm n hn with he | hmn | hnm
  · have heq := hM.1.eq_of_same_members m n he
    subst n
    rcases first_difference_or_agree_d hM hw hm hS hT (fun _ h => h) (fun _ h => h) with hAgree | ⟨i,hDiff⟩
    · exact .inl (hAgree.graph_eq hM.1 hS hT)
    · exact .inr (first_difference_lex_d hM hw (fun _ h => h) (fun _ h => h) hDiff)
  · have hSub : M.MemberSubset m n := fun i hi => (hOrd.mem hn).transitive m hmn i hi
    rcases first_difference_or_agree_d hM hw hm hS hT (fun _ h => h) hSub with hAgree | ⟨i,hDiff⟩
    · exact .inr (.inl ⟨m,hmn,hAgree,.inl rfl⟩)
    · exact .inr (first_difference_lex_d hM hw (fun _ h => h) hSub hDiff)
  · have hSub : M.MemberSubset n m := fun i hi => (hOrd.mem hm).transitive n hnm i hi
    rcases first_difference_or_agree_d hM hw hn hS hT hSub (fun _ h => h) with hAgree | ⟨i,hDiff⟩
    · exact .inr (.inr ⟨n,hnm,hAgree.symm,.inl rfl⟩)
    · exact .inr (first_difference_lex_d hM hw hSub (fun _ h => h) hDiff)

theorem Lex.trichotomy_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory) {C : ExpressionData M.Domain} (hC : C.Valid M)
    {s t : M.Domain} (hs : M.mem s C.expressions) (ht : M.mem t C.expressions) : s=t ∨ Lex M C s t ∨ Lex M C t s := by
  obtain ⟨m,hm,hS⟩ := (hC.expressions s).mp hs
  obtain ⟨n,hn,hT⟩ := (hC.expressions t).mp ht
  exact (LexAt.trichotomy_d hM hC.omega hm hn hS.1.2 hT.1.2).imp id
    (fun h => h.imp ((Lex.at_iff hM.1 hS hT).mpr) ((Lex.at_iff hM.1 hT hS).mpr))

theorem Lex.asymm_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory) {C : ExpressionData M.Domain} (hC : C.Valid M)
    {s t : M.Domain} (h : Lex M C s t) : ¬Lex M C t s := fun h' => Lex.irrefl_d hM (h.trans_d hM hC h')

theorem LexAt.prefix_iff_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory) {w s t m n : M.Domain}
    (hT : Graph M t n w) (hAgree : ValuesAgreeBelow M w s t m) : LexAt M w s m t n ↔ M.mem m n := by
  constructor
  · rintro ⟨i,hi,_,he | ⟨him,a,ha,b,_,hA,hB,hab⟩⟩
    · exact he ▸ hi
    · have he := hT.unique i a b ((hAgree i him a ha).mp hA) hB
      exact False.elim (SetTheory.KP.mem_irrefl_d (KP1Y.models_weakKP hM) b (he ▸ hab))
  · exact fun hmn => ⟨m,hmn,hAgree,.inl rfl⟩

theorem Lex.prefix_iff_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory) {C : ExpressionData M.Domain} {s t m n : M.Domain}
    (hS : LegalAt M C.omega C.zero C.one s m) (hT : LegalAt M C.omega C.zero C.one t n)
    (hPrefix : Prefix M s t m C.omega) : Lex M C s t ↔ M.mem m n :=
  (Lex.at_iff hM.1 hS hT).trans (LexAt.prefix_iff_d hM hT.1.2 hPrefix.rows)

theorem Lex.true_prefix_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory) {C : ExpressionData M.Domain} (hC : C.Valid M)
    {s t m n : M.Domain} (hS : LegalAt M C.omega C.zero C.one s m) (hT : LegalAt M C.omega C.zero C.one t n)
    (hPrefix : Prefix M s t m C.omega) (hSub : M.MemberSubset m n) (hProper : m≠n) : Lex M C s t := by
  have hOrd := omega_isOrdinal_d hM hC.omega
  rcases hOrd.wellOrder.linear.compare m hS.1.1 n hT.1.1 with he | hmn | hnm
  · exact False.elim (hProper (hM.1.eq_of_same_members m n he))
  · exact (Lex.prefix_iff_d hM hS hT hPrefix).mpr hmn
  · exact False.elim (SetTheory.KP.mem_irrefl_d (KP1Y.models_weakKP hM) n (hSub n hnm))

theorem DifferentAt.values_ne {M : SetTheory.Structure.{u}} {w s t m n i a b : M.Domain}
    (hS : Graph M s m w) (hT : Graph M t n w) (h : DifferentAt M w s t i)
    (hA : MemPair M s i a) (hB : MemPair M t i b) : a≠b := by
  obtain ⟨x,_,y,_,hX,hY,hne⟩ := h
  have hxa := hS.unique i x a hX hA
  have hyb := hT.unique i y b hY hB
  exact fun he => hne (hxa.trans (he.trans hyb.symm))

theorem LexAt.first_difference_iff_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {w s t m n cut i a b : M.Domain} (hw : M.IsOmega w) (hm : M.mem m w) (hn : M.mem n w)
    (hS : Graph M s m w) (hT : Graph M t n w) (hCutS : M.MemberSubset cut m) (hCutT : M.MemberSubset cut n)
    (hFirst : FirstDifference M w s t cut i) (hA : MemPair M s i a) (hB : MemPair M t i b) :
    LexAt M w s m t n ↔ M.mem a b := by
  have ha := (hS.bounds hM.1 hA).2
  have hb := (hT.bounds hM.1 hB).2
  constructor
  · intro hLex
    rcases (omega_isOrdinal_d hM hw).wellOrder.linear.compare a ha b hb with he | hab | hba
    · exact False.elim (hFirst.2.1.values_ne hS hT hA hB (hM.1.eq_of_same_members a b he))
    · exact hab
    · have hReverse : LexAt M w t n s m := ⟨i,hCutS i hFirst.1,hFirst.2.2.symm,.inr ⟨hCutT i hFirst.1,b,hb,a,ha,hB,hA,hba⟩⟩
      exact False.elim (LexAt.irrefl_d hM hS (hLex.trans_d hM hw hm hn hm hT hReverse))
  · intro hab
    exact ⟨i,hCutT i hFirst.1,hFirst.2.2,.inr ⟨hCutS i hFirst.1,a,ha,b,hb,hA,hB,hab⟩⟩

structure LexRelation (M : SetTheory.Structure.{u}) (C : ExpressionData M.Domain) (L : M.Domain) : Prop where
  support : RelationSupport M L C.expressions C.expressions
  rows : ∀s t, MemPair M L s t ↔ Lex M C s t

def lexRelationFormula {n : Nat} (C : ExpressionData (Project.Term n)) (L : Project.Term n) : Project.Formula 1 n :=
  .conj (relationSupportFormula L C.expressions C.expressions)
    (Project.Formula.forallMem C.expressions (Project.Formula.forallMem C.expressions.weaken
      (.iff (memPairFormula L.weaken.weaken (.bound 1) (.bound 0)) (lexFormula C.weaken.weaken (.bound 1) (.bound 0)))))

theorem lexRelationFormula_delta0 {n : Nat} (C : ExpressionData (Project.Term n)) (L : Project.Term n) :
    (lexRelationFormula C L).IsDelta0 := .conj (relationSupportFormula_delta0 _ _ _) (.forallMem _ (.forallMem _
      (.iff (memPairFormula_delta0 _ _ _) (lexFormula_delta0 _ _ _))))

theorem lexRelationFormula_freeClosed {n : Nat} {C : ExpressionData (Project.Term n)} (hC : C.Closed)
    (L : Project.Term n) (hL : L.freeSupport=[]) : (lexRelationFormula C L).FreeClosed := by
  have hLex := lexFormula_freeClosed hC.weaken.weaken (.bound 1) (.bound 0) rfl rfl
  simp [lexRelationFormula,relationSupportFormula,memPairFormula,codeFormula,pairFormula,Project.Formula.forallMem,
    Project.Formula.existsMem,Definitional.Formula.FreeClosed,hC.expressions,hL,hLex]

theorem lexRelationFormula_iff {M : SetTheory.Structure.{u}} (he : Extensional M) {n : Nat} (e : Env M n)
    (C : ExpressionData (Project.Term n)) (L : Project.Term n) (hC : (C.eval e).Valid M) :
    Project.Formula.satisfies e (lexRelationFormula C L) ↔ LexRelation M (C.eval e) (L.eval e) := by
  simp only [lexRelationFormula,Project.Formula.satisfies_conj_iff,relationSupportFormula_iff he,
    Project.Formula.satisfies_forallMem_iff,Project.Formula.satisfies_iff_iff,memPairFormula_iff he,
    lexFormula_iff he,ExpressionData.eval_weaken,Term.eval_weaken]
  constructor
  · rintro ⟨hSupport,hRows⟩
    refine ⟨hSupport,fun s t => ?_⟩
    exact ⟨fun h => (hRows s (hSupport.bounds he h).1 t (hSupport.bounds he h).2).mp h,
      fun h => (hRows s (h.bounds hC).1 t (h.bounds hC).2).mpr h⟩
  · exact fun h => ⟨h.support,fun s _ t _ => h.rows s t⟩

private def lexSchema : Project.Delta0BinarySchema 5 where
  body := lexFormula ⟨.bound 6,.bound 5,.bound 4,.bound 3,.bound 2⟩ (.bound 1) (.bound 0)
  freeClosed := lexFormula_freeClosed ⟨rfl,rfl,rfl,rfl,rfl⟩ _ _ rfl rfl
  delta0 := lexFormula_delta0 _ _ _

theorem lex_relation_exists_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) : ∃L, LexRelation M C L := by
  let e := ((((oneEnv C.omega).push C.zero).push C.one).push C.sequences).push C.expressions
  obtain ⟨L,hSupport,hRaw⟩ := relation_comprehension_d hM lexSchema e C.expressions C.expressions
  refine ⟨L,hSupport,fun s t => ?_⟩
  have hφ : Project.Formula.satisfies ((e.push s).push t) lexSchema.body ↔ Lex M C s t := lexFormula_iff hM.1 _ _ _ _
  rw [hRaw s t,hφ]
  exact ⟨fun h => h.2.2,fun h => ⟨(h.bounds hC).1,(h.bounds hC).2,h⟩⟩

theorem LexRelation.unique {M : SetTheory.Structure.{u}} (he : Extensional M) {C : ExpressionData M.Domain} {L K : M.Domain}
    (hL : LexRelation M C L) (hK : LexRelation M C K) : L=K :=
  relation_ext he hL.support hK.support (fun s t => (hL.rows s t).trans (hK.rows s t).symm)

theorem LexRelation.irrefl_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory) {C : ExpressionData M.Domain} {L : M.Domain}
    (hL : LexRelation M C L) (s : M.Domain) : ¬MemPair M L s s := fun h => Lex.irrefl_d hM ((hL.rows s s).mp h)

theorem LexRelation.trans_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory) {C : ExpressionData M.Domain} (hC : C.Valid M)
    {L s t u : M.Domain} (hL : LexRelation M C L) (hST : MemPair M L s t) (hTU : MemPair M L t u) : MemPair M L s u :=
  (hL.rows s u).mpr (((hL.rows s t).mp hST).trans_d hM hC ((hL.rows t u).mp hTU))

theorem LexRelation.trichotomy_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory) {C : ExpressionData M.Domain} (hC : C.Valid M)
    {L s t : M.Domain} (hL : LexRelation M C L) (hs : M.mem s C.expressions) (ht : M.mem t C.expressions) :
    s=t ∨ MemPair M L s t ∨ MemPair M L t s :=
  (Lex.trichotomy_d hM hC hs ht).imp id (fun h => h.imp ((hL.rows s t).mpr) ((hL.rows t s).mpr))

end KP1Y.OneYFinite
