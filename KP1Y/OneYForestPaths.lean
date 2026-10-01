import KP1Y.OneYAncestry

/-! 内部有限父链的构造、分解与根；全部可变长度由对象归纳处理。 -/
namespace KP1Y.OneYFinite
open YesMetaZFC YesMetaZFC.SetTheory YesMetaZFC.SetTheory.Definitional
open KP1Y.Kuratowski KP1Y.Functions KP1Y.Naturals KP1Y.Bounded
universe u

theorem ParentPath.start_bound {M : SetTheory.Structure.{u}} (he : Extensional M)
    {C : ExpressionData M.Domain} {m P f n a c : M.Domain} (h : ParentPath M C m P f n a c) : M.mem a m := by
  obtain ⟨_,_,_,ha,_⟩ := h.endpoints
  exact (h.graph.bounds he ha).2

theorem ParentPath.end_bound {M : SetTheory.Structure.{u}} (he : Extensional M)
    {C : ExpressionData M.Domain} {m P f n a c : M.Domain} (h : ParentPath M C m P f n a c) : M.mem c m := by
  obtain ⟨_,_,_,_,hc⟩ := h.endpoints
  exact (h.graph.bounds he hc).2

theorem ParentPath.zero_in_length {M : SetTheory.Structure.{u}} (he : Extensional M)
    {C : ExpressionData M.Domain} {m P f n a c : M.Domain} (h : ParentPath M C m P f n a c) : M.mem C.zero n := by
  obtain ⟨_,_,_,ha,_⟩ := h.endpoints
  exact (h.graph.bounds he ha).1

theorem ParentPath.sequence_member_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {m P f n a c : M.Domain}
    (hm : M.mem m C.omega) (h : ParentPath M C m P f n a c) : M.mem f C.sequences :=
  (hC.sequences f).mpr ⟨n,h.length,h.graph.mono_values (fun x hx => (omega_isOrdinal_d hM hC.omega).transitive m hm x hx)⟩

theorem parent_path_singleton_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {m P c : M.Domain} (hc : M.mem c m) :
    ∃ f, ParentPath M C m P f C.one c c := by
  obtain ⟨f,hF,hRows⟩ := append_graph_d hM (empty_graph (V := m) hC.zero_empty) hC.one_succ (fun _ h => h) hc
  have hRow : MemPair M f C.zero c := (hRows C.zero c).mpr (Or.inr ⟨rfl,rfl⟩)
  refine ⟨f,hC.one_nat,hF,⟨C.zero,hC.one_succ.predecessor_mem,hC.one_succ,hRow,hRow⟩,?_⟩
  intro i j x y hi hj _ _ hs
  have hIZ : i=C.zero := by
    rcases (hC.one_succ i).mp hi with hi | he
    · exact False.elim (hC.zero_empty i hi)
    · exact hM.1.eq_of_same_members i C.zero he
  have hJZ : j=C.zero := by
    rcases (hC.one_succ j).mp hj with hj | he
    · exact False.elim (hC.zero_empty j hj)
    · exact hM.1.eq_of_same_members j C.zero he
  have hBad := hs.predecessor_mem
  rw [hIZ,hJZ] at hBad
  exact False.elim (hC.zero_empty C.zero hBad)

theorem ParentPath.append_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {m P f n a c d : M.Domain}
    (h : ParentPath M C m P f n a c) (hd : M.mem d m) (hParent : MemPair M P d c) :
    ∃ next g, M.SuccessorOf next n ∧ ParentPath M C m P g next a d := by
  obtain ⟨next,hNext,hNextNat⟩ := hC.omega.1.2 n h.length
  obtain ⟨g,hG,hRows⟩ := append_graph_d hM h.graph hNext (fun _ h => h) hd
  have hOld (i : M.Domain) (hi : M.mem i n) (x : M.Domain) : MemPair M g i x ↔ MemPair M f i x := by
    rw [hRows i x]
    constructor
    · rintro (hx | ⟨he,_⟩)
      · exact hx
      · exact False.elim (SetTheory.KP.mem_irrefl_d (KP1Y.models_weakKP hM) n (he ▸ hi))
    · exact Or.inl
  obtain ⟨last,hLast,hLastSucc,hStart,hEnd⟩ := h.endpoints
  have hgn : MemPair M g n d := (hRows n d).mpr (Or.inr ⟨rfl,rfl⟩)
  refine ⟨next,g,hNext,hNextNat,hG,
    ⟨n,hNext.predecessor_mem,hNext,(hOld C.zero (h.graph.bounds hM.1 hStart).1 a).mpr hStart,hgn⟩,?_⟩
  intro i j x y hi hj hix hjy hs
  rcases (hNext j).mp hj with hjOld | hjEq
  · have hiOld := ((omega_isOrdinal_d hM hC.omega).mem h.length).transitive j hjOld i hs.predecessor_mem
    exact h.edges i j x y hiOld hjOld ((hOld i hiOld x).mp hix) ((hOld j hjOld y).mp hjy) hs
  · have hjn := hM.1.eq_of_same_members j n hjEq
    subst j
    have hli := Structure.SuccessorOf.predecessor_eq hM.1
      (((omega_isOrdinal_d hM hC.omega).mem h.length).mem hLast) hLastSucc hs
    subst i
    have hxc := hG.unique last x c hix ((hOld last hLast c).mpr hEnd)
    have hyd := hG.unique n y d hjy hgn
    subst x
    subst y
    exact hParent

/-- 去掉最后一列；单点路径与真正有父边的情形完全分开。 -/
theorem ParentPath.peel_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {m P f n a c : M.Domain}
    (h : ParentPath M C m P f n a c) :
    (n=C.one ∧ a=c ∧ ∀ i x, MemPair M f i x → i=C.zero ∧ x=c) ∨
      ∃ last g b, M.SuccessorOf n last ∧ M.mem last C.omega ∧
        Prefix M g f last m ∧ ParentPath M C m P g last a b ∧ MemPair M P c b := by
  obtain ⟨last,hLast,hSucc,hFirst,hEnd⟩ := h.endpoints
  have hLastNat := (omega_isOrdinal_d hM hC.omega).transitive n h.length last hLast
  by_cases hLastZero : last=C.zero
  · subst last
    have hnOne := Structure.SuccessorOf.eq hM.1 hSucc hC.one_succ
    have hac := h.graph.unique C.zero a c hFirst hEnd
    refine Or.inl ⟨hnOne,hac,?_⟩
    intro i x hix
    have hiOne : M.mem i C.one := hnOne ▸ (h.graph.bounds hM.1 hix).1
    have hiZero : i=C.zero := by
      rcases (hC.one_succ i).mp hiOne with hi | hi
      · exact False.elim (hC.zero_empty i hi)
      · exact hM.1.eq_of_same_members i C.zero hi
    subst i
    exact ⟨rfl,h.graph.unique C.zero x c hix hEnd⟩
  · have hZLast := (hC.zero_mem_iff hM hLastNat).mpr hLastZero
    rcases natural_cases hM hC.omega hLastNat with he | ⟨prev,_,hPrevSucc⟩
    · exact False.elim (he C.zero hZLast)
    · have hSub : M.MemberSubset last n := fun i hi => (hSucc i).mpr (Or.inl hi)
      obtain ⟨g,hG⟩ := restrict_prefix_d hM h.graph hSub
      obtain ⟨b,hb,hPrev⟩ := h.graph.total prev (hSub prev hPrevSucc.predecessor_mem)
      have hPath : ParentPath M C m P g last a b := by
        refine ⟨hLastNat,hG.graph,⟨prev,hPrevSucc.predecessor_mem,hPrevSucc,
          (hG.rows C.zero hZLast a (h.graph.bounds hM.1 hFirst).2).mpr hFirst,
          (hG.rows prev hPrevSucc.predecessor_mem b hb).mpr hPrev⟩,?_⟩
        intro i j x y hi hj hix hjy hs
        exact h.edges i j x y (hSub i hi) (hSub j hj)
          ((hG.all_rows hM.1 h.graph i hi x).mp hix) ((hG.all_rows hM.1 h.graph j hj y).mp hjy) hs
      exact Or.inr ⟨last,g,b,hSucc,hLastNat,hG,hPath,
        h.edges prev last b c (hSub prev hPrevSucc.predecessor_mem) hLast hPrev hEnd hPrevSucc⟩

private def pathEnv {M : SetTheory.Structure.{u}} (C : ExpressionData M.Domain) (m P : M.Domain) : Env M 7 :=
  ((((((oneEnv C.omega).push C.zero).push C.one).push C.sequences).push C.expressions).push m).push P

private def pathValueSchema : Project.UnarySchema 7 where
  body := .forallE (.forallE (.forallE (.imp
    (parentPathFormula ⟨.bound 10,.bound 9,.bound 8,.bound 7,.bound 6⟩
      (.bound 5) (.bound 4) (.bound 2) (.bound 3) (.bound 1) (.bound 0))
    (.forallE (.forallE (.imp (memPairFormula (.bound 4) (.bound 1) (.bound 0))
      (.disj (Project.Formula.extensionalEq (.bound 0) (.bound 2)) (.mem (.bound 0) (.bound 2)))))))))
  freeClosed := by
    have hPath := parentPathFormula_freeClosed
      (show (⟨.bound 10,.bound 9,.bound 8,.bound 7,.bound 6⟩ : ExpressionData (Project.Term 11)).Closed from ⟨rfl,rfl,rfl,rfl,rfl⟩)
      (.bound 5) (.bound 4) (.bound 2) (.bound 3) (.bound 1) (.bound 0) rfl rfl rfl rfl rfl rfl
    simp [Definitional.Formula.FreeClosed,hPath,memPairFormula,codeFormula,pairFormula,
      Project.Formula.forallMem,Project.Formula.existsMem]

private theorem pathValueSchema_iff {M : SetTheory.Structure.{u}} (he : Extensional M)
    (C : ExpressionData M.Domain) (m P n : M.Domain) :
    Project.Formula.satisfies ((pathEnv C m P).push n) pathValueSchema.body ↔
      ∀ f a c, ParentPath M C m P f n a c → ∀ i x, MemPair M f i x → x=c ∨ M.mem x c := by
  simp only [pathValueSchema,Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_imp_iff,
    parentPathFormula_iff he,memPairFormula_iff he,Project.Formula.satisfies_disj_iff,
    Project.Formula.satisfies_extensionalEq_iff_eq he,Project.Formula.satisfies_mem_iff]
  rfl

theorem ParentPath.values_below_last_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {m P f n a c : M.Domain}
    (hF : Forest M C.omega m P) (h : ParentPath M C m P f n a c) :
    ∀ i x, MemPair M f i x → x=c ∨ M.mem x c := by
  have hAll := natural_induction_d hM pathValueSchema (pathEnv C m P) hC.omega
    (fun z hz => (pathValueSchema_iff hM.1 C m P z).mpr (by
      intro f a c hPath
      exact False.elim (hz C.zero (hPath.zero_in_length hM.1))))
    (fun p hp ih next hs => (pathValueSchema_iff hM.1 C m P next).mpr (by
      intro f a c hPath i x hix
      rcases hPath.peel_d hM hC with ⟨_,_,hSingle⟩ | ⟨last,g,b,hSucc,_,hG,hOld,hParent⟩
      · exact Or.inl (hSingle i x hix).2
      · have hpLast := Structure.SuccessorOf.predecessor_eq hM.1 ((omega_isOrdinal_d hM hC.omega).mem hp) hs hSucc
        subst last
        rcases (hs i).mp (hPath.graph.bounds hM.1 hix).1 with hip | hiEq
        · have hig := (hG.all_rows hM.1 hPath.graph i hip x).mpr hix
          rcases (pathValueSchema_iff hM.1 C m P p).mp ih g a b hOld i x hig with hxb | hxb
          · exact Or.inr (hxb ▸ hF.left c b hParent)
          · exact Or.inr (((omega_isOrdinal_d hM hC.omega).mem
              ((omega_isOrdinal_d hM hC.omega).transitive m hF.width c (hPath.end_bound hM.1))).transitive
                b (hF.left c b hParent) x hxb)
        · have hip := hM.1.eq_of_same_members i p hiEq
          subst i
          obtain ⟨l,hl,hLast,hFirst,hEnd⟩ := hPath.endpoints
          have hpl := Structure.SuccessorOf.predecessor_eq hM.1 ((omega_isOrdinal_d hM hC.omega).mem hp) hs hLast
          subst l
          exact Or.inl (hPath.graph.unique p x c hix hEnd)))
  exact (pathValueSchema_iff hM.1 C m P n).mp (hAll n h.length) f a c h

theorem ParentPath.endpoints_ordered_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {m P f n a c : M.Domain}
    (hF : Forest M C.omega m P) (h : ParentPath M C m P f n a c) : a=c ∨ M.mem a c := by
  obtain ⟨_,_,_,ha,_⟩ := h.endpoints
  exact h.values_below_last_d hM hC hF C.zero a ha

theorem ancestor_direct_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {m P a c : M.Domain}
    (hF : Forest M C.omega m P) (hParent : MemPair M P c a) : Ancestor M C m P a c := by
  obtain ⟨f,hPath⟩ := parent_path_singleton_d (P := P) hM hC (hF.bounds hM.1 hParent).2
  obtain ⟨n,g,_,hG⟩ := hPath.append_d hM hC (hF.bounds hM.1 hParent).1 hParent
  exact ⟨hF.left c a hParent,n,hG.length,g,hG.sequence_member_d hM hC hF.width,hG⟩

theorem ancestor_step_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {m P a b c : M.Domain}
    (hF : Forest M C.omega m P) (hAnc : Ancestor M C m P a b) (hParent : MemPair M P c b) :
    Ancestor M C m P a c := by
  obtain ⟨hab,n,_,f,_,hPath⟩ := hAnc
  obtain ⟨next,g,_,hG⟩ := hPath.append_d hM hC (hF.bounds hM.1 hParent).1 hParent
  have hcω := (omega_isOrdinal_d hM hC.omega).transitive m hF.width c (hF.bounds hM.1 hParent).1
  exact ⟨((omega_isOrdinal_d hM hC.omega).mem hcω).transitive b (hF.left c b hParent) a hab,
    next,hG.length,g,hG.sequence_member_d hM hC hF.width,hG⟩

theorem ancestor_parent_cases_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {m P a c : M.Domain}
    (hF : Forest M C.omega m P) (hAnc : Ancestor M C m P a c) :
    ∃ b, MemPair M P c b ∧ (a=b ∨ Ancestor M C m P a b) := by
  obtain ⟨hac,n,_,f,_,hPath⟩ := hAnc
  rcases hPath.peel_d hM hC with ⟨_,he,_⟩ | ⟨last,g,b,_,_,_,hG,hParent⟩
  · exact False.elim (SetTheory.KP.mem_irrefl_d (KP1Y.models_weakKP hM) c (he ▸ hac))
  · refine ⟨b,hParent,?_⟩
    rcases hG.endpoints_ordered_d hM hC hF with he | hab
    · exact Or.inl he
    · exact Or.inr ⟨hab,last,hG.length,g,hG.sequence_member_d hM hC hF.width,hG⟩

theorem Ancestor.bounds {M : SetTheory.Structure.{u}} (he : Extensional M)
    {C : ExpressionData M.Domain} {m P a c : M.Domain} (h : Ancestor M C m P a c) : M.mem a m ∧ M.mem c m := by
  obtain ⟨_,_,_,_,_,hPath⟩ := h
  exact ⟨hPath.start_bound he,hPath.end_bound he⟩

theorem no_ancestor_of_no_parent_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {m P a c : M.Domain}
    (hF : Forest M C.omega m P) (hNo : NoParent M m P c) : ¬Ancestor M C m P a c := by
  intro hAnc
  obtain ⟨b,hb,_⟩ := ancestor_parent_cases_d hM hC hF hAnc
  exact hNo b (hF.bounds hM.1 hb).2 hb

theorem root_of_no_parent_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {m P c q : M.Domain}
    (hF : Forest M C.omega m P) (hNo : NoParent M m P c) (h : Root M C m P c q) : q=c := by
  rcases h.2.2 with he | hAnc
  · exact he
  · exact False.elim (no_ancestor_of_no_parent_d hM hC hF hNo hAnc)

theorem root_parent_iff_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {m P c p q : M.Domain}
    (hF : Forest M C.omega m P) (hParent : MemPair M P c p) :
    Root M C m P c q ↔ Root M C m P p q := by
  constructor
  · rintro ⟨hq,hNo,he | hAnc⟩
    · subst q
      exact False.elim (hNo p (hF.bounds hM.1 hParent).2 hParent)
    · obtain ⟨p',hp',hqPath⟩ := ancestor_parent_cases_d hM hC hF hAnc
      have hp'p := hF.unique c p' p hp' hParent
      subst p'
      exact ⟨hq,hNo,hqPath⟩
  · rintro ⟨hq,hNo,hqp⟩
    refine ⟨hq,hNo,Or.inr ?_⟩
    rcases hqp with he | hAnc
    · subst q
      exact ancestor_direct_d hM hC hF hParent
    · exact ancestor_step_d hM hC hF hAnc hParent

private def rootExistenceSchema : Project.UnarySchema 7 where
  body := .imp (.mem (.bound 0) (.bound 2)) (Project.Formula.existsMem (.bound 2)
    (rootFormula ⟨.bound 8,.bound 7,.bound 6,.bound 5,.bound 4⟩ (.bound 3) (.bound 2) (.bound 1) (.bound 0)))
  freeClosed := by
    have hRoot := rootFormula_freeClosed
      (show (⟨.bound 8,.bound 7,.bound 6,.bound 5,.bound 4⟩ : ExpressionData (Project.Term 9)).Closed from ⟨rfl,rfl,rfl,rfl,rfl⟩)
      (.bound 3) (.bound 2) (.bound 1) (.bound 0) rfl rfl rfl rfl
    simp [Definitional.Formula.FreeClosed,Project.Formula.existsMem,hRoot]

private theorem rootExistenceSchema_iff {M : SetTheory.Structure.{u}} (he : Extensional M)
    (C : ExpressionData M.Domain) (m P c : M.Domain) :
    Project.Formula.satisfies ((pathEnv C m P).push c) rootExistenceSchema.body ↔
      (M.mem c m → ∃ q, Root M C m P c q) := by
  simp only [rootExistenceSchema,Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_mem_iff,
    Project.Formula.satisfies_existsMem_iff,rootFormula_iff he]
  exact ⟨fun h hc => by obtain ⟨q,_,hq⟩ := h hc; exact ⟨q,hq⟩,
    fun h hc => by obtain ⟨q,hq⟩ := h hc; exact ⟨q,hq.1,hq⟩⟩

theorem root_exists_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {m P c : M.Domain}
    (hF : Forest M C.omega m P) (hc : M.mem c m) : ∃ q, Root M C m P c q := by
  classical
  have hAll := KP1Y.induction_d hM rootExistenceSchema (pathEnv C m P)
    (fun c ih => (rootExistenceSchema_iff hM.1 C m P c).mpr (by
      intro hc
      by_cases hNo : NoParent M m P c
      · exact ⟨c,hc,hNo,Or.inl rfl⟩
      · have hSome : ∃ p, M.mem p m ∧ MemPair M P c p := by
          apply Classical.byContradiction
          intro hNone
          exact hNo (fun p hp hcp => hNone ⟨p,hp,hcp⟩)
        obtain ⟨p,hp,hcp⟩ := hSome
        obtain ⟨q,hq⟩ := (rootExistenceSchema_iff hM.1 C m P p).mp (ih p (hF.left c p hcp)) hp
        exact ⟨q,(root_parent_iff_d hM hC hF hcp).mpr hq⟩))
  exact (rootExistenceSchema_iff hM.1 C m P c).mp (hAll c) hc

private def rootUniqueSchema : Project.UnarySchema 7 where
  body := .forallE (.forallE (.imp
    (.conj (rootFormula ⟨.bound 9,.bound 8,.bound 7,.bound 6,.bound 5⟩ (.bound 4) (.bound 3) (.bound 2) (.bound 1))
      (rootFormula ⟨.bound 9,.bound 8,.bound 7,.bound 6,.bound 5⟩ (.bound 4) (.bound 3) (.bound 2) (.bound 0)))
    (Project.Formula.extensionalEq (.bound 1) (.bound 0))))
  freeClosed := by
    have hC : (⟨.bound 9,.bound 8,.bound 7,.bound 6,.bound 5⟩ : ExpressionData (Project.Term 10)).Closed := ⟨rfl,rfl,rfl,rfl,rfl⟩
    have hL := rootFormula_freeClosed hC (.bound 4) (.bound 3) (.bound 2) (.bound 1) rfl rfl rfl rfl
    have hR := rootFormula_freeClosed hC (.bound 4) (.bound 3) (.bound 2) (.bound 0) rfl rfl rfl rfl
    simp [Definitional.Formula.FreeClosed,hL,hR]

private theorem rootUniqueSchema_iff {M : SetTheory.Structure.{u}} (he : Extensional M)
    (C : ExpressionData M.Domain) (m P c : M.Domain) :
    Project.Formula.satisfies ((pathEnv C m P).push c) rootUniqueSchema.body ↔
      ∀ q r, Root M C m P c q → Root M C m P c r → q=r := by
  simp only [rootUniqueSchema,Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_imp_iff,
    Project.Formula.satisfies_conj_iff,rootFormula_iff he,Project.Formula.satisfies_extensionalEq_iff_eq he]
  exact ⟨fun h q r hq hr => h q r ⟨hq,hr⟩,fun h q r hs => h q r hs.1 hs.2⟩

theorem root_unique_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {m P c q r : M.Domain}
    (hF : Forest M C.omega m P) (hq : Root M C m P c q) (hr : Root M C m P c r) : q=r := by
  classical
  have hAll := KP1Y.induction_d hM rootUniqueSchema (pathEnv C m P)
    (fun c ih => (rootUniqueSchema_iff hM.1 C m P c).mpr (by
      intro q r hq hr
      by_cases hNo : NoParent M m P c
      · exact (root_of_no_parent_d hM hC hF hNo hq).trans (root_of_no_parent_d hM hC hF hNo hr).symm
      · have hSome : ∃ p, M.mem p m ∧ MemPair M P c p := by
          apply Classical.byContradiction
          intro hNone
          exact hNo (fun p hp hcp => hNone ⟨p,hp,hcp⟩)
        obtain ⟨p,_,hcp⟩ := hSome
        exact (rootUniqueSchema_iff hM.1 C m P p).mp (ih p (hF.left c p hcp)) q r
          ((root_parent_iff_d hM hC hF hcp).mp hq) ((root_parent_iff_d hM hC hF hcp).mp hr)))
  exact (rootUniqueSchema_iff hM.1 C m P c).mp (hAll c) q r hq hr

private def rootGraphSchema : Project.Delta0BinarySchema 7 where
  body := rootFormula ⟨.bound 8,.bound 7,.bound 6,.bound 5,.bound 4⟩ (.bound 3) (.bound 2) (.bound 1) (.bound 0)
  freeClosed := rootFormula_freeClosed ⟨rfl,rfl,rfl,rfl,rfl⟩ _ _ _ _ rfl rfl rfl rfl
  delta0 := rootFormula_delta0 _ _ _ _ _

private theorem rootGraphSchema_iff {M : SetTheory.Structure.{u}} (he : Extensional M)
    (C : ExpressionData M.Domain) (m P c q : M.Domain) :
    Project.Formula.satisfies (((pathEnv C m P).push c).push q) rootGraphSchema.body ↔ Root M C m P c q := by
  rw [rootGraphSchema,rootFormula_iff he]
  rfl

theorem root_graph_exists_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {m P : M.Domain} (hF : Forest M C.omega m P) :
    ∃ Q, Graph M Q m m ∧ ∀ c q, MemPair M Q c q ↔ Root M C m P c q := by
  obtain ⟨Q,hSupport,hQ⟩ := relation_comprehension_d hM rootGraphSchema (pathEnv C m P) m m
  have hRows : ∀ c q, MemPair M Q c q ↔ Root M C m P c q := by
    intro c q
    have h := hQ c q
    rw [rootGraphSchema_iff hM.1] at h
    refine h.trans ⟨fun h => h.2.2,fun h => ⟨?_,h.1,h⟩⟩
    rcases h.2.2 with he | hAnc
    · exact he ▸ h.1
    · exact (hAnc.bounds hM.1).2
  refine ⟨Q,⟨hSupport,?_,?_⟩,hRows⟩
  · intro c hc
    obtain ⟨q,hq⟩ := root_exists_d hM hC hF hc
    exact ⟨q,hq.1,(hRows c q).mpr hq⟩
  · intro c q r hcq hcr
    exact root_unique_d hM hC hF ((hRows c q).mp hcq) ((hRows c r).mp hcr)

theorem root_parent_same_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {m P c p q r : M.Domain}
    (hF : Forest M C.omega m P) (hParent : MemPair M P c p)
    (hq : Root M C m P c q) (hr : Root M C m P p r) : q=r :=
  root_unique_d hM hC hF ((root_parent_iff_d hM hC hF hParent).mp hq) hr

private def indexValueSchema : Project.UnarySchema 1 where
  body := .forallE (.imp (memPairFormula (.bound 2) (.bound 1) (.bound 0))
    (.disj (Project.Formula.extensionalEq (.bound 1) (.bound 0)) (.mem (.bound 1) (.bound 0))))
  freeClosed := by
    simp [memPairFormula,codeFormula,pairFormula,Project.Formula.forallMem,Project.Formula.existsMem,Definitional.Formula.FreeClosed]

private theorem indexValueSchema_iff {M : SetTheory.Structure.{u}} (he : Extensional M) (f i : M.Domain) :
    Project.Formula.satisfies ((oneEnv f).push i) indexValueSchema.body ↔
      ∀ x, MemPair M f i x → i=x ∨ M.mem i x := by
  simp only [indexValueSchema,Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_imp_iff,
    memPairFormula_iff he,Project.Formula.satisfies_disj_iff,
    Project.Formula.satisfies_extensionalEq_iff_eq he,Project.Formula.satisfies_mem_iff]
  rfl

theorem ParentPath.index_le_value_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {m P f n a c : M.Domain}
    (hF : Forest M C.omega m P) (h : ParentPath M C m P f n a c) :
    ∀ i x, MemPair M f i x → i=x ∨ M.mem i x := by
  have hwOrd := omega_isOrdinal_d hM hC.omega
  have hnOrd := hwOrd.mem h.length
  have hAll := KP1Y.induction_d hM indexValueSchema (oneEnv f)
    (fun i ih => (indexValueSchema_iff hM.1 f i).mpr (by
      intro y hiy
      have hi := (h.graph.bounds hM.1 hiy).1
      have hiw := hwOrd.transitive n h.length i hi
      have hyw := hwOrd.transitive m hF.width y (h.graph.bounds hM.1 hiy).2
      rcases natural_cases hM hC.omega hiw with he | ⟨j,_,hs⟩
      · have hiz := hM.1.eq_of_same_members i C.zero (fun x => iff_of_false (he x) (hC.zero_empty x))
        subst i
        by_cases hyz : y=C.zero
        · exact Or.inl hyz.symm
        · exact Or.inr ((hC.zero_mem_iff hM hyw).mpr hyz)
      · have hjn := hnOrd.transitive i hi j hs.predecessor_mem
        obtain ⟨x,_,hjx⟩ := h.graph.total j hjn
        have hjxLe := (indexValueSchema_iff hM.1 f j).mp (ih j hs.predecessor_mem) x hjx
        have hxy := hF.left y x (h.edges j i x y hjn hi hjx hiy hs)
        have hjy : M.mem j y := by
          rcases hjxLe with he | hjx
          · exact he ▸ hxy
          · exact (hwOrd.mem hyw).transitive x hxy j hjx
        have hSub : M.MemberSubset i y := by
          intro v hv
          rcases (hs v).mp hv with hvj | hvj
          · exact (hwOrd.mem hyw).transitive j hjy v hvj
          · exact (hM.1.eq_of_same_members v j hvj) ▸ hjy
        exact ordinal_subset_cases_d hM (hwOrd.mem hiw) (hwOrd.mem hyw) hSub))
  exact fun i => (indexValueSchema_iff hM.1 f i).mp (hAll i)

/-- 路径的内部长度至多是末列 c 的后继；没有借用外部有限性。 -/
theorem ParentPath.length_bound_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {m P f n a c : M.Domain}
    (hF : Forest M C.omega m P) (h : ParentPath M C m P f n a c) :
    ∃ s, M.mem s C.omega ∧ M.SuccessorOf s c ∧ M.MemberSubset n s := by
  have hwOrd := omega_isOrdinal_d hM hC.omega
  have hcω := hwOrd.transitive m hF.width c (h.end_bound hM.1)
  obtain ⟨s,hs,hsω⟩ := hC.omega.1.2 c hcω
  obtain ⟨last,_,hLast,_,hEnd⟩ := h.endpoints
  have hlc := h.index_le_value_d hM hC hF last c hEnd
  refine ⟨s,hsω,hs,?_⟩
  intro i hi
  rcases (hLast i).mp hi with hiLast | hiEq
  · apply (hs i).mpr ∘ Or.inl
    rcases hlc with he | hlc
    · exact he ▸ hiLast
    · exact (hwOrd.mem hcω).transitive last hlc i hiLast
  · have hil := hM.1.eq_of_same_members i last hiEq
    subst i
    rcases hlc with he | hlc
    · exact he.symm ▸ hs.predecessor_mem
    · exact (hs last).mpr (Or.inl hlc)

/-- 深度 d 是从根到 c 的内部有限父链的边数（路径长度为 d+1）。 -/
def Depth (M : SetTheory.Structure.{u}) (C : ExpressionData M.Domain) (m P c d : M.Domain) : Prop :=
  M.mem d C.omega ∧ ∃ q, M.mem q m ∧ ∃ n, M.mem n C.omega ∧ ∃ f, M.mem f C.sequences ∧
    NoParent M m P q ∧ ParentPath M C m P f n q c ∧ M.SuccessorOf n d

def depthFormula {n : Nat} (C : ExpressionData (Project.Term n)) (m P c d : Project.Term n) : Project.Formula 1 n :=
  .conj (.mem d C.omega) (Project.Formula.existsMem m (Project.Formula.existsMem C.omega.weaken
    (Project.Formula.existsMem C.sequences.weaken.weaken
      (.conj (noParentFormula m.weaken.weaken.weaken P.weaken.weaken.weaken (.bound 2))
        (.conj (parentPathFormula C.weaken.weaken.weaken m.weaken.weaken.weaken P.weaken.weaken.weaken
          (.bound 0) (.bound 1) (.bound 2) c.weaken.weaken.weaken)
          (successorFormula (.bound 1) d.weaken.weaken.weaken))))))

theorem depthFormula_delta0 {n : Nat} (C : ExpressionData (Project.Term n)) (m P c d : Project.Term n) :
    (depthFormula C m P c d).IsDelta0 :=
  .conj (.mem _ _) (.existsMem _ (.existsMem _ (.existsMem _ (.conj (noParentFormula_delta0 _ _ _)
    (.conj (parentPathFormula_delta0 _ _ _ _ _ _ _) (successorFormula_delta0 _ _))))))

theorem depthFormula_freeClosed {n : Nat} {C : ExpressionData (Project.Term n)} (hC : C.Closed)
    (m P c d : Project.Term n) (hm : m.freeSupport=[]) (hP : P.freeSupport=[])
    (hc : c.freeSupport=[]) (hd : d.freeSupport=[]) : (depthFormula C m P c d).FreeClosed := by
  have hPath := parentPathFormula_freeClosed hC.weaken.weaken.weaken m.weaken.weaken.weaken P.weaken.weaken.weaken
    (.bound 0) (.bound 1) (.bound 2) c.weaken.weaken.weaken (by simpa using hm) (by simpa using hP)
    rfl rfl rfl (by simpa using hc)
  simp [depthFormula,noParentFormula,memPairFormula,codeFormula,pairFormula,successorFormula,
    Project.Formula.forallMem,Project.Formula.existsMem,Definitional.Formula.FreeClosed,
    hC.omega,hC.sequences,hm,hP,hd,hPath]

theorem depthFormula_iff {M : SetTheory.Structure.{u}} (he : Extensional M) {n : Nat}
    (e : Env M n) (C : ExpressionData (Project.Term n)) (m P c d : Project.Term n) :
    Project.Formula.satisfies e (depthFormula C m P c d) ↔
      Depth M (C.eval e) (m.eval e) (P.eval e) (c.eval e) (d.eval e) := by
  simp only [depthFormula,Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_mem_iff,
    Project.Formula.satisfies_existsMem_iff,noParentFormula_iff he,parentPathFormula_iff he,
    successorFormula_iff he,ExpressionData.eval_weaken,Term.eval_weaken]
  rfl

theorem Depth.column_bound {M : SetTheory.Structure.{u}} (he : Extensional M)
    {C : ExpressionData M.Domain} {m P c d : M.Domain} (h : Depth M C m P c d) : M.mem c m := by
  obtain ⟨_,_,_,_,_,_,_,_,hPath,_⟩ := h
  exact hPath.end_bound he

theorem depth_le_column_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {m P c d : M.Domain}
    (hF : Forest M C.omega m P) (h : Depth M C m P c d) : d=c ∨ M.mem d c := by
  obtain ⟨hd,_,_,n,_,f,_,_,hPath,hs⟩ := h
  obtain ⟨last,_,hLast,_,hEnd⟩ := hPath.endpoints
  have hdl := Structure.SuccessorOf.predecessor_eq hM.1 ((omega_isOrdinal_d hM hC.omega).mem hd) hs hLast
  subst last
  exact hPath.index_le_value_d hM hC hF d c hEnd

theorem depth_exists_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {m P c : M.Domain}
    (hF : Forest M C.omega m P) (hc : M.mem c m) : ∃ d, Depth M C m P c d := by
  obtain ⟨q,hq,hNo,hEq | hAnc⟩ := root_exists_d hM hC hF hc
  · subst q
    obtain ⟨f,hPath⟩ := parent_path_singleton_d (P := P) hM hC hc
    exact ⟨C.zero,hC.zero_nat,c,hc,C.one,hC.one_nat,f,hPath.sequence_member_d hM hC hF.width,hNo,hPath,hC.one_succ⟩
  · obtain ⟨_,n,hn,f,hf,hPath⟩ := hAnc
    obtain ⟨d,hd,hs,_,_⟩ := hPath.endpoints
    exact ⟨d,(omega_isOrdinal_d hM hC.omega).transitive n hn d hd,q,hq,n,hn,f,hf,hNo,hPath,hs⟩

theorem depth_of_no_parent_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {m P c d : M.Domain}
    (hF : Forest M C.omega m P) (hNo : NoParent M m P c) (h : Depth M C m P c d) : d=C.zero := by
  obtain ⟨hd,_,_,n,_,_,_,_,hPath,hs⟩ := h
  rcases hPath.peel_d hM hC with ⟨hn,_,_⟩ | ⟨_,_,b,_,_,_,_,hParent⟩
  · subst n
    exact Structure.SuccessorOf.predecessor_eq hM.1 ((omega_isOrdinal_d hM hC.omega).mem hd) hs hC.one_succ
  · exact False.elim (hNo b (hF.bounds hM.1 hParent).2 hParent)

theorem depth_parent_predecessor_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {m P c p d : M.Domain}
    (hF : Forest M C.omega m P) (hParent : MemPair M P c p) (h : Depth M C m P c d) :
    ∃ e, Depth M C m P p e ∧ M.SuccessorOf d e := by
  obtain ⟨hd,q,hq,n,_,_,_,hNo,hPath,hs⟩ := h
  rcases hPath.peel_d hM hC with ⟨_,he,_⟩ | ⟨last,g,b,hLast,_,_,hG,hcb⟩
  · subst q
    exact False.elim (hNo p (hF.bounds hM.1 hParent).2 hParent)
  · have hbp := hF.unique c b p hcb hParent
    subst b
    have hdl := Structure.SuccessorOf.predecessor_eq hM.1 ((omega_isOrdinal_d hM hC.omega).mem hd) hs hLast
    subst last
    obtain ⟨e,he,heSucc,_,_⟩ := hG.endpoints
    exact ⟨e,⟨(omega_isOrdinal_d hM hC.omega).transitive d hG.length e he,
      q,hq,d,hG.length,g,hG.sequence_member_d hM hC hF.width,hNo,hG,heSucc⟩,heSucc⟩

private def depthUniqueSchema : Project.UnarySchema 7 where
  body := .forallE (.forallE (.imp
    (.conj (depthFormula ⟨.bound 9,.bound 8,.bound 7,.bound 6,.bound 5⟩ (.bound 4) (.bound 3) (.bound 2) (.bound 1))
      (depthFormula ⟨.bound 9,.bound 8,.bound 7,.bound 6,.bound 5⟩ (.bound 4) (.bound 3) (.bound 2) (.bound 0)))
    (Project.Formula.extensionalEq (.bound 1) (.bound 0))))
  freeClosed := by
    have hC : (⟨.bound 9,.bound 8,.bound 7,.bound 6,.bound 5⟩ : ExpressionData (Project.Term 10)).Closed := ⟨rfl,rfl,rfl,rfl,rfl⟩
    have hL := depthFormula_freeClosed hC (.bound 4) (.bound 3) (.bound 2) (.bound 1) rfl rfl rfl rfl
    have hR := depthFormula_freeClosed hC (.bound 4) (.bound 3) (.bound 2) (.bound 0) rfl rfl rfl rfl
    simp [Definitional.Formula.FreeClosed,hL,hR]

private theorem depthUniqueSchema_iff {M : SetTheory.Structure.{u}} (he : Extensional M)
    (C : ExpressionData M.Domain) (m P c : M.Domain) :
    Project.Formula.satisfies ((pathEnv C m P).push c) depthUniqueSchema.body ↔
      ∀ d e, Depth M C m P c d → Depth M C m P c e → d=e := by
  simp only [depthUniqueSchema,Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_imp_iff,
    Project.Formula.satisfies_conj_iff,depthFormula_iff he,Project.Formula.satisfies_extensionalEq_iff_eq he]
  exact ⟨fun h d e hd he => h d e ⟨hd,he⟩,fun h d e hs => h d e hs.1 hs.2⟩

theorem depth_unique_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {m P c d e : M.Domain}
    (hF : Forest M C.omega m P) (hd : Depth M C m P c d) (he : Depth M C m P c e) : d=e := by
  classical
  have hAll := KP1Y.induction_d hM depthUniqueSchema (pathEnv C m P)
    (fun c ih => (depthUniqueSchema_iff hM.1 C m P c).mpr (by
      intro d e hd he
      by_cases hNo : NoParent M m P c
      · exact (depth_of_no_parent_d hM hC hF hNo hd).trans (depth_of_no_parent_d hM hC hF hNo he).symm
      · have hSome : ∃ p, M.mem p m ∧ MemPair M P c p := by
          apply Classical.byContradiction
          intro hNone
          exact hNo (fun p hp hcp => hNone ⟨p,hp,hcp⟩)
        obtain ⟨p,_,hcp⟩ := hSome
        obtain ⟨d',hd',hdSucc⟩ := depth_parent_predecessor_d hM hC hF hcp hd
        obtain ⟨e',he',heSucc⟩ := depth_parent_predecessor_d hM hC hF hcp he
        have hde := (depthUniqueSchema_iff hM.1 C m P p).mp (ih p (hF.left c p hcp)) d' e' hd' he'
        subst e'
        exact Structure.SuccessorOf.eq hM.1 hdSucc heSucc))
  exact (depthUniqueSchema_iff hM.1 C m P c).mp (hAll c) d e hd he

theorem depth_parent_successor_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {m P c p d e : M.Domain}
    (hF : Forest M C.omega m P) (hParent : MemPair M P c p)
    (hd : Depth M C m P c d) (he : Depth M C m P p e) : M.SuccessorOf d e := by
  obtain ⟨e',he',hs⟩ := depth_parent_predecessor_d hM hC hF hParent hd
  exact depth_unique_d hM hC hF he' he ▸ hs

theorem depth_zero_iff_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {m P c d : M.Domain}
    (hF : Forest M C.omega m P) (h : Depth M C m P c d) : d=C.zero ↔ NoParent M m P c := by
  constructor
  · intro hd p _ hParent
    obtain ⟨e,_,hs⟩ := depth_parent_predecessor_d hM hC hF hParent h
    exact hC.zero_empty e (hd ▸ hs.predecessor_mem)
  · exact fun hNo => depth_of_no_parent_d hM hC hF hNo h

private def depthGraphSchema : Project.Delta0BinarySchema 7 where
  body := depthFormula ⟨.bound 8,.bound 7,.bound 6,.bound 5,.bound 4⟩ (.bound 3) (.bound 2) (.bound 1) (.bound 0)
  freeClosed := depthFormula_freeClosed ⟨rfl,rfl,rfl,rfl,rfl⟩ _ _ _ _ rfl rfl rfl rfl
  delta0 := depthFormula_delta0 _ _ _ _ _

private theorem depthGraphSchema_iff {M : SetTheory.Structure.{u}} (he : Extensional M)
    (C : ExpressionData M.Domain) (m P c d : M.Domain) :
    Project.Formula.satisfies (((pathEnv C m P).push c).push d) depthGraphSchema.body ↔ Depth M C m P c d := by
  rw [depthGraphSchema,depthFormula_iff he]
  rfl

theorem depth_graph_exists_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {m P : M.Domain} (hF : Forest M C.omega m P) :
    ∃ D, Graph M D m m ∧ ∀ c d, MemPair M D c d ↔ Depth M C m P c d := by
  obtain ⟨D,hSupport,hD⟩ := relation_comprehension_d hM depthGraphSchema (pathEnv C m P) m m
  have hRows : ∀ c d, MemPair M D c d ↔ Depth M C m P c d := by
    intro c d
    have h := hD c d
    rw [depthGraphSchema_iff hM.1] at h
    refine h.trans ⟨fun h => h.2.2,fun h => ⟨h.column_bound hM.1,?_,h⟩⟩
    rcases depth_le_column_d hM hC hF h with he | hdc
    · exact he ▸ h.column_bound hM.1
    · exact ((omega_isOrdinal_d hM hC.omega).mem hF.width).transitive c (h.column_bound hM.1) d hdc
  refine ⟨D,⟨hSupport,?_,?_⟩,hRows⟩
  · intro c hc
    obtain ⟨d,hd⟩ := depth_exists_d hM hC hF hc
    have hdm : M.mem d m := by
      rcases depth_le_column_d hM hC hF hd with he | hdc
      · exact he ▸ hc
      · exact ((omega_isOrdinal_d hM hC.omega).mem hF.width).transitive c hc d hdc
    exact ⟨d,hdm,(hRows c d).mpr hd⟩
  · intro c d e hcd hce
    exact depth_unique_d hM hC hF ((hRows c d).mp hcd) ((hRows c e).mp hce)

end KP1Y.OneYFinite
