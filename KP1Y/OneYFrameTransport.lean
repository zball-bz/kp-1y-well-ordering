import KP1Y.OneYForestPaths
import KP1Y.AssignmentTuple

/-! 内部有限帧的截断父图与严格列嵌入运输。父图通过真实 Δ₀ 编码构造，保持性由构造证明。 -/
namespace KP1Y.OneYFinite
open YesMetaZFC YesMetaZFC.SetTheory YesMetaZFC.SetTheory.Definitional
open KP1Y.Kuratowski KP1Y.Functions KP1Y.Assignments KP1Y.Naturals KP1Y.Bounded
universe u

/-- cutoff 前为线性前驱，之后采用给定森林；自然数 0 的父始终不存在。 -/
def CutoffForest (M : SetTheory.Structure.{u}) (m P k Q : M.Domain) : Prop :=
  ∀ c p, MemPair M Q c p ↔ M.mem c m ∧ M.mem p m ∧
    ((M.mem c k ∧ M.SuccessorOf c p) ∨ (¬M.mem c k ∧ MemPair M P c p))

private def cutoffSchema : Project.Delta0BinarySchema 2 where
  body := .disj (.conj (.mem (.bound 1) (.bound 2)) (successorFormula (.bound 1) (.bound 0)))
    (.conj (.neg (.mem (.bound 1) (.bound 2))) (memPairFormula (.bound 3) (.bound 1) (.bound 0)))
  freeClosed := by
    simp [successorFormula,memPairFormula,codeFormula,pairFormula,Project.Formula.forallMem,
      Project.Formula.existsMem,Definitional.Formula.FreeClosed]
  delta0 := .disj (.conj (.mem _ _) (successorFormula_delta0 _ _))
    (.conj (.neg (.mem _ _)) (memPairFormula_delta0 _ _ _))

theorem cutoff_forest_exists_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {m P : M.Domain}
    (hP : Forest M C.omega m P) (k : M.Domain) : ∃ Q, Forest M C.omega m Q ∧ CutoffForest M m P k Q := by
  have hφ (c p : M.Domain) : Project.Formula.satisfies ((((oneEnv P).push k).push c).push p) cutoffSchema.body ↔
      (M.mem c k ∧ M.SuccessorOf c p) ∨ (¬M.mem c k ∧ MemPair M P c p) := by
    simp only [cutoffSchema,Project.Formula.satisfies_disj_iff,Project.Formula.satisfies_conj_iff,
      Project.Formula.satisfies_neg_iff,Project.Formula.satisfies_mem_iff,successorFormula_iff hM.1,memPairFormula_iff hM.1]
    rfl
  obtain ⟨Q,hSupport,hRaw⟩ := relation_comprehension_d hM cutoffSchema ((oneEnv P).push k) m m
  have hRows : CutoffForest M m P k Q := fun c p => by simpa only [hφ] using hRaw c p
  refine ⟨Q,⟨hP.width,hSupport,?_,?_⟩,hRows⟩
  · intro c p q hcp hcq
    obtain ⟨_,hp,hpCases⟩ := (hRows c p).mp hcp
    obtain ⟨_,_,hqCases⟩ := (hRows c q).mp hcq
    rcases hpCases with ⟨hc,hpS⟩ | ⟨hc,hpP⟩ <;> rcases hqCases with ⟨hc',hqS⟩ | ⟨hc',hqP⟩
    · exact Structure.SuccessorOf.predecessor_eq hM.1
        ((omega_isOrdinal_d hM hC.omega).mem ((omega_isOrdinal_d hM hC.omega).transitive m hP.width p hp)) hpS hqS
    · exact False.elim (hc' hc)
    · exact False.elim (hc hc')
    · exact hP.unique c p q hpP hqP
  · intro c p hcp
    rcases ((hRows c p).mp hcp).2.2 with ⟨_,hpS⟩ | ⟨_,hpP⟩
    · exact hpS.predecessor_mem
    · exact hP.left c p hpP

theorem cutoff_parent_before {M : SetTheory.Structure.{u}} {m P k Q c p : M.Domain}
    (hQ : CutoffForest M m P k Q) (hc : M.mem c k) :
    MemPair M Q c p ↔ M.mem c m ∧ M.mem p m ∧ M.SuccessorOf c p := by
  rw [hQ c p]
  simp only [hc,true_and,not_true_eq_false,false_and,or_false]

theorem cutoff_parent_after {M : SetTheory.Structure.{u}} (he : Extensional M) {w m P k Q c p : M.Domain}
    (hP : Forest M w m P) (hQ : CutoffForest M m P k Q) (hc : ¬M.mem c k) :
    MemPair M Q c p ↔ MemPair M P c p := by
  rw [hQ c p]
  simp only [hc,false_and,not_false_eq_true,true_and,false_or]
  exact ⟨fun h => h.2.2,fun h => ⟨(hP.bounds he h).1,(hP.bounds he h).2,h⟩⟩

theorem cutoff_terminal {M : SetTheory.Structure.{u}} (he : Extensional M) {w m P z Q : M.Domain}
    (hP : Forest M w m P) (hQ : CutoffForest M m P z Q) (hz : ∀ c, ¬M.mem c z) :
    ∀ c p, MemPair M Q c p ↔ MemPair M P c p := fun c _ => cutoff_parent_after he hP hQ (hz c)

theorem cutoff_step_other {M : SetTheory.Structure.{u}} (he : Extensional M) {m P k next Q R c : M.Domain}
    (hs : M.SuccessorOf next k) (hQ : CutoffForest M m P k Q) (hR : CutoffForest M m P next R)
    (hNot : c≠k) : ∀ p, MemPair M Q c p ↔ MemPair M R c p := by
  have hSame : M.mem c next ↔ M.mem c k := by
    constructor
    · intro hc
      rcases (hs c).mp hc with hc | hEq
      · exact hc
      · exact False.elim (hNot (he.eq_of_same_members c k hEq))
    · intro hc
      exact (hs c).mpr (Or.inl hc)
  intro p
  rw [hQ c p,hR c p,hSame]

structure ColumnEmbedding (M : SetTheory.Structure.{u}) (m n J : M.Domain) : Prop where
  graph : Graph M J m n
  strict : ∀ a, M.mem a m → ∀ c, M.mem c m → M.mem a c →
    ∀ x y, MemPair M J a x → MemPair M J c y → M.mem x y

theorem ColumnEmbedding.injective_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {w m n J : M.Domain} (hw : M.IsOmega w) (hm : M.mem m w) (hJ : ColumnEmbedding M m n J)
    {a c x : M.Domain} (ha : MemPair M J a x) (hc : MemPair M J c x) : a=c := by
  have haM := (hJ.graph.bounds hM.1 ha).1
  have hcM := (hJ.graph.bounds hM.1 hc).1
  rcases ((omega_isOrdinal_d hM hw).mem hm).wellOrder.linear.compare a haM c hcM with he | hac | hca
  · exact hM.1.eq_of_same_members a c he
  · exact False.elim (SetTheory.KP.mem_irrefl_d (KP1Y.models_weakKP hM) x (hJ.strict a haM c hcM hac x x ha hc))
  · exact False.elim (SetTheory.KP.mem_irrefl_d (KP1Y.models_weakKP hM) x (hJ.strict c hcM a haM hca x x hc ha))

/-- 目标父图就是原图两坐标经同一实际嵌入 J 取像，无额外边。 -/
def ForestTransport (M : SetTheory.Structure.{u}) (m P J Q : M.Domain) : Prop :=
  ∀ x y, MemPair M Q x y ↔ ∃ c, M.mem c m ∧ ∃ p, M.mem p m ∧
    MemPair M P c p ∧ MemPair M J c x ∧ MemPair M J p y

private def transportSchema : Project.Delta0BinarySchema 3 where
  body := Project.Formula.existsMem (.bound 2) (Project.Formula.existsMem (.bound 3)
    (.conj (memPairFormula (.bound 6) (.bound 1) (.bound 0))
      (.conj (memPairFormula (.bound 5) (.bound 1) (.bound 3)) (memPairFormula (.bound 5) (.bound 0) (.bound 2)))))
  freeClosed := by
    simp [memPairFormula,codeFormula,pairFormula,Project.Formula.existsMem,Project.Formula.forallMem,Definitional.Formula.FreeClosed]
  delta0 := .existsMem _ (.existsMem _ (.conj (memPairFormula_delta0 _ _ _)
    (.conj (memPairFormula_delta0 _ _ _) (memPairFormula_delta0 _ _ _))))

theorem forest_transport_exists_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {m n P J : M.Domain}
    (hP : Forest M C.omega m P) (hn : M.mem n C.omega) (hJ : ColumnEmbedding M m n J) :
    ∃ Q, Forest M C.omega n Q ∧ ForestTransport M m P J Q := by
  let env := ((oneEnv P).push J).push m
  have hφ (x y : M.Domain) : Project.Formula.satisfies ((env.push x).push y) transportSchema.body ↔
      ∃ c, M.mem c m ∧ ∃ p, M.mem p m ∧ MemPair M P c p ∧ MemPair M J c x ∧ MemPair M J p y := by
    simp only [transportSchema,Project.Formula.satisfies_existsMem_iff,Project.Formula.satisfies_conj_iff,memPairFormula_iff hM.1]
    rfl
  obtain ⟨Q,hSupport,hRaw⟩ := relation_comprehension_d hM transportSchema env n n
  have hRows : ForestTransport M m P J Q := by
    intro x y
    have h := hRaw x y
    rw [hφ] at h
    refine h.trans ⟨fun h => h.2.2,?_⟩
    intro h
    obtain ⟨c,hc,p,hp,hcp,hcx,hpy⟩ := h
    exact ⟨(hJ.graph.bounds hM.1 hcx).2,(hJ.graph.bounds hM.1 hpy).2,c,hc,p,hp,hcp,hcx,hpy⟩
  refine ⟨Q,⟨hn,hSupport,?_,?_⟩,hRows⟩
  · intro x y z hxy hxz
    obtain ⟨c,_,p,_,hcp,hcx,hpy⟩ := (hRows x y).mp hxy
    obtain ⟨c',_,p',_,hcp',hcx',hpz⟩ := (hRows x z).mp hxz
    have hcc' := hJ.injective_d hM hC.omega hP.width hcx hcx'
    subst c'
    have hpp' := hP.unique c p p' hcp hcp'
    subst p'
    exact hJ.graph.unique p y z hpy hpz
  · intro x y hxy
    obtain ⟨c,hc,p,hp,hcp,hcx,hpy⟩ := (hRows x y).mp hxy
    exact hJ.strict p hp c hc (hP.left c p hcp) y x hpy hcx

theorem transported_parent_iff_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {m n P J Q c p x y : M.Domain}
    (hP : Forest M C.omega m P) (hJ : ColumnEmbedding M m n J) (hQ : ForestTransport M m P J Q)
    (hcx : MemPair M J c x) (hpy : MemPair M J p y) : MemPair M Q x y ↔ MemPair M P c p := by
  constructor
  · intro hxy
    obtain ⟨c',_,p',_,hcp,hcx',hpy'⟩ := (hQ x y).mp hxy
    have hcc' := hJ.injective_d hM hC.omega hP.width hcx hcx'
    have hpp' := hJ.injective_d hM hC.omega hP.width hpy hpy'
    subst c'
    subst p'
    exact hcp
  · intro hcp
    exact (hQ x y).mpr ⟨c,(hP.bounds hM.1 hcp).1,p,(hP.bounds hM.1 hcp).2,hcp,hcx,hpy⟩

theorem transported_no_parent_iff_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {m n P J Q c x : M.Domain}
    (hP : Forest M C.omega m P) (hJ : ColumnEmbedding M m n J) (hQ : ForestTransport M m P J Q)
    (hcx : MemPair M J c x) : NoParent M n Q x ↔ NoParent M m P c := by
  constructor
  · intro hNone p hp hcp
    obtain ⟨y,hy,hpy⟩ := hJ.graph.total p hp
    exact hNone y hy ((transported_parent_iff_d hM hC hP hJ hQ hcx hpy).mpr hcp)
  · intro hNone y _ hxy
    obtain ⟨c',_,p,hp,hcp,hcx',_⟩ := (hQ x y).mp hxy
    have hcc' := hJ.injective_d hM hC.omega hP.width hcx hcx'
    subst c'
    exact hNone p hp hcp

theorem ParentPath.transport_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} {m n P J Q f len a c x y : M.Domain}
    (hJ : Graph M J m n) (hQ : ForestTransport M m P J Q)
    (hPath : ParentPath M C m P f len a c) (hax : MemPair M J a x) (hcy : MemPair M J c y) :
    ∃ g, ParentPath M C n Q g len x y := by
  obtain ⟨g,hG⟩ := tuple_value_exists_d hM hPath.graph hJ
  obtain ⟨last,hl,hSucc,hFirst,hLast⟩ := hPath.endpoints
  refine ⟨g,hPath.length,hG.values,⟨last,hl,hSucc,?_,?_⟩,?_⟩
  · exact (hG.rows C.zero (hPath.graph.bounds hM.1 hFirst).1 a (hPath.graph.bounds hM.1 hFirst).2 x
      (hJ.bounds hM.1 hax).2 hFirst).mpr hax
  · exact (hG.rows last hl c (hPath.graph.bounds hM.1 hLast).2 y (hJ.bounds hM.1 hcy).2 hLast).mpr hcy
  · intro i j u v hi hj hIu hJv hs
    obtain ⟨a,ha,hIa⟩ := hPath.graph.total i hi
    obtain ⟨b,hb,hJb⟩ := hPath.graph.total j hj
    have hau := (hG.rows i hi a ha u (hG.values.bounds hM.1 hIu).2 hIa).mp hIu
    have hbv := (hG.rows j hj b hb v (hG.values.bounds hM.1 hJv).2 hJb).mp hJv
    exact (hQ v u).mpr ⟨b,hb,a,ha,hPath.edges i j a b hi hj hIa hJb hs,hbv,hau⟩

theorem ancestor_transport_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {m n P J Q a c x y : M.Domain}
    (hn : M.mem n C.omega) (hJ : ColumnEmbedding M m n J) (hQ : ForestTransport M m P J Q)
    (hAnc : Ancestor M C m P a c) (hax : MemPair M J a x) (hcy : MemPair M J c y) : Ancestor M C n Q x y := by
  obtain ⟨hac,len,_,f,_,hPath⟩ := hAnc
  obtain ⟨g,hG⟩ := hPath.transport_d hM hJ.graph hQ hax hcy
  have hSeq := (hC.sequences g).mpr ⟨len,hG.length,hG.graph.mono_values
    (fun z hz => (omega_isOrdinal_d hM hC.omega).transitive n hn z hz)⟩
  exact ⟨hJ.strict a (hJ.graph.bounds hM.1 hax).1 c (hJ.graph.bounds hM.1 hcy).1 hac x y hax hcy,len,hG.length,g,hSeq,hG⟩

private def pullbackCore {d : Nat} (C : ExpressionData (Project.Term d)) (m n P Q J len : Project.Term d) : Project.Formula 1 d :=
  Project.Formula.forallMem C.sequences (Project.Formula.forallMem m.weaken
    (Project.Formula.forallMem m.weaken.weaken (Project.Formula.forallMem n.weaken.weaken.weaken
      (Project.Formula.forallMem n.weaken.weaken.weaken.weaken
        (.imp (.conj (memPairFormula J.weaken.weaken.weaken.weaken.weaken (.bound 3) (.bound 1))
          (.conj (memPairFormula J.weaken.weaken.weaken.weaken.weaken (.bound 2) (.bound 0))
            (parentPathFormula C.weaken.weaken.weaken.weaken.weaken n.weaken.weaken.weaken.weaken.weaken
              Q.weaken.weaken.weaken.weaken.weaken (.bound 4) len.weaken.weaken.weaken.weaken.weaken (.bound 1) (.bound 0))))
          (Project.Formula.existsMem C.sequences.weaken.weaken.weaken.weaken.weaken
            (parentPathFormula C.weaken.weaken.weaken.weaken.weaken.weaken m.weaken.weaken.weaken.weaken.weaken.weaken
              P.weaken.weaken.weaken.weaken.weaken.weaken (.bound 0) len.weaken.weaken.weaken.weaken.weaken.weaken (.bound 4) (.bound 3))))))))

private def pullbackEnv {M : SetTheory.Structure.{u}} (C : ExpressionData M.Domain) (m n P Q J : M.Domain) : Env M 10 :=
  (((((((((oneEnv C.omega).push C.zero).push C.one).push C.sequences).push C.expressions).push m).push n).push P).push Q).push J

private def pullbackSchema : Project.UnarySchema 10 where
  body := pullbackCore ⟨.bound 10,.bound 9,.bound 8,.bound 7,.bound 6⟩ (.bound 5) (.bound 4) (.bound 3) (.bound 2) (.bound 1) (.bound 0)
  freeClosed := by
    simp [pullbackCore,parentPathFormula,ExpressionData.weaken,ExpressionData.map,graphFormula,
      successorFormula,memPairFormula,codeFormula,pairFormula,Project.Formula.forallMem,
      Project.Formula.existsMem,Definitional.Formula.FreeClosed]

private theorem pullbackSchema_iff {M : SetTheory.Structure.{u}} (he : Extensional M)
    (C : ExpressionData M.Domain) (m n P Q J len : M.Domain) :
    Project.Formula.satisfies ((pullbackEnv C m n P Q J).push len) pullbackSchema.body ↔
      ∀ f, M.mem f C.sequences → ∀ a, M.mem a m → ∀ c, M.mem c m →
        ∀ x, M.mem x n → ∀ y, M.mem y n →
          MemPair M J a x ∧ MemPair M J c y ∧ ParentPath M C n Q f len x y →
            ∃ g, M.mem g C.sequences ∧ ParentPath M C m P g len a c := by
  simp only [pullbackSchema,pullbackCore,Project.Formula.satisfies_forallMem_iff,
    Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_existsMem_iff,
    memPairFormula_iff he,parentPathFormula_iff he,ExpressionData.eval_weaken,Term.eval_weaken]
  rfl

/-- 目标路径逐步逆像为同长度源路径；对内部路径长度使用对象自然数归纳。 -/
theorem ParentPath.pullback_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {m n P J Q f len a c x y : M.Domain}
    (hP : Forest M C.omega m P) (hn : M.mem n C.omega)
    (hJ : ColumnEmbedding M m n J) (hQ : ForestTransport M m P J Q)
    (hPath : ParentPath M C n Q f len x y) (hax : MemPair M J a x) (hcy : MemPair M J c y) :
    ∃ g, ParentPath M C m P g len a c := by
  have hAll := natural_induction_d hM pullbackSchema (pullbackEnv C m n P Q J) hC.omega
    (fun zero hEmpty => (pullbackSchema_iff hM.1 C m n P Q J zero).mpr (by
      intro f _ a _ c _ x _ y _ hAnte
      exact False.elim (hEmpty C.zero (hAnte.2.2.zero_in_length hM.1))))
    (fun last hLast ih next hNext => (pullbackSchema_iff hM.1 C m n P Q J next).mpr (by
      intro f _ a ha c hc x hx y hy hAnte
      obtain ⟨hax,hcy,hPath⟩ := hAnte
      rcases hPath.peel_d hM hC with ⟨hOne,hxy,_⟩ | ⟨prev,g,b,hPrev,hPrevNat,_,hOld,hYb⟩
      · subst y
        have hac := hJ.injective_d hM hC.omega hP.width hax hcy
        subst c
        obtain ⟨g,hG⟩ := parent_path_singleton_d (P := P) hM hC ha
        have hG' : ParentPath M C m P g next a a := Eq.mpr (congrArg (fun l => ParentPath M C m P g l a a) hOne) hG
        exact ⟨g,hG'.sequence_member_d hM hC hP.width,hG'⟩
      · have hPrevLast := Structure.SuccessorOf.predecessor_eq hM.1 ((omega_isOrdinal_d hM hC.omega).mem hPrevNat) hPrev hNext
        subst prev
        obtain ⟨c',_,p,hp,hcp,hc'y,hpb⟩ := (hQ y b).mp hYb
        have hcc' := hJ.injective_d hM hC.omega hP.width hcy hc'y
        subst c'
        obtain ⟨source,_,hSource⟩ := (pullbackSchema_iff hM.1 C m n P Q J last).mp ih
          g (hOld.sequence_member_d hM hC hn) a ha p hp x hx b (hOld.end_bound hM.1) ⟨hax,hpb,hOld⟩
        obtain ⟨next',g',hNext',hG'⟩ := hSource.append_d hM hC hc hcp
        have hNextEq := Structure.SuccessorOf.eq hM.1 hNext' hNext
        subst next'
        exact ⟨g',hG'.sequence_member_d hM hC hP.width,hG'⟩))
  obtain ⟨g,_,hG⟩ := (pullbackSchema_iff hM.1 C m n P Q J len).mp (hAll len hPath.length)
    f (hPath.sequence_member_d hM hC hn) a (hJ.graph.bounds hM.1 hax).1 c (hJ.graph.bounds hM.1 hcy).1
      x (hJ.graph.bounds hM.1 hax).2 y (hJ.graph.bounds hM.1 hcy).2 ⟨hax,hcy,hPath⟩
  exact ⟨g,hG⟩

theorem transported_ancestor_iff_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {m n P J Q a c x y : M.Domain}
    (hP : Forest M C.omega m P) (hn : M.mem n C.omega)
    (hJ : ColumnEmbedding M m n J) (hQ : ForestTransport M m P J Q)
    (hax : MemPair M J a x) (hcy : MemPair M J c y) :
    Ancestor M C n Q x y ↔ Ancestor M C m P a c := by
  constructor
  · rintro ⟨hxy,len,_,f,_,hPath⟩
    obtain ⟨g,hG⟩ := hPath.pullback_d hM hC hP hn hJ hQ hax hcy
    have hac : M.mem a c := by
      rcases hG.endpoints_ordered_d hM hC hP with he | hac
      · subst c
        have hxyEq := hJ.graph.unique a x y hax hcy
        exact False.elim (SetTheory.KP.mem_irrefl_d (KP1Y.models_weakKP hM) y (hxyEq ▸ hxy))
      · exact hac
    exact ⟨hac,len,hG.length,g,hG.sequence_member_d hM hC hP.width,hG⟩
  · exact fun hAnc => ancestor_transport_d hM hC hn hJ hQ hAnc hax hcy

theorem transported_root_iff_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {m n P J Q a c x y : M.Domain}
    (hP : Forest M C.omega m P) (hn : M.mem n C.omega)
    (hJ : ColumnEmbedding M m n J) (hQ : ForestTransport M m P J Q)
    (hax : MemPair M J a x) (hcy : MemPair M J c y) : Root M C n Q y x ↔ Root M C m P c a := by
  constructor
  · rintro ⟨_,hNo,hRel⟩
    refine ⟨(hJ.graph.bounds hM.1 hax).1,(transported_no_parent_iff_d hM hC hP hJ hQ hax).mp hNo,?_⟩
    rcases hRel with he | hAnc
    · subst y
      exact Or.inl (hJ.injective_d hM hC.omega hP.width hax hcy)
    · exact Or.inr ((transported_ancestor_iff_d hM hC hP hn hJ hQ hax hcy).mp hAnc)
  · rintro ⟨_,hNo,hRel⟩
    refine ⟨(hJ.graph.bounds hM.1 hax).2,(transported_no_parent_iff_d hM hC hP hJ hQ hax).mpr hNo,?_⟩
    rcases hRel with he | hAnc
    · subst c
      exact Or.inl (hJ.graph.unique a x y hax hcy)
    · exact Or.inr ((transported_ancestor_iff_d hM hC hP hn hJ hQ hax hcy).mpr hAnc)

theorem depth_transport_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {m n P J Q c y d : M.Domain}
    (hP : Forest M C.omega m P) (hn : M.mem n C.omega)
    (hJ : ColumnEmbedding M m n J) (hQ : ForestTransport M m P J Q)
    (hcy : MemPair M J c y) (hD : Depth M C m P c d) : Depth M C n Q y d := by
  obtain ⟨hd,q,hq,len,hLen,f,_,hNo,hPath,hs⟩ := hD
  obtain ⟨x,hx,hqx⟩ := hJ.graph.total q hq
  obtain ⟨g,hG⟩ := hPath.transport_d hM hJ.graph hQ hqx hcy
  exact ⟨hd,x,hx,len,hLen,g,hG.sequence_member_d hM hC hn,
    (transported_no_parent_iff_d hM hC hP hJ hQ hqx).mpr hNo,hG,hs⟩

theorem transported_depth_iff_d {M : SetTheory.Structure.{u}} (hM : M.Models KP1Y.theory)
    {C : ExpressionData M.Domain} (hC : C.Valid M) {m n P J Q c y d : M.Domain}
    (hP : Forest M C.omega m P) (hTarget : Forest M C.omega n Q)
    (hJ : ColumnEmbedding M m n J) (hQ : ForestTransport M m P J Q) (hcy : MemPair M J c y) :
    Depth M C n Q y d ↔ Depth M C m P c d := by
  constructor
  · intro hD
    obtain ⟨e,hE⟩ := depth_exists_d hM hC hP (hJ.graph.bounds hM.1 hcy).1
    have hETarget := depth_transport_d hM hC hP hTarget.width hJ hQ hcy hE
    exact depth_unique_d hM hC hTarget hETarget hD ▸ hE
  · exact fun hD => depth_transport_d hM hC hP hTarget.width hJ hQ hcy hD

end KP1Y.OneYFinite
